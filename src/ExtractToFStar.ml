(** Extract to F* *)

open Errors
open Pure
open PureUtils
open TranslateCore
open PureToExtract
open StringUtils
module F = Format

(** A qualifier for a type definition.

    Controls whether we should use `type ...` or `and ...` (for mutually
    recursive datatypes).
 *)
type type_decl_qualif =
  | Type  (** `type t = ...` *)
  | And  (** `type t0 = ... and t1 = ...` *)
  | AssumeType  (** `assume type t` *)
  | TypeVal  (** In an fsti: `val t : Type0` *)

(** A qualifier for function definitions.

    Controls whether we should use `let ...`, `let rec ...` or `and ...`,
    or only generate a declaration with `val` or `assume val`
 *)
type fun_decl_qualif = Let | LetRec | And | Val | AssumeVal

let fun_decl_qualif_keyword (qualif : fun_decl_qualif) : string =
  match qualif with
  | Let -> "let"
  | LetRec -> "let rec"
  | And -> "and"
  | Val -> "val"
  | AssumeVal -> "assume val"

(** Small helper to compute the name of an int type *)
let fstar_int_name (int_ty : integer_type) =
  match int_ty with
  | Isize -> "isize"
  | I8 -> "i8"
  | I16 -> "i16"
  | I32 -> "i32"
  | I64 -> "i64"
  | I128 -> "i128"
  | Usize -> "usize"
  | U8 -> "u8"
  | U16 -> "u16"
  | U32 -> "u32"
  | U64 -> "u64"
  | U128 -> "u128"

(** Small helper to compute the name of a unary operation *)
let fstar_unop_name (unop : unop) : string =
  match unop with
  | Not -> "not"
  | Neg int_ty -> fstar_int_name int_ty ^ "_neg"
  | Cast _ -> raise (Failure "Unsupported")

(** Small helper to compute the name of a binary operation (note that many
    binary operations like "less than" are extracted to primitive operations,
    like `<`.
 *)
let fstar_named_binop_name (binop : E.binop) (int_ty : integer_type) : string =
  let binop =
    match binop with
    | Div -> "div"
    | Rem -> "rem"
    | Add -> "add"
    | Sub -> "sub"
    | Mul -> "mul"
    | _ -> raise (Failure "Unreachable")
  in
  fstar_int_name int_ty ^ "_" ^ binop

(** A list of keywords/identifiers used in F* and with which we want to check
    collision. *)
let fstar_keywords =
  let named_unops =
    fstar_unop_name Not
    :: List.map (fun it -> fstar_unop_name (Neg it)) T.all_signed_int_types
  in
  let named_binops = [ E.Div; Rem; Add; Sub; Mul ] in
  let named_binops =
    List.concat
      (List.map
         (fun bn ->
           List.map (fun it -> fstar_named_binop_name bn it) T.all_int_types)
         named_binops)
  in
  let misc =
    [
      "let";
      "rec";
      "in";
      "fn";
      "val";
      "int";
      "nat";
      "list";
      "FStar";
      "FStar.Mul";
      "type";
      "match";
      "with";
      "assert";
      "assert_norm";
      "Type0";
      "unit";
      "not";
      "scalar_cast";
    ]
  in
  List.concat [ named_unops; named_binops; misc ]

let fstar_assumed_adts : (assumed_ty * string) list =
  [ (State, "state"); (Result, "result"); (Option, "option"); (Vec, "vec") ]

let fstar_assumed_structs : (assumed_ty * string) list = []

let fstar_assumed_variants : (assumed_ty * VariantId.id * string) list =
  [
    (Result, result_return_id, "Return");
    (Result, result_fail_id, "Fail");
    (Option, option_some_id, "Some");
    (Option, option_none_id, "None");
  ]

let fstar_assumed_functions :
    (A.assumed_fun_id * T.RegionGroupId.id option * string) list =
  let rg0 = Some T.RegionGroupId.zero in
  [
    (Replace, None, "mem_replace_fwd");
    (Replace, rg0, "mem_replace_back");
    (VecNew, None, "vec_new");
    (VecPush, None, "vec_push_fwd") (* Shouldn't be used *);
    (VecPush, rg0, "vec_push_back");
    (VecInsert, None, "vec_insert_fwd") (* Shouldn't be used *);
    (VecInsert, rg0, "vec_insert_back");
    (VecLen, None, "vec_len");
    (VecIndex, None, "vec_index_fwd");
    (VecIndex, rg0, "vec_index_back") (* shouldn't be used *);
    (VecIndexMut, None, "vec_index_mut_fwd");
    (VecIndexMut, rg0, "vec_index_mut_back");
  ]

let fstar_names_map_init =
  {
    keywords = fstar_keywords;
    assumed_adts = fstar_assumed_adts;
    assumed_structs = fstar_assumed_structs;
    assumed_variants = fstar_assumed_variants;
    assumed_functions = fstar_assumed_functions;
  }

let fstar_extract_unop (extract_expr : bool -> texpression -> unit)
    (fmt : F.formatter) (inside : bool) (unop : unop) (arg : texpression) : unit
    =
  match unop with
  | Not | Neg _ ->
      let unop = fstar_unop_name unop in
      if inside then F.pp_print_string fmt "(";
      F.pp_print_string fmt unop;
      F.pp_print_space fmt ();
      extract_expr true arg;
      if inside then F.pp_print_string fmt ")"
  | Cast (src, tgt) ->
      (* The source type is an implicit parameter *)
      if inside then F.pp_print_string fmt "(";
      F.pp_print_string fmt "scalar_cast";
      F.pp_print_space fmt ();
      F.pp_print_string fmt
        (StringUtils.capitalize_first_letter
           (PrintPure.integer_type_to_string src));
      F.pp_print_space fmt ();
      F.pp_print_string fmt
        (StringUtils.capitalize_first_letter
           (PrintPure.integer_type_to_string tgt));
      F.pp_print_space fmt ();
      extract_expr true arg;
      if inside then F.pp_print_string fmt ")"

let fstar_extract_binop (extract_expr : bool -> texpression -> unit)
    (fmt : F.formatter) (inside : bool) (binop : E.binop)
    (int_ty : integer_type) (arg0 : texpression) (arg1 : texpression) : unit =
  if inside then F.pp_print_string fmt "(";
  (* Some binary operations have a special treatment *)
  (match binop with
  | Eq | Lt | Le | Ne | Ge | Gt ->
      let binop =
        match binop with
        | Eq -> "="
        | Lt -> "<"
        | Le -> "<="
        | Ne -> "<>"
        | Ge -> ">="
        | Gt -> ">"
        | _ -> raise (Failure "Unreachable")
      in
      extract_expr false arg0;
      F.pp_print_space fmt ();
      F.pp_print_string fmt binop;
      F.pp_print_space fmt ();
      extract_expr false arg1
  | Div | Rem | Add | Sub | Mul ->
      let binop = fstar_named_binop_name binop int_ty in
      F.pp_print_string fmt binop;
      F.pp_print_space fmt ();
      extract_expr false arg0;
      F.pp_print_space fmt ();
      extract_expr false arg1
  | BitXor | BitAnd | BitOr | Shl | Shr -> raise Unimplemented);
  if inside then F.pp_print_string fmt ")"

(**
 * [ctx]: we use the context to lookup type definitions, to retrieve type names.
 * This is used to compute variable names, when they have no basenames: in this
 * case we use the first letter of the type name.
 *
 * [variant_concatenate_type_name]: if true, add the type name as a prefix
 * to the variant names.
 * Ex.:
 * In Rust:
 *   ```
 *   enum List = {
 *     Cons(u32, Box<List>),x
 *     Nil,
 *   }
 *   ```
 *
 * F*, if option activated:
 *   ```
 *   type list =
 *   | ListCons : u32 -> list -> list
 *   | ListNil : list
 *   ```
 *
 * F*, if option not activated:
 *   ```
 *   type list =
 *   | Cons : u32 -> list -> list
 *   | Nil : list
 *   ```
 *
 * Rk.: this should be true by default, because in Rust all the variant names
 * are actively uniquely identifier by the type name `List::Cons(...)`, while
 * in other languages it is not necessarily the case, and thus clashes can mess
 * up type checking. Note that some languages actually forbids the name clashes
 * (it is the case of F* ).
 *)
let mk_formatter (ctx : trans_ctx) (crate_name : string)
    (variant_concatenate_type_name : bool) : formatter =
  let int_name = fstar_int_name in

  (* Prepare a name.
   * The first id elem is always the crate: if it is the local crate,
   * we remove it.
   * We also remove all the disambiguators, then convert everything to strings.
   * **Rmk:** because we remove the disambiguators, there may be name collisions
   * (which is ok, because we check for name collisions and fail if there is any).
   *)
  let get_name (name : name) : string list =
    (* Rmk.: initially we only filtered the disambiguators equal to 0 *)
    let name = Names.filter_disambiguators name in
    match name with
    | Ident crate :: name ->
        let name = if crate = crate_name then name else Ident crate :: name in
        let name =
          List.map
            (function
              | Names.Ident s -> s
              | Disambiguator d -> Names.Disambiguator.to_string d)
            name
        in
        name
    | _ ->
        raise (Failure ("Unexpected name shape: " ^ Print.name_to_string name))
  in
  let get_type_name = get_name in
  let type_name_to_camel_case name =
    let name = get_type_name name in
    let name = List.map to_camel_case name in
    String.concat "" name
  in
  let type_name_to_snake_case name =
    let name = get_type_name name in
    let name = List.map to_snake_case name in
    String.concat "_" name
  in
  let type_name name = type_name_to_snake_case name ^ "_t" in
  let field_name (def_name : name) (field_id : FieldId.id)
      (field_name : string option) : string =
    let def_name = type_name_to_snake_case def_name ^ "_" in
    match field_name with
    | Some field_name -> def_name ^ field_name
    | None -> def_name ^ FieldId.to_string field_id
  in
  let variant_name (def_name : name) (variant : string) : string =
    let variant = to_camel_case variant in
    if variant_concatenate_type_name then
      type_name_to_camel_case def_name ^ variant
    else variant
  in
  let struct_constructor (basename : name) : string =
    let tname = type_name basename in
    "Mk" ^ tname
  in
  let get_fun_name = get_name in
  let fun_name_to_snake_case (fname : fun_name) : string =
    let fname = get_fun_name fname in
    (* Converting to snake case should be a no-op, but it doesn't cost much *)
    let fname = List.map to_snake_case fname in
    (* Concatenate the elements *)
    String.concat "_" fname
  in
  let fun_name (_fid : A.fun_id) (fname : fun_name) (is_global : bool) (num_rgs : int)
      (rg : region_group_info option) (filter_info : bool * int) : string =
    let fname = fun_name_to_snake_case fname in
    (* Compute the suffix *)
    let suffix = default_fun_suffix is_global num_rgs rg filter_info in
    (* Concatenate *)
    fname ^ suffix
  in

  let decreases_clause_name (_fid : A.FunDeclId.id) (fname : fun_name) : string =
    let fname = fun_name_to_snake_case fname in
    (* Compute the suffix *)
    let suffix = "_decreases" in
    (* Concatenate *)
    fname ^ suffix
  in

  let var_basename (_varset : StringSet.t) (basename : string option) (ty : ty)
      : string =
    (* If there is a basename, we use it *)
    match basename with
    | Some basename ->
        (* This should be a no-op *)
        to_snake_case basename
    | None -> (
        (* No basename: we use the first letter of the type *)
        match ty with
        | Adt (type_id, tys) -> (
            match type_id with
            | Tuple ->
                (* The "pair" case is frequent enough to have its special treatment *)
                if List.length tys = 2 then "p" else "t"
            | Assumed Result -> "r"
            | Assumed Option -> "opt"
            | Assumed Vec -> "v"
            | Assumed State -> "st"
            | AdtId adt_id ->
                let def =
                  TypeDeclId.Map.find adt_id ctx.type_context.type_decls
                in
                (* We do the following:
                 * - compute the type name, and retrieve the last ident
                 * - convert this to snake case
                 * - take the first letter of every "letter group"
                 * Ex.: ["hashmap"; "HashMap"] ~~> "HashMap" -> "hash_map" -> "hm"
                 *)
                (* Thename shouldn't be empty, and its last element should
                 * be an ident *)
                let cl = List.nth def.name (List.length def.name - 1) in
                let cl = to_snake_case (Names.as_ident cl) in
                let cl = String.split_on_char '_' cl in
                let cl = List.filter (fun s -> String.length s > 0) cl in
                assert (List.length cl > 0);
                let cl = List.map (fun s -> s.[0]) cl in
                StringUtils.string_of_chars cl)
        | TypeVar _ -> "x" (* lacking imagination here... *)
        | Bool -> "b"
        | Char -> "c"
        | Integer _ -> "i"
        | Str -> "s"
        | Arrow _ -> "f"
        | Array _ | Slice _ -> raise Unimplemented)
  in
  let type_var_basename (_varset : StringSet.t) (basename : string) : string =
    (* This is *not* a no-op: type variables in Rust often start with
     * a capital letter *)
    to_snake_case basename
  in
  let append_index (basename : string) (i : int) : string =
    basename ^ string_of_int i
  in

  let extract_constant_value (fmt : F.formatter) (_inside : bool)
      (cv : constant_value) : unit =
    match cv with
    | Scalar sv -> F.pp_print_string fmt (Z.to_string sv.V.value)
    | Bool b ->
        let b = if b then "true" else "false" in
        F.pp_print_string fmt b
    | Char c -> F.pp_print_string fmt ("'" ^ String.make 1 c ^ "'")
    | String s ->
        (* We need to replace all the line breaks *)
        let s =
          StringUtils.map
            (fun c -> if c = '\n' then "\n" else String.make 1 c)
            s
        in
        F.pp_print_string fmt ("\"" ^ s ^ "\"")
  in
  {
    bool_name = "bool";
    char_name = "char";
    int_name;
    str_name = "string";
    field_name;
    variant_name;
    struct_constructor;
    type_name;
    fun_name;
    decreases_clause_name;
    var_basename;
    type_var_basename;
    append_index;
    extract_constant_value;
    extract_unop = fstar_extract_unop;
    extract_binop = fstar_extract_binop;
  }

(** [inside] constrols whether we should add parentheses or not around type
    application (if `true` we add parentheses).
 *)
let rec extract_ty (ctx : extraction_ctx) (fmt : F.formatter) (inside : bool)
    (ty : ty) : unit =
  match ty with
  | Adt (type_id, tys) -> (
      match type_id with
      | Tuple ->
          (* This is a bit annoying, but in F* `()` is not the unit type:
           * we have to write `unit`... *)
          if tys = [] then F.pp_print_string fmt "unit"
          else (
            F.pp_print_string fmt "(";
            Collections.List.iter_link
              (fun () ->
                F.pp_print_space fmt ();
                F.pp_print_string fmt "&";
                F.pp_print_space fmt ())
              (extract_ty ctx fmt true) tys;
            F.pp_print_string fmt ")")
      | AdtId _ | Assumed _ ->
          let print_paren = inside && tys <> [] in
          if print_paren then F.pp_print_string fmt "(";
          F.pp_print_string fmt (ctx_get_type type_id ctx);
          if tys <> [] then F.pp_print_space fmt ();
          Collections.List.iter_link (F.pp_print_space fmt)
            (extract_ty ctx fmt true) tys;
          if print_paren then F.pp_print_string fmt ")")
  | TypeVar vid -> F.pp_print_string fmt (ctx_get_type_var vid ctx)
  | Bool -> F.pp_print_string fmt ctx.fmt.bool_name
  | Char -> F.pp_print_string fmt ctx.fmt.char_name
  | Integer int_ty -> F.pp_print_string fmt (ctx.fmt.int_name int_ty)
  | Str -> F.pp_print_string fmt ctx.fmt.str_name
  | Arrow (arg_ty, ret_ty) ->
      if inside then F.pp_print_string fmt "(";
      extract_ty ctx fmt false arg_ty;
      F.pp_print_space fmt ();
      F.pp_print_string fmt "->";
      F.pp_print_space fmt ();
      extract_ty ctx fmt false ret_ty;
      if inside then F.pp_print_string fmt ")"
  | Array _ | Slice _ -> raise Unimplemented

(** Compute the names for all the top-level identifiers used in a type
    definition (type name, variant names, field names, etc. but not type
    parameters).
    
    We need to do this preemptively, beforce extracting any definition,
    because of recursive definitions.
 *)
let extract_type_decl_register_names (ctx : extraction_ctx) (def : type_decl) :
    extraction_ctx =
  (* Compute and register the type def name *)
  let ctx = ctx_add_type_decl def ctx in
  (* Compute and register:
   * - the variant names, if this is an enumeration
   * - the field names, if this is a structure
   *)
  let ctx =
    match def.kind with
    | Struct fields ->
        (* Add the fields *)
        let ctx =
          fst
            (ctx_add_fields def (FieldId.mapi (fun id f -> (id, f)) fields) ctx)
        in
        (* Add the constructor name *)
        fst (ctx_add_struct def ctx)
    | Enum variants ->
        fst
          (ctx_add_variants def
             (VariantId.mapi (fun id v -> (id, v)) variants)
             ctx)
    | Opaque ->
        (* Nothing to do *)
        ctx
  in
  (* Return *)
  ctx

let extract_type_decl_struct_body (ctx : extraction_ctx) (fmt : F.formatter)
    (def : type_decl) (fields : field list) : unit =
  (* We want to generate a definition which looks like this:
   * ```
   * type t = { x : int; y : bool; }
   * ```
   *
   * If there isn't enough space on one line:
   * ```
   * type t =
   * {
   *   x : int; y : bool;
   * }
   * ```
   * 
   * And if there is even less space:
   * ```
   * type t =
   * {
   *   x : int;
   *   y : bool;
   * }
   * ```
   *
   * Also, in case there are no fields, we need to define the type as `unit`
   * (`type t = {}` doesn't work in F* ).
   *)
  (* Note that we already printed: `type t =` *)
  if fields = [] then (
    F.pp_print_space fmt ();
    F.pp_print_string fmt "unit")
  else (
    F.pp_print_space fmt ();
    F.pp_print_string fmt "{";
    F.pp_print_break fmt 1 ctx.indent_incr;
    (* The body itself *)
    F.pp_open_hvbox fmt 0;
    (* Print the fields *)
    let print_field (field_id : FieldId.id) (f : field) : unit =
      let field_name = ctx_get_field (AdtId def.def_id) field_id ctx in
      F.pp_open_box fmt ctx.indent_incr;
      F.pp_print_string fmt field_name;
      F.pp_print_space fmt ();
      F.pp_print_string fmt ":";
      F.pp_print_space fmt ();
      extract_ty ctx fmt false f.field_ty;
      F.pp_print_string fmt ";";
      F.pp_close_box fmt ()
    in
    let fields = FieldId.mapi (fun fid f -> (fid, f)) fields in
    Collections.List.iter_link (F.pp_print_space fmt)
      (fun (fid, f) -> print_field fid f)
      fields;
    (* Close *)
    F.pp_close_box fmt ();
    F.pp_print_space fmt ();
    F.pp_print_string fmt "}")

let extract_type_decl_enum_body (ctx : extraction_ctx) (fmt : F.formatter)
    (def : type_decl) (def_name : string) (type_params : string list)
    (variants : variant list) : unit =
  (* We want to generate a definition which looks like this:
   * ```
   * type list a = | Cons : a -> list a -> list a | Nil : list a
   * ```
   *
   * If there isn't enough space on one line:
   * ```
   * type s =
   * | Cons : a -> list a -> list a
   * | Nil : list a
   * ```
   *
   * And if we need to write the type of a variant on several lines:
   * ```
   * type s =
   * | Cons :
   *   a ->
   *   list a ->
   *   list a
   * | Nil : list a
   * ```
   *
   * Finally, it is possible to give names to the variant fields in Rust.
   * In this situation, we generate a definition like this:
   * ```
   * type s =
   * | Cons : hd:a -> tl:list a -> list a
   * | Nil : list a
   * ```
   *
   * Note that we already printed: `type s =`
   *)
  (* Print the variants *)
  let print_variant (variant_id : VariantId.id) (variant : variant) : unit =
    let variant_name = ctx_get_variant (AdtId def.def_id) variant_id ctx in
    F.pp_print_space fmt ();
    F.pp_open_hvbox fmt ctx.indent_incr;
    (* variant box *)
    (* `| Cons :`
     * Note that we really don't want any break above so we print everything
     * at once. *)
    F.pp_print_string fmt ("| " ^ variant_name ^ " :");
    F.pp_print_space fmt ();
    let print_field (fid : FieldId.id) (f : field) (ctx : extraction_ctx) :
        extraction_ctx =
      (* Open the field box *)
      F.pp_open_box fmt ctx.indent_incr;
      (* Print the field names
       * `  x :`
       * Note that when printing fields, we register the field names as
       * *variables*: they don't need to be unique at the top level. *)
      let ctx =
        match f.field_name with
        | None -> ctx
        | Some field_name ->
            let var_id = VarId.of_int (FieldId.to_int fid) in
            let field_name =
              ctx.fmt.var_basename ctx.names_map.names_set (Some field_name)
                f.field_ty
            in
            let ctx, field_name = ctx_add_var field_name var_id ctx in
            F.pp_print_string fmt (field_name ^ " :");
            F.pp_print_space fmt ();
            ctx
      in
      (* Print the field type *)
      extract_ty ctx fmt false f.field_ty;
      (* Print the arrow `->`*)
      F.pp_print_space fmt ();
      F.pp_print_string fmt "->";
      (* Close the field box *)
      F.pp_close_box fmt ();
      F.pp_print_space fmt ();
      (* Return *)
      ctx
    in
    (* Print the fields *)
    let fields = FieldId.mapi (fun fid f -> (fid, f)) variant.fields in
    let _ =
      List.fold_left (fun ctx (fid, f) -> print_field fid f ctx) ctx fields
    in
    (* Print the final type *)
    F.pp_open_hovbox fmt 0;
    F.pp_print_string fmt def_name;
    List.iter
      (fun type_param ->
        F.pp_print_space fmt ();
        F.pp_print_string fmt type_param)
      type_params;
    F.pp_close_box fmt ();
    (* Close the variant box *)
    F.pp_close_box fmt ()
  in
  (* Print the variants *)
  let variants = VariantId.mapi (fun vid v -> (vid, v)) variants in
  List.iter (fun (vid, v) -> print_variant vid v) variants

(** Extract a type declaration.

    Note that all the names used for extraction should already have been
    registered.
 *)
let extract_type_decl (ctx : extraction_ctx) (fmt : F.formatter)
    (qualif : type_decl_qualif) (def : type_decl) : unit =
  (* Retrieve the definition name *)
  let def_name = ctx_get_local_type def.def_id ctx in
  (* Add the type params - note that we need those bindings only for the
   * body translation (they are not top-level) *)
  let ctx_body, type_params = ctx_add_type_params def.type_params ctx in
  (* Add a break before *)
  F.pp_print_break fmt 0 0;
  (* Print a comment to link the extracted type to its original rust definition *)
  F.pp_print_string fmt ("(** [" ^ Print.name_to_string def.name ^ "] *)");
  F.pp_print_space fmt ();
  (* Open a box for the definition, so that whenever possible it gets printed on
   * one line *)
  F.pp_open_hvbox fmt 0;
  (* Open a box for "type TYPE_NAME (TYPE_PARAMS) =" *)
  F.pp_open_hovbox fmt ctx.indent_incr;
  (* > "type TYPE_NAME" *)
  let extract_body, qualif =
    match qualif with
    | Type -> (true, "type")
    | And -> (true, "and")
    | AssumeType -> (false, "assume type")
    | TypeVal -> (false, "val")
  in
  F.pp_print_string fmt (qualif ^ " " ^ def_name);
  (* Print the type parameters *)
  if def.type_params <> [] then (
    F.pp_print_space fmt ();
    F.pp_print_string fmt "(";
    List.iter
      (fun (p : type_var) ->
        let pname = ctx_get_type_var p.index ctx_body in
        F.pp_print_string fmt pname;
        F.pp_print_space fmt ())
      def.type_params;
    F.pp_print_string fmt ":";
    F.pp_print_space fmt ();
    F.pp_print_string fmt "Type0)");
  (* Print the "=" if we extract the body*)
  if extract_body then (
    F.pp_print_space fmt ();
    F.pp_print_string fmt "=")
  else (
    (* Otherwise print ": Type0" *)
    F.pp_print_space fmt ();
    F.pp_print_string fmt ":";
    F.pp_print_space fmt ();
    F.pp_print_string fmt "Type0");
  (* Close the box for "type TYPE_NAME (TYPE_PARAMS) =" *)
  F.pp_close_box fmt ();
  (if extract_body then
   match def.kind with
   | Struct fields -> extract_type_decl_struct_body ctx_body fmt def fields
   | Enum variants ->
       extract_type_decl_enum_body ctx_body fmt def def_name type_params
         variants
   | Opaque -> raise (Failure "Unreachable"));
  (* Close the box for the definition *)
  F.pp_close_box fmt ();
  (* Add breaks to insert new lines between definitions *)
  F.pp_print_break fmt 0 0

(** Extract the state type declaration. *)
let extract_state_type (fmt : F.formatter) (ctx : extraction_ctx)
    (qualif : type_decl_qualif) : unit =
  (* Add a break before *)
  F.pp_print_break fmt 0 0;
  (* Print a comment  *)
  F.pp_print_string fmt "(** The state type used in the state-error monad *)";
  F.pp_print_space fmt ();
  (* Open a box for the definition, so that whenever possible it gets printed on
   * one line *)
  F.pp_open_hvbox fmt 0;
  (* Retrieve the name *)
  let state_name = ctx_get_assumed_type State ctx in
  (* The qualif should be `AssumeType` or `TypeVal` *)
  (match qualif with
  | Type | And -> raise (Failure "Unexpected")
  | AssumeType ->
      F.pp_print_string fmt "assume";
      F.pp_print_space fmt ();
      F.pp_print_string fmt "type";
      F.pp_print_space fmt ();
      F.pp_print_string fmt state_name;
      F.pp_print_space fmt ();
      F.pp_print_string fmt ":";
      F.pp_print_space fmt ();
      F.pp_print_string fmt "Type0"
  | TypeVal ->
      F.pp_print_string fmt "val";
      F.pp_print_space fmt ();
      F.pp_print_string fmt state_name;
      F.pp_print_space fmt ();
      F.pp_print_string fmt ":";
      F.pp_print_space fmt ();
      F.pp_print_string fmt "Type0");
  (* Close the box for the definition *)
  F.pp_close_box fmt ();
  (* Add breaks to insert new lines between definitions *)
  F.pp_print_break fmt 0 0

(** Compute the names for all the pure functions generated from a rust function
    (forward function and backward functions).
 *)
let extract_fun_decl_register_names (ctx : extraction_ctx) (keep_fwd : bool)
    (has_decreases_clause : bool) (def : pure_fun_translation) : extraction_ctx
    =
  let fwd, back_ls = def in
  (* Register the decrease clause, if necessary *)
  let ctx =
    if has_decreases_clause then ctx_add_decrases_clause fwd ctx else ctx
  in
  (* Register the forward function name *)
  let ctx = ctx_add_fun_decl (keep_fwd, def) fwd ctx in
  (* Register the backward functions' names *)
  let ctx =
    List.fold_left
      (fun ctx back -> ctx_add_fun_decl (keep_fwd, def) back ctx)
      ctx back_ls
  in
  (* Return *)
  ctx

(** The following function factorizes the extraction of ADT values.

    Note that patterns can introduce new variables: we thus return an extraction
    context updated with new bindings.
    
    TODO: we don't need something very generic anymore
 *)
let extract_adt_g_value
    (extract_value : extraction_ctx -> bool -> 'v -> extraction_ctx)
    (fmt : F.formatter) (ctx : extraction_ctx) (inside : bool)
    (variant_id : VariantId.id option) (field_values : 'v list) (ty : ty) :
    extraction_ctx =
  match ty with
  | Adt (Tuple, _) ->
      (* Tuple *)
      F.pp_print_string fmt "(";
      let ctx =
        Collections.List.fold_left_link
          (fun () ->
            F.pp_print_string fmt ",";
            F.pp_print_space fmt ())
          (fun ctx v -> extract_value ctx false v)
          ctx field_values
      in
      F.pp_print_string fmt ")";
      ctx
  | Adt (adt_id, _) ->
      (* "Regular" ADT *)
      (* We print something of the form: `Cons field0 ... fieldn`.
       * We could update the code to print something of the form:
       * `{ field0=...; ...; fieldn=...; }` in case of structures.
       *)
      let cons =
        match variant_id with
        | Some vid -> ctx_get_variant adt_id vid ctx
        | None -> ctx_get_struct adt_id ctx
      in
      if inside && field_values <> [] then F.pp_print_string fmt "(";
      F.pp_print_string fmt cons;
      let ctx =
        Collections.List.fold_left
          (fun ctx v ->
            F.pp_print_space fmt ();
            extract_value ctx true v)
          ctx field_values
      in
      if inside && field_values <> [] then F.pp_print_string fmt ")";
      ctx
  | _ -> raise (Failure "Inconsistent typed value")

(** [inside]: see [extract_ty].

    As an pattern can introduce new variables, we return an extraction context
    updated with new bindings.
 *)
let rec extract_typed_pattern (ctx : extraction_ctx) (fmt : F.formatter)
    (inside : bool) (v : typed_pattern) : extraction_ctx =
  match v.value with
  | PatConcrete cv ->
      ctx.fmt.extract_constant_value fmt inside cv;
      ctx
  | PatVar (v, _) ->
      let vname =
        ctx.fmt.var_basename ctx.names_map.names_set v.basename v.ty
      in
      let ctx, vname = ctx_add_var vname v.id ctx in
      F.pp_print_string fmt vname;
      ctx
  | PatDummy ->
      F.pp_print_string fmt "_";
      ctx
  | PatAdt av ->
      let extract_value ctx inside v = extract_typed_pattern ctx fmt inside v in
      extract_adt_g_value extract_value fmt ctx inside av.variant_id
        av.field_values v.ty

(** [inside]: controls the introduction of parentheses. See [extract_ty]
    
    TODO: replace the formatting boolean [inside] with something more general?
    Also, it seems we don't really use it...
    Cases to consider:
    - right-expression in a let: `let x = re in _` (never parentheses?)
    - next expression in a let:  `let x = _ in next_e` (never parentheses?)
    - application argument: `f (exp)`
    - match/if scrutinee: `if exp then _ else _`/`match exp | _ -> _`
 *)
let rec extract_texpression (ctx : extraction_ctx) (fmt : F.formatter)
    (inside : bool) (e : texpression) : unit =
  match e.e with
  | Var var_id ->
      let var_name = ctx_get_var var_id ctx in
      F.pp_print_string fmt var_name
  | Const cv -> ctx.fmt.extract_constant_value fmt inside cv
  | App _ ->
      let app, args = destruct_apps e in
      extract_App ctx fmt inside app args
  | Abs _ ->
      let xl, e = destruct_abs_list e in
      extract_Abs ctx fmt inside xl e
  | Qualif _ ->
      (* We use the app case *)
      extract_App ctx fmt inside e []
  | Let (monadic, lv, re, next_e) ->
      extract_Let ctx fmt inside monadic lv re next_e
  | Switch (scrut, body) -> extract_Switch ctx fmt inside scrut body
  | Meta (_, e) -> extract_texpression ctx fmt inside e

and extract_App (ctx : extraction_ctx) (fmt : F.formatter) (inside : bool)
    (app : texpression) (args : texpression list) : unit =
  (* We don't do the same thing if the app is a top-level identifier (function,
   * ADT constructor...) or a "regular" expression *)
  match app.e with
  | Qualif qualif -> (
      (* Top-level qualifier *)
      match qualif.id with
      | Func fun_id ->
          extract_function_call ctx fmt inside fun_id qualif.type_args args
      | Global global_id ->
          failwith "TODO ExtractToFStar.ml:911"
          (* Previous code:
          let fid = A.global_to_fun_id ctx.trans_ctx.fun_context.gid_conv global_id in
          let fun_id = Regular (A.Regular fid, None) in
          extract_function_call ctx fmt inside fun_id qualif.type_args args
          *)
      | AdtCons adt_cons_id ->
          extract_adt_cons ctx fmt inside adt_cons_id qualif.type_args args
      | Proj proj ->
          extract_field_projector ctx fmt inside app proj qualif.type_args args
    )
  | _ ->
      (* "Regular" expression *)
      (* Open parentheses *)
      if inside then F.pp_print_string fmt "(";
      (* Open a box for the application *)
      F.pp_open_hovbox fmt ctx.indent_incr;
      (* Print the app expression *)
      let app_inside = (inside && args = []) || args <> [] in
      extract_texpression ctx fmt app_inside app;
      (* Print the arguments *)
      List.iter
        (fun ve ->
          F.pp_print_space fmt ();
          extract_texpression ctx fmt true ve)
        args;
      (* Close the box for the application *)
      F.pp_close_box fmt ();
      (* Close parentheses *)
      if inside then F.pp_print_string fmt ")"

(** Subcase of the app case: function call *)
and extract_function_call (ctx : extraction_ctx) (fmt : F.formatter)
    (inside : bool) (fid : fun_id) (type_args : ty list)
    (args : texpression list) : unit =
  match (fid, args) with
  | Unop unop, [ arg ] ->
      (* A unop can have *at most* one argument (the result can't be a function!).
       * Note that the way we generate the translation, we shouldn't get the
       * case where we have no argument (all functions are fully instantiated,
       * and no AST transformation introduces partial calls). *)
      ctx.fmt.extract_unop (extract_texpression ctx fmt) fmt inside unop arg
  | Binop (binop, int_ty), [ arg0; arg1 ] ->
      (* Number of arguments: similar to unop *)
      ctx.fmt.extract_binop
        (extract_texpression ctx fmt)
        fmt inside binop int_ty arg0 arg1
  | Regular (fun_id, rg_id), _ ->
      if inside then F.pp_print_string fmt "(";
      (* Open a box for the function call *)
      F.pp_open_hovbox fmt ctx.indent_incr;
      (* Print the function name *)
      let fun_name = ctx_get_function fun_id rg_id ctx in
      F.pp_print_string fmt fun_name;
      (* Print the type parameters *)
      List.iter
        (fun ty ->
          F.pp_print_space fmt ();
          extract_ty ctx fmt true ty)
        type_args;
      (* Print the arguments *)
      List.iter
        (fun ve ->
          F.pp_print_space fmt ();
          extract_texpression ctx fmt true ve)
        args;
      (* Close the box for the function call *)
      F.pp_close_box fmt ();
      (* Return *)
      if inside then F.pp_print_string fmt ")"
  | _ ->
      raise
        (Failure
           ("Unreachable:\n" ^ "Function: " ^ show_fun_id fid
          ^ ",\nNumber of arguments: "
           ^ string_of_int (List.length args)
           ^ ",\nArguments: "
           ^ String.concat " " (List.map show_texpression args)))

(** Subcase of the app case: ADT constructor *)
and extract_adt_cons (ctx : extraction_ctx) (fmt : F.formatter) (inside : bool)
    (adt_cons : adt_cons_id) (type_args : ty list) (args : texpression list) :
    unit =
  match adt_cons.adt_id with
  | Tuple ->
      (* Tuple *)
      (* For now, we only support fully applied tuple constructors *)
      assert (List.length type_args = List.length args);
      F.pp_print_string fmt "(";
      Collections.List.iter_link
        (fun () ->
          F.pp_print_string fmt ",";
          F.pp_print_space fmt ())
        (fun v -> extract_texpression ctx fmt false v)
        args;
      F.pp_print_string fmt ")"
  | _ ->
      (* "Regular" ADT *)
      (* We print something of the form: `Cons field0 ... fieldn`.
       * We could update the code to print something of the form:
       * `{ field0=...; ...; fieldn=...; }` in case of fully
       * applied structure constructors.
       *)
      let cons =
        match adt_cons.variant_id with
        | Some vid -> ctx_get_variant adt_cons.adt_id vid ctx
        | None -> ctx_get_struct adt_cons.adt_id ctx
      in
      let use_parentheses = inside && args <> [] in
      if use_parentheses then F.pp_print_string fmt "(";
      F.pp_print_string fmt cons;
      Collections.List.iter
        (fun v ->
          F.pp_print_space fmt ();
          extract_texpression ctx fmt true v)
        args;
      if use_parentheses then F.pp_print_string fmt ")"

(** Subcase of the app case: ADT field projector.  *)
and extract_field_projector (ctx : extraction_ctx) (fmt : F.formatter)
    (inside : bool) (original_app : texpression) (proj : projection)
    (_proj_type_params : ty list) (args : texpression list) : unit =
  (* We isolate the first argument (if there is), in order to pretty print the
   * projection (`x.field` instead of `MkAdt?.field x` *)
  match args with
  | [ arg ] ->
      (* Exactly one argument: pretty-print *)
      let field_name = ctx_get_field proj.adt_id proj.field_id ctx in
      (* Open a box *)
      F.pp_open_hovbox fmt ctx.indent_incr;
      (* Extract the expression *)
      extract_texpression ctx fmt true arg;
      (* We allow to break where the "." appears *)
      F.pp_print_break fmt 0 0;
      F.pp_print_string fmt ".";
      F.pp_print_string fmt field_name;
      (* Close the box *)
      F.pp_close_box fmt ()
  | arg :: args ->
      (* Call extract_App again, but in such a way that the first argument is
       * isolated *)
      extract_App ctx fmt inside (mk_app original_app arg) args
  | [] ->
      (* No argument: shouldn't happen *)
      raise (Failure "Unreachable")

and extract_Abs (ctx : extraction_ctx) (fmt : F.formatter) (inside : bool)
    (xl : typed_pattern list) (e : texpression) : unit =
  (* Open a box for the abs expression *)
  F.pp_open_hovbox fmt ctx.indent_incr;
  (* Open parentheses *)
  if inside then F.pp_print_string fmt "(";
  (* Print the lambda - note that there should always be at least one variable *)
  assert (xl <> []);
  F.pp_print_string fmt "fun";
  let ctx =
    List.fold_left
      (fun ctx x ->
        F.pp_print_space fmt ();
        extract_typed_pattern ctx fmt true x)
      ctx xl
  in
  F.pp_print_space fmt ();
  F.pp_print_string fmt "->";
  F.pp_print_space fmt ();
  (* Print the body *)
  extract_texpression ctx fmt false e;
  (* Close parentheses *)
  if inside then F.pp_print_string fmt ")";
  (* Close the box for the abs expression *)
  F.pp_close_box fmt ()

and extract_Let (ctx : extraction_ctx) (fmt : F.formatter) (inside : bool)
    (monadic : bool) (lv : typed_pattern) (re : texpression)
    (next_e : texpression) : unit =
  (* Open a box for the whole expression *)
  F.pp_open_hvbox fmt 0;
  (* Open parentheses *)
  if inside then F.pp_print_string fmt "(";
  (* Open a box for the let-binding *)
  F.pp_open_hovbox fmt ctx.indent_incr;
  let ctx =
    if monadic then (
      (* Note that in F*, the left value of a monadic let-binding can only be
       * a variable *)
      let ctx = extract_typed_pattern ctx fmt true lv in
      F.pp_print_space fmt ();
      F.pp_print_string fmt "<--";
      F.pp_print_space fmt ();
      extract_texpression ctx fmt false re;
      F.pp_print_string fmt ";";
      ctx)
    else (
      F.pp_print_string fmt "let";
      F.pp_print_space fmt ();
      let ctx = extract_typed_pattern ctx fmt true lv in
      F.pp_print_space fmt ();
      F.pp_print_string fmt "=";
      F.pp_print_space fmt ();
      extract_texpression ctx fmt false re;
      F.pp_print_space fmt ();
      F.pp_print_string fmt "in";
      ctx)
  in
  (* Close the box for the let-binding *)
  F.pp_close_box fmt ();
  (* Print the next expression *)
  F.pp_print_space fmt ();
  extract_texpression ctx fmt false next_e;
  (* Close parentheses *)
  if inside then F.pp_print_string fmt ")";
  (* Close the box for the whole expression *)
  F.pp_close_box fmt ()

and extract_Switch (ctx : extraction_ctx) (fmt : F.formatter) (inside : bool)
    (scrut : texpression) (body : switch_body) : unit =
  (* Open a box for the whole expression *)
  F.pp_open_hvbox fmt 0;
  (* Open parentheses *)
  if inside then F.pp_print_string fmt "(";
  (* Extract the switch *)
  (match body with
  | If (e_then, e_else) ->
      (* Open a box for the `if` *)
      F.pp_open_hovbox fmt ctx.indent_incr;
      F.pp_print_string fmt "if";
      F.pp_print_space fmt ();
      let scrut_inside = PureUtils.let_group_requires_parentheses scrut in
      extract_texpression ctx fmt scrut_inside scrut;
      (* Close the box for the `if` *)
      F.pp_close_box fmt ();
      (* Extract the branches *)
      let extract_branch (is_then : bool) (e_branch : texpression) : unit =
        F.pp_print_space fmt ();
        (* Open a box for the then/else+branch *)
        F.pp_open_hovbox fmt ctx.indent_incr;
        let then_or_else = if is_then then "then" else "else" in
        F.pp_print_string fmt then_or_else;
        F.pp_print_space fmt ();
        (* Open a box for the branch *)
        F.pp_open_hovbox fmt ctx.indent_incr;
        (* Print the `begin` if necessary *)
        let parenth = PureUtils.let_group_requires_parentheses e_branch in
        if parenth then (
          F.pp_print_string fmt "begin";
          F.pp_print_space fmt ());
        (* Print the branch expression *)
        extract_texpression ctx fmt false e_branch;
        (* Close the `begin ... end ` *)
        if parenth then (
          F.pp_print_space fmt ();
          F.pp_print_string fmt "end");
        (* Close the box for the branch *)
        F.pp_close_box fmt ();
        (* Close the box for the then/else+branch *)
        F.pp_close_box fmt ()
      in

      extract_branch true e_then;
      extract_branch false e_else
  | Match branches ->
      (* Open a box for the `match ... with` *)
      F.pp_open_hovbox fmt ctx.indent_incr;
      (* Print the `match ... with` *)
      F.pp_print_string fmt "begin match";
      F.pp_print_space fmt ();
      let scrut_inside = PureUtils.let_group_requires_parentheses scrut in
      extract_texpression ctx fmt scrut_inside scrut;
      F.pp_print_space fmt ();
      F.pp_print_string fmt "with";
      (* Close the box for the `match ... with` *)
      F.pp_close_box fmt ();

      (* Extract the branches *)
      let extract_branch (br : match_branch) : unit =
        F.pp_print_space fmt ();
        (* Open a box for the pattern+branch *)
        F.pp_open_hovbox fmt ctx.indent_incr;
        F.pp_print_string fmt "|";
        (* Print the pattern *)
        F.pp_print_space fmt ();
        let ctx = extract_typed_pattern ctx fmt false br.pat in
        F.pp_print_space fmt ();
        F.pp_print_string fmt "->";
        F.pp_print_space fmt ();
        (* Open a box for the branch *)
        F.pp_open_hovbox fmt ctx.indent_incr;
        (* Print the branch itself *)
        extract_texpression ctx fmt false br.branch;
        (* Close the box for the branch *)
        F.pp_close_box fmt ();
        (* Close the box for the pattern+branch *)
        F.pp_close_box fmt ()
      in

      List.iter extract_branch branches;

      (* End the match *)
      F.pp_print_space fmt ();
      F.pp_print_string fmt "end");
  (* Close parentheses *)
  if inside then F.pp_print_string fmt ")";
  (* Close the box for the whole expression *)
  F.pp_close_box fmt ()

(** A small utility to print the parameters of a function signature.

    We return two contexts:
    - the context augmented with bindings for the type parameters
    - the previous context augmented with bindings for the input values
 *)
let extract_fun_parameters (ctx : extraction_ctx) (fmt : F.formatter)
    (def : fun_decl) : extraction_ctx * extraction_ctx =
  (* Add the type parameters - note that we need those bindings only for the
   * body translation (they are not top-level) *)
  let ctx, _ = ctx_add_type_params def.signature.type_params ctx in
  (* Print the parameters - rk.: we should have filtered the functions
   * with no input parameters *)
  (* The type parameters *)
  if def.signature.type_params <> [] then (
    (* Open a box for the type parameters *)
    F.pp_open_hovbox fmt 0;
    F.pp_print_string fmt "(";
    List.iter
      (fun (p : type_var) ->
        let pname = ctx_get_type_var p.index ctx in
        F.pp_print_string fmt pname;
        F.pp_print_space fmt ())
      def.signature.type_params;
    F.pp_print_string fmt ":";
    F.pp_print_space fmt ();
    F.pp_print_string fmt "Type0)";
    (* Close the box for the type parameters *)
    F.pp_close_box fmt ();
    F.pp_print_space fmt ());
  (* The input parameters - note that doing this adds bindings to the context *)
  let ctx_body =
    match def.body with
    | None -> ctx
    | Some body ->
        List.fold_left
          (fun ctx (lv : typed_pattern) ->
            (* Open a box for the input parameter *)
            F.pp_open_hovbox fmt 0;
            F.pp_print_string fmt "(";
            let ctx = extract_typed_pattern ctx fmt false lv in
            F.pp_print_space fmt ();
            F.pp_print_string fmt ":";
            F.pp_print_space fmt ();
            extract_ty ctx fmt false lv.ty;
            F.pp_print_string fmt ")";
            (* Close the box for the input parameters *)
            F.pp_close_box fmt ();
            F.pp_print_space fmt ();
            ctx)
          ctx body.inputs_lvs
  in
  (ctx, ctx_body)

(** A small utility to print the types of the input parameters in the form:
    `u32 -> list u32 -> ...`
    (we don't print the return type of the function)
    
    This is used for opaque function declarations, in particular.
 *)
let extract_fun_input_parameters_types (ctx : extraction_ctx)
    (fmt : F.formatter) (def : fun_decl) : unit =
  let extract_param (ty : ty) : unit =
    let inside = false in
    extract_ty ctx fmt inside ty;
    F.pp_print_space fmt ();
    F.pp_print_string fmt "->";
    F.pp_print_space fmt ()
  in
  List.iter extract_param def.signature.inputs

(** Extract a decrease clause function template body.

    In order to help the user, we can generate a template for the functions
    required by the decreases clauses. We simply generate definitions of
    the following form in a separate file:
    ```
    let f_decrease (t : Type0) (x : t) : nat = admit()
    ```
    
    Where the translated functions for `f` look like this:
    ```
    let f_fwd (t : Type0) (x : t) : Tot ... (decreases (f_decrease t x)) = ...
    ```
 *)
let extract_template_decreases_clause (ctx : extraction_ctx) (fmt : F.formatter)
    (def : fun_decl) : unit =
  (* Retrieve the function name *)
  let def_name = ctx_get_decreases_clause def.def_id ctx in
  (* Add a break before *)
  F.pp_print_break fmt 0 0;
  (* Print a comment to link the extracted type to its original rust definition *)
  F.pp_print_string fmt
    ("(** [" ^ Print.fun_name_to_string def.basename ^ "]: decreases clause *)");
  F.pp_print_space fmt ();
  (* Open a box for the definition, so that whenever possible it gets printed on
   * one line *)
  F.pp_open_hvbox fmt 0;
  (* Add the `unfold` keyword *)
  F.pp_print_string fmt "unfold";
  F.pp_print_space fmt ();
  (* Open a box for "let FUN_NAME (PARAMS) : EFFECT = admit()" *)
  F.pp_open_hvbox fmt ctx.indent_incr;
  (* Open a box for "let FUN_NAME (PARAMS) : EFFECT =" *)
  F.pp_open_hovbox fmt ctx.indent_incr;
  (* > "let FUN_NAME" *)
  F.pp_print_string fmt ("let " ^ def_name);
  F.pp_print_space fmt ();
  (* Extract the parameters *)
  let _, _ = extract_fun_parameters ctx fmt def in
  F.pp_print_string fmt ":";
  (* Print the signature *)
  F.pp_print_space fmt ();
  F.pp_print_string fmt "nat";
  (* Print the "=" *)
  F.pp_print_space fmt ();
  F.pp_print_string fmt "=";
  (* Close the box for "let FUN_NAME (PARAMS) : EFFECT =" *)
  F.pp_close_box fmt ();
  F.pp_print_space fmt ();
  (* Print the "admit ()" *)
  F.pp_print_string fmt "admit ()";
  (* Close the box for "let FUN_NAME (PARAMS) : EFFECT = admit()" *)
  F.pp_close_box fmt ();
  (* Close the box for the whole definition *)
  F.pp_close_box fmt ();
  (* Add breaks to insert new lines between definitions *)
  F.pp_print_break fmt 0 0

(** Extract a function declaration.

    Note that all the names used for extraction should already have been
    registered.
    
    We take the definition of the forward translation as parameter (which is
    equal to the definition to extract, if we extract a forward function) because
    it is useful for the decrease clause.
 *)
let extract_fun_decl (ctx : extraction_ctx) (fmt : F.formatter)
    (qualif : fun_decl_qualif) (has_decreases_clause : bool) (def : fun_decl) :
    unit =
  (* Retrieve the function name *)
  let def_name = ctx_get_local_function def.def_id def.back_id ctx in
  (* (* Add the type parameters - note that we need those bindings only for the
     * body translation (they are not top-level) *)
      let ctx, _ = ctx_add_type_params def.signature.type_params ctx in *)
  (* Add a break before *)
  F.pp_print_break fmt 0 0;
  (* Print a comment to link the extracted type to its original rust definition *)
  F.pp_print_string fmt
    ("(** [" ^ Print.fun_name_to_string def.basename ^ "] *)");
  F.pp_print_space fmt ();
  (* Open a box for the definition, so that whenever possible it gets printed on
   * one line *)
  F.pp_open_hvbox fmt ctx.indent_incr;
  (* Open a box for "let FUN_NAME (PARAMS) : EFFECT =" *)
  F.pp_open_hovbox fmt ctx.indent_incr;
  (* > "let FUN_NAME" *)
  let is_opaque = Option.is_none def.body in
  let qualif = fun_decl_qualif_keyword qualif in
  F.pp_print_string fmt (qualif ^ " " ^ def_name);
  F.pp_print_space fmt ();
  (* Open a box for "(PARAMS) : EFFECT =" *)
  F.pp_open_hvbox fmt 0;
  (* Open a box for "(PARAMS)" *)
  F.pp_open_hovbox fmt 0;
  let ctx, ctx_body = extract_fun_parameters ctx fmt def in
  (* Close the box for "(PARAMS)" *)
  F.pp_close_box fmt ();
  (* Print the return type - note that we have to be careful when
   * printing the input values for the decrease clause, because
   * it introduces bindings in the context... We thus "forget"
   * the bindings we introduced above.
   * TODO: figure out a cleaner way *)
  let _ =
    F.pp_print_string fmt ":";
    F.pp_print_space fmt ();
    (* Open a box for the EFFECT *)
    F.pp_open_hvbox fmt 0;
    (* Open a box for the return type *)
    F.pp_open_hovbox fmt ctx.indent_incr;
    (* Print the return type *)
    (* For opaque definitions, as we don't have named parameters under the hand,
     * we don't print parameters in the form `(x : a) (y : b) ...` above,
     * but wait until here to print the types: `a -> b -> ...`. *)
    if is_opaque then extract_fun_input_parameters_types ctx fmt def;
    (* `Tot` *)
    if has_decreases_clause then (
      F.pp_print_string fmt "Tot";
      F.pp_print_space fmt ());
    extract_ty ctx fmt has_decreases_clause def.signature.output;
    (* Close the box for the return type *)
    F.pp_close_box fmt ();
    (* Print the decrease clause - rk.: a function with a decreases clause
     * is necessarily a transparent function *)
    if has_decreases_clause then (
      F.pp_print_space fmt ();
      (* Open a box for the decrease clause *)
      F.pp_open_hovbox fmt 0;
      (* *)
      F.pp_print_string fmt "(decreases";
      F.pp_print_space fmt ();
      F.pp_print_string fmt "(";
      (* The name of the decrease clause *)
      let decr_name = ctx_get_decreases_clause def.def_id ctx in
      F.pp_print_string fmt decr_name;
      (* Print the type parameters *)
      List.iter
        (fun (p : type_var) ->
          let pname = ctx_get_type_var p.index ctx in
          F.pp_print_space fmt ();
          F.pp_print_string fmt pname)
        def.signature.type_params;
      (* Print the input values: we have to be careful here to print
       * only the input values which are in common with the *forward*
       * function (the additional input values "given back" to the
       * backward functions have no influence on termination: we thus
       * share the decrease clauses between the forward and the backward
       * functions).
       *)
      let inputs_lvs =
        let all_inputs = (Option.get def.body).inputs_lvs in
        (* We have to count:
         * - the forward inputs
         * - the state
         *)
        let num_fwd_inputs = def.signature.info.num_fwd_inputs in
        let num_fwd_inputs =
          if def.signature.info.effect_info.input_state then 1 + num_fwd_inputs
          else num_fwd_inputs
        in
        Collections.List.prefix num_fwd_inputs all_inputs
      in
      let _ =
        List.fold_left
          (fun ctx (lv : typed_pattern) ->
            F.pp_print_space fmt ();
            let ctx = extract_typed_pattern ctx fmt false lv in
            ctx)
          ctx inputs_lvs
      in
      F.pp_print_string fmt "))";
      (* Close the box for the decrease clause *)
      F.pp_close_box fmt ());
    (* Close the box for the EFFECT *)
    F.pp_close_box fmt ()
  in
  (* Print the "=" *)
  if not is_opaque then (
    F.pp_print_space fmt ();
    F.pp_print_string fmt "=");
  (* Close the box for "(PARAMS) : EFFECT =" *)
  F.pp_close_box fmt ();
  (* Close the box for "let FUN_NAME (PARAMS) : EFFECT =" *)
  F.pp_close_box fmt ();
  if not is_opaque then (
    F.pp_print_space fmt ();
    (* Open a box for the body *)
    F.pp_open_hvbox fmt 0;
    (* Extract the body *)
    let _ = extract_texpression ctx_body fmt false (Option.get def.body).body in
    (* Close the box for the body *)
    F.pp_close_box fmt ());
  (* Close the box for the definition *)
  F.pp_close_box fmt ();
  (* Add breaks to insert new lines between definitions *)
  F.pp_print_break fmt 0 0

(* Change the suffix from "_c" to "_body" *)
let global_decl_to_body_name (decl : string) : string =
  (* The declaration length without the global suffix *)
  let base_len = String.length decl - 2 in
  (* TODO: Use String.ends_with instead when a more recent version of OCaml is used *)
  assert (String.sub decl base_len 2 = "_c");
  (String.sub decl 0 base_len) ^ "_body"

(** Extract a global definition of the shape "QUALIF NAME : TYPE = BODY" with a custom body extractor *)
let extract_global_definition (ctx : extraction_ctx) (fmt : F.formatter)
  (qualif : fun_decl_qualif) (name : string) (ty : ty)
  (extract_body : (F.formatter -> unit) Option.t)
    : unit =
  let is_opaque = Option.is_none extract_body in

  (* Open the definition box (depth=0) *)
  F.pp_open_hvbox fmt ctx.indent_incr;

  (* Open "QUALIF NAME : TYPE =" box (depth=1) *)
  F.pp_open_hovbox fmt ctx.indent_incr;
  (* Print "QUALIF NAME " *)
  F.pp_print_string fmt (fun_decl_qualif_keyword qualif ^ " " ^ name);
  F.pp_print_space  fmt ();

  (* Open ": TYPE =" box (depth=2) *)
  F.pp_open_hvbox fmt 0;
  (* Print ": " *)
  F.pp_print_string fmt ":";
  F.pp_print_space fmt ();

  (* Open "TYPE" box (depth=3) *)
  F.pp_open_hovbox fmt ctx.indent_incr;
  (* Print "TYPE" *)
  extract_ty ctx fmt false ty;
  (* Close "TYPE" box (depth=3) *)
  F.pp_close_box fmt ();

  if not is_opaque then (
    (* Print " =" *)
    F.pp_print_space fmt ();
    F.pp_print_string fmt "=";
  );
  (* Close ": TYPE =" box (depth=2) *)
  F.pp_close_box fmt ();
  (* Close "QUALIF NAME : TYPE =" box (depth=1) *)
  F.pp_close_box fmt ();

  if not is_opaque then (
    F.pp_print_space fmt ();
    (* Open "BODY" box (depth=1) *)
    F.pp_open_hvbox fmt 0;
    (* Print "BODY" *)
    (Option.get extract_body) fmt;
    (* Close "BODY" box (depth=1) *)
    F.pp_close_box fmt ()
  );
  (* Close the definition box (depth=0) *)
  F.pp_close_box fmt ()

(** Extract a global declaration.
    This has similarity with the function extraction above (without parameters).
    However, generate its body separately from its declaration to extract the result value.

    For example,
    `let x = 3`

    will be translated to
    `let x_body : result int = Return 3`
    `let x_c : int = eval_global x_body`
 *)
let extract_global_decl (ctx : extraction_ctx) (fmt : F.formatter)
  (qualif : fun_decl_qualif) (def : fun_decl)
    : unit =
  (* TODO Lookup LLBC decl *)
  (* Sanity checks for globals *)
  assert (def.is_global_body);
  failwith "TODO ExtractToFStar.ml:1559"
  (* Previous code:
  assert (Option.is_none def.back_id);
  assert (List.length def.signature.inputs = 0);
  assert (List.length def.signature.doutputs = 1);
  assert (List.length def.signature.type_params = 0);
  assert (not def.signature.info.effect_info.can_fail);

  (* Add a break then the name of the corresponding LLBC declaration *)
  F.pp_print_break  fmt 0 0;
  F.pp_print_string fmt ("(** [" ^ Print.fun_name_to_string def.basename ^ "] *)");
  F.pp_print_space  fmt ();

  let def_name = ctx_get_local_function def.def_id def.back_id ctx in
  match def.body with
  | None ->
      extract_global_definition ctx fmt qualif def_name def.signature.output None
  | Some body ->
      let body_name = global_decl_to_body_name def_name in
      let body_ty = mk_result_ty def.signature.output in
      extract_global_definition ctx fmt qualif body_name body_ty (Some (fun fmt ->
        extract_texpression ctx fmt false body.body
      ));
      F.pp_print_break fmt 0 0;
      extract_global_definition ctx fmt qualif def_name def.signature.output (Some (fun fmt ->
        F.pp_print_string fmt ("eval_global " ^ body_name)
      ));
  F.pp_print_break fmt 0 0
  *)

(** Extract a unit test, if the function is a unit function (takes no
    parameters, returns unit).
    
    A unit test simply checks that the function normalizes to `Return ()`:
    ```
    let _ = assert_norm (FUNCTION () = Return ())
    ```
 *)
let extract_unit_test_if_unit_fun (ctx : extraction_ctx) (fmt : F.formatter)
    (def : fun_decl) : unit =
  (* We only insert unit tests for forward functions *)
  assert (def.back_id = None);
  (* Check if this is a unit function *)
  let sg = def.signature in
  if
    sg.type_params = []
    && (sg.inputs = [ mk_unit_ty ] || sg.inputs = [])
    && sg.output = mk_result_ty mk_unit_ty
  then (
    (* Add a break before *)
    F.pp_print_break fmt 0 0;
    (* Print a comment *)
    F.pp_print_string fmt
      ("(** Unit test for [" ^ Print.fun_name_to_string def.basename ^ "] *)");
    F.pp_print_space fmt ();
    (* Open a box for the test *)
    F.pp_open_hovbox fmt ctx.indent_incr;
    (* Print the test *)
    F.pp_print_string fmt "let _ =";
    F.pp_print_space fmt ();
    F.pp_print_string fmt "assert_norm";
    F.pp_print_space fmt ();
    F.pp_print_string fmt "(";
    let fun_name = ctx_get_local_function def.def_id def.back_id ctx in
    F.pp_print_string fmt fun_name;
    if sg.inputs <> [] then (
      F.pp_print_space fmt ();
      F.pp_print_string fmt "()");
    F.pp_print_space fmt ();
    F.pp_print_string fmt "=";
    F.pp_print_space fmt ();
    let success = ctx_get_variant (Assumed Result) result_return_id ctx in
    F.pp_print_string fmt (success ^ " ())");
    (* Close the box for the test *)
    F.pp_close_box fmt ();
    (* Add a break after *)
    F.pp_print_break fmt 0 0)
  else (* Do nothing *)
    ()
