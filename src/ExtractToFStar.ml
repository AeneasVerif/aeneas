(** Extract to F* *)

open Errors
open Pure
open TranslateCore
open PureToExtract
open StringUtils
module F = Format

(** A qualifier for a type definition.

    Controls whether we should use `type ...` or `and ...` (for mutually
    recursive datatypes).
 *)
type type_def_qualif = Type | And

(** A qualifier for function definitions.

    Controls whether we should use `let ...`, `let rec ...` or `and ...`
 *)
type fun_def_qualif = Let | LetRec | And

(** A list of keywords/identifiers used in F* and with which we want to check
    collision. *)
let fstar_keywords =
  [
    "let";
    "rec";
    "in";
    "fn";
    "int";
    "list";
    "FStar";
    "FStar.Mul";
    "type";
    "match";
    "with";
    "assert";
    "Type0";
  ]

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
 *     Cons(u32, Box<List>),
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
let mk_name_formatter (ctx : trans_ctx) (variant_concatenate_type_name : bool) =
  let int_name (int_ty : integer_type) =
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
  in
  (* For now, we treat only the case where type names are of the
   * form: `Module::Type`
   *)
  let get_type_name (name : name) : string =
    match name with
    | [ _module; name ] -> name
    | _ -> failwith ("Unexpected name shape: " ^ Print.name_to_string name)
  in
  let type_name_to_camel_case name =
    let name = get_type_name name in
    to_camel_case name
  in
  let type_name_to_snake_case name =
    let name = get_type_name name in
    to_snake_case name
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
  (* For now, we treat only the case where function names are of the
   * form: `function` (no module prefix)
   *)
  let get_fun_name (name : name) : string =
    match name with
    | [ name ] -> name
    | _ -> failwith ("Unexpected name shape: " ^ Print.name_to_string name)
  in
  let fun_name (_fid : A.fun_id) (fname : name) (num_rgs : int)
      (rg : region_group_info option) : string =
    let fname = get_fun_name fname in
    (* Converting to snake case should be a no-op, but it doesn't cost much *)
    let fname = to_snake_case fname in
    (* Compute the suffix *)
    let suffix = default_fun_suffix num_rgs rg in
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
            | AdtId adt_id ->
                let def =
                  TypeDefId.Map.find adt_id ctx.type_context.type_defs
                in
                StringUtils.string_of_chars [ (get_type_name def.name).[0] ])
        | TypeVar _ -> "x" (* lacking imagination here... *)
        | Bool -> "b"
        | Char -> "c"
        | Integer _ -> "i"
        | Str -> "s"
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
  {
    bool_name = "bool";
    char_name = "char";
    int_name;
    str_name = "string";
    field_name;
    variant_name;
    type_name;
    fun_name;
    var_basename;
    type_var_basename;
    append_index;
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
          F.pp_print_string fmt "(";
          Collections.List.iter_link (F.pp_print_space fmt)
            (extract_ty ctx fmt true) tys;
          F.pp_print_string fmt ")"
      | AdtId _ | Assumed _ ->
          if inside then F.pp_print_string fmt "(";
          F.pp_print_string fmt (ctx_get_type type_id ctx);
          if tys <> [] then F.pp_print_space fmt ();
          Collections.List.iter_link (F.pp_print_space fmt)
            (extract_ty ctx fmt true) tys;
          if inside then F.pp_print_string fmt ")")
  | TypeVar vid -> F.pp_print_string fmt (ctx_get_type_var vid ctx)
  | Bool -> F.pp_print_string fmt ctx.fmt.bool_name
  | Char -> F.pp_print_string fmt ctx.fmt.char_name
  | Integer int_ty -> F.pp_print_string fmt (ctx.fmt.int_name int_ty)
  | Str -> F.pp_print_string fmt ctx.fmt.str_name
  | Array _ | Slice _ -> raise Unimplemented

(** Compute the names for all the top-level identifiers used in a type
    definition (type name, variant names, field names, etc. but not type
    parameters).
    
    We need to do this preemptively, beforce extracting any definition,
    because of recursive definitions.
 *)
let extract_type_def_register_names (ctx : extraction_ctx) (def : type_def) :
    extraction_ctx =
  (* Compute and register the type def name *)
  let ctx, def_name = ctx_add_type_def def ctx in
  (* Compute and register:
   * - the variant names, if this is an enumeration
   * - the field names, if this is a structure
   *)
  let ctx =
    match def.kind with
    | Struct fields ->
        fst (ctx_add_fields def (FieldId.mapi (fun id f -> (id, f)) fields) ctx)
    | Enum variants ->
        fst
          (ctx_add_variants def
             (VariantId.mapi (fun id v -> (id, v)) variants)
             ctx)
  in
  (* Return *)
  ctx

let extract_type_def_struct_body (ctx : extraction_ctx) (fmt : F.formatter)
    (def : type_def) (fields : field list) : unit =
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
      let field_name = ctx_get_field def.def_id field_id ctx in
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

let extract_type_def_enum_body (ctx : extraction_ctx) (fmt : F.formatter)
    (def : type_def) (def_name : string) (type_params : string list)
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
    let variant_name = ctx_get_variant def.def_id variant_id ctx in
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

(** Extract a type definition.

    Note that all the names used for extraction should already have been
    registered.
 *)
let extract_type_def (ctx : extraction_ctx) (fmt : F.formatter)
    (qualif : type_def_qualif) (def : type_def) : unit =
  (* Retrieve the definition name *)
  let def_name = ctx_get_local_type def.def_id ctx in
  (* Add the type params - note that we remember those bindings only for the
   * body translation: the updated ctx we return at the end of the function
   * only contains the registered type def and variant names *)
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
  let qualif = match qualif with Type -> "type" | And -> "and" in
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
  (* Print the "=" *)
  F.pp_print_space fmt ();
  F.pp_print_string fmt "=";
  (* Close the box for "type TYPE_NAME (TYPE_PARAMS) =" *)
  F.pp_close_box fmt ();
  (match def.kind with
  | Struct fields -> extract_type_def_struct_body ctx_body fmt def fields
  | Enum variants ->
      extract_type_def_enum_body ctx_body fmt def def_name type_params variants);
  (* Close the box for the definition *)
  F.pp_close_box fmt ();
  (* Add breaks to insert new lines between definitions *)
  F.pp_print_break fmt 0 0

(** Compute the names for all the pure functions generated from a rust function
    (forward function and backward functions).
 *)
let extract_fun_def_register_names (ctx : extraction_ctx)
    (def : pure_fun_translation) : extraction_ctx =
  let fwd, back_ls = def in
  (* Register the forward function name *)
  let ctx = ctx_add_fun_def fwd ctx in
  (* Register the backward functions' names *)
  let ctx =
    List.fold_left (fun ctx back -> ctx_add_fun_def back ctx) ctx back_ls
  in
  (* Return *)
  ctx
