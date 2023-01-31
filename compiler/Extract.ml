(** The generic extraction *)
(* Turn the whole module into a functor: it is very annoying to carry the
   the formatter everywhere...
*)

open Utils
open Pure
open PureUtils
open TranslateCore
open ExtractBase
open StringUtils
open Config
module F = Format

(** Small helper to compute the name of an int type *)
let int_name (int_ty : integer_type) =
  let isize, usize, i_format, u_format =
    match !backend with
    | FStar | Coq ->
        "isize", "usize", format_of_string "i%d", format_of_string "u%d"
    | Lean ->
        "ISize", "USize", format_of_string "Int%d", format_of_string "UInt%d"
  in
  match int_ty with
  | Isize -> isize
  | I8 -> Printf.sprintf i_format 8
  | I16 -> Printf.sprintf i_format 16
  | I32 -> Printf.sprintf i_format 32
  | I64 -> Printf.sprintf i_format 64
  | I128 -> Printf.sprintf i_format 128
  | Usize -> usize
  | U8 -> Printf.sprintf u_format 8
  | U16 -> Printf.sprintf u_format 16
  | U32 -> Printf.sprintf u_format 32
  | U64 -> Printf.sprintf u_format 64
  | U128 -> Printf.sprintf u_format 128

(** Small helper to compute the name of a unary operation *)
let unop_name (unop : unop) : string =
  match unop with
  | Not -> ( match !backend with FStar | Lean -> "not" | Coq -> "negb")
  | Neg (int_ty: integer_type) ->
      begin match !backend with
      | Lean -> int_name int_ty ^ ".checked_neg"
      | _ -> int_name int_ty ^ "_neg"
      end
  | Cast _ -> raise (Failure "Unsupported")

(** Small helper to compute the name of a binary operation (note that many
    binary operations like "less than" are extracted to primitive operations,
    like [<].
 *)
let named_binop_name (binop : E.binop) (int_ty : integer_type) : string =
  let binop =
    match binop with
    | Div -> "div"
    | Rem -> "rem"
    | Add -> "add"
    | Sub -> "sub"
    | Mul -> "mul"
    | _ -> raise (Failure "Unreachable")
  in
  match !backend with
  | Lean -> int_name int_ty ^ ".checked_" ^ binop
  | FStar | Coq -> int_name int_ty ^ "_" ^ binop

(** A list of keywords/identifiers used by the backend and with which we
    want to check collision. *)
let keywords () =
  let named_unops =
    unop_name Not
    :: List.map (fun it -> unop_name (Neg it)) T.all_signed_int_types
  in
  let named_binops = [ E.Div; Rem; Add; Sub; Mul ] in
  let named_binops =
    List.concat_map
       (fun bn -> List.map (fun it -> named_binop_name bn it) T.all_int_types)
       named_binops
  in
  let misc =
    match !backend with
    | FStar ->
        [
          "let";
          "rec";
          "in";
          "fun";
          "fn";
          "val";
          "int";
          "list";
          "FStar";
          "FStar.Mul";
          "type";
          "match";
          "with";
          "assert";
          "assert_norm";
          "assume";
          "Type0";
          "Type";
          "unit";
          "not";
          "scalar_cast";
        ]
    | Coq ->
        [
          "Record";
          "Inductive";
          "Fixpoint";
          "Definition";
          "Arguments";
          "Notation";
          "Check";
          "Search";
          "SearchPattern";
          "Axiom";
          "Type";
          "Set";
          "let";
          "rec";
          "in";
          "unit";
          "fun";
          "type";
          "int";
          "match";
          "with";
          "assert";
          "not";
          (* [tt] is unit *)
          "tt";
          "char_of_byte";
        ]
    | Lean ->
        [] (* TODO *)
  in
  List.concat [ named_unops; named_binops; misc ]

let assumed_adts () : (assumed_ty * string) list =
  [
    (State, "state");
    (Result, "result");
    (Error, "error");
    (Fuel, "nat");
    (Option, if !backend = Lean then "Option" else "option");
    (Vec, "vec");
  ]

let assumed_structs : (assumed_ty * string) list = []

let assumed_variants () : (assumed_ty * VariantId.id * string) list =
  match !backend with
  | FStar ->
      [
        (Result, result_return_id, "Return");
        (Result, result_fail_id, "Fail");
        (Error, error_failure_id, "Failure");
        (Error, error_out_of_fuel_id, "OutOfFuel");
        (* No Fuel::Zero on purpose *)
        (* No Fuel::Succ on purpose *)
        (Option, option_some_id, "Some");
        (Option, option_none_id, "None");
      ]
  | Coq ->
      [
        (Result, result_return_id, "Return");
        (Result, result_fail_id, "Fail_");
        (Error, error_failure_id, "Failure");
        (Error, error_out_of_fuel_id, "OutOfFuel");
        (Fuel, fuel_zero_id, "O");
        (Fuel, fuel_succ_id, "S");
        (Option, option_some_id, "Some");
        (Option, option_none_id, "None");
      ]
  | Lean ->
      [
        (Result, result_return_id, "ret");
        (Result, result_fail_id, "fail");
        (Error, error_failure_id, "panic");
        (* No Fuel::Zero on purpose *)
        (* No Fuel::Succ on purpose *)
        (Option, option_some_id, "some");
        (Option, option_none_id, "none");
      ]

let assumed_llbc_functions :
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

let assumed_pure_functions (): (pure_assumed_fun_id * string) list =
  match !backend with
  | FStar ->
      [
        (Return, "return");
        (Fail, "fail");
        (Assert, "massert");
        (FuelDecrease, "decrease");
        (FuelEqZero, "is_zero");
      ]
  | Coq ->
      (* We don't provide [FuelDecrease] and [FuelEqZero] on purpose *)
      [ (Return, "return_"); (Fail, "fail_"); (Assert, "massert") ]
  | Lean ->
      [
        (Return, "return");
        (Fail, "fail_");
        (Assert, "massert");
        (* TODO: figure out how to deal with this *)
        (FuelDecrease, "decrease");
        (FuelEqZero, "is_zero");
      ]

let names_map_init () : names_map_init =
  {
    keywords = keywords ();
    assumed_adts = assumed_adts ();
    assumed_structs;
    assumed_variants = assumed_variants ();
    assumed_llbc_functions;
    assumed_pure_functions = assumed_pure_functions ();
  }

let extract_unop (extract_expr : bool -> texpression -> unit)
    (fmt : F.formatter) (inside : bool) (unop : unop) (arg : texpression) : unit
    =
  match unop with
  | Not | Neg _ ->
      let unop = unop_name unop in
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

let extract_binop (extract_expr : bool -> texpression -> unit)
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
        | Ne -> if !backend = Lean then "!=" else "<>"
        | Ge -> ">="
        | Gt -> ">"
        | _ -> raise (Failure "Unreachable")
      in
      let binop = match !backend with FStar | Lean -> binop | Coq -> "s" ^ binop in
      extract_expr false arg0;
      F.pp_print_space fmt ();
      F.pp_print_string fmt binop;
      F.pp_print_space fmt ();
      extract_expr false arg1
  | Div | Rem | Add | Sub | Mul ->
      let binop = named_binop_name binop int_ty in
      F.pp_print_string fmt binop;
      F.pp_print_space fmt ();
      extract_expr false arg0;
      F.pp_print_space fmt ();
      extract_expr false arg1
  | BitXor | BitAnd | BitOr | Shl | Shr -> raise Unimplemented);
  if inside then F.pp_print_string fmt ")"

let type_decl_kind_to_qualif (kind : decl_kind)
    (type_kind : type_decl_kind option): string =
  match !backend with
  | FStar -> (
      match kind with
      | SingleNonRec -> "type"
      | SingleRec -> "type"
      | MutRecFirst -> "type"
      | MutRecInner -> "and"
      | MutRecLast -> "and"
      | Assumed -> "assume type"
      | Declared -> "val")
  | Coq -> (
      match (kind, type_kind) with
      | SingleNonRec, Some Enum -> "Inductive"
      | SingleNonRec, Some Struct -> "Record"
      | (SingleRec | MutRecFirst), Some _ -> "Inductive"
      | (MutRecInner | MutRecLast), Some _ ->
          (* Coq doesn't support groups of mutually recursive definitions which mix
           * records and inducties: we convert everything to records if this happens
           *)
          "with"
      | (Assumed | Declared), None -> "Axiom"
      | _ -> raise (Failure "Unexpected"))
  | Lean -> (
      match kind with
      | SingleNonRec -> if type_kind = Some Struct then "structure" else "inductive"
      | SingleRec -> "inductive"
      | MutRecFirst -> "mutual inductive"
      | MutRecInner -> "inductive"
      | MutRecLast -> "inductive" (* TODO: need to print end afterwards *)
      | Assumed -> "axiom"
      | Declared -> "axiom")

let fun_decl_kind_to_qualif (kind : decl_kind) =
  match !backend with
  | FStar -> (
      match kind with
      | SingleNonRec -> "let"
      | SingleRec -> "let rec"
      | MutRecFirst -> "let rec"
      | MutRecInner -> "and"
      | MutRecLast -> "and"
      | Assumed -> "assume val"
      | Declared -> "val")
  | Coq -> (
      match kind with
      | SingleNonRec -> "Definition"
      | SingleRec -> "Fixpoint"
      | MutRecFirst -> "Fixpoint"
      | MutRecInner -> "with"
      | MutRecLast -> "with"
      | Assumed -> "Axiom"
      | Declared -> "Axiom")
  | Lean -> (
      match kind with
      | SingleNonRec -> "def"
      | SingleRec -> "def"
      | MutRecFirst -> "mutual def"
      | MutRecInner -> "def"
      | MutRecLast -> "def" (* TODO: need to print end afterwards *)
      | Assumed -> "axiom"
      | Declared -> "axiom")


(**
   [ctx]: we use the context to lookup type definitions, to retrieve type names.
   This is used to compute variable names, when they have no basenames: in this
   case we use the first letter of the type name.

   [variant_concatenate_type_name]: if true, add the type name as a prefix
   to the variant names.
   Ex.:
   In Rust:
     {[
       enum List = {
         Cons(u32, Box<List>),x
         Nil,
       }
     ]}

   F*, if option activated:
     {[
       type list =
       | ListCons : u32 -> list -> list
       | ListNil : list
     ]}

   F*, if option not activated:
     {[
       type list =
       | Cons : u32 -> list -> list
       | Nil : list
     ]}

   Rk.: this should be true by default, because in Rust all the variant names
   are actively uniquely identifier by the type name [List::Cons(...)], while
   in other languages it is not necessarily the case, and thus clashes can mess
   up type checking. Note that some languages actually forbids the name clashes
   (it is the case of F* ).
 *)
let mk_formatter (ctx : trans_ctx) (crate_name : string)
    (variant_concatenate_type_name : bool) : formatter =
  let int_name = int_name in

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
    let name = String.concat "_" name in
    match !backend with FStar | Lean -> name | Coq -> capitalize_first_letter name
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
    let prefix = match !backend with FStar -> "Mk" | Lean | Coq -> "mk" in
    prefix ^ tname
  in
  let get_fun_name = get_name in
  let fun_name_to_snake_case (fname : fun_name) : string =
    let fname = get_fun_name fname in
    (* Converting to snake case should be a no-op, but it doesn't cost much *)
    let fname = List.map to_snake_case fname in
    (* Concatenate the elements *)
    String.concat "_" fname
  in
  let global_name (name : global_name) : string =
    (* Converting to snake case also lowercases the letters (in Rust, global
     * names are written in capital letters). *)
    let parts = List.map to_snake_case (get_name name) in
    String.concat "_" parts
  in
  let fun_name (fname : fun_name) (num_loops : int) (loop_id : LoopId.id option)
      (num_rgs : int) (rg : region_group_info option) (filter_info : bool * int)
      : string =
    let fname = fun_name_to_snake_case fname in
    (* Compute the suffix *)
    let suffix = default_fun_suffix num_loops loop_id num_rgs rg filter_info in
    (* Concatenate *)
    fname ^ suffix
  in

  let decreases_clause_name (_fid : A.FunDeclId.id) (fname : fun_name)
      (num_loops : int) (loop_id : LoopId.id option) : string =
    let fname = fun_name_to_snake_case fname in
    let lp_suffix = default_fun_loop_suffix num_loops loop_id in
    (* Compute the suffix *)
    let suffix = "_decreases" in
    (* Concatenate *)
    fname ^ lp_suffix ^ suffix
  in

  let terminates_clause_name (_fid : A.FunDeclId.id) (fname : fun_name)
      (num_loops : int) (loop_id : LoopId.id option) : string =
    let fname = fun_name_to_snake_case fname in
    let lp_suffix = default_fun_loop_suffix num_loops loop_id in
    (* Compute the suffix *)
    let suffix = "_terminates" in
    (* Concatenate *)
    fname ^ lp_suffix ^ suffix
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
            | Assumed Error -> ConstStrings.error_basename
            | Assumed Fuel -> ConstStrings.fuel_basename
            | Assumed Option -> "opt"
            | Assumed Vec -> "v"
            | Assumed State -> ConstStrings.state_basename
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
        | TypeVar _ -> (
            (* TODO: use "t" also for F* *)
            match !backend with
            | FStar -> "x" (* lacking inspiration here... *)
            | Coq | Lean -> "t" (* lacking inspiration here... *))
        | Bool -> "b"
        | Char -> "c"
        | Integer _ -> "i"
        | Str -> "s"
        | Arrow _ -> "f"
        | Array _ | Slice _ -> raise Unimplemented)
  in
  let type_var_basename (_varset : StringSet.t) (basename : string) : string =
    (* Rust type variables are snake-case and start with a capital letter *)
    match !backend with
    | FStar ->
        (* This is *not* a no-op: this removes the capital letter *)
        to_snake_case basename
    | Coq | Lean -> basename
  in
  let append_index (basename : string) (i : int) : string =
    basename ^ string_of_int i
  in

  let extract_primitive_value (fmt : F.formatter) (inside : bool)
      (cv : primitive_value) : unit =
    match cv with
    | Scalar sv -> (
        match !backend with
        | FStar -> F.pp_print_string fmt (Z.to_string sv.PV.value)
        | Coq ->
            if inside then F.pp_print_string fmt "(";
            (* We need to add parentheses if the value is negative *)
            if sv.PV.value >= Z.of_int 0 then
              F.pp_print_string fmt (Z.to_string sv.PV.value)
            else F.pp_print_string fmt ("(" ^ Z.to_string sv.PV.value ^ ")");
            F.pp_print_string fmt ("%" ^ int_name sv.PV.int_ty);
            if inside then F.pp_print_string fmt ")"
        | Lean ->
            F.pp_print_string fmt "(";
            F.pp_print_string fmt (int_name sv.int_ty);
            F.pp_print_string fmt ".ofNatCore ";
            Z.pp_print fmt sv.value;
            F.pp_print_string fmt (" (by intlit))"))
    | Bool b ->
        let b = if b then "true" else "false" in
        F.pp_print_string fmt b
    | Char c -> (
        match !backend with
        | FStar | Lean -> F.pp_print_string fmt ("'" ^ String.make 1 c ^ "'")
        | Coq ->
            if inside then F.pp_print_string fmt "(";
            F.pp_print_string fmt "char_of_byte";
            F.pp_print_space fmt ();
            (* Convert the the char to ascii *)
            let c =
              let i = Char.code c in
              let x0 = i / 16 in
              let x1 = i mod 16 in
              "Coq.Init.Byte.x" ^ string_of_int x0 ^ string_of_int x1
            in
            F.pp_print_string fmt c;
            if inside then F.pp_print_string fmt ")")

    | String s ->
        (* We need to replace all the line breaks *)
        let s =
          StringUtils.map
            (fun c -> if c = '\n' then "\n" else String.make 1 c)
            s
        in
        F.pp_print_string fmt ("\"" ^ s ^ "\"")
  in
  let bool_name = if !backend = Lean then "Bool" else "bool" in
  let char_name = if !backend = Lean then "Char" else "char" in
  let str_name = if !backend = Lean then "String" else "string" in
  {
    bool_name;
    char_name;
    int_name;
    str_name;
    type_decl_kind_to_qualif;
    fun_decl_kind_to_qualif;
    field_name;
    variant_name;
    struct_constructor;
    type_name;
    global_name;
    fun_name;
    decreases_clause_name;
    terminates_clause_name;
    var_basename;
    type_var_basename;
    append_index;
    extract_primitive_value;
    extract_unop;
    extract_binop;
  }

let mk_formatter_and_names_map (ctx : trans_ctx) (crate_name : string)
    (variant_concatenate_type_name : bool) : formatter * names_map =
  let fmt = mk_formatter ctx crate_name variant_concatenate_type_name in
  let names_map = initialize_names_map fmt (names_map_init ()) in
  (fmt, names_map)

(** In Coq, a group of definitions must be ended with a "." *)
let print_decl_end_delimiter (fmt : F.formatter) (kind : decl_kind) =
  if !backend = Coq && decl_is_last_from_group kind then (
    F.pp_print_cut fmt ();
    F.pp_print_string fmt ".")

let unit_name () =
  match !backend with | Lean -> "Unit" | Coq | FStar -> "unit"

(** [inside] constrols whether we should add parentheses or not around type
    applications (if [true] we add parentheses).
 *)
let rec extract_ty (ctx : extraction_ctx) (fmt : F.formatter) (inside : bool)
    (ty : ty) : unit =
  match ty with
  | Adt (type_id, tys) -> (
      match type_id with
      | Tuple ->
          (* This is a bit annoying, but in F*/Coq [()] is not the unit type:
           * we have to write [unit]... *)
          if tys = [] then F.pp_print_string fmt (unit_name ())
          else (
            F.pp_print_string fmt "(";
            Collections.List.iter_link
              (fun () ->
                F.pp_print_space fmt ();
                let product = match !backend with FStar -> "&" | Coq -> "*" | Lean -> "×" in
                F.pp_print_string fmt product;
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

(** Print the variants *)
let extract_type_decl_variant (ctx : extraction_ctx) (fmt : F.formatter)
    (type_name : string) (type_params : string list) (cons_name : string)
    (fields : field list) : unit =
  F.pp_print_space fmt ();
  (* variant box *)
  F.pp_open_hvbox fmt ctx.indent_incr;
  (* [| Cons :]
   * Note that we really don't want any break above so we print everything
   * at once. *)
  F.pp_print_string fmt ("| " ^ cons_name ^ " :");
  F.pp_print_space fmt ();
  let print_field (fid : FieldId.id) (f : field) (ctx : extraction_ctx) :
      extraction_ctx =
    (* Open the field box *)
    F.pp_open_box fmt ctx.indent_incr;
    (* Print the field names, if the backend accepts it.
     * [  x :]
     * Note that when printing fields, we register the field names as
     * *variables*: they don't need to be unique at the top level. *)
    let ctx =
      match !backend with
      | FStar -> (
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
              ctx)
      | Coq | Lean -> ctx
    in
    (* Print the field type *)
    extract_ty ctx fmt false f.field_ty;
    (* Print the arrow [->]*)
    F.pp_print_space fmt ();
    F.pp_print_string fmt "->";
    (* Close the field box *)
    F.pp_close_box fmt ();
    F.pp_print_space fmt ();
    (* Return *)
    ctx
  in
  (* Print the fields *)
  let fields = FieldId.mapi (fun fid f -> (fid, f)) fields in
  let _ =
    List.fold_left (fun ctx (fid, f) -> print_field fid f ctx) ctx fields
  in
  (* Print the final type *)
  F.pp_open_hovbox fmt 0;
  F.pp_print_string fmt type_name;
  List.iter
    (fun type_param ->
      F.pp_print_space fmt ();
      F.pp_print_string fmt type_param)
    type_params;
  F.pp_close_box fmt ();
  (* Close the variant box *)
  F.pp_close_box fmt ()

(* TODO: we don' need the [def_name] paramter: it can be retrieved from the context *)
let extract_type_decl_enum_body (ctx : extraction_ctx) (fmt : F.formatter)
    (def : type_decl) (def_name : string) (type_params : string list)
    (variants : variant list) : unit =
  (* We want to generate a definition which looks like this (taking F* as example):
     {[
       type list a = | Cons : a -> list a -> list a | Nil : list a
     ]}

     If there isn't enough space on one line:
     {[
       type s =
       | Cons : a -> list a -> list a
       | Nil : list a
     ]}

     And if we need to write the type of a variant on several lines:
     {[
       type s =
       | Cons :
         a ->
         list a ->
         list a
       | Nil : list a
     ]}

     Finally, it is possible to give names to the variant fields in Rust.
     In this situation, we generate a definition like this:
     {[
       type s =
       | Cons : hd:a -> tl:list a -> list a
       | Nil : list a
     ]}

     Note that we already printed: [type s =]
  *)
  let print_variant variant_id v =
    let cons_name = ctx_get_variant (AdtId def.def_id) variant_id ctx in
    let fields = v.fields in
    extract_type_decl_variant ctx fmt def_name type_params cons_name fields
  in
  (* Print the variants *)
  let variants = VariantId.mapi (fun vid v -> (vid, v)) variants in
  List.iter (fun (vid, v) -> print_variant vid v) variants

let extract_type_decl_struct_body (ctx : extraction_ctx) (fmt : F.formatter)
    (kind : decl_kind) (def : type_decl) (type_params : string list)
    (fields : field list) : unit =
  (* We want to generate a definition which looks like this (taking F* as example):
     {[
       type t = { x : int; y : bool; }
     ]}

     If there isn't enough space on one line:
     {[
       type t =
       {
         x : int; y : bool;
       }
     ]}

     And if there is even less space:
     {[
       type t =
       {
         x : int;
         y : bool;
       }
     ]}

     Also, in case there are no fields, we need to define the type as [unit]
     ([type t = {}] doesn't work in F* ).

     Coq:
     ====
     We need to define the constructor name upon defining the struct (record, in Coq).
     The syntex is:
     {[
       Record Foo = mkFoo { x : int; y : bool; }.
     }]

     Also, Coq doesn't support groups of mutually recursive inductives and records.
     This is fine, because we can then define records as inductives, and leverage
     the fact that when record fields are accessed, the records are symbolically
     expanded which introduces let bindings of the form: [let RecordCons ... = x in ...].
     As a consequence, we never use the record projectors (unless we reconstruct
     them in the micro passes of course).
  *)
  (* Note that we already printed: [type t =] *)
  let is_rec = decl_is_from_rec_group kind in
  let _ =
    if !backend = FStar && fields = [] then (
      F.pp_print_space fmt ();
      F.pp_print_string fmt (unit_name ()))
    else if (not is_rec) || !backend = FStar then (
      F.pp_print_space fmt ();
      (* If Coq: print the constructor name *)
      (* TODO: remove superfluous test not is_rec below *)
      if !backend = Coq && not is_rec then (
        F.pp_print_string fmt (ctx_get_struct (AdtId def.def_id) ctx);
        F.pp_print_string fmt " ");
      if !backend <> Lean then
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
        if !backend <> Lean then
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
      if !backend <> Lean then
        F.pp_print_string fmt "}")
    else (
      (* We extract for Coq, and we have a recursive record, or a record in
         a group of mutually recursive types: we extract it as an inductive type
      *)
      assert (is_rec && !backend = Coq);
      let cons_name = ctx_get_struct (AdtId def.def_id) ctx in
      let def_name = ctx_get_local_type def.def_id ctx in
      extract_type_decl_variant ctx fmt def_name type_params cons_name fields)
  in
  ()

(** Extract a nestable, muti-line comment *)
let extract_comment (fmt: F.formatter) (s: string): unit =
  match !backend with
  | Coq | FStar ->
      F.pp_print_string fmt "(** ";
      F.pp_print_string fmt s;
      F.pp_print_string fmt " *)";
  | Lean ->
      F.pp_print_string fmt "/- ";
      F.pp_print_string fmt s;
      F.pp_print_string fmt " -/"

(** Extract a type declaration.

    Note that all the names used for extraction should already have been
    registered.
 *)
let extract_type_decl (ctx : extraction_ctx) (fmt : F.formatter)
    (kind : decl_kind) (def : type_decl) : unit =
  let extract_body =
    match kind with
    | SingleNonRec | SingleRec | MutRecFirst | MutRecInner | MutRecLast -> true
    | Assumed | Declared -> false
  in
  let type_kind =
    if extract_body then
      match def.kind with
      | Struct _ -> Some Struct
      | Enum _ -> Some Enum
      | Opaque -> None
    else None
  in
  (* If in Coq and the declaration is opaque, it must have the shape:
     [Axiom Ident : forall (T0 ... Tn : Type), ... -> ... -> ...].

     The boolean [is_opaque_coq] is used to detect this case.
  *)
  let is_opaque_coq = !backend = Coq && type_kind = None in
  let use_forall = is_opaque_coq && def.type_params <> [] in
  (* Retrieve the definition name *)
  let def_name = ctx_get_local_type def.def_id ctx in
  (* Add the type params - note that we need those bindings only for the
   * body translation (they are not top-level) *)
  let ctx_body, type_params = ctx_add_type_params def.type_params ctx in
  (* Add a break before *)
  F.pp_print_break fmt 0 0;
  (* Print a comment to link the extracted type to its original rust definition *)
  extract_comment fmt ("[" ^ Print.name_to_string def.name ^ "]");
  F.pp_print_space fmt ();
  (* Open a box for the definition, so that whenever possible it gets printed on
   * one line *)
  F.pp_open_hvbox fmt 0;
  (* Open a box for "type TYPE_NAME (TYPE_PARAMS) =" *)
  F.pp_open_hovbox fmt ctx.indent_incr;
  (* > "type TYPE_NAME" *)
  let qualif = ctx.fmt.type_decl_kind_to_qualif kind type_kind in
  F.pp_print_string fmt (qualif ^ " " ^ def_name);
  (* Print the type parameters *)
  let type_keyword = match !backend with FStar -> "Type0" | Coq | Lean -> "Type" in
  if def.type_params <> [] then (
    if use_forall then (
      F.pp_print_space fmt ();
      F.pp_print_string fmt ":";
      F.pp_print_space fmt ();
      F.pp_print_string fmt "forall");
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
    F.pp_print_string fmt (type_keyword ^ ")"));
  (* Print the "=" if we extract the body*)
  if extract_body then (
    F.pp_print_space fmt ();
    let eq = match !backend with
      | FStar -> "="
      | Coq -> ":="
      | Lean -> if type_kind = Some Struct && kind = SingleNonRec then "where" else ":="
    in
    F.pp_print_string fmt eq)
  else (
    (* Otherwise print ": Type0" *)
    if use_forall then F.pp_print_string fmt ","
    else (
      F.pp_print_space fmt ();
      F.pp_print_string fmt ":");
    F.pp_print_space fmt ();
    F.pp_print_string fmt type_keyword);
  (* Close the box for "type TYPE_NAME (TYPE_PARAMS) =" *)
  F.pp_close_box fmt ();
  (if extract_body then
   match def.kind with
   | Struct fields ->
       extract_type_decl_struct_body ctx_body fmt kind def type_params fields
   | Enum variants ->
       extract_type_decl_enum_body ctx_body fmt def def_name type_params
         variants
   | Opaque -> raise (Failure "Unreachable"));
  (* If Coq: end the definition with a "." *)
  print_decl_end_delimiter fmt kind;
  (* Close the box for the definition *)
  F.pp_close_box fmt ();
  (* Add breaks to insert new lines between definitions *)
  F.pp_print_break fmt 0 0

(** Auxiliary function.

    Generate [Arguments] instructions in Coq.
 *)
let extract_type_decl_coq_arguments (ctx : extraction_ctx) (fmt : F.formatter)
    (kind : decl_kind) (decl : type_decl) : unit =
  assert (!backend = Coq);
  (* Generating the [Arguments] instructions is useful only if there are type parameters *)
  if decl.type_params = [] then ()
  else
    (* Add the type params - note that we need those bindings only for the
     * body translation (they are not top-level) *)
    let _ctx_body, type_params = ctx_add_type_params decl.type_params ctx in
    (* Auxiliary function to extract an [Arguments Cons {T} _ _.] instruction *)
    let extract_arguments_info (cons_name : string) (fields : 'a list) : unit =
      (* Add a break before *)
      F.pp_print_break fmt 0 0;
      (* Open a box *)
      F.pp_open_hovbox fmt ctx.indent_incr;
      (* Small utility *)
      let print_type_vars () =
        List.iter
          (fun (var : string) ->
            F.pp_print_space fmt ();
            F.pp_print_string fmt ("{" ^ var ^ "}"))
          type_params
      in
      let print_fields () =
        List.iter
          (fun _ ->
            F.pp_print_space fmt ();
            F.pp_print_string fmt "_")
          fields
      in
      F.pp_print_break fmt 0 0;
      F.pp_print_string fmt "Arguments";
      F.pp_print_space fmt ();
      F.pp_print_string fmt cons_name;
      print_type_vars ();
      print_fields ();
      F.pp_print_string fmt ".";

      (* Close the box *)
      F.pp_close_box fmt ()
    in

    (* Generate the [Arguments] instruction *)
    match decl.kind with
    | Opaque -> ()
    | Struct fields ->
        let adt_id = AdtId decl.def_id in
        (* Generate the instruction for the record constructor *)
        let cons_name = ctx_get_struct adt_id ctx in
        extract_arguments_info cons_name fields;
        (* Generate the instruction for the record projectors, if there are *)
        let is_rec = decl_is_from_rec_group kind in
        if not is_rec then
          FieldId.iteri
            (fun fid _ ->
              let cons_name = ctx_get_field adt_id fid ctx in
              extract_arguments_info cons_name [])
            fields;
        (* Add breaks to insert new lines between definitions *)
        F.pp_print_break fmt 0 0
    | Enum variants ->
        (* Generate the instructions *)
        VariantId.iteri
          (fun vid (v : variant) ->
            let cons_name = ctx_get_variant (AdtId decl.def_id) vid ctx in
            extract_arguments_info cons_name v.fields)
          variants;
        (* Add breaks to insert new lines between definitions *)
        F.pp_print_break fmt 0 0

(** Auxiliary function.

    Generate field projectors in Coq.

    Sometimes we extract records as inductives in Coq: when this happens we
    have to define the field projectors afterwards.
 *)
let extract_type_decl_record_field_projectors (ctx : extraction_ctx)
    (fmt : F.formatter) (kind : decl_kind) (decl : type_decl) : unit =
  assert (!backend = Coq);
  match decl.kind with
  | Opaque | Enum _ -> ()
  | Struct fields ->
      (* Records are extracted as inductives only if they are recursive *)
      let is_rec = decl_is_from_rec_group kind in
      if is_rec then
        (* Add the type params *)
        let ctx, type_params = ctx_add_type_params decl.type_params ctx in
        let ctx, record_var = ctx_add_var "x" (VarId.of_int 0) ctx in
        let ctx, field_var = ctx_add_var "x" (VarId.of_int 1) ctx in
        let def_name = ctx_get_local_type decl.def_id ctx in
        let cons_name = ctx_get_struct (AdtId decl.def_id) ctx in
        let extract_field_proj (field_id : FieldId.id) (_ : field) : unit =
          F.pp_print_space fmt ();
          (* Outer box for the projector definition *)
          F.pp_open_hvbox fmt 0;
          (* Inner box for the projector definition *)
          F.pp_open_hvbox fmt ctx.indent_incr;
          (* Open a box for the [Definition PROJ ... :=] *)
          F.pp_open_hovbox fmt ctx.indent_incr;
          F.pp_print_string fmt "Definition";
          F.pp_print_space fmt ();
          let field_name = ctx_get_field (AdtId decl.def_id) field_id ctx in
          F.pp_print_string fmt field_name;
          F.pp_print_space fmt ();
          (* Print the type parameters *)
          if type_params <> [] then (
            F.pp_print_string fmt "{";
            List.iter
              (fun p ->
                F.pp_print_string fmt p;
                F.pp_print_space fmt ())
              type_params;
            F.pp_print_string fmt ":";
            F.pp_print_space fmt ();
            F.pp_print_string fmt "Type}";
            F.pp_print_space fmt ());
          (* Print the record parameter *)
          F.pp_print_string fmt "(";
          F.pp_print_string fmt record_var;
          F.pp_print_space fmt ();
          F.pp_print_string fmt ":";
          F.pp_print_space fmt ();
          F.pp_print_string fmt def_name;
          List.iter
            (fun p ->
              F.pp_print_space fmt ();
              F.pp_print_string fmt p)
            type_params;
          F.pp_print_string fmt ")";
          (* *)
          F.pp_print_space fmt ();
          F.pp_print_string fmt ":=";
          (* Close the box for the [Definition PROJ ... :=] *)
          F.pp_close_box fmt ();
          F.pp_print_space fmt ();
          (* Open a box for the whole match *)
          F.pp_open_hvbox fmt 0;
          (* Open a box for the [match ... with] *)
          F.pp_open_hovbox fmt ctx.indent_incr;
          F.pp_print_string fmt "match";
          F.pp_print_space fmt ();
          F.pp_print_string fmt record_var;
          F.pp_print_space fmt ();
          F.pp_print_string fmt "with";
          (* Close the box for the [match ... with] *)
          F.pp_close_box fmt ();

          (* Open a box for the branch *)
          F.pp_open_hovbox fmt ctx.indent_incr;
          (* Print the match branch *)
          F.pp_print_space fmt ();
          F.pp_print_string fmt "|";
          F.pp_print_space fmt ();
          F.pp_print_string fmt cons_name;
          FieldId.iteri
            (fun id _ ->
              F.pp_print_space fmt ();
              if field_id = id then F.pp_print_string fmt field_var
              else F.pp_print_string fmt "_")
            fields;
          F.pp_print_space fmt ();
          F.pp_print_string fmt "=>";
          F.pp_print_space fmt ();
          F.pp_print_string fmt field_var;
          (* Close the box for the branch *)
          F.pp_close_box fmt ();
          (* Print the [end] *)
          F.pp_print_space fmt ();
          F.pp_print_string fmt "end";
          (* Close the box for the whole match *)
          F.pp_close_box fmt ();
          (* Close the inner box projector *)
          F.pp_close_box fmt ();
          (* If Coq: end the definition with a "." *)
          print_decl_end_delimiter fmt kind;
          (* Close the outer box projector  *)
          F.pp_close_box fmt ();
          (* Add breaks to insert new lines between definitions *)
          F.pp_print_break fmt 0 0
        in

        let extract_proj_notation (field_id : FieldId.id) (_ : field) : unit =
          F.pp_print_space fmt ();
          (* Outer box for the projector definition *)
          F.pp_open_hvbox fmt 0;
          (* Inner box for the projector definition *)
          F.pp_open_hovbox fmt ctx.indent_incr;
          let ctx, record_var = ctx_add_var "x" (VarId.of_int 0) ctx in
          F.pp_print_string fmt "Notation";
          F.pp_print_space fmt ();
          let field_name = ctx_get_field (AdtId decl.def_id) field_id ctx in
          F.pp_print_string fmt ("\"" ^ record_var ^ " .(" ^ field_name ^ ")\"");
          F.pp_print_space fmt ();
          F.pp_print_string fmt ":=";
          F.pp_print_space fmt ();
          F.pp_print_string fmt "(";
          F.pp_print_string fmt field_name;
          F.pp_print_space fmt ();
          F.pp_print_string fmt record_var;
          F.pp_print_string fmt ")";
          F.pp_print_space fmt ();
          F.pp_print_string fmt "(at level 9)";
          (* Close the inner box projector *)
          F.pp_close_box fmt ();
          (* If Coq: end the definition with a "." *)
          print_decl_end_delimiter fmt kind;
          (* Close the outer box projector  *)
          F.pp_close_box fmt ();
          (* Add breaks to insert new lines between definitions *)
          F.pp_print_break fmt 0 0
        in

        let extract_field_proj_and_notation (field_id : FieldId.id)
            (field : field) : unit =
          extract_field_proj field_id field;
          extract_proj_notation field_id field
        in

        FieldId.iteri extract_field_proj_and_notation fields

(** Extract extra information for a type (e.g., [Arguments] instructions in Coq).

    Note that all the names used for extraction should already have been
    registered.
 *)
let extract_type_decl_extra_info (ctx : extraction_ctx) (fmt : F.formatter)
    (kind : decl_kind) (decl : type_decl) : unit =
  match !backend with
  | FStar | Lean -> ()
  | Coq ->
      extract_type_decl_coq_arguments ctx fmt kind decl;
      extract_type_decl_record_field_projectors ctx fmt kind decl

(** Extract the state type declaration. *)
let extract_state_type (fmt : F.formatter) (ctx : extraction_ctx)
    (kind : decl_kind) : unit =
  (* Add a break before *)
  F.pp_print_break fmt 0 0;
  (* Print a comment  *)
  extract_comment fmt "The state type used in the state-error monad";
  F.pp_print_space fmt ();
  (* Open a box for the definition, so that whenever possible it gets printed on
   * one line *)
  F.pp_open_hvbox fmt 0;
  (* Retrieve the name *)
  let state_name = ctx_get_assumed_type State ctx in
  (* The syntax for Lean and Coq is almost identical. *)
  let print_axiom () =
    if !backend = Coq then
      F.pp_print_string fmt "Axiom"
    else
      F.pp_print_string fmt "axiom";
    F.pp_print_space fmt ();
    F.pp_print_string fmt state_name;
    F.pp_print_space fmt ();
    F.pp_print_string fmt ":";
    F.pp_print_space fmt ();
    F.pp_print_string fmt "Type";
    if !backend = Coq then
      F.pp_print_string fmt "."
  in
  (* The kind should be [Assumed] or [Declared] *)
  (match kind with
  | SingleNonRec | SingleRec | MutRecFirst | MutRecInner | MutRecLast ->
      raise (Failure "Unexpected")
  | Assumed -> (
      match !backend with
      | FStar ->
          F.pp_print_string fmt "assume";
          F.pp_print_space fmt ();
          F.pp_print_string fmt "type";
          F.pp_print_space fmt ();
          F.pp_print_string fmt state_name;
          F.pp_print_space fmt ();
          F.pp_print_string fmt ":";
          F.pp_print_space fmt ();
          F.pp_print_string fmt "Type0"
      | Coq | Lean ->
          print_axiom ())
  | Declared -> (
      match !backend with
      | FStar ->
          F.pp_print_string fmt "val";
          F.pp_print_space fmt ();
          F.pp_print_string fmt state_name;
          F.pp_print_space fmt ();
          F.pp_print_string fmt ":";
          F.pp_print_space fmt ();
          F.pp_print_string fmt "Type0"
      | Coq | Lean ->
          print_axiom ()));
  (* Close the box for the definition *)
  F.pp_close_box fmt ();
  (* Add breaks to insert new lines between definitions *)
  F.pp_print_break fmt 0 0

(** Compute the names for all the pure functions generated from a rust function
    (forward function and backward functions).
 *)
let extract_fun_decl_register_names (ctx : extraction_ctx) (keep_fwd : bool)
    (has_decreases_clause : fun_decl -> bool) (def : pure_fun_translation) :
    extraction_ctx =
  let (fwd, loop_fwds), back_ls = def in
  (* Register the decrease clauses, if necessary *)
  let register_decreases ctx def =
    if has_decreases_clause def then
      let ctx = ctx_add_decreases_clause def ctx in
      ctx_add_terminates_clause def ctx
    else
      ctx
  in
  let ctx = List.fold_left register_decreases ctx (fwd :: loop_fwds) in
  (* Register the function names *)
  let register_fun ctx f = ctx_add_fun_decl (keep_fwd, def) f ctx in
  let register_funs ctx fl = List.fold_left register_fun ctx fl in
  (* Register the forward functions' names *)
  let ctx = register_funs ctx (fwd :: loop_fwds) in
  (* Register the backward functions' names *)
  let ctx =
    List.fold_left
      (fun ctx (back, loop_backs) ->
        let ctx = register_fun ctx back in
        register_funs ctx loop_backs)
      ctx back_ls
  in

  (* Return *)
  ctx

(** Simply add the global name to the context. *)
let extract_global_decl_register_names (ctx : extraction_ctx)
    (def : A.global_decl) : extraction_ctx =
  ctx_add_global_decl_and_body def ctx

(** The following function factorizes the extraction of ADT values.

    Note that patterns can introduce new variables: we thus return an extraction
    context updated with new bindings.

    TODO: we don't need something very generic anymore (some definitions used
    to be polymorphic).

    TODO: this does roughly the same thing as extract_adt_cons -- make the
    latter call the former
 *)
let extract_adt_g_value
    (extract_value : extraction_ctx -> bool -> 'v -> extraction_ctx)
    (fmt : F.formatter) (ctx : extraction_ctx) (inside : bool)
    (variant_id : VariantId.id option) (field_values : 'v list) (ty : ty) :
    extraction_ctx =
  match ty with
  | Adt (Tuple, _) ->
      (* Tuple *)
      (* This is very annoying: in Coq, we can't write [()] for the value of
         type [unit], we have to write [tt]. *)
      if !backend = Coq && field_values = [] then (
        F.pp_print_string fmt "tt";
        ctx)
      else (
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
        ctx)
  | Adt (adt_id, _) ->
      (* "Regular" ADT *)
      (* We print something of the form: [Cons field0 ... fieldn].
       * We could update the code to print something of the form:
       * [{ field0=...; ...; fieldn=...; }] in case of structures.
       *)
      let cons =
        match variant_id with
        | Some vid ->
            if !backend = Lean then
              ctx_get_type adt_id ctx ^ "." ^ ctx_get_variant adt_id vid ctx
            else
              ctx_get_variant adt_id vid ctx
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

(* Extract globals in the same way as variables *)
let extract_global (ctx : extraction_ctx) (fmt : F.formatter)
    (id : A.GlobalDeclId.id) : unit =
  F.pp_print_string fmt (ctx_get_global id ctx)

(** [inside]: see {!extract_ty}.

    As a pattern can introduce new variables, we return an extraction context
    updated with new bindings.
 *)
let rec extract_typed_pattern (ctx : extraction_ctx) (fmt : F.formatter)
    (inside : bool) (v : typed_pattern) : extraction_ctx =
  match v.value with
  | PatConstant cv ->
      ctx.fmt.extract_primitive_value fmt inside cv;
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
    - right-expression in a let: [let x = re in _] (never parentheses?)
    - next expression in a let:  [let x = _ in next_e] (never parentheses?)
    - application argument: [f (exp)]
    - match/if scrutinee: [if exp then _ else _]/[match exp | _ -> _]
 *)
let rec extract_texpression (ctx : extraction_ctx) (fmt : F.formatter)
    (inside : bool) (e : texpression) : unit =
  match e.e with
  | Var var_id ->
      let var_name = ctx_get_var var_id ctx in
      F.pp_print_string fmt var_name
  | Const cv -> ctx.fmt.extract_primitive_value fmt inside cv
  | App _ ->
      let app, args = destruct_apps e in
      extract_App ctx fmt inside app args
  | Abs _ ->
      let xl, e = destruct_abs_list e in
      extract_Abs ctx fmt inside xl e
  | Qualif _ ->
      (* We use the app case *)
      extract_App ctx fmt inside e []
  | Let (_, _, _, _) -> extract_lets ctx fmt inside e
  | Switch (scrut, body) -> extract_Switch ctx fmt inside scrut body
  | Meta (_, e) -> extract_texpression ctx fmt inside e
  | Loop _ ->
      (* The loop nodes should have been eliminated in {!PureMicroPasses} *)
      raise (Failure "Unreachable")

(* Extract an application *or* a top-level qualif (function extraction has
 * to handle top-level qualifiers, so it seemed more natural to merge the
 * two cases) *)
and extract_App (ctx : extraction_ctx) (fmt : F.formatter) (inside : bool)
    (app : texpression) (args : texpression list) : unit =
  (* We don't do the same thing if the app is a top-level identifier (function,
   * ADT constructor...) or a "regular" expression *)
  match app.e with
  | Qualif qualif -> (
      (* Top-level qualifier *)
      match qualif.id with
      | FunOrOp fun_id ->
          extract_function_call ctx fmt inside fun_id qualif.type_args args
      | Global global_id -> extract_global ctx fmt global_id
      | AdtCons adt_cons_id ->
          extract_adt_cons ctx fmt inside adt_cons_id qualif.type_args args
      | Proj proj ->
          extract_field_projector ctx fmt inside app proj qualif.type_args args)
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
    (inside : bool) (fid : fun_or_op_id) (type_args : ty list)
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
  | Fun fun_id, _ ->
      if inside then F.pp_print_string fmt "(";
      (* Open a box for the function call *)
      F.pp_open_hovbox fmt ctx.indent_incr;
      (* Print the function name *)
      let fun_name = ctx_get_function fun_id ctx in
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
  | (Unop _ | Binop _), _ ->
      raise
        (Failure
           ("Unreachable:\n" ^ "Function: " ^ show_fun_or_op_id fid
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
      (* This is very annoying: in Coq, we can't write [()] for the value of
         type [unit], we have to write [tt]. *)
      assert (List.length type_args = List.length args);
      if !backend = Coq && args = [] then F.pp_print_string fmt "tt"
      else (
        F.pp_print_string fmt "(";
        Collections.List.iter_link
          (fun () ->
            F.pp_print_string fmt ",";
            F.pp_print_space fmt ())
          (fun v -> extract_texpression ctx fmt false v)
          args;
        F.pp_print_string fmt ")")
  | _ ->
      (* "Regular" ADT *)
      (* We print something of the form: [Cons field0 ... fieldn].
       * We could update the code to print something of the form:
       * [{ field0=...; ...; fieldn=...; }] in case of fully
       * applied structure constructors.
       *)
      let cons =
        match adt_cons.variant_id with
        | Some vid ->
            if !backend = Lean then
              ctx_get_type adt_cons.adt_id ctx ^ "." ^ ctx_get_variant adt_cons.adt_id vid ctx
            else
              ctx_get_variant adt_cons.adt_id vid ctx
        | None -> ctx_get_struct adt_cons.adt_id ctx
      in
      let is_lean_struct = !backend = Lean && adt_cons.variant_id = None in
      if is_lean_struct then
        (* TODO: when only one or two fields differ, considering using the with
           syntax (peephole optimization) *)
        let decl_id = match adt_cons.adt_id with | AdtId id -> id | _ -> assert false in
        let def_kind = (TypeDeclId.Map.find decl_id ctx.trans_ctx.type_context.type_decls).kind in
        let fields = match def_kind with | T.Struct fields -> fields | _ -> assert false in
        let fields = FieldId.mapi (fun fid f -> (fid, f)) fields in
        F.pp_open_hvbox fmt 0;
        F.pp_open_hvbox fmt ctx.indent_incr;
        F.pp_print_string fmt "{";
        F.pp_print_space fmt ();
        F.pp_open_hvbox fmt ctx.indent_incr;
        F.pp_open_hvbox fmt 0;
        Collections.List.iter_link
          (fun () ->
            F.pp_print_string fmt ",";
            F.pp_close_box fmt ();
            F.pp_print_space fmt ()
          )
          (fun ((fid, _), e) ->
            F.pp_open_hovbox fmt 0;
            let f = ctx_get_field adt_cons.adt_id fid ctx in
            F.pp_print_string fmt f;
            F.pp_print_string fmt " := ";
            F.pp_open_hvbox fmt ctx.indent_incr;
            extract_texpression ctx fmt true e;
            F.pp_close_box fmt ()
          )
          (List.combine fields args);
        F.pp_close_box fmt ();
        F.pp_close_box fmt ();
        F.pp_close_box fmt ();
        F.pp_close_box fmt ();
        F.pp_print_space fmt ();
        F.pp_print_string fmt "}"
      else
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
   * projection ([x.field] instead of [MkAdt?.field x] *)
  match args with
  | [ arg ] ->
      (* Exactly one argument: pretty-print *)
      let field_name = ctx_get_field proj.adt_id proj.field_id ctx in
      (* Open a box *)
      F.pp_open_hovbox fmt ctx.indent_incr;
      (* Extract the expression *)
      extract_texpression ctx fmt true arg;
      (* We allow to break where the "." appears (except Lean, it's a syntax error) *)
      if !backend <> Lean then
        F.pp_print_break fmt 0 0;
      F.pp_print_string fmt ".";
      (* If in Coq, the field projection has to be parenthesized *)
      (match !backend with
      | FStar -> F.pp_print_string fmt field_name
      | Coq -> F.pp_print_string fmt ("(" ^ field_name ^ ")")
      | Lean -> F.pp_print_string fmt field_name
      );
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

and extract_lets (ctx : extraction_ctx) (fmt : F.formatter) (inside : bool)
    (e : texpression) : unit =
  let lets, next_e = destruct_lets e in
  (* Open a box for the whole expression *)
  F.pp_open_hvbox fmt 0;
  (* Open parentheses *)
  if inside && !backend <> Lean then F.pp_print_string fmt "(";
  (* Extract the let-bindings *)
  let extract_let (ctx : extraction_ctx) (monadic : bool) (lv : typed_pattern)
      (re : texpression) : extraction_ctx =
    (* Open a box for the let-binding *)
    F.pp_open_hovbox fmt ctx.indent_incr;
    let is_fstar_monadic = monadic && !backend = FStar in
    let ctx =
      (* There are two cases:
       * - do we use a notation like [x <-- y;]
       * - do we use notation with let-bindings
       * Note that both notations can be used for monadic let-bindings.
       * For instance, in F*, you can write:
       * {[
       *   let* x = y in // monadic
       *   ...
       * ]}
       * *)
      if monadic && !backend = Coq then (
        let ctx = extract_typed_pattern ctx fmt true lv in
        F.pp_print_space fmt ();
        let arrow = match !backend with FStar -> "<--" | Coq -> "<-" | Lean -> failwith "impossible" in
        F.pp_print_string fmt arrow;
        F.pp_print_space fmt ();
        extract_texpression ctx fmt false re;
        F.pp_print_string fmt ";";
        ctx)
      else (
        F.pp_print_string fmt (if is_fstar_monadic then "let*" else "let");
        F.pp_print_space fmt ();
        let ctx = extract_typed_pattern ctx fmt true lv in
        F.pp_print_space fmt ();
        let eq = match !backend with FStar -> "=" | Coq -> ":=" | Lean -> if monadic then "<-" else ":=" in
        F.pp_print_string fmt eq;
        F.pp_print_space fmt ();
        extract_texpression ctx fmt false re;
        F.pp_print_space fmt ();
        if !backend <> Lean then
          F.pp_print_string fmt "in";
        ctx)
    in
    (* Close the box for the let-binding *)
    F.pp_close_box fmt ();
    F.pp_print_space fmt ();
    (* Return *)
    ctx
  in
  let exists_monadic = List.exists (fun (m, _, _) -> m) lets in
  (* If Lean, we rely on monadic blocks, so we insert a do and open a new box
     immediately *)
  if !backend = Lean && exists_monadic then begin
    F.pp_open_vbox fmt ctx.indent_incr;
    F.pp_print_string fmt "do";
    F.pp_print_space fmt ();
  end;
  let ctx =
    List.fold_left
      (fun ctx (monadic, lv, re) -> extract_let ctx monadic lv re)
      ctx lets
  in
  (* Open a box for the next expression *)
  F.pp_open_hovbox fmt ctx.indent_incr;
  (* Print the next expression *)
  extract_texpression ctx fmt false next_e;
  (* Close the box for the next expression *)
  F.pp_close_box fmt ();
  (* do-box (Lean only) *)
  if !backend = Lean && exists_monadic then
    F.pp_close_box fmt ();
  (* Close parentheses *)
  if inside && !backend <> Lean then F.pp_print_string fmt ")";
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
      (* Open a box for the [if] *)
      F.pp_open_hovbox fmt ctx.indent_incr;
      F.pp_print_string fmt "if";
      F.pp_print_space fmt ();
      let scrut_inside = PureUtils.let_group_requires_parentheses scrut in
      extract_texpression ctx fmt scrut_inside scrut;
      (* Close the box for the [if] *)
      F.pp_close_box fmt ();
      (* Extract the branches *)
      let extract_branch (is_then : bool) (e_branch : texpression) : unit =
        F.pp_print_space fmt ();
        (* Open a box for the then/else+branch *)
        F.pp_open_hovbox fmt ctx.indent_incr;
        let then_or_else = if is_then then "then" else "else" in
        F.pp_print_string fmt then_or_else;
        let parenth = PureUtils.let_group_requires_parentheses e_branch in
        (* Open a box for the branch - we do this only if it is not a parenthesized
           group of nested let bindings.
        *)
        if not parenth then (
          F.pp_print_space fmt ();
          F.pp_open_hovbox fmt ctx.indent_incr);
        (* Open the parenthesized expression *)
        (if parenth then
         match !backend with
         | FStar ->
             F.pp_print_space fmt ();
             F.pp_print_string fmt "begin";
             F.pp_print_space fmt ()
         | Coq ->
             F.pp_print_string fmt " (";
             F.pp_print_cut fmt ()
         | Lean ->
             F.pp_print_cut fmt ()
        );
        (* Print the branch expression *)
        extract_texpression ctx fmt false e_branch;
        (* Close the parenthesized expression *)
        (if parenth then
         match !backend with
         | FStar ->
             F.pp_print_space fmt ();
             F.pp_print_string fmt "end"
         | Coq -> F.pp_print_string fmt ")"
         | Lean -> ()
        );
        (* Close the box for the branch *)
        if not parenth then F.pp_close_box fmt ();
        (* Close the box for the then/else+branch *)
        F.pp_close_box fmt ()
      in

      extract_branch true e_then;
      extract_branch false e_else
  | Match branches ->
      (* Open a box for the [match ... with] *)
      F.pp_open_hovbox fmt ctx.indent_incr;
      (* Print the [match ... with] *)
      let match_begin =
        match !backend with FStar -> "begin match" | Coq | Lean -> "match"
      in
      F.pp_print_string fmt match_begin;
      F.pp_print_space fmt ();
      let scrut_inside = PureUtils.let_group_requires_parentheses scrut in
      extract_texpression ctx fmt scrut_inside scrut;
      F.pp_print_space fmt ();
      F.pp_print_string fmt "with";
      (* Close the box for the [match ... with] *)
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
        let arrow = match !backend with FStar -> "->" | Coq | Lean -> "=>" in
        F.pp_print_string fmt arrow;
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
      (* Relying on indentation in Lean *)
      if !backend <> Lean then
        F.pp_print_string fmt "end");
  (* Close parentheses *)
  if inside then F.pp_print_string fmt ")";
  (* Close the box for the whole expression *)
  F.pp_close_box fmt ()

(** Insert a space, if necessary *)
let insert_req_space (fmt : F.formatter) (space : bool ref) : unit =
  if !space then space := false else F.pp_print_space fmt ()

(** A small utility to print the parameters of a function signature.

    We return two contexts:
    - the context augmented with bindings for the type parameters
    - the previous context augmented with bindings for the input values
 *)
let extract_fun_parameters (space : bool ref) (ctx : extraction_ctx)
    (fmt : F.formatter) (def : fun_decl) : extraction_ctx * extraction_ctx =
  (* Add the type parameters - note that we need those bindings only for the
   * body translation (they are not top-level) *)
  let ctx, _ = ctx_add_type_params def.signature.type_params ctx in
  (* Print the parameters - rk.: we should have filtered the functions
   * with no input parameters *)
  (* The type parameters *)
  if def.signature.type_params <> [] then (
    (* Open a box for the type parameters *)
    F.pp_open_hovbox fmt 0;
    insert_req_space fmt space;
    F.pp_print_string fmt "(";
    List.iter
      (fun (p : type_var) ->
        let pname = ctx_get_type_var p.index ctx in
        F.pp_print_string fmt pname;
        F.pp_print_space fmt ())
      def.signature.type_params;
    F.pp_print_string fmt ":";
    F.pp_print_space fmt ();
    let type_keyword = match !backend with FStar -> "Type0" | Coq | Lean -> "Type" in
    F.pp_print_string fmt (type_keyword ^ ")");
    (* Close the box for the type parameters *)
    F.pp_close_box fmt ());
  (* The input parameters - note that doing this adds bindings to the context *)
  let ctx_body =
    match def.body with
    | None -> ctx
    | Some body ->
        List.fold_left
          (fun ctx (lv : typed_pattern) ->
            insert_req_space fmt space;
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
            ctx)
          ctx body.inputs_lvs
  in
  (ctx, ctx_body)

(** A small utility to print the types of the input parameters in the form:
    [u32 -> list u32 -> ...]
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

let assert_backend_supports_decreases_clauses () =
  match !backend with
  | FStar | Lean -> ()
  | _ -> failwith "decreases clauses only supported for the Lean & F* backends"

(** Extract a decrease clause function template body.

    Only for F*.

    In order to help the user, we can generate a template for the functions
    required by the decreases clauses for. We simply generate definitions of
    the following form in a separate file:
    {[
      let f_decrease (t : Type0) (x : t) : nat = admit()
    ]}

    Where the translated functions for [f] look like this:
    {[
      let f_fwd (t : Type0) (x : t) : Tot ... (decreases (f_decrease t x)) = ...
    ]}
 *)
let extract_template_decreases_clause (ctx : extraction_ctx) (fmt : F.formatter)
    (def : fun_decl) : unit =
  assert (!backend = FStar);

  (* Retrieve the function name *)
  let def_name = ctx_get_decreases_clause def.def_id def.loop_id ctx in
  (* Add a break before *)
  F.pp_print_break fmt 0 0;
  (* Print a comment to link the extracted type to its original rust definition *)
  extract_comment fmt ("[" ^ Print.fun_name_to_string def.basename ^ "]: decreases clause");
  F.pp_print_space fmt ();
  (* Open a box for the definition, so that whenever possible it gets printed on
   * one line *)
  F.pp_open_hvbox fmt 0;
  (* Add the [unfold] keyword *)
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
  let space = ref true in
  let _, _ = extract_fun_parameters space ctx fmt def in
  insert_req_space fmt space;
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

(** Extract templates for the termination_by and decreases_by clauses of a
    recursive function definition.

    For Lean only.

    We extract two commands. The first one is a regular definition for the
    termination measure (the value derived from the function arguments that
    decreases over function calls). The second one is a macro definition that
    defines a proof script (allowed to refer to function arguments) that proves
    termination.
*)
let extract_termination_and_decreasing (ctx: extraction_ctx) (fmt: F.formatter) (def: fun_decl): unit =
  assert (!backend = Lean);

  (* Retrieve the function name *)
  let def_name = ctx_get_terminates_clause def.def_id def.loop_id ctx in
  let def_body = Option.get def.body in
  (* Add a break before *)
  F.pp_print_break fmt 0 0;
  (* Print a comment to link the extracted type to its original rust definition *)
  extract_comment fmt ("[" ^ Print.fun_name_to_string def.basename ^ "]: termination measure");
  F.pp_print_space fmt ();
  (* Open a box for the definition, so that whenever possible it gets printed on
   * one line *)
  F.pp_open_hvbox fmt 0;
  (* Add the [unfold] keyword *)
  F.pp_print_string fmt "@[simp]";
  F.pp_print_space fmt ();
  (* Open a box for "let FUN_NAME (PARAMS) : EFFECT = admit()" *)
  F.pp_open_hvbox fmt ctx.indent_incr;
  (* Open a box for "let FUN_NAME (PARAMS) : EFFECT =" *)
  F.pp_open_hovbox fmt ctx.indent_incr;
  (* > "let FUN_NAME" *)
  F.pp_print_string fmt ("def " ^ def_name);
  F.pp_print_space fmt ();
  (* Extract the parameters *)
  let space = ref true in
  let _, ctx_body = extract_fun_parameters space ctx fmt def in
  (* Print the ":=" *)
  F.pp_print_space fmt ();
  F.pp_print_string fmt ":=";
  (* Close the box for "let FUN_NAME (PARAMS) : EFFECT =" *)
  F.pp_close_box fmt ();
  F.pp_print_space fmt ();
  (* Tuple of the arguments *)
  let vars = List.map (fun (v: var) -> v.id) def_body.inputs in
  if List.length vars = 1 then
    F.pp_print_string fmt (ctx_get_var (List.hd vars) ctx_body)
  else begin
    F.pp_open_hovbox fmt 0;
    F.pp_print_string fmt "(";
    Collections.List.iter_link
      (fun () ->
        F.pp_print_string fmt ",";
        F.pp_print_space fmt ())
      (fun v -> F.pp_print_string fmt (ctx_get_var v ctx_body))
      vars;
    F.pp_print_string fmt ")";
    F.pp_close_box fmt ();
  end;
  (* Close the box for "let FUN_NAME (PARAMS) : EFFECT = admit()" *)
  F.pp_close_box fmt ();
  (* Close the box for the whole definition *)
  F.pp_close_box fmt ();
  (* Add breaks to insert new lines between definitions *)
  F.pp_print_break fmt 0 0;

  (* Now extract a template for the termination proof *)
  let def_name = ctx_get_decreases_clause def.def_id def.loop_id ctx in
  (* syntax <def_name> term ... term : tactic *)
  F.pp_print_break fmt 0 0;
  F.pp_open_hvbox fmt 0;
  F.pp_print_string fmt "syntax \"";
  F.pp_print_string fmt def_name;
  F.pp_print_string fmt "\" term+ : tactic";
  F.pp_print_break fmt 0 0;
  F.pp_print_break fmt 0 0;
  (* macro_rules | `(tactic| fact_termination_proof $x) => `(tactic| ( *)
  F.pp_print_string fmt "macro_rules";
  F.pp_print_space fmt ();
  F.pp_open_hovbox fmt ctx.indent_incr;
  F.pp_open_hovbox fmt 0;
  F.pp_print_string fmt "| `(tactic| ";
  F.pp_print_string fmt def_name;
  F.pp_print_space fmt ();
  Collections.List.iter_link (F.pp_print_space fmt)
    (fun v ->
      F.pp_print_string fmt "$";
      F.pp_print_string fmt (ctx_get_var v ctx_body))
    vars;
  F.pp_print_string fmt ") =>";
  F.pp_close_box fmt ();
  F.pp_open_hovbox fmt ctx.indent_incr;
  F.pp_print_string fmt "`(tactic| sorry)";
  F.pp_close_box fmt ();
  F.pp_close_box fmt ();
  F.pp_close_box fmt ();
  F.pp_print_break fmt 0 0

(** Extract a function declaration.

    Note that all the names used for extraction should already have been
    registered.

    We take the definition of the forward translation as parameter (which is
    equal to the definition to extract, if we extract a forward function) because
    it is useful for the decrease clause.
 *)
let extract_fun_decl (ctx : extraction_ctx) (fmt : F.formatter)
    (kind : decl_kind) (has_decreases_clause : bool) (def : fun_decl) : unit =
  assert (not def.is_global_decl_body);
  (* Retrieve the function name *)
  let def_name =
    ctx_get_local_function def.def_id def.loop_id def.back_id ctx
  in
  (* Add a break before *)
  F.pp_print_break fmt 0 0;
  (* Print a comment to link the extracted type to its original rust definition *)
  extract_comment fmt ("[" ^ Print.fun_name_to_string def.basename ^ "]");
  F.pp_print_space fmt ();
  (* Open two boxes for the definition, so that whenever possible it gets printed on
   * one line and indents are correct *)
  F.pp_open_hvbox fmt 0;
  F.pp_open_hvbox fmt ctx.indent_incr;
  (* Open a box for "let FUN_NAME (PARAMS) : EFFECT =" *)
  F.pp_open_hovbox fmt ctx.indent_incr;
  (* > "let FUN_NAME" *)
  let is_opaque = Option.is_none def.body in
  (* If in Coq and the declaration is opaque, it must have the shape:
     [Axiom Ident : forall (T0 ... Tn : Type), ... -> ... -> ...].

     The boolean [is_opaque_coq] is used to detect this case.
  *)
  let is_opaque_coq = !backend = Coq && is_opaque in
  let use_forall = is_opaque_coq && def.signature.type_params <> [] in
  (* *)
  let qualif = ctx.fmt.fun_decl_kind_to_qualif kind in
  F.pp_print_string fmt (qualif ^ " " ^ def_name);
  F.pp_print_space fmt ();
  if use_forall then (
    F.pp_print_string fmt ":";
    F.pp_print_space fmt ();
    F.pp_print_string fmt "forall");
  (* Open a box for "(PARAMS) : EFFECT =" *)
  F.pp_open_hvbox fmt 0;
  (* Open a box for "(PARAMS) :" *)
  F.pp_open_hovbox fmt 0;
  let space = ref true in
  let ctx, ctx_body = extract_fun_parameters space ctx fmt def in
  (* Print the return type - note that we have to be careful when
   * printing the input values for the decrease clause, because
   * it introduces bindings in the context... We thus "forget"
   * the bindings we introduced above.
   * TODO: figure out a cleaner way *)
  let _ =
    if use_forall then F.pp_print_string fmt ","
    else (
      insert_req_space fmt space;
      F.pp_print_string fmt ":");
    (* Close the box for "(PARAMS) :" *)
    F.pp_close_box fmt ();
    F.pp_print_space fmt ();
    (* Open a box for the EFFECT *)
    F.pp_open_hvbox fmt 0;
    (* Open a box for the return type *)
    F.pp_open_hovbox fmt ctx.indent_incr;
    (* Print the return type *)
    (* For opaque definitions, as we don't have named parameters under the hand,
     * we don't print parameters in the form [(x : a) (y : b) ...] above,
     * but wait until here to print the types: [a -> b -> ...]. *)
    if is_opaque then extract_fun_input_parameters_types ctx fmt def;
    (* [Tot] *)
    if has_decreases_clause then (
      assert_backend_supports_decreases_clauses ();
      F.pp_print_string fmt "Tot";
      F.pp_print_space fmt ());
    extract_ty ctx fmt has_decreases_clause def.signature.output;
    (* Close the box for the return type *)
    F.pp_close_box fmt ();
    (* Print the decrease clause - rk.: a function with a decreases clause
     * is necessarily a transparent function *)
    if has_decreases_clause then (
      assert_backend_supports_decreases_clauses ();
      F.pp_print_space fmt ();
      (* Open a box for the decreases clause *)
      F.pp_open_hovbox fmt ctx.indent_incr;
      (* *)
      F.pp_print_string fmt "(decreases (";
      F.pp_print_cut fmt ();
      (* Open a box for the decreases term *)
      F.pp_open_hovbox fmt ctx.indent_incr;
      (* The name of the decrease clause *)
      let decr_name = ctx_get_decreases_clause def.def_id def.loop_id ctx in
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
       * functions - we also ignore the additional state received by the
       * backward function, if there is one).
       *)
      let inputs_lvs =
        let all_inputs = (Option.get def.body).inputs_lvs in
        let num_fwd_inputs =
          def.signature.info.num_fwd_inputs_with_fuel_with_state
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
      (* Close the box for the decreases term *)
      F.pp_close_box fmt ();
      (* Close the box for the decreases clause *)
      F.pp_close_box fmt ());
    (* Close the box for the EFFECT *)
    F.pp_close_box fmt ()
  in
  (* Print the "=" *)
  if not is_opaque then (
    F.pp_print_space fmt ();
    let eq = match !backend with FStar -> "=" | Coq | Lean -> ":=" in
    F.pp_print_string fmt eq);
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
  (* Close the inner box for the definition *)
  F.pp_close_box fmt ();
  (* Coq: add a "." *)
  print_decl_end_delimiter fmt kind;
  (* Close the outer box for the definition *)
  F.pp_close_box fmt ();
  (* Add breaks to insert new lines between definitions *)
  F.pp_print_break fmt 0 0

(** Extract a global declaration body of the shape "QUALIF NAME : TYPE = BODY"
    with a custom body extractor
 *)
let extract_global_decl_body (ctx : extraction_ctx) (fmt : F.formatter)
    (kind : decl_kind) (name : string) (ty : ty)
    (extract_body : (F.formatter -> unit) Option.t) : unit =
  let is_opaque = Option.is_none extract_body in

  (* Open the definition boxes (depth=0) *)
  F.pp_open_hvbox fmt 0;
  F.pp_open_hvbox fmt ctx.indent_incr;

  (* Open "QUALIF NAME : TYPE =" box (depth=1) *)
  F.pp_open_hovbox fmt ctx.indent_incr;
  (* Print "QUALIF NAME " *)
  F.pp_print_string fmt (ctx.fmt.fun_decl_kind_to_qualif kind);
  F.pp_print_space fmt ();
  F.pp_print_string fmt name;
  F.pp_print_space fmt ();

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
    let eq = match !backend with FStar -> "=" | Coq | Lean -> ":=" in
    F.pp_print_string fmt eq);
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
    F.pp_close_box fmt ());

  (* Close the inner definition box (depth=0) *)
  F.pp_close_box fmt ();

  (* Coq: add a "." *)
  print_decl_end_delimiter fmt Declared;

  (* Close the outer definition box (depth=0) *)
  F.pp_close_box fmt ()

(** Extract a global declaration.

    We generate the body which computes the global value separately from the
    value declaration itself.

    For example in Rust,
    [static X: u32 = 3;]

    will be translated to the following F*:
    [let x_body : result u32 = Return 3]
    [let x_c : u32 = eval_global x_body]
 *)
let extract_global_decl (ctx : extraction_ctx) (fmt : F.formatter)
    (global : A.global_decl) (body : fun_decl) (interface : bool) : unit =
  assert body.is_global_decl_body;
  assert (Option.is_none body.back_id);
  assert (List.length body.signature.inputs = 0);
  assert (List.length body.signature.doutputs = 1);
  assert (List.length body.signature.type_params = 0);

  (* Add a break then the name of the corresponding LLBC declaration *)
  F.pp_print_break fmt 0 0;
  extract_comment fmt ("[" ^ Print.global_name_to_string global.name ^ "]");
  F.pp_print_space fmt ();

  let decl_name = ctx_get_global global.def_id ctx in
  let body_name =
    ctx_get_function (FromLlbc (Regular global.body_id, None, None)) ctx
  in

  let decl_ty, body_ty =
    let ty = body.signature.output in
    if body.signature.info.effect_info.can_fail then (unwrap_result_ty ty, ty)
    else (ty, mk_result_ty ty)
  in
  match body.body with
  | None ->
      let kind = if interface then Declared else Assumed in
      extract_global_decl_body ctx fmt kind decl_name decl_ty None
  | Some body ->
      extract_global_decl_body ctx fmt SingleNonRec body_name body_ty
        (Some (fun fmt -> extract_texpression ctx fmt false body.body));
      F.pp_print_break fmt 0 0;
      extract_global_decl_body ctx fmt SingleNonRec decl_name decl_ty
        (Some
           (fun fmt ->
             let body =
               match !backend with
               | FStar -> "eval_global " ^ body_name
               | Lean -> "eval_global " ^ body_name ^ " (by simp)"
               | Coq -> body_name ^ "%global"
             in
             F.pp_print_string fmt body));
      (* Add a break to insert lines between declarations *)
      F.pp_print_break fmt 0 0

(** Extract a unit test, if the function is a unit function (takes no
    parameters, returns unit).

    A unit test simply checks that the function normalizes to [Return ()].

    F*:
    {[
      let _ = assert_norm (FUNCTION = Return ())
    ]}

    Coq:
    {[
      Check (FUNCTION)%return).
    ]}
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
    extract_comment fmt ("Unit test for [" ^ Print.fun_name_to_string def.basename ^ "]");
    F.pp_print_space fmt ();
    (* Open a box for the test *)
    F.pp_open_hovbox fmt ctx.indent_incr;
    (* Print the test *)
    (match !backend with
    | FStar ->
        F.pp_print_string fmt "let _ =";
        F.pp_print_space fmt ();
        F.pp_print_string fmt "assert_norm";
        F.pp_print_space fmt ();
        F.pp_print_string fmt "(";
        let fun_name =
          ctx_get_local_function def.def_id def.loop_id def.back_id ctx
        in
        F.pp_print_string fmt fun_name;
        if sg.inputs <> [] then (
          F.pp_print_space fmt ();
          F.pp_print_string fmt "()");
        F.pp_print_space fmt ();
        F.pp_print_string fmt "=";
        F.pp_print_space fmt ();
        let success = ctx_get_variant (Assumed Result) result_return_id ctx in
        F.pp_print_string fmt (success ^ " ())")
    | Coq ->
        F.pp_print_string fmt "Check";
        F.pp_print_space fmt ();
        F.pp_print_string fmt "(";
        let fun_name =
          ctx_get_local_function def.def_id def.loop_id def.back_id ctx
        in
        F.pp_print_string fmt fun_name;
        if sg.inputs <> [] then (
          F.pp_print_space fmt ();
          F.pp_print_string fmt "()");
        F.pp_print_space fmt ();
        F.pp_print_string fmt ")%return."
    | Lean ->
        F.pp_print_string fmt "#assert";
        F.pp_print_space fmt ();
        F.pp_print_string fmt "(";
        let fun_name =
          ctx_get_local_function def.def_id def.loop_id def.back_id ctx
        in
        F.pp_print_string fmt fun_name;
        if sg.inputs <> [] then (
          F.pp_print_space fmt ();
          F.pp_print_string fmt "()");
        F.pp_print_space fmt ();
        F.pp_print_string fmt "=";
        F.pp_print_space fmt ();
        let success = ctx_get_variant (Assumed Result) result_return_id ctx in
        F.pp_print_string fmt (success ^ " ())")
    );
    (* Close the box for the test *)
    F.pp_close_box fmt ();
    (* Add a break after *)
    F.pp_print_break fmt 0 0)
  else (* Do nothing *)
    ()
