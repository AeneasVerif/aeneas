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
    | FStar | Coq | HOL4 ->
        ("isize", "usize", format_of_string "i%d", format_of_string "u%d")
    | Lean -> ("Isize", "Usize", format_of_string "I%d", format_of_string "U%d")
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
  | Not -> (
      match !backend with FStar | Lean -> "not" | Coq -> "negb" | HOL4 -> "~")
  | Neg (int_ty : integer_type) -> (
      match !backend with Lean -> "-" | _ -> int_name int_ty ^ "_neg")
  | Cast _ ->
      (* We never directly use the unop name in this case *)
      raise (Failure "Unsupported")

(** Small helper to compute the name of a binary operation (note that many
    binary operations like "less than" are extracted to primitive operations,
    like [<]).
 *)
let named_binop_name (binop : E.binop) (int_ty : integer_type) : string =
  let binop =
    match binop with
    | Div -> "div"
    | Rem -> "rem"
    | Add -> "add"
    | Sub -> "sub"
    | Mul -> "mul"
    | Lt -> "lt"
    | Le -> "le"
    | Ge -> "ge"
    | Gt -> "gt"
    | _ -> raise (Failure "Unreachable")
  in
  (* Remark: the Lean case is actually not used *)
  match !backend with
  | Lean -> int_name int_ty ^ "." ^ binop
  | FStar | Coq | HOL4 -> int_name int_ty ^ "_" ^ binop

(** A list of keywords/identifiers used by the backend and with which we
    want to check collision.

    Remark: this is useful mostly to look for collisions when generating
    names for *variables*.
 *)
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
          "assert";
          "assert_norm";
          "assume";
          "else";
          "fun";
          "fn";
          "FStar";
          "FStar.Mul";
          "if";
          "in";
          "include";
          "int";
          "let";
          "list";
          "match";
          "not";
          "open";
          "rec";
          "scalar_cast";
          "then";
          "type";
          "Type0";
          "Type";
          "unit";
          "val";
          "with";
        ]
    | Coq ->
        [
          "assert";
          "Arguments";
          "Axiom";
          "char_of_byte";
          "Check";
          "Declare";
          "Definition";
          "else";
          "End";
          "fun";
          "Fixpoint";
          "if";
          "in";
          "int";
          "Inductive";
          "Import";
          "let";
          "Lemma";
          "match";
          "Module";
          "not";
          "Notation";
          "Proof";
          "Qed";
          "rec";
          "Record";
          "Require";
          "Scope";
          "Search";
          "SearchPattern";
          "Set";
          "then";
          (* [tt] is unit *)
          "tt";
          "type";
          "Type";
          "unit";
          "with";
        ]
    | Lean ->
        [
          "by";
          "class";
          "decreasing_by";
          "def";
          "deriving";
          "do";
          "else";
          "end";
          "for";
          "have";
          "if";
          "inductive";
          "instance";
          "import";
          "let";
          "macro";
          "match";
          "namespace";
          "opaque";
          "open";
          "run_cmd";
          "set_option";
          "simp";
          "structure";
          "syntax";
          "termination_by";
          "then";
          "Type";
          "unsafe";
          "where";
          "with";
          "opaque_defs";
        ]
    | HOL4 ->
        [
          "Axiom";
          "case";
          "Definition";
          "else";
          "End";
          "fix";
          "fix_exec";
          "fn";
          "fun";
          "if";
          "in";
          "int";
          "Inductive";
          "let";
          "of";
          "Proof";
          "QED";
          "then";
          "Theorem";
        ]
  in
  List.concat [ named_unops; named_binops; misc ]

let assumed_adts () : (assumed_ty * string) list =
  match !backend with
  | Lean ->
      [
        (State, "State");
        (Result, "Result");
        (Error, "Error");
        (Fuel, "Nat");
        (Option, "Option");
        (Vec, "Vec");
        (Array, "Array");
        (Slice, "Slice");
        (Str, "Str");
        (Range, "Range");
      ]
  | Coq | FStar ->
      [
        (State, "state");
        (Result, "result");
        (Error, "error");
        (Fuel, "nat");
        (Option, "option");
        (Vec, "vec");
        (Array, "array");
        (Slice, "slice");
        (Str, "str");
        (Range, "range");
      ]
  | HOL4 ->
      [
        (State, "state");
        (Result, "result");
        (Error, "error");
        (Fuel, "num");
        (Option, "option");
        (Vec, "vec");
        (Array, "array");
        (Slice, "slice");
        (Str, "str");
        (Range, "range");
      ]

let assumed_struct_constructors () : (assumed_ty * string) list =
  match !backend with
  | Lean -> [ (Range, "Range.mk"); (Array, "Array.make") ]
  | Coq -> [ (Range, "mk_range"); (Array, "mk_array") ]
  | FStar -> [ (Range, "Mkrange"); (Array, "mk_array") ]
  | HOL4 -> [ (Range, "mk_range"); (Array, "mk_array") ]

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
  | HOL4 ->
      [
        (Result, result_return_id, "Return");
        (Result, result_fail_id, "Fail");
        (Error, error_failure_id, "Failure");
        (* No Fuel::Zero on purpose *)
        (* No Fuel::Succ on purpose *)
        (Option, option_some_id, "SOME");
        (Option, option_none_id, "NONE");
      ]

let assumed_llbc_functions () :
    (A.assumed_fun_id * T.RegionGroupId.id option * string) list =
  let rg0 = Some T.RegionGroupId.zero in
  match !backend with
  | FStar | Coq | HOL4 ->
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
        (ArrayIndexShared, None, "array_index_shared");
        (ArrayIndexMut, None, "array_index_mut_fwd");
        (ArrayIndexMut, rg0, "array_index_mut_back");
        (ArrayToSliceShared, None, "array_to_slice_shared");
        (ArrayToSliceMut, None, "array_to_slice_mut_fwd");
        (ArrayToSliceMut, rg0, "array_to_slice_mut_back");
        (ArraySubsliceShared, None, "array_subslice_shared");
        (ArraySubsliceMut, None, "array_subslice_mut_fwd");
        (ArraySubsliceMut, rg0, "array_subslice_mut_back");
        (SliceIndexShared, None, "slice_index_shared");
        (SliceIndexMut, None, "slice_index_mut_fwd");
        (SliceIndexMut, rg0, "slice_index_mut_back");
        (SliceSubsliceShared, None, "slice_subslice_shared");
        (SliceSubsliceMut, None, "slice_subslice_mut_fwd");
        (SliceSubsliceMut, rg0, "slice_subslice_mut_back");
        (SliceLen, None, "slice_len");
      ]
  | Lean ->
      [
        (Replace, None, "mem.replace");
        (Replace, rg0, "mem.replace_back");
        (VecNew, None, "Vec.new");
        (VecPush, None, "Vec.push_fwd") (* Shouldn't be used *);
        (VecPush, rg0, "Vec.push");
        (VecInsert, None, "Vec.insert_fwd") (* Shouldn't be used *);
        (VecInsert, rg0, "Vec.insert");
        (VecLen, None, "Vec.len");
        (VecIndex, None, "Vec.index_shared");
        (VecIndex, rg0, "Vec.index_shared_back") (* shouldn't be used *);
        (VecIndexMut, None, "Vec.index_mut");
        (VecIndexMut, rg0, "Vec.index_mut_back");
        (ArrayIndexShared, None, "Array.index_shared");
        (ArrayIndexMut, None, "Array.index_mut");
        (ArrayIndexMut, rg0, "Array.index_mut_back");
        (ArrayToSliceShared, None, "Array.to_slice_shared");
        (ArrayToSliceMut, None, "Array.to_slice_mut");
        (ArrayToSliceMut, rg0, "Array.to_slice_mut_back");
        (ArraySubsliceShared, None, "Array.subslice_shared");
        (ArraySubsliceMut, None, "Array.subslice_mut");
        (ArraySubsliceMut, rg0, "Array.subslice_mut_back");
        (SliceIndexShared, None, "Slice.index_shared");
        (SliceIndexMut, None, "Slice.index_mut");
        (SliceIndexMut, rg0, "Slice.index_mut_back");
        (SliceSubsliceShared, None, "Slice.subslice_shared");
        (SliceSubsliceMut, None, "Slice.subslice_mut");
        (SliceSubsliceMut, rg0, "Slice.subslice_mut_back");
        (SliceLen, None, "Slice.len");
      ]

let assumed_pure_functions () : (pure_assumed_fun_id * string) list =
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
      (* We don't provide [FuelDecrease] and [FuelEqZero] on purpose *)
      [ (Return, "return"); (Fail, "fail_"); (Assert, "massert") ]
  | HOL4 ->
      (* We don't provide [FuelDecrease] and [FuelEqZero] on purpose *)
      [ (Return, "return"); (Fail, "fail"); (Assert, "massert") ]

let names_map_init () : names_map_init =
  {
    keywords = keywords ();
    assumed_adts = assumed_adts ();
    assumed_structs = assumed_struct_constructors ();
    assumed_variants = assumed_variants ();
    assumed_llbc_functions = assumed_llbc_functions ();
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
  | Cast (src, tgt) -> (
      (* HOL4 has a special treatment: because it doesn't support dependent
         types, we don't have a specific operator for the cast *)
      match !backend with
      | HOL4 ->
          (* Casting, say, an u32 to an i32 would be done as follows:
             {[
               mk_i32 (u32_to_int x)
             ]}
          *)
          if inside then F.pp_print_string fmt "(";
          F.pp_print_string fmt ("mk_" ^ int_name tgt);
          F.pp_print_space fmt ();
          F.pp_print_string fmt "(";
          F.pp_print_string fmt (int_name src ^ "_to_int");
          F.pp_print_space fmt ();
          extract_expr true arg;
          F.pp_print_string fmt ")";
          if inside then F.pp_print_string fmt ")"
      | FStar | Coq | Lean ->
          (* Rem.: the source type is an implicit parameter *)
          if inside then F.pp_print_string fmt "(";
          let cast_str =
            match !backend with
            | Coq | FStar -> "scalar_cast"
            | Lean -> (* TODO: I8.cast, I16.cast, etc.*) "Scalar.cast"
            | HOL4 -> raise (Failure "Unreachable")
          in
          F.pp_print_string fmt cast_str;
          F.pp_print_space fmt ();
          if !backend <> Lean then (
            F.pp_print_string fmt
              (StringUtils.capitalize_first_letter
                 (PrintPure.integer_type_to_string src));
            F.pp_print_space fmt ());
          if !backend = Lean then F.pp_print_string fmt ("." ^ int_name tgt)
          else
            F.pp_print_string fmt
              (StringUtils.capitalize_first_letter
                 (PrintPure.integer_type_to_string tgt));
          F.pp_print_space fmt ();
          extract_expr true arg;
          if inside then F.pp_print_string fmt ")")

(** [extract_expr] : the boolean argument is [inside] *)
let extract_binop (extract_expr : bool -> texpression -> unit)
    (fmt : F.formatter) (inside : bool) (binop : E.binop)
    (int_ty : integer_type) (arg0 : texpression) (arg1 : texpression) : unit =
  if inside then F.pp_print_string fmt "(";
  (* Some binary operations have a special notation depending on the backend *)
  (match (!backend, binop) with
  | HOL4, (Eq | Ne)
  | (FStar | Coq | Lean), (Eq | Lt | Le | Ne | Ge | Gt)
  | Lean, (Div | Rem | Add | Sub | Mul) ->
      let binop =
        match binop with
        | Eq -> "="
        | Lt -> "<"
        | Le -> "<="
        | Ne -> if !backend = Lean then "!=" else "<>"
        | Ge -> ">="
        | Gt -> ">"
        | Div -> "/"
        | Rem -> "%"
        | Add -> "+"
        | Sub -> "-"
        | Mul -> "*"
        | _ -> raise (Failure "Unreachable")
      in
      let binop =
        match !backend with FStar | Lean | HOL4 -> binop | Coq -> "s" ^ binop
      in
      extract_expr false arg0;
      F.pp_print_space fmt ();
      F.pp_print_string fmt binop;
      F.pp_print_space fmt ();
      extract_expr false arg1
  | _, (Lt | Le | Ge | Gt | Div | Rem | Add | Sub | Mul) ->
      let binop = named_binop_name binop int_ty in
      F.pp_print_string fmt binop;
      F.pp_print_space fmt ();
      extract_expr true arg0;
      F.pp_print_space fmt ();
      extract_expr true arg1
  | _, (BitXor | BitAnd | BitOr | Shl | Shr) -> raise Unimplemented);
  if inside then F.pp_print_string fmt ")"

let type_decl_kind_to_qualif (kind : decl_kind)
    (type_kind : type_decl_kind option) : string option =
  match !backend with
  | FStar -> (
      match kind with
      | SingleNonRec -> Some "type"
      | SingleRec -> Some "type"
      | MutRecFirst -> Some "type"
      | MutRecInner -> Some "and"
      | MutRecLast -> Some "and"
      | Assumed -> Some "assume type"
      | Declared -> Some "val")
  | Coq -> (
      match (kind, type_kind) with
      | SingleNonRec, Some Enum -> Some "Inductive"
      | SingleNonRec, Some Struct -> Some "Record"
      | (SingleRec | MutRecFirst), Some _ -> Some "Inductive"
      | (MutRecInner | MutRecLast), Some _ ->
          (* Coq doesn't support groups of mutually recursive definitions which mix
           * records and inducties: we convert everything to records if this happens
           *)
          Some "with"
      | (Assumed | Declared), None -> Some "Axiom"
      | _ -> raise (Failure "Unexpected"))
  | Lean -> (
      match kind with
      | SingleNonRec ->
          if type_kind = Some Struct then Some "structure" else Some "inductive"
      | SingleRec -> Some "inductive"
      | MutRecFirst -> Some "inductive"
      | MutRecInner -> Some "inductive"
      | MutRecLast -> Some "inductive"
      | Assumed -> Some "axiom"
      | Declared -> Some "axiom")
  | HOL4 -> None

let fun_decl_kind_to_qualif (kind : decl_kind) : string option =
  match !backend with
  | FStar -> (
      match kind with
      | SingleNonRec -> Some "let"
      | SingleRec -> Some "let rec"
      | MutRecFirst -> Some "let rec"
      | MutRecInner -> Some "and"
      | MutRecLast -> Some "and"
      | Assumed -> Some "assume val"
      | Declared -> Some "val")
  | Coq -> (
      match kind with
      | SingleNonRec -> Some "Definition"
      | SingleRec -> Some "Fixpoint"
      | MutRecFirst -> Some "Fixpoint"
      | MutRecInner -> Some "with"
      | MutRecLast -> Some "with"
      | Assumed -> Some "Axiom"
      | Declared -> Some "Axiom")
  | Lean -> (
      match kind with
      | SingleNonRec -> Some "def"
      | SingleRec -> Some "divergent def"
      | MutRecFirst -> Some "mutual divergent def"
      | MutRecInner -> Some "divergent def"
      | MutRecLast -> Some "divergent def"
      | Assumed -> Some "axiom"
      | Declared -> Some "axiom")
  | HOL4 -> None

(** The type of types.

    TODO: move inside the formatter?
 *)
let type_keyword () =
  match !backend with
  | FStar -> "Type0"
  | Coq | Lean -> "Type"
  | HOL4 -> raise (Failure "Unexpected")

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
    match !backend with
    | FStar | Lean | HOL4 -> name
    | Coq -> capitalize_first_letter name
  in
  let type_name name =
    match !backend with
    | FStar | Coq | HOL4 -> type_name_to_snake_case name ^ "_t"
    | Lean -> String.concat "." (get_type_name name)
  in
  let field_name (def_name : name) (field_id : FieldId.id)
      (field_name : string option) : string =
    let field_name =
      match field_name with
      | Some field_name -> field_name
      | None -> FieldId.to_string field_id
    in
    if !Config.record_fields_short_names then field_name
    else
      let def_name = type_name_to_snake_case def_name ^ "_" in
      def_name ^ field_name
  in
  let variant_name (def_name : name) (variant : string) : string =
    match !backend with
    | FStar | Coq | HOL4 ->
        let variant = to_camel_case variant in
        if variant_concatenate_type_name then
          type_name_to_camel_case def_name ^ variant
        else variant
    | Lean -> variant
  in
  let struct_constructor (basename : name) : string =
    let tname = type_name basename in
    let prefix =
      match !backend with FStar -> "Mk" | Coq | HOL4 -> "mk" | Lean -> ""
    in
    let suffix =
      match !backend with FStar | Coq | HOL4 -> "" | Lean -> ".mk"
    in
    prefix ^ tname ^ suffix
  in
  let get_fun_name fname =
    let fname = get_name fname in
    (* TODO: don't convert to snake case for Coq, HOL4, F* *)
    match !backend with
    | FStar | Coq | HOL4 -> String.concat "_" (List.map to_snake_case fname)
    | Lean -> String.concat "." fname
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
    let fname = get_fun_name fname in
    (* Compute the suffix *)
    let suffix = default_fun_suffix num_loops loop_id num_rgs rg filter_info in
    (* Concatenate *)
    fname ^ suffix
  in

  let termination_measure_name (_fid : A.FunDeclId.id) (fname : fun_name)
      (num_loops : int) (loop_id : LoopId.id option) : string =
    let fname = get_fun_name fname in
    let lp_suffix = default_fun_loop_suffix num_loops loop_id in
    (* Compute the suffix *)
    let suffix =
      match !Config.backend with
      | FStar -> "_decreases"
      | Lean -> "_terminates"
      | Coq | HOL4 -> raise (Failure "Unexpected")
    in
    (* Concatenate *)
    fname ^ lp_suffix ^ suffix
  in

  let decreases_proof_name (_fid : A.FunDeclId.id) (fname : fun_name)
      (num_loops : int) (loop_id : LoopId.id option) : string =
    let fname = get_fun_name fname in
    let lp_suffix = default_fun_loop_suffix num_loops loop_id in
    (* Compute the suffix *)
    let suffix =
      match !Config.backend with
      | Lean -> "_decreases"
      | FStar | Coq | HOL4 -> raise (Failure "Unexpected")
    in
    (* Concatenate *)
    fname ^ lp_suffix ^ suffix
  in

  let opaque_pre () =
    match !Config.backend with
    | FStar | Coq | HOL4 -> ""
    | Lean -> if !Config.wrap_opaque_in_sig then "opaque_defs." else ""
  in

  let var_basename (_varset : StringSet.t) (basename : string option) (ty : ty)
      : string =
    (* Small helper to derive var names from ADT type names.

       We do the following:
       - convert the type name to snake case
       - take the first letter of every "letter group"
       Ex.: "HashMap" -> "hash_map" -> "hm"
    *)
    let name_from_type_ident (name : string) : string =
      let cl = to_snake_case name in
      let cl = String.split_on_char '_' cl in
      let cl = List.filter (fun s -> String.length s > 0) cl in
      assert (List.length cl > 0);
      let cl = List.map (fun s -> s.[0]) cl in
      StringUtils.string_of_chars cl
    in
    (* If there is a basename, we use it *)
    match basename with
    | Some basename ->
        (* This should be a no-op *)
        to_snake_case basename
    | None -> (
        (* No basename: we use the first letter of the type *)
        match ty with
        | Adt (type_id, generics) -> (
            match type_id with
            | Tuple ->
                (* The "pair" case is frequent enough to have its special treatment *)
                if List.length generics.types = 2 then "p" else "t"
            | Assumed Result -> "r"
            | Assumed Error -> ConstStrings.error_basename
            | Assumed Fuel -> ConstStrings.fuel_basename
            | Assumed Option -> "opt"
            | Assumed Vec -> "v"
            | Assumed Array -> "a"
            | Assumed Slice -> "s"
            | Assumed Str -> "s"
            | Assumed Range -> "r"
            | Assumed State -> ConstStrings.state_basename
            | AdtId adt_id ->
                let def =
                  TypeDeclId.Map.find adt_id ctx.type_context.type_decls
                in
                (* Derive the var name from the last ident of the type name
                 * Ex.: ["hashmap"; "HashMap"] ~~> "HashMap" -> "hash_map" -> "hm"
                 *)
                (* The name shouldn't be empty, and its last element should
                 * be an ident *)
                let cl = List.nth def.name (List.length def.name - 1) in
                name_from_type_ident (Names.as_ident cl))
        | TypeVar _ -> (
            (* TODO: use "t" also for F* *)
            match !backend with
            | FStar -> "x" (* lacking inspiration here... *)
            | Coq | Lean | HOL4 -> "t" (* lacking inspiration here... *))
        | Literal lty -> (
            match lty with Bool -> "b" | Char -> "c" | Integer _ -> "i")
        | Arrow _ -> "f"
        | TraitType (_, _, name) -> name_from_type_ident name)
  in
  let type_var_basename (_varset : StringSet.t) (basename : string) : string =
    (* Rust type variables are snake-case and start with a capital letter *)
    match !backend with
    | FStar ->
        (* This is *not* a no-op: this removes the capital letter *)
        to_snake_case basename
    | HOL4 ->
        (* In HOL4, type variable names must start with "'" *)
        "'" ^ to_snake_case basename
    | Coq | Lean -> basename
  in
  let const_generic_var_basename (_varset : StringSet.t) (basename : string) :
      string =
    (* Rust type variables are snake-case and start with a capital letter *)
    match !backend with
    | FStar | HOL4 ->
        (* This is *not* a no-op: this removes the capital letter *)
        to_snake_case basename
    | Coq | Lean -> basename
  in
  let trait_clause_basename (_varset : StringSet.t) (_clause : trait_clause) :
      string =
    (* TODO: actually use the clause to derive the name *)
    "cl"
  in
  let append_index (basename : string) (i : int) : string =
    basename ^ string_of_int i
  in

  let extract_literal (fmt : F.formatter) (inside : bool) (cv : literal) : unit
      =
    match cv with
    | Scalar sv -> (
        match !backend with
        | FStar -> F.pp_print_string fmt (Z.to_string sv.PV.value)
        | Coq | HOL4 ->
            let print_brackets = inside && !backend = HOL4 in
            if print_brackets then F.pp_print_string fmt "(";
            (match !backend with
            | Coq -> ()
            | HOL4 ->
                F.pp_print_string fmt ("int_to_" ^ int_name sv.PV.int_ty);
                F.pp_print_space fmt ()
            | _ -> raise (Failure "Unreachable"));
            (* We need to add parentheses if the value is negative *)
            if sv.PV.value >= Z.of_int 0 then
              F.pp_print_string fmt (Z.to_string sv.PV.value)
            else F.pp_print_string fmt ("(" ^ Z.to_string sv.PV.value ^ ")");
            (match !backend with
            | Coq -> F.pp_print_string fmt ("%" ^ int_name sv.PV.int_ty)
            | HOL4 -> ()
            | _ -> raise (Failure "Unreachable"));
            if print_brackets then F.pp_print_string fmt ")"
        | Lean ->
            F.pp_print_string fmt "(";
            F.pp_print_string fmt (int_name sv.int_ty);
            F.pp_print_string fmt ".ofInt ";
            (* Something very annoying: negated values like `-3` are
               ambiguous in Lean because of conversions, so we have to
               be extremely explicit with negative numbers.
            *)
            if Z.lt sv.value Z.zero then (
              F.pp_print_string fmt "(";
              F.pp_print_string fmt "-";
              F.pp_print_string fmt "(";
              Z.pp_print fmt (Z.neg sv.value);
              F.pp_print_string fmt ":Int";
              F.pp_print_string fmt ")";
              F.pp_print_string fmt ")")
            else Z.pp_print fmt sv.value;
            F.pp_print_string fmt ")")
    | Bool b ->
        let b =
          match !backend with
          | HOL4 -> if b then "T" else "F"
          | Coq | FStar | Lean -> if b then "true" else "false"
        in
        F.pp_print_string fmt b
    | Char c -> (
        match !backend with
        | HOL4 ->
            (* [#"a"] is a notation for [CHR 97] (97 is the ASCII code for 'a') *)
            F.pp_print_string fmt ("#\"" ^ String.make 1 c ^ "\"")
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
    termination_measure_name;
    decreases_proof_name;
    opaque_pre;
    var_basename;
    type_var_basename;
    const_generic_var_basename;
    trait_clause_basename;
    append_index;
    extract_literal;
    extract_unop;
    extract_binop;
  }

let mk_formatter_and_names_map (ctx : trans_ctx) (crate_name : string)
    (variant_concatenate_type_name : bool) : formatter * names_map =
  let fmt = mk_formatter ctx crate_name variant_concatenate_type_name in
  let names_map = initialize_names_map fmt (names_map_init ()) in
  (fmt, names_map)

let is_single_opaque_fun_decl_group (dg : Pure.fun_decl list) : bool =
  match dg with [ d ] -> d.body = None | _ -> false

let is_single_opaque_type_decl_group (dg : Pure.type_decl list) : bool =
  match dg with [ d ] -> d.kind = Opaque | _ -> false

let is_empty_record_type_decl (d : Pure.type_decl) : bool = d.kind = Struct []

let is_empty_record_type_decl_group (dg : Pure.type_decl list) : bool =
  match dg with [ d ] -> is_empty_record_type_decl d | _ -> false

(** In some provers, groups of definitions must be delimited.

    - in Coq, *every* group (including singletons) must end with "."
    - in Lean, groups of mutually recursive definitions must end with "end"
    - in HOL4 (in most situations) the whole group must be within a `Define` command

    Calls to {!extract_fun_decl} should be inserted between calls to
    {!start_fun_decl_group} and {!end_fun_decl_group}.

    TODO: maybe those [{start/end}_decl_group] functions are not that much a good
    idea and we should merge them with the corresponding [extract_decl] functions.
 *)
let start_fun_decl_group (ctx : extraction_ctx) (fmt : F.formatter)
    (is_rec : bool) (dg : Pure.fun_decl list) =
  match !backend with
  | FStar | Coq | Lean -> ()
  | HOL4 ->
      (* In HOL4, opaque functions have a special treatment *)
      if is_single_opaque_fun_decl_group dg then ()
      else
        let with_opaque_pre = false in
        let compute_fun_def_name (def : Pure.fun_decl) : string =
          ctx_get_local_function with_opaque_pre def.def_id def.loop_id
            def.back_id ctx
          ^ "_def"
        in
        let names = List.map compute_fun_def_name dg in
        (* Add a break before *)
        F.pp_print_break fmt 0 0;
        (* Open the box for the delimiters *)
        F.pp_open_vbox fmt 0;
        (* Open the box for the definitions themselves *)
        F.pp_open_vbox fmt ctx.indent_incr;
        (* Print the delimiters *)
        if is_rec then
          F.pp_print_string fmt
            ("val [" ^ String.concat ", " names ^ "] = DefineDiv ‘")
        else (
          assert (List.length names = 1);
          let name = List.hd names in
          F.pp_print_string fmt ("val " ^ name ^ " = Define ‘"));
        F.pp_print_cut fmt ()

(** See {!start_fun_decl_group}. *)
let end_fun_decl_group (fmt : F.formatter) (is_rec : bool)
    (dg : Pure.fun_decl list) =
  match !backend with
  | FStar -> ()
  | Coq ->
      (* For aesthetic reasons, we print the Coq end group delimiter directly
         in {!extract_fun_decl}. *)
      ()
  | Lean ->
      (* We must add the "end" keyword to groups of mutually recursive functions *)
      if is_rec && List.length dg > 1 then (
        F.pp_print_cut fmt ();
        F.pp_print_string fmt "end";
        (* Add breaks to insert new lines between definitions *)
        F.pp_print_break fmt 0 0)
      else ()
  | HOL4 ->
      (* In HOL4, opaque functions have a special treatment *)
      if is_single_opaque_fun_decl_group dg then ()
      else (
        (* Close the box for the definitions *)
        F.pp_close_box fmt ();
        (* Print the end delimiter *)
        F.pp_print_cut fmt ();
        F.pp_print_string fmt "’";
        (* Close the box for the delimiters *)
        F.pp_close_box fmt ();
        (* Add breaks to insert new lines between definitions *)
        F.pp_print_break fmt 0 0)

(** See {!start_fun_decl_group}: similar usage, but for the type declarations. *)
let start_type_decl_group (ctx : extraction_ctx) (fmt : F.formatter)
    (is_rec : bool) (dg : Pure.type_decl list) =
  match !backend with
  | FStar | Coq -> ()
  | Lean ->
      if is_rec && List.length dg > 1 then (
        F.pp_print_space fmt ();
        F.pp_print_string fmt "mutual";
        F.pp_print_space fmt ())
  | HOL4 ->
      (* In HOL4, opaque types and empty records have a special treatment *)
      if
        is_single_opaque_type_decl_group dg
        || is_empty_record_type_decl_group dg
      then ()
      else (
        (* Add a break before *)
        F.pp_print_break fmt 0 0;
        (* Open the box for the delimiters *)
        F.pp_open_vbox fmt 0;
        (* Open the box for the definitions themselves *)
        F.pp_open_vbox fmt ctx.indent_incr;
        (* Print the delimiters *)
        F.pp_print_string fmt "Datatype:";
        F.pp_print_cut fmt ())

(** See {!start_fun_decl_group}. *)
let end_type_decl_group (fmt : F.formatter) (is_rec : bool)
    (dg : Pure.type_decl list) =
  match !backend with
  | FStar -> ()
  | Coq ->
      (* For aesthetic reasons, we print the Coq end group delimiter directly
         in {!extract_fun_decl}. *)
      ()
  | Lean ->
      (* We must add the "end" keyword to groups of mutually recursive functions *)
      if is_rec && List.length dg > 1 then (
        F.pp_print_cut fmt ();
        F.pp_print_string fmt "end";
        (* Add breaks to insert new lines between definitions *)
        F.pp_print_break fmt 0 0)
      else ()
  | HOL4 ->
      (* In HOL4, opaque types and empty records have a special treatment *)
      if
        is_single_opaque_type_decl_group dg
        || is_empty_record_type_decl_group dg
      then ()
      else (
        (* Close the box for the definitions *)
        F.pp_close_box fmt ();
        (* Print the end delimiter *)
        F.pp_print_cut fmt ();
        F.pp_print_string fmt "End";
        (* Close the box for the delimiters *)
        F.pp_close_box fmt ();
        (* Add breaks to insert new lines between definitions *)
        F.pp_print_break fmt 0 0)

let unit_name () =
  match !backend with Lean -> "Unit" | Coq | FStar | HOL4 -> "unit"

(** Small helper *)
let extract_arrow (fmt : F.formatter) () : unit =
  if !Config.backend = Lean then F.pp_print_string fmt "→"
  else F.pp_print_string fmt "->"

let extract_const_generic (ctx : extraction_ctx) (fmt : F.formatter)
    (inside : bool) (cg : const_generic) : unit =
  match cg with
  | ConstGenericGlobal id ->
      let s = ctx_get_global ctx.use_opaque_pre id ctx in
      F.pp_print_string fmt s
  | ConstGenericValue v -> ctx.fmt.extract_literal fmt inside v
  | ConstGenericVar id ->
      let s = ctx_get_const_generic_var id ctx in
      F.pp_print_string fmt s

let extract_literal_type (ctx : extraction_ctx) (fmt : F.formatter)
    (ty : literal_type) : unit =
  match ty with
  | Bool -> F.pp_print_string fmt ctx.fmt.bool_name
  | Char -> F.pp_print_string fmt ctx.fmt.char_name
  | Integer int_ty -> F.pp_print_string fmt (ctx.fmt.int_name int_ty)

(** [inside] constrols whether we should add parentheses or not around type
    applications (if [true] we add parentheses).

    [no_params_tys]: for all the types inside this set, do not print the type parameters.
    This is used for HOL4. As polymorphism is uniform in HOL4, printing the
    type parameters in the recursive definitions is useless (and actually
    forbidden).

    For instance, where in F* we would write:
    {[
      type list a = | Nil : list a | Cons : a -> list a -> list a
    ]}

    In HOL4 we would simply write:
    {[
      Datatype:
        list = Nil 'a | Cons 'a list
      End
    ]}
 *)
let rec extract_ty (ctx : extraction_ctx) (fmt : F.formatter)
    (no_params_tys : TypeDeclId.Set.t) (inside : bool) (ty : ty) : unit =
  let extract_rec = extract_ty ctx fmt no_params_tys in
  match ty with
  | Adt (type_id, generics) -> (
      let has_params = generics <> empty_generic_args in
      match type_id with
      | Tuple ->
          (* This is a bit annoying, but in F*/Coq/HOL4 [()] is not the unit type:
           * we have to write [unit]... *)
          if generics.types = [] then F.pp_print_string fmt (unit_name ())
          else (
            F.pp_print_string fmt "(";
            Collections.List.iter_link
              (fun () ->
                F.pp_print_space fmt ();
                let product =
                  match !backend with
                  | FStar -> "&"
                  | Coq -> "*"
                  | Lean -> "×"
                  | HOL4 -> "#"
                in
                F.pp_print_string fmt product;
                F.pp_print_space fmt ())
              (extract_rec true) generics.types;
            F.pp_print_string fmt ")")
      | AdtId _ | Assumed _ -> (
          (* HOL4 behaves differently. Where in Coq/FStar/Lean we would write:
             `tree a b`

             In HOL4 we would write:
             `('a, 'b) tree`
          *)
          let with_opaque_pre = false in
          match !backend with
          | FStar | Coq | Lean ->
              let print_paren = inside && has_params in
              if print_paren then F.pp_print_string fmt "(";
              (* TODO: for now, only the opaque *functions* are extracted in the
                 opaque module. The opaque *types* are assumed. *)
              F.pp_print_string fmt (ctx_get_type with_opaque_pre type_id ctx);
              extract_generic_args ctx fmt no_params_tys generics;
              if print_paren then F.pp_print_string fmt ")"
          | HOL4 ->
              let { types; const_generics; trait_refs } = generics in
              (* Const generics are not supported in HOL4 *)
              assert (const_generics = []);
              let print_tys =
                match type_id with
                | AdtId id -> not (TypeDeclId.Set.mem id no_params_tys)
                | Assumed _ -> true
                | _ -> raise (Failure "Unreachable")
              in
              if const_generics <> [] && print_tys then (
                let print_paren = List.length types > 1 in
                if print_paren then F.pp_print_string fmt "(";
                Collections.List.iter_link
                  (fun () ->
                    F.pp_print_string fmt ",";
                    F.pp_print_space fmt ())
                  (extract_rec true) types;
                if print_paren then F.pp_print_string fmt ")";
                F.pp_print_space fmt ());
              F.pp_print_string fmt (ctx_get_type with_opaque_pre type_id ctx);
              if trait_refs <> [] then (
                F.pp_print_space fmt ();
                Collections.List.iter_link (F.pp_print_space fmt)
                  (extract_trait_ref ctx fmt no_params_tys true)
                  trait_refs)))
  | TypeVar vid -> F.pp_print_string fmt (ctx_get_type_var vid ctx)
  | Literal lty -> extract_literal_type ctx fmt lty
  | Arrow (arg_ty, ret_ty) ->
      if inside then F.pp_print_string fmt "(";
      extract_rec false arg_ty;
      F.pp_print_space fmt ();
      extract_arrow fmt ();
      F.pp_print_space fmt ();
      extract_rec false ret_ty;
      if inside then F.pp_print_string fmt ")"
  | TraitType (trait_ref, generics, type_name) ->
      if !parameterize_trait_types then raise (Failure "Unimplemented")
      else if trait_ref.trait_id <> Self then (
        (* HOL4 doesn't have 1st class types *)
        assert (!backend <> HOL4);
        let use_brackets = generics <> empty_generic_args in
        if use_brackets then F.pp_print_string fmt "(";
        extract_trait_ref ctx fmt no_params_tys false trait_ref;
        extract_generic_args ctx fmt no_params_tys generics;
        let name =
          ctx_get_trait_assoc_type trait_ref.trait_decl_ref.trait_decl_id
            type_name ctx
        in
        if use_brackets then F.pp_print_string fmt ")";
        F.pp_print_string fmt ("." ^ name))
      else
        (* Can only happen when extracting the signature of a trait method
           *declaration* or a provided trait method (for a declaration).
           If extracting items for a trait method implementation,
           the type should have been normalized. For trait method declarations
           we directly reference the item. *)
        assert (ctx.trait_decl_id <> None);
      assert (generics = empty_generic_args);
      let name = ctx_get_local_trait_assoc_type type_name ctx in
      F.pp_print_string fmt name

and extract_trait_ref (ctx : extraction_ctx) (fmt : F.formatter)
    (no_params_tys : TypeDeclId.Set.t) (inside : bool) (tr : trait_ref) : unit =
  let use_brackets = tr.generics <> empty_generic_args && inside in
  if use_brackets then F.pp_print_string fmt "(";
  extract_trait_instance_id ctx fmt no_params_tys inside tr.trait_id;
  extract_generic_args ctx fmt no_params_tys tr.generics;
  if use_brackets then F.pp_print_string fmt ")"

and extract_generic_args (ctx : extraction_ctx) (fmt : F.formatter)
    (no_params_tys : TypeDeclId.Set.t) (generics : generic_args) : unit =
  let { types; const_generics; trait_refs } = generics in
  if !backend <> HOL4 then (
    if types <> [] then (
      F.pp_print_space fmt ();
      Collections.List.iter_link (F.pp_print_space fmt)
        (extract_ty ctx fmt no_params_tys true)
        types);
    if const_generics <> [] then (
      assert (!backend <> HOL4);
      F.pp_print_space fmt ();
      Collections.List.iter_link (F.pp_print_space fmt)
        (extract_const_generic ctx fmt true)
        const_generics));
  if trait_refs <> [] then (
    F.pp_print_space fmt ();
    Collections.List.iter_link (F.pp_print_space fmt)
      (extract_trait_ref ctx fmt no_params_tys true)
      trait_refs)

and extract_trait_instance_id (ctx : extraction_ctx) (fmt : F.formatter)
    (no_params_tys : TypeDeclId.Set.t) (inside : bool) (id : trait_instance_id)
    : unit =
  let with_opaque_pre = false in
  match id with
  | Self ->
      (* This has specific treatment depending on the item we're extracting
         (associated type, etc.). We should have caught this elsewhere. *)
      raise (Failure "Unexpected")
  | TraitImpl id ->
      let name = ctx_get_trait_impl with_opaque_pre id ctx in
      F.pp_print_string fmt name
  | Clause id ->
      let name = ctx_get_local_trait_clause id ctx in
      F.pp_print_string fmt name
  | ParentClause (inst_id, decl_id, clause_id) ->
      (* Use the trait decl id to lookup the name *)
      let name = ctx_get_trait_parent_clause decl_id clause_id ctx in
      extract_trait_instance_id ctx fmt no_params_tys true inst_id;
      F.pp_print_string fmt ("." ^ name)
  | ItemClause (inst_id, decl_id, item_name, clause_id) ->
      (* Use the trait decl id to lookup the name *)
      let name = ctx_get_trait_item_clause decl_id item_name clause_id ctx in
      extract_trait_instance_id ctx fmt no_params_tys true inst_id;
      F.pp_print_string fmt ("." ^ name)
  | TraitRef trait_ref ->
      extract_trait_ref ctx fmt no_params_tys inside trait_ref
  | UnknownTrait _ ->
      (* This is an error case *)
      raise (Failure "Unexpected")

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
    (type_decl_group : TypeDeclId.Set.t) (type_name : string)
    (type_params : string list) (cg_params : string list) (cons_name : string)
    (fields : field list) : unit =
  F.pp_print_space fmt ();
  (* variant box *)
  F.pp_open_hvbox fmt ctx.indent_incr;
  (* [| Cons :]
   * Note that we really don't want any break above so we print everything
   * at once. *)
  let opt_colon = if !backend <> HOL4 then " :" else "" in
  F.pp_print_string fmt ("| " ^ cons_name ^ opt_colon);
  let print_field (fid : FieldId.id) (f : field) (ctx : extraction_ctx) :
      extraction_ctx =
    F.pp_print_space fmt ();
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
      | Coq | Lean | HOL4 -> ctx
    in
    (* Print the field type *)
    let inside = !backend = HOL4 in
    extract_ty ctx fmt type_decl_group inside f.field_ty;
    (* Print the arrow [->] *)
    if !backend <> HOL4 then (
      F.pp_print_space fmt ();
      extract_arrow fmt ());
    (* Close the field box *)
    F.pp_close_box fmt ();
    (* Return *)
    ctx
  in
  (* Print the fields *)
  let fields = FieldId.mapi (fun fid f -> (fid, f)) fields in
  let _ =
    List.fold_left (fun ctx (fid, f) -> print_field fid f ctx) ctx fields
  in
  (* Sanity check: HOL4 doesn't support const generics *)
  assert (cg_params = [] || !backend <> HOL4);
  (* Print the final type *)
  if !backend <> HOL4 then (
    F.pp_print_space fmt ();
    F.pp_open_hovbox fmt 0;
    F.pp_print_string fmt type_name;
    List.iter
      (fun p ->
        F.pp_print_space fmt ();
        F.pp_print_string fmt p)
      (List.append type_params cg_params);
    F.pp_close_box fmt ());
  (* Close the variant box *)
  F.pp_close_box fmt ()

(* TODO: we don' need the [def_name] paramter: it can be retrieved from the context *)
let extract_type_decl_enum_body (ctx : extraction_ctx) (fmt : F.formatter)
    (type_decl_group : TypeDeclId.Set.t) (def : type_decl) (def_name : string)
    (type_params : string list) (cg_params : string list)
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
  let print_variant _variant_id (v : variant) =
    (* We don't lookup the name, because it may have a prefix for the type
       id (in the case of Lean) *)
    let cons_name = ctx.fmt.variant_name def.name v.variant_name in
    let fields = v.fields in
    extract_type_decl_variant ctx fmt type_decl_group def_name type_params
      cg_params cons_name fields
  in
  (* Print the variants *)
  let variants = VariantId.mapi (fun vid v -> (vid, v)) variants in
  List.iter (fun (vid, v) -> print_variant vid v) variants

let extract_type_decl_struct_body (ctx : extraction_ctx) (fmt : F.formatter)
    (type_decl_group : TypeDeclId.Set.t) (kind : decl_kind) (def : type_decl)
    (type_params : string list) (cg_params : string list) (fields : field list)
    : unit =
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

     HOL4:
     =====
     Type definitions are written as follows:
     {[
       Datatype:
         tree =
           TLeaf 'a
         | TNode node ;

         node =
           Node (tree list)
       End
     ]}
  *)
  (* Note that we already printed: [type t =] *)
  let is_rec = decl_is_from_rec_group kind in
  let _ =
    if !backend = FStar && fields = [] then (
      F.pp_print_space fmt ();
      F.pp_print_string fmt (unit_name ()))
    else if !backend = Lean && fields = [] then ()
      (* If the definition is recursive, we may need to extract it as an inductive
         (instead of a record). We start with the "normal" case: we extract it
         as a record. *)
    else if (not is_rec) || (!backend <> Coq && !backend <> Lean) then (
      if !backend <> Lean then F.pp_print_space fmt ();
      (* If Coq: print the constructor name *)
      (* TODO: remove superfluous test not is_rec below *)
      if !backend = Coq && not is_rec then (
        let with_opaque_pre = false in
        F.pp_print_string fmt
          (ctx_get_struct with_opaque_pre (AdtId def.def_id) ctx);
        F.pp_print_string fmt " ");
      (match !backend with
      | Lean -> ()
      | FStar | Coq -> F.pp_print_string fmt "{"
      | HOL4 -> F.pp_print_string fmt "<|");
      F.pp_print_break fmt 1 ctx.indent_incr;
      (* The body itself *)
      (* Open a box for the body *)
      (match !backend with
      | Coq | FStar | HOL4 -> F.pp_open_hvbox fmt 0
      | Lean -> F.pp_open_vbox fmt 0);
      (* Print the fields *)
      let print_field (field_id : FieldId.id) (f : field) : unit =
        let field_name = ctx_get_field (AdtId def.def_id) field_id ctx in
        (* Open a box for the field *)
        F.pp_open_box fmt ctx.indent_incr;
        F.pp_print_string fmt field_name;
        F.pp_print_space fmt ();
        F.pp_print_string fmt ":";
        F.pp_print_space fmt ();
        extract_ty ctx fmt type_decl_group false f.field_ty;
        if !backend <> Lean then F.pp_print_string fmt ";";
        (* Close the box for the field *)
        F.pp_close_box fmt ()
      in
      let fields = FieldId.mapi (fun fid f -> (fid, f)) fields in
      Collections.List.iter_link (F.pp_print_space fmt)
        (fun (fid, f) -> print_field fid f)
        fields;
      (* Close the box for the body *)
      F.pp_close_box fmt ();
      match !backend with
      | Lean -> ()
      | FStar | Coq ->
          F.pp_print_space fmt ();
          F.pp_print_string fmt "}"
      | HOL4 ->
          F.pp_print_space fmt ();
          F.pp_print_string fmt "|>")
    else (
      (* We extract for Coq or Lean, and we have a recursive record, or a record in
         a group of mutually recursive types: we extract it as an inductive type *)
      assert (is_rec && (!backend = Coq || !backend = Lean));
      let with_opaque_pre = false in
      (* Small trick: in Lean we use namespaces, meaning we don't need to prefix
         the constructor name with the name of the type at definition site,
         i.e., instead of generating `inductive Foo := | MkFoo ...` like in Coq
         we generate `inductive Foo := | mk ... *)
      let cons_name =
        if !backend = Lean then "mk"
        else ctx_get_struct with_opaque_pre (AdtId def.def_id) ctx
      in
      let def_name = ctx_get_local_type with_opaque_pre def.def_id ctx in
      extract_type_decl_variant ctx fmt type_decl_group def_name type_params
        cg_params cons_name fields)
  in
  ()

(** Extract a nestable, muti-line comment *)
let extract_comment (fmt : F.formatter) (sl : string list) : unit =
  (* Delimiters, space after we break a line *)
  let ld, space, rd =
    match !backend with
    | Coq | FStar | HOL4 -> ("(** ", 4, " *)")
    | Lean -> ("/- ", 3, " -/")
  in
  F.pp_open_vbox fmt space;
  F.pp_print_string fmt ld;
  (match sl with
  | [] -> ()
  | s :: sl ->
      F.pp_print_string fmt s;
      List.iter
        (fun s ->
          F.pp_print_space fmt ();
          F.pp_print_string fmt s)
        sl);
  F.pp_print_string fmt rd;
  F.pp_close_box fmt ()

let extract_trait_clause_type (ctx : extraction_ctx) (fmt : F.formatter)
    (no_params_tys : TypeDeclId.Set.t) (clause : trait_clause) : unit =
  let with_opaque_pre = false in
  let trait_name = ctx_get_trait_decl with_opaque_pre clause.trait_id ctx in
  F.pp_print_string fmt trait_name;
  extract_generic_args ctx fmt no_params_tys clause.generics

(** Insert a space, if necessary *)
let insert_req_space (fmt : F.formatter) (space : bool ref) : unit =
  if !space then space := false else F.pp_print_space fmt ()

let extract_generic_params (ctx : extraction_ctx) (fmt : F.formatter)
    (no_params_tys : TypeDeclId.Set.t) (use_forall : bool) (as_implicits : bool)
    (space : bool ref option) (generics : generic_params)
    (type_params : string list) (cg_params : string list)
    (trait_clauses : string list) : unit =
  let all_params = List.concat [ type_params; cg_params; trait_clauses ] in
  (* HOL4 doesn't support const generics *)
  assert (cg_params = [] || !backend <> HOL4);
  let left_bracket () =
    if as_implicits then F.pp_print_string fmt "{"
    else F.pp_print_string fmt "("
  in
  let right_bracket () =
    if as_implicits then F.pp_print_string fmt "}"
    else F.pp_print_string fmt ")"
  in
  let insert_req_space () =
    match space with
    | None -> F.pp_print_space fmt ()
    | Some space -> insert_req_space fmt space
  in
  (* Print the type/const generic parameters *)
  if all_params <> [] then (
    if use_forall then (
      insert_req_space ();
      F.pp_print_string fmt ":";
      F.pp_print_space fmt ();
      F.pp_print_string fmt "forall");
    (* Note that in HOL4 we don't print the type parameters. *)
    if !backend <> HOL4 then (
      (* Print the type parameters *)
      if type_params <> [] then (
        insert_req_space ();
        (* ( *)
        left_bracket ();
        List.iter
          (fun s ->
            F.pp_print_string fmt s;
            F.pp_print_space fmt ())
          type_params;
        F.pp_print_string fmt ":";
        F.pp_print_space fmt ();
        F.pp_print_string fmt (type_keyword ());
        (* ) *)
        right_bracket ());
      (* Print the const generic parameters *)
      List.iter
        (fun (var : const_generic_var) ->
          insert_req_space ();
          (* ( *)
          left_bracket ();
          let n = ctx_get_const_generic_var var.index ctx in
          F.pp_print_string fmt n;
          F.pp_print_space fmt ();
          F.pp_print_string fmt ":";
          F.pp_print_space fmt ();
          extract_literal_type ctx fmt var.ty;
          (* ) *)
          right_bracket ())
        generics.const_generics);
    (* Print the trait clauses *)
    List.iter
      (fun (clause : trait_clause) ->
        insert_req_space ();
        (* ( *)
        left_bracket ();
        let n = ctx_get_local_trait_clause clause.clause_id ctx in
        F.pp_print_string fmt n;
        F.pp_print_space fmt ();
        F.pp_print_string fmt ":";
        F.pp_print_space fmt ();
        extract_trait_clause_type ctx fmt no_params_tys clause;
        (* ) *)
        right_bracket ())
      generics.trait_clauses)

(** Extract a type declaration.

    This function is for all type declarations and all backends **at the exception**
    of opaque (assumed/declared) types format4 HOL4.

    See {!extract_type_decl}.
 *)
let extract_type_decl_gen (ctx : extraction_ctx) (fmt : F.formatter)
    (type_decl_group : TypeDeclId.Set.t) (kind : decl_kind) (def : type_decl)
    (extract_body : bool) : unit =
  (* Sanity check *)
  assert (extract_body || !backend <> HOL4);
  let type_kind =
    if extract_body then
      match def.kind with
      | Struct _ -> Some Struct
      | Enum _ -> Some Enum
      | Opaque -> None
    else None
  in
  (* If in Coq and the declaration is opaque, it must have the shape:
     [Axiom Ident : forall (T0 ... Tn : Type) (N0 : ...) ... (Nn : ...), ... -> ... -> ...].

     The boolean [is_opaque_coq] is used to detect this case.
  *)
  let is_opaque = type_kind = None in
  let is_opaque_coq = !backend = Coq && is_opaque in
  let use_forall = is_opaque_coq && def.generics <> empty_generic_params in
  (* Retrieve the definition name *)
  let with_opaque_pre = false in
  let def_name = ctx_get_local_type with_opaque_pre def.def_id ctx in
  (* Add the type and const generic params - note that we need those bindings only for the
   * body translation (they are not top-level) *)
  let ctx_body, type_params, cg_params, trait_clauses =
    ctx_add_generic_params def.generics ctx
  in
  (* Add a break before *)
  if !backend <> HOL4 || not (decl_is_first_from_group kind) then
    F.pp_print_break fmt 0 0;
  (* Print a comment to link the extracted type to its original rust definition *)
  extract_comment fmt [ "[" ^ Print.name_to_string def.name ^ "]" ];
  F.pp_print_break fmt 0 0;
  (* Open a box for the definition, so that whenever possible it gets printed on
   * one line. Note however that in the case of Lean line breaks are important
   * for parsing: we thus use a hovbox. *)
  (match !backend with
  | Coq | FStar | HOL4 -> F.pp_open_hvbox fmt 0
  | Lean -> F.pp_open_vbox fmt 0);
  (* Open a box for "type TYPE_NAME (TYPE_PARAMS CONST_GEN_PARAMS) =" *)
  F.pp_open_hovbox fmt ctx.indent_incr;
  (* > "type TYPE_NAME" *)
  let qualif = ctx.fmt.type_decl_kind_to_qualif kind type_kind in
  (match qualif with
  | Some qualif -> F.pp_print_string fmt (qualif ^ " " ^ def_name)
  | None -> F.pp_print_string fmt def_name);
  (* HOL4 doesn't support const generics, and type definitions in HOL4 don't
     support trait clauses *)
  assert ((cg_params = [] && trait_clauses = []) || !backend <> HOL4);
  (* Print the generic parameters *)
  let as_implicits = false in
  extract_generic_params ctx_body fmt type_decl_group use_forall as_implicits
    None def.generics type_params cg_params trait_clauses;
  (* Print the "=" if we extract the body*)
  if extract_body then (
    F.pp_print_space fmt ();
    let eq =
      match !backend with
      | FStar -> "="
      | Coq -> ":="
      | Lean ->
          if type_kind = Some Struct && kind = SingleNonRec then "where"
          else ":="
      | HOL4 -> "="
    in
    F.pp_print_string fmt eq)
  else (
    (* Otherwise print ": Type", unless it is the HOL4 backend (in
       which case we declare the type with `new_type`) *)
    if use_forall then F.pp_print_string fmt ","
    else (
      F.pp_print_space fmt ();
      F.pp_print_string fmt ":");
    F.pp_print_space fmt ();
    F.pp_print_string fmt (type_keyword ()));
  (* Close the box for "type TYPE_NAME (TYPE_PARAMS) =" *)
  F.pp_close_box fmt ();
  (if extract_body then
     match def.kind with
     | Struct fields ->
         extract_type_decl_struct_body ctx_body fmt type_decl_group kind def
           type_params cg_params fields
     | Enum variants ->
         extract_type_decl_enum_body ctx_body fmt type_decl_group def def_name
           type_params cg_params variants
     | Opaque -> raise (Failure "Unreachable"));
  (* Add the definition end delimiter *)
  if !backend = HOL4 && decl_is_not_last_from_group kind then (
    F.pp_print_space fmt ();
    F.pp_print_string fmt ";")
  else if !backend = Coq && decl_is_last_from_group kind then (
    (* This is actually an end of group delimiter. For aesthetic reasons
       we print it here instead of in {!end_type_decl_group}. *)
    F.pp_print_cut fmt ();
    F.pp_print_string fmt ".");
  (* Close the box for the definition *)
  F.pp_close_box fmt ();
  (* Add breaks to insert new lines between definitions *)
  if !backend <> HOL4 || decl_is_not_last_from_group kind then
    F.pp_print_break fmt 0 0

(** Extract an opaque type declaration to HOL4.

    Remark (SH): having to treat this specific case separately is very annoying,
    but I could not find a better way.
 *)
let extract_type_decl_hol4_opaque (ctx : extraction_ctx) (fmt : F.formatter)
    (def : type_decl) : unit =
  (* Retrieve the definition name *)
  let with_opaque_pre = false in
  let def_name = ctx_get_local_type with_opaque_pre def.def_id ctx in
  (* Generic parameters are unsupported *)
  assert (def.generics.const_generics = []);
  (* Trait clauses on type definitions are unsupported *)
  assert (def.generics.trait_clauses = []);
  (* Types  *)
  (* Count the number of parameters *)
  let num_params = List.length def.generics.types in
  (* Generate the declaration *)
  F.pp_print_space fmt ();
  F.pp_print_string fmt
    ("val _ = new_type (\"" ^ def_name ^ "\", " ^ string_of_int num_params ^ ")");
  F.pp_print_space fmt ()

(** Extract an empty record type declaration to HOL4.

    Empty records are not supported in HOL4, so we extract them as type
    abbreviations to the unit type.

    Remark (SH): having to treat this specific case separately is very annoying,
    but I could not find a better way.
 *)
let extract_type_decl_hol4_empty_record (ctx : extraction_ctx)
    (fmt : F.formatter) (def : type_decl) : unit =
  (* Retrieve the definition name *)
  let with_opaque_pre = false in
  let def_name = ctx_get_local_type with_opaque_pre def.def_id ctx in
  (* Sanity check *)
  assert (def.generics = empty_generic_params);
  (* Generate the declaration *)
  F.pp_print_space fmt ();
  F.pp_print_string fmt ("Type " ^ def_name ^ " = “: unit”");
  F.pp_print_space fmt ()

(** Extract a type declaration.

    Note that all the names used for extraction should already have been
    registered.

    This function should be inserted between calls to {!start_type_decl_group}
    and {!end_type_decl_group}.
 *)
let extract_type_decl (ctx : extraction_ctx) (fmt : F.formatter)
    (type_decl_group : TypeDeclId.Set.t) (kind : decl_kind) (def : type_decl) :
    unit =
  let extract_body =
    match kind with
    | SingleNonRec | SingleRec | MutRecFirst | MutRecInner | MutRecLast -> true
    | Assumed | Declared -> false
  in
  if extract_body then
    if !backend = HOL4 && is_empty_record_type_decl def then
      extract_type_decl_hol4_empty_record ctx fmt def
    else extract_type_decl_gen ctx fmt type_decl_group kind def extract_body
  else
    match !backend with
    | FStar | Coq | Lean ->
        extract_type_decl_gen ctx fmt type_decl_group kind def extract_body
    | HOL4 -> extract_type_decl_hol4_opaque ctx fmt def

(** Auxiliary function.

    Generate [Arguments] instructions in Coq.
 *)
let extract_type_decl_coq_arguments (ctx : extraction_ctx) (fmt : F.formatter)
    (kind : decl_kind) (decl : type_decl) : unit =
  assert (!backend = Coq);
  (* Generating the [Arguments] instructions is useful only if there are type parameters *)
  if decl.generics.types = [] && decl.generics.const_generics = [] then ()
  else
    (* Add the type params - note that we need those bindings only for the
     * body translation (they are not top-level) *)
    let _ctx_body, type_params, cg_params, trait_clauses =
      ctx_add_generic_params decl.generics ctx
    in
    (* Auxiliary function to extract an [Arguments Cons {T} _ _.] instruction *)
    let extract_arguments_info (cons_name : string) (fields : 'a list) : unit =
      (* Add a break before *)
      F.pp_print_break fmt 0 0;
      (* Open a box *)
      F.pp_open_hovbox fmt ctx.indent_incr;
      F.pp_print_break fmt 0 0;
      F.pp_print_string fmt "Arguments";
      F.pp_print_space fmt ();
      F.pp_print_string fmt cons_name;
      (* Print the type/const params and the trait clauses (`{T}`) *)
      List.iter
        (fun (var : string) ->
          F.pp_print_space fmt ();
          F.pp_print_string fmt ("{" ^ var ^ "}"))
        (List.concat [ type_params; cg_params; trait_clauses ]);
      (* Print the fields (`_`) *)
      List.iter
        (fun _ ->
          F.pp_print_space fmt ();
          F.pp_print_string fmt "_")
        fields;
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
        let with_opaque_pre = false in
        let cons_name = ctx_get_struct with_opaque_pre adt_id ctx in
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
        let ctx, type_params, cg_params, trait_clauses =
          ctx_add_generic_params decl.generics ctx
        in
        let ctx, record_var = ctx_add_var "x" (VarId.of_int 0) ctx in
        let ctx, field_var = ctx_add_var "x" (VarId.of_int 1) ctx in
        let with_opaque_pre = false in
        let def_name = ctx_get_local_type with_opaque_pre decl.def_id ctx in
        let cons_name =
          ctx_get_struct with_opaque_pre (AdtId decl.def_id) ctx
        in
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
          (* Print the generics *)
          let use_forall = false in
          let as_implicits = true in
          extract_generic_params ctx fmt TypeDeclId.Set.empty use_forall
            as_implicits None decl.generics type_params cg_params trait_clauses;
          (* Print the record parameter *)
          F.pp_print_space fmt ();
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
          if !backend = Coq then (
            F.pp_print_cut fmt ();
            F.pp_print_string fmt ".");
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
          if !backend = Coq then (
            F.pp_print_cut fmt ();
            F.pp_print_string fmt ".");
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
  | FStar | Lean | HOL4 -> ()
  | Coq ->
      extract_type_decl_coq_arguments ctx fmt kind decl;
      extract_type_decl_record_field_projectors ctx fmt kind decl

(** Extract the state type declaration. *)
let extract_state_type (fmt : F.formatter) (ctx : extraction_ctx)
    (kind : decl_kind) : unit =
  (* Add a break before *)
  F.pp_print_break fmt 0 0;
  (* Print a comment  *)
  extract_comment fmt [ "The state type used in the state-error monad" ];
  F.pp_print_break fmt 0 0;
  (* Open a box for the definition, so that whenever possible it gets printed on
   * one line *)
  F.pp_open_hvbox fmt 0;
  (* Retrieve the name *)
  let state_name = ctx_get_assumed_type State ctx in
  (* The syntax for Lean and Coq is almost identical. *)
  let print_axiom () =
    let axiom =
      match !backend with
      | Coq -> "Axiom"
      | Lean -> "axiom"
      | FStar | HOL4 -> raise (Failure "Unexpected")
    in
    F.pp_print_string fmt axiom;
    F.pp_print_space fmt ();
    F.pp_print_string fmt state_name;
    F.pp_print_space fmt ();
    F.pp_print_string fmt ":";
    F.pp_print_space fmt ();
    F.pp_print_string fmt "Type";
    if !backend = Coq then F.pp_print_string fmt "."
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
      | HOL4 ->
          F.pp_print_string fmt ("val _ = new_type (\"" ^ state_name ^ "\", 0)")
      | Coq | Lean -> print_axiom ())
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
      | HOL4 ->
          F.pp_print_string fmt ("val _ = new_type (\"" ^ state_name ^ "\", 0)")
      | Coq | Lean -> print_axiom ()));
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
      (* Add the termination measure *)
      let ctx = ctx_add_termination_measure def ctx in
      (* Add the decreases proof for Lean only *)
      match !Config.backend with
      | Coq | FStar -> ctx
      | HOL4 -> raise (Failure "Unexpected")
      | Lean -> ctx_add_decreases_proof def ctx
    else ctx
  in
  let ctx = List.fold_left register_decreases ctx (fwd :: loop_fwds) in
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

    [is_single_pat]: are we extracting a single pattern (a pattern for a let-binding
    or a lambda).

    TODO: we don't need something very generic anymore (some definitions used
    to be polymorphic).
 *)
let extract_adt_g_value
    (extract_value : extraction_ctx -> bool -> 'v -> extraction_ctx)
    (fmt : F.formatter) (ctx : extraction_ctx) (is_single_pat : bool)
    (inside : bool) (variant_id : VariantId.id option) (field_values : 'v list)
    (ty : ty) : extraction_ctx =
  match ty with
  | Adt (Tuple, generics) ->
      (* Tuple *)
      (* For now, we only support fully applied tuple constructors *)
      assert (List.length generics.types = List.length field_values);
      assert (generics.const_generics = [] && generics.trait_refs = []);
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

      (* If we are generating a pattern for a let-binding and we target Lean,
         the syntax is: `let ⟨ x0, ..., xn ⟩ := ...`.

         Otherwise, it is: `let Cons x0 ... xn = ...`
      *)
      if is_single_pat && !Config.backend = Lean then (
        F.pp_print_string fmt "⟨";
        F.pp_print_space fmt ();
        let ctx =
          Collections.List.fold_left_link
            (fun _ ->
              F.pp_print_string fmt ",";
              F.pp_print_space fmt ())
            (fun ctx v -> extract_value ctx true v)
            ctx field_values
        in
        F.pp_print_space fmt ();
        F.pp_print_string fmt "⟩";
        ctx)
      else
        (* We print something of the form: [Cons field0 ... fieldn].
         * We could update the code to print something of the form:
         * [{ field0=...; ...; fieldn=...; }] in case of structures.
         *)
        let cons =
          (* The ADT shouldn't be opaque *)
          let with_opaque_pre = false in
          match variant_id with
          | Some vid -> (
              (* In the case of Lean, we might have to add the type name as a prefix *)
              match (!backend, adt_id) with
              | Lean, Assumed _ ->
                  ctx_get_type with_opaque_pre adt_id ctx
                  ^ "."
                  ^ ctx_get_variant adt_id vid ctx
              | _ -> ctx_get_variant adt_id vid ctx)
          | None -> ctx_get_struct with_opaque_pre adt_id ctx
        in
        let use_parentheses = inside && field_values <> [] in
        if use_parentheses then F.pp_print_string fmt "(";
        F.pp_print_string fmt cons;
        let ctx =
          Collections.List.fold_left
            (fun ctx v ->
              F.pp_print_space fmt ();
              extract_value ctx true v)
            ctx field_values
        in
        if use_parentheses then F.pp_print_string fmt ")";
        ctx
  | _ -> raise (Failure "Inconsistent typed value")

(* Extract globals in the same way as variables *)
let extract_global (ctx : extraction_ctx) (fmt : F.formatter)
    (id : A.GlobalDeclId.id) : unit =
  let with_opaque_pre = ctx.use_opaque_pre in
  F.pp_print_string fmt (ctx_get_global with_opaque_pre id ctx)

(** [inside]: see {!extract_ty}.

    As a pattern can introduce new variables, we return an extraction context
    updated with new bindings.
 *)
let rec extract_typed_pattern (ctx : extraction_ctx) (fmt : F.formatter)
    (is_let : bool) (inside : bool) (v : typed_pattern) : extraction_ctx =
  match v.value with
  | PatConstant cv ->
      ctx.fmt.extract_literal fmt inside cv;
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
      let extract_value ctx inside v =
        extract_typed_pattern ctx fmt is_let inside v
      in
      extract_adt_g_value extract_value fmt ctx is_let inside av.variant_id
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
  | CVar var_id ->
      let var_name = ctx_get_const_generic_var var_id ctx in
      F.pp_print_string fmt var_name
  | Const cv -> ctx.fmt.extract_literal fmt inside cv
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
  | StructUpdate supd -> extract_StructUpdate ctx fmt inside e.ty supd
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
          extract_function_call ctx fmt inside fun_id qualif.generics args
      | Global global_id -> extract_global ctx fmt global_id
      | AdtCons adt_cons_id ->
          extract_adt_cons ctx fmt inside adt_cons_id qualif.generics args
      | Proj proj ->
          extract_field_projector ctx fmt inside app proj qualif.generics args)
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
    (inside : bool) (fid : fun_or_op_id) (generics : generic_args)
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
      let with_opaque_pre = ctx.use_opaque_pre in
      let fun_name = ctx_get_function with_opaque_pre fun_id ctx in
      F.pp_print_string fmt fun_name;
      (* Sanity check: HOL4 doesn't support const generics *)
      assert (generics.const_generics = [] || !backend <> HOL4);
      (* Print the generics *)
      extract_generic_args ctx fmt TypeDeclId.Set.empty generics;
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
    (adt_cons : adt_cons_id) (generics : generic_args) (args : texpression list)
    : unit =
  let e_ty = Adt (adt_cons.adt_id, generics) in
  let is_single_pat = false in
  let _ =
    extract_adt_g_value
      (fun ctx inside e ->
        extract_texpression ctx fmt inside e;
        ctx)
      fmt ctx is_single_pat inside adt_cons.variant_id args e_ty
  in
  ()

(** Subcase of the app case: ADT field projector.  *)
and extract_field_projector (ctx : extraction_ctx) (fmt : F.formatter)
    (inside : bool) (original_app : texpression) (proj : projection)
    (_generics : generic_args) (args : texpression list) : unit =
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
      if !backend <> Lean then F.pp_print_break fmt 0 0;
      F.pp_print_string fmt ".";
      (* If in Coq, the field projection has to be parenthesized *)
      (match !backend with
      | FStar | Lean | HOL4 -> F.pp_print_string fmt field_name
      | Coq -> F.pp_print_string fmt ("(" ^ field_name ^ ")"));
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
        extract_typed_pattern ctx fmt true true x)
      ctx xl
  in
  F.pp_print_space fmt ();
  if !backend = Lean then F.pp_print_string fmt "=>"
  else F.pp_print_string fmt "->";
  F.pp_print_space fmt ();
  (* Print the body *)
  extract_texpression ctx fmt false e;
  (* Close parentheses *)
  if inside then F.pp_print_string fmt ")";
  (* Close the box for the abs expression *)
  F.pp_close_box fmt ()

and extract_lets (ctx : extraction_ctx) (fmt : F.formatter) (inside : bool)
    (e : texpression) : unit =
  (* Destruct the lets.

     Note that in the case of HOL4, we stop destructing the lets if at some point
     the "kind" (monadic or non-monadic) of the lets changes.

     We do this because in HOL4 the parsing is not very powerful:
     if we mix monadic let-bindings and non monadic let-bindings, we have to
     wrap the let-bindings inside a [do ... od] whenever we need to extract
     a monadic let-binding non immediately inside a monadic let-binding.

     Ex.:
     {[
       do
         x <- ...;
         let y = f x in
         do
           z <- g y;
           ...
         od
       od
     ]}
  *)
  let lets, next_e =
    match !backend with
    | HOL4 -> destruct_lets_no_interleave e
    | FStar | Coq | Lean -> destruct_lets e
  in
  (* Open a box for the whole expression.

     In the case of Lean, we use a vbox so that line breaks are inserted
     at the end of every let-binding: let-bindings are indeed not ended
     with an "in" keyword.
  *)
  if !Config.backend = Lean then F.pp_open_vbox fmt 0 else F.pp_open_hvbox fmt 0;
  (* Open parentheses *)
  if inside && !backend <> Lean then F.pp_print_string fmt "(";
  (* Extract the let-bindings *)
  let extract_let (ctx : extraction_ctx) (monadic : bool) (lv : typed_pattern)
      (re : texpression) : extraction_ctx =
    (* Open a box for the let-binding *)
    F.pp_open_hovbox fmt ctx.indent_incr;
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
       * TODO: cleanup
       * *)
      if monadic && (!backend = Coq || !backend = HOL4) then (
        let ctx = extract_typed_pattern ctx fmt true true lv in
        F.pp_print_space fmt ();
        let arrow =
          match !backend with
          | Coq | HOL4 -> "<-"
          | FStar | Lean -> raise (Failure "impossible")
        in
        F.pp_print_string fmt arrow;
        F.pp_print_space fmt ();
        extract_texpression ctx fmt false re;
        F.pp_print_string fmt ";";
        ctx)
      else (
        (* Print the "let" *)
        if monadic then
          match !backend with
          | FStar ->
              F.pp_print_string fmt "let*";
              F.pp_print_space fmt ()
          | Coq | Lean ->
              F.pp_print_string fmt "let";
              F.pp_print_space fmt ()
          | HOL4 -> ()
        else (
          F.pp_print_string fmt "let";
          F.pp_print_space fmt ());
        let ctx = extract_typed_pattern ctx fmt true true lv in
        F.pp_print_space fmt ();
        let eq =
          match !backend with
          | FStar -> "="
          | Coq -> ":="
          | Lean -> if monadic then "←" else ":="
          | HOL4 -> if monadic then "<-" else "="
        in
        F.pp_print_string fmt eq;
        F.pp_print_space fmt ();
        extract_texpression ctx fmt false re;
        (* End the let-binding *)
        (match !backend with
        | Lean ->
            (* In Lean, (monadic) let-bindings don't require to end with anything *)
            ()
        | Coq | FStar | HOL4 ->
            F.pp_print_space fmt ();
            F.pp_print_string fmt "in");
        ctx)
    in
    (* Close the box for the let-binding *)
    F.pp_close_box fmt ();
    F.pp_print_space fmt ();
    (* Return *)
    ctx
  in
  (* If Lean and HOL4, we rely on monadic blocks, so we insert a do and open a new box
     immediately *)
  let wrap_in_do_od =
    match !backend with
    | Lean ->
        (* For Lean, we wrap in a block iff at least one of the let-bindings is monadic *)
        List.exists (fun (m, _, _) -> m) lets
    | HOL4 ->
        (* HOL4 is similar to HOL4, but we add a sanity check *)
        let wrap_in_do = List.exists (fun (m, _, _) -> m) lets in
        if wrap_in_do then assert (List.for_all (fun (m, _, _) -> m) lets);
        wrap_in_do
    | FStar | Coq -> false
  in
  if wrap_in_do_od then (
    F.pp_open_vbox fmt (if !backend = Lean then ctx.indent_incr else 0);
    F.pp_print_string fmt "do";
    F.pp_print_space fmt ());
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

  (* do-box (Lean and HOL4 only) *)
  if wrap_in_do_od then (
    if !backend = HOL4 then (
      F.pp_print_space fmt ();
      F.pp_print_string fmt "od");
    F.pp_close_box fmt ());
  (* Close parentheses *)
  if inside && !backend <> Lean then F.pp_print_string fmt ")";
  (* Close the box for the whole expression *)
  F.pp_close_box fmt ()

and extract_Switch (ctx : extraction_ctx) (fmt : F.formatter) (_inside : bool)
    (scrut : texpression) (body : switch_body) : unit =
  (* Remark: we don't use the [inside] parameter because we extract matches in
     a conservative manner: we always make sure they are parenthesized/delimited
     with keywords such as [end] *)
  (* Open a box for the whole expression.

     In the case of Lean, we rely on indentation to delimit the end of the
     branches, and need to insert line breaks: we thus use a vbox.
  *)
  if !Config.backend = Lean then F.pp_open_vbox fmt 0 else F.pp_open_hvbox fmt 0;
  (* Extract the switch *)
  (match body with
  | If (e_then, e_else) ->
      (* Open a box for the [if e] *)
      F.pp_open_hovbox fmt ctx.indent_incr;
      F.pp_print_string fmt "if";
      if !backend = Lean && ctx.use_dep_ite then F.pp_print_string fmt " h:";
      F.pp_print_space fmt ();
      let scrut_inside = PureUtils.texpression_requires_parentheses scrut in
      extract_texpression ctx fmt scrut_inside scrut;
      (* Close the box for the [if e] *)
      F.pp_close_box fmt ();

      (* Extract the branches *)
      let extract_branch (is_then : bool) (e_branch : texpression) : unit =
        F.pp_print_space fmt ();
        (* Open a box for the then/else+branch *)
        F.pp_open_hvbox fmt ctx.indent_incr;
        (* Open a box for the then/else + space + opening parenthesis *)
        F.pp_open_hovbox fmt 0;
        let then_or_else = if is_then then "then" else "else" in
        F.pp_print_string fmt then_or_else;
        let parenth = PureUtils.texpression_requires_parentheses e_branch in
        (* Open the parenthesized expression *)
        let print_space_after_parenth =
          if parenth then (
            match !backend with
            | FStar ->
                F.pp_print_space fmt ();
                F.pp_print_string fmt "begin";
                F.pp_print_space fmt
            | Coq | Lean | HOL4 ->
                F.pp_print_space fmt ();
                F.pp_print_string fmt "(";
                F.pp_print_cut fmt)
          else F.pp_print_space fmt
        in
        (* Close the box for the then/else + space + opening parenthesis *)
        F.pp_close_box fmt ();
        print_space_after_parenth ();
        (* Open a box for the branch *)
        F.pp_open_hovbox fmt ctx.indent_incr;
        (* Print the branch expression *)
        extract_texpression ctx fmt false e_branch;
        (* Close the box for the branch *)
        F.pp_close_box fmt ();
        (* Close the parenthesized expression *)
        (if parenth then
           match !backend with
           | FStar ->
               F.pp_print_space fmt ();
               F.pp_print_string fmt "end"
           | Coq | Lean | HOL4 -> F.pp_print_string fmt ")");
        (* Close the box for the then/else+branch *)
        F.pp_close_box fmt ()
      in

      extract_branch true e_then;
      extract_branch false e_else
  | Match branches -> (
      (* Open a box for the [match ... with] *)
      F.pp_open_hovbox fmt ctx.indent_incr;
      (* Print the [match ... with] *)
      let match_begin =
        match !backend with
        | FStar -> "begin match"
        | Coq -> "match"
        | Lean -> if ctx.use_dep_ite then "match h:" else "match"
        | HOL4 ->
            (* We're being extra safe in the case of HOL4 *)
            "(case"
      in
      F.pp_print_string fmt match_begin;
      F.pp_print_space fmt ();
      let scrut_inside = PureUtils.texpression_requires_parentheses scrut in
      extract_texpression ctx fmt scrut_inside scrut;
      F.pp_print_space fmt ();
      let match_scrut_end =
        match !backend with FStar | Coq | Lean -> "with" | HOL4 -> "of"
      in
      F.pp_print_string fmt match_scrut_end;
      (* Close the box for the [match ... with] *)
      F.pp_close_box fmt ();

      (* Extract the branches *)
      let extract_branch (br : match_branch) : unit =
        F.pp_print_space fmt ();
        (* Open a box for the pattern+branch *)
        F.pp_open_hvbox fmt ctx.indent_incr;
        (* Open a box for the pattern *)
        F.pp_open_hovbox fmt ctx.indent_incr;
        (* Print the pattern *)
        F.pp_print_string fmt "|";
        F.pp_print_space fmt ();
        let ctx = extract_typed_pattern ctx fmt false false br.pat in
        F.pp_print_space fmt ();
        let arrow =
          match !backend with FStar -> "->" | Coq | Lean | HOL4 -> "=>"
        in
        F.pp_print_string fmt arrow;
        (* Close the box for the pattern *)
        F.pp_close_box fmt ();
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
      match !backend with
      | Lean -> (*We rely on indentation in Lean *) ()
      | FStar | Coq ->
          F.pp_print_space fmt ();
          F.pp_print_string fmt "end"
      | HOL4 -> F.pp_print_string fmt ")"));
  (* Close the box for the whole expression *)
  F.pp_close_box fmt ()

and extract_StructUpdate (ctx : extraction_ctx) (fmt : F.formatter)
    (inside : bool) (e_ty : ty) (supd : struct_update) : unit =
  (* We can't update a subset of the fields in Coq (i.e., we can do
     [{| x:= 3; y := 4 |}], but there is no syntax for [{| s with x := 3 |}]) *)
  assert (!backend <> Coq || supd.init = None);
  (* In the case of HOL4, records with no fields are not supported and are
     thus extracted to unit. We need to check that by looking up the definition *)
  let extract_as_unit =
    match (!backend, supd.struct_id) with
    | HOL4, AdtId adt_id ->
        let d =
          TypeDeclId.Map.find adt_id ctx.trans_ctx.type_context.type_decls
        in
        d.kind = Struct []
    | _ -> false
  in
  if extract_as_unit then
    (* Remark: this is only valid for HOL4 (for instance the Coq unit value is [tt]) *)
    F.pp_print_string fmt "()"
  else
    (* There are two cases:
       - this is a regular struct
       - this is an array
    *)
    match supd.struct_id with
    | AdtId _ ->
        F.pp_open_hvbox fmt 0;
        F.pp_open_hvbox fmt ctx.indent_incr;
        (* Inner/outer brackets: there are several syntaxes for the field updates.

           For instance, in F*:
           {[
             { x with f = ..., ... }
           ]}

           In HOL4:
           {[
             x with <| f = ..., ... |>
           ]}

           In the above examples:
           - in F*, the { } brackets are "outer" brackets
           - in HOL4, the <| |> brackets are "inner" brackets
        *)
        (* Outer brackets *)
        let olb, orb =
          match !backend with
          | Lean | FStar -> (Some "{", Some "}")
          | Coq -> (Some "{|", Some "|}")
          | HOL4 -> (None, None)
        in
        (* Inner brackets *)
        let ilb, irb =
          match !backend with
          | Lean | FStar | Coq -> (None, None)
          | HOL4 -> (Some "<|", Some "|>")
        in
        (* Helper *)
        let print_bracket (is_left : bool) b =
          match b with
          | Some b ->
              if not is_left then F.pp_print_space fmt ();
              F.pp_print_string fmt b;
              if is_left then F.pp_print_space fmt ()
          | None -> ()
        in
        print_bracket true olb;
        let need_paren = inside && !backend = HOL4 in
        if need_paren then F.pp_print_string fmt "(";
        F.pp_open_hvbox fmt ctx.indent_incr;
        if supd.init <> None then (
          let var_name = ctx_get_var (Option.get supd.init) ctx in
          F.pp_print_string fmt var_name;
          F.pp_print_space fmt ();
          F.pp_print_string fmt "with";
          F.pp_print_space fmt ());
        print_bracket true ilb;
        F.pp_open_hvbox fmt 0;
        let delimiter =
          match !backend with Lean -> "," | Coq | FStar | HOL4 -> ";"
        in
        let assign =
          match !backend with Coq | Lean | HOL4 -> ":=" | FStar -> "="
        in
        Collections.List.iter_link
          (fun () ->
            F.pp_print_string fmt delimiter;
            F.pp_print_space fmt ())
          (fun (fid, fe) ->
            F.pp_open_hvbox fmt ctx.indent_incr;
            let f = ctx_get_field supd.struct_id fid ctx in
            F.pp_print_string fmt f;
            F.pp_print_string fmt (" " ^ assign);
            F.pp_print_space fmt ();
            F.pp_open_hvbox fmt ctx.indent_incr;
            extract_texpression ctx fmt true fe;
            F.pp_close_box fmt ();
            F.pp_close_box fmt ())
          supd.updates;
        F.pp_close_box fmt ();
        print_bracket false irb;
        F.pp_close_box fmt ();
        F.pp_close_box fmt ();
        if need_paren then F.pp_print_string fmt ")";
        print_bracket false orb;
        F.pp_close_box fmt ()
    | Assumed Array ->
        (* Open the boxes *)
        F.pp_open_hvbox fmt ctx.indent_incr;
        let need_paren = inside in
        if need_paren then F.pp_print_string fmt "(";
        (* Open the box for `Array.mk T N [` *)
        F.pp_open_hovbox fmt ctx.indent_incr;
        (* Print the array constructor *)
        let cs = ctx_get_struct false (Assumed Array) ctx in
        F.pp_print_string fmt cs;
        (* Print the parameters *)
        let _, generics = ty_as_adt e_ty in
        let ty = Collections.List.to_cons_nil generics.types in
        F.pp_print_space fmt ();
        extract_ty ctx fmt TypeDeclId.Set.empty true ty;
        let cg = Collections.List.to_cons_nil generics.const_generics in
        F.pp_print_space fmt ();
        extract_const_generic ctx fmt true cg;
        F.pp_print_space fmt ();
        F.pp_print_string fmt "[";
        (* Close the box for `Array.mk T N [` *)
        F.pp_close_box fmt ();
        (* Print the values *)
        let delimiter =
          match !backend with Lean -> "," | Coq | FStar | HOL4 -> ";"
        in
        F.pp_print_space fmt ();
        F.pp_open_hovbox fmt 0;
        Collections.List.iter_link
          (fun () ->
            F.pp_print_string fmt delimiter;
            F.pp_print_space fmt ())
          (fun (_, fe) -> extract_texpression ctx fmt false fe)
          supd.updates;
        (* Close the boxes *)
        F.pp_close_box fmt ();
        if supd.updates <> [] then F.pp_print_space fmt ();
        F.pp_print_string fmt "]";
        if need_paren then F.pp_print_string fmt ")";
        F.pp_close_box fmt ()
    | _ -> raise (Failure "Unreachable")

(** A small utility to print the parameters of a function signature.

    We return two contexts:
    - the context augmented with bindings for the type parameters
    - the context augmented with bindings for the type parameters *and*
      bindings for the input values

    We also return names for the type parameters, const generics, etc.

    TODO: do we really need the first one? We should probably always use
    the second one.
    It comes from the fact that when we print the input values for the
    decrease clause, we introduce bindings in the context (because we print
    patterns, not the variables). We should figure a cleaner way.
 *)
let extract_fun_parameters (space : bool ref) (ctx : extraction_ctx)
    (fmt : F.formatter) (def : fun_decl) :
    extraction_ctx * extraction_ctx * string list =
  (* Add the type parameters - note that we need those bindings only for the
   * body translation (they are not top-level) *)
  let ctx, type_params, cg_params, trait_clauses =
    ctx_add_generic_params def.signature.generics ctx
  in
  (* Print the generics *)
  (* Open a box for the generics *)
  F.pp_open_hovbox fmt 0;
  let use_forall = false in
  let as_implicits = false in
  extract_generic_params ctx fmt TypeDeclId.Set.empty use_forall as_implicits
    (Some space) def.signature.generics type_params cg_params trait_clauses;
  (* Close the box for the generics *)
  F.pp_close_box fmt ();
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
            let ctx = extract_typed_pattern ctx fmt true false lv in
            F.pp_print_space fmt ();
            F.pp_print_string fmt ":";
            F.pp_print_space fmt ();
            extract_ty ctx fmt TypeDeclId.Set.empty false lv.ty;
            F.pp_print_string fmt ")";
            (* Close the box for the input parameters *)
            F.pp_close_box fmt ();
            ctx)
          ctx body.inputs_lvs
  in
  (ctx, ctx_body, List.concat [ type_params; cg_params; trait_clauses ])

(** A small utility to print the types of the input parameters in the form:
    [u32 -> list u32 -> ...]
    (we don't print the return type of the function)

    This is used for opaque function declarations, in particular.
 *)
let extract_fun_input_parameters_types (ctx : extraction_ctx)
    (fmt : F.formatter) (def : fun_decl) : unit =
  let extract_param (ty : ty) : unit =
    let inside = false in
    extract_ty ctx fmt TypeDeclId.Set.empty inside ty;
    F.pp_print_space fmt ();
    extract_arrow fmt ();
    F.pp_print_space fmt ()
  in
  List.iter extract_param def.signature.inputs

let assert_backend_supports_decreases_clauses () =
  match !backend with
  | FStar | Lean -> ()
  | _ ->
      raise
        (Failure "decreases clauses only supported for the Lean & F* backends")

(** Extract a decreases clause function template body.

    For F* only.

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
let extract_template_fstar_decreases_clause (ctx : extraction_ctx)
    (fmt : F.formatter) (def : fun_decl) : unit =
  assert (!backend = FStar);

  (* Retrieve the function name *)
  let def_name = ctx_get_termination_measure def.def_id def.loop_id ctx in
  (* Add a break before *)
  F.pp_print_break fmt 0 0;
  (* Print a comment to link the extracted type to its original rust definition *)
  extract_comment fmt
    [ "[" ^ Print.fun_name_to_string def.basename ^ "]: decreases clause" ];
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
  let _, _, _ = extract_fun_parameters space ctx fmt def in
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

(** Extract templates for the [termination_by] and [decreasing_by] clauses of a
    recursive function definition.

    For Lean only.

    We extract two commands. The first one is a regular definition for the
    termination measure (the value derived from the function arguments that
    decreases over function calls). The second one is a macro definition that
    defines a proof script (allowed to refer to function arguments) that proves
    termination.
*)
let extract_template_lean_termination_and_decreasing (ctx : extraction_ctx)
    (fmt : F.formatter) (def : fun_decl) : unit =
  assert (!backend = Lean);
  (*
   * Extract a template for the termination measure
   *)
  (* Retrieve the function name *)
  let def_name = ctx_get_termination_measure def.def_id def.loop_id ctx in
  let def_body = Option.get def.body in
  (* Add a break before *)
  F.pp_print_break fmt 0 0;
  (* Print a comment to link the extracted type to its original rust definition *)
  extract_comment fmt
    [ "[" ^ Print.fun_name_to_string def.basename ^ "]: termination measure" ];
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
  let _, ctx_body, _ = extract_fun_parameters space ctx fmt def in
  (* Print the ":=" *)
  F.pp_print_space fmt ();
  F.pp_print_string fmt ":=";
  (* Close the box for "let FUN_NAME (PARAMS) : EFFECT =" *)
  F.pp_close_box fmt ();
  F.pp_print_space fmt ();
  (* Tuple of the arguments *)
  let vars = List.map (fun (v : var) -> v.id) def_body.inputs in

  if List.length vars = 1 then
    F.pp_print_string fmt (ctx_get_var (List.hd vars) ctx_body)
  else (
    F.pp_open_hovbox fmt 0;
    F.pp_print_string fmt "(";
    Collections.List.iter_link
      (fun () ->
        F.pp_print_string fmt ",";
        F.pp_print_space fmt ())
      (fun v -> F.pp_print_string fmt (ctx_get_var v ctx_body))
      vars;
    F.pp_print_string fmt ")";
    F.pp_close_box fmt ());
  (* Close the box for "let FUN_NAME (PARAMS) : EFFECT = admit()" *)
  F.pp_close_box fmt ();
  (* Close the box for the whole definition *)
  F.pp_close_box fmt ();
  (* Add breaks to insert new lines between definitions *)
  F.pp_print_break fmt 0 0;

  (*
   * Extract a template for the decreases proof
   *)
  let def_name = ctx_get_decreases_proof def.def_id def.loop_id ctx in
  (* syntax <def_name> term ... term : tactic *)
  F.pp_print_break fmt 0 0;
  extract_comment fmt
    [ "[" ^ Print.fun_name_to_string def.basename ^ "]: decreases_by tactic" ];
  F.pp_print_space fmt ();
  F.pp_open_hvbox fmt 0;
  F.pp_print_string fmt "syntax \"";
  F.pp_print_string fmt def_name;
  F.pp_print_string fmt "\" term+ : tactic";
  F.pp_print_break fmt 0 0;
  (* macro_rules | `(tactic| fact_termination_proof $x) => `(tactic| ( *)
  F.pp_print_string fmt "macro_rules";
  F.pp_print_space fmt ();
  F.pp_open_hovbox fmt ctx.indent_incr;
  F.pp_open_hovbox fmt 0;
  F.pp_print_string fmt "| `(tactic| ";
  F.pp_print_string fmt def_name;
  List.iter
    (fun v ->
      F.pp_print_space fmt ();
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

let extract_fun_comment (ctx : extraction_ctx) (fmt : F.formatter)
    (def : fun_decl) : unit =
  let { keep_fwd; num_backs } =
    PureUtils.RegularFunIdMap.find
      (A.Regular def.def_id, def.loop_id, def.back_id)
      ctx.fun_name_info
  in
  let comment_pre = "[" ^ Print.fun_name_to_string def.basename ^ "]: " in
  let comment =
    let loop_comment =
      match def.loop_id with
      | None -> ""
      | Some id -> "loop " ^ LoopId.to_string id ^ ": "
    in
    let fwd_back_comment =
      match def.back_id with
      | None -> [ "forward function" ]
      | Some id ->
          (* Check if there is only one backward function, and no forward function *)
          if (not keep_fwd) && num_backs = 1 then
            [
              "merged forward/backward function";
              "(there is a single backward function, and the forward function \
               returns ())";
            ]
          else [ "backward function " ^ T.RegionGroupId.to_string id ]
    in
    match fwd_back_comment with
    | [] -> raise (Failure "Unreachable")
    | [ s ] -> [ comment_pre ^ loop_comment ^ s ]
    | s :: sl -> (comment_pre ^ loop_comment ^ s) :: sl
  in
  extract_comment fmt comment

(** Extract a function declaration.

    This function is for all function declarations and all backends **at the exception**
    of opaque (assumed/declared) functions for HOL4.

    See {!extract_fun_decl}.
 *)
let extract_fun_decl_gen (ctx : extraction_ctx) (fmt : F.formatter)
    (kind : decl_kind) (has_decreases_clause : bool) (def : fun_decl) : unit =
  assert (not def.is_global_decl_body);
  (* Retrieve the function name *)
  let with_opaque_pre = false in
  let def_name =
    ctx_get_local_function with_opaque_pre def.def_id def.loop_id def.back_id
      ctx
  in
  (* Add a break before *)
  if !backend <> HOL4 || not (decl_is_first_from_group kind) then
    F.pp_print_break fmt 0 0;
  (* Print a comment to link the extracted definition to its original rust definition *)
  extract_fun_comment ctx fmt def;
  F.pp_print_space fmt ();
  (* Open two boxes for the definition, so that whenever possible it gets printed on
   * one line and indents are correct *)
  F.pp_open_hvbox fmt 0;
  F.pp_open_vbox fmt ctx.indent_incr;
  (* For HOL4: we may need to put parentheses around the definition *)
  let parenthesize = !backend = HOL4 && decl_is_not_last_from_group kind in
  if parenthesize then F.pp_print_string fmt "(";
  (* Open a box for "let FUN_NAME (PARAMS) : EFFECT =" *)
  F.pp_open_hovbox fmt ctx.indent_incr;
  (* > "let FUN_NAME" *)
  let is_opaque = Option.is_none def.body in
  (* If in Coq and the declaration is opaque, it must have the shape:
     [Axiom Ident : forall (T0 ... Tn : Type), ... -> ... -> ...].

     The boolean [is_opaque_coq] is used to detect this case.
  *)
  let is_opaque_coq = !backend = Coq && is_opaque in
  let use_forall =
    is_opaque_coq && def.signature.generics <> empty_generic_params
  in
  (* Print the qualifier ("assume", etc.).

     if `wrap_opaque_in_sig`: we generate a record of assumed funcions.
     TODO: this is obsolete.
  *)
  (if not (!Config.wrap_opaque_in_sig && (kind = Assumed || kind = Declared))
   then
     let qualif = ctx.fmt.fun_decl_kind_to_qualif kind in
     match qualif with
     | Some qualif ->
         F.pp_print_string fmt qualif;
         F.pp_print_space fmt ()
     | None -> ());
  F.pp_print_string fmt def_name;
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
  let ctx, ctx_body, all_params = extract_fun_parameters space ctx fmt def in
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
      if !backend = FStar then (
        F.pp_print_string fmt "Tot";
        F.pp_print_space fmt ()));
    extract_ty ctx fmt TypeDeclId.Set.empty has_decreases_clause
      def.signature.output;
    (* Close the box for the return type *)
    F.pp_close_box fmt ();
    (* Print the decrease clause - rk.: a function with a decreases clause
     * is necessarily a transparent function *)
    if has_decreases_clause && !backend = FStar then (
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
      let decr_name = ctx_get_termination_measure def.def_id def.loop_id ctx in
      F.pp_print_string fmt decr_name;
      (* Print the generic parameters - TODO: we do this many
         times, we should have a helper to factor it out *)
      List.iter
        (fun (name : string) ->
          F.pp_print_space fmt ();
          F.pp_print_string fmt name)
        all_params;
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
      (* TODO: we should probably print the input variables, not the typed
         patterns *)
      let _ =
        List.fold_left
          (fun ctx (lv : typed_pattern) ->
            F.pp_print_space fmt ();
            let ctx = extract_typed_pattern ctx fmt true false lv in
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
    let eq = match !backend with FStar | HOL4 -> "=" | Coq | Lean -> ":=" in
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
  (* Termination clause and proof for Lean *)
  if has_decreases_clause && !backend = Lean then (
    let def_body = Option.get def.body in
    let all_vars = List.map (fun (v : var) -> v.id) def_body.inputs in
    let num_fwd_inputs =
      def.signature.info.num_fwd_inputs_with_fuel_with_state
    in
    let vars = Collections.List.prefix num_fwd_inputs all_vars in

    (* termination_by *)
    let terminates_name =
      ctx_get_termination_measure def.def_id def.loop_id ctx
    in
    F.pp_print_break fmt 0 0;
    (* Open a box for the whole [termination_by CALL => DECREASES] *)
    F.pp_open_hvbox fmt ctx.indent_incr;
    (* Open a box for {termination_by CALL =>} *)
    F.pp_open_hovbox fmt ctx.indent_incr;
    F.pp_print_string fmt "termination_by";
    F.pp_print_space fmt ();
    F.pp_print_string fmt def_name;
    List.iter
      (fun v ->
        F.pp_print_space fmt ();
        F.pp_print_string fmt (ctx_get_var v ctx_body))
      all_vars;
    F.pp_print_space fmt ();
    F.pp_print_string fmt "=>";
    (* Close the box for [termination_by CALL =>] *)
    F.pp_close_box fmt ();
    F.pp_print_space fmt ();
    (* Open the box for [DECREASES] *)
    F.pp_open_hovbox fmt ctx.indent_incr;
    F.pp_print_string fmt terminates_name;
    (* Print the generic params - TODO: factor out *)
    List.iter
      (fun (name : string) ->
        F.pp_print_space fmt ();
        F.pp_print_string fmt name)
      all_params;
    (* Print the variables *)
    List.iter
      (fun v ->
        F.pp_print_space fmt ();
        F.pp_print_string fmt (ctx_get_var v ctx_body))
      vars;
    (* Close the box for [DECREASES] *)
    F.pp_close_box fmt ();
    (* Close the box for the whole [termination_by CALL => DECREASES] *)
    F.pp_close_box fmt ();

    F.pp_print_break fmt 0 0;
    (* Open a box for the [decreasing by ...] *)
    F.pp_open_hvbox fmt ctx.indent_incr;
    let decreases_name = ctx_get_decreases_proof def.def_id def.loop_id ctx in
    F.pp_print_string fmt "decreasing_by";
    F.pp_print_space fmt ();
    F.pp_open_hvbox fmt ctx.indent_incr;
    F.pp_print_string fmt decreases_name;
    List.iter
      (fun v ->
        F.pp_print_space fmt ();
        F.pp_print_string fmt (ctx_get_var v ctx_body))
      vars;
    F.pp_close_box fmt ();
    (* Close the box for the [decreasing by ...] *)
    F.pp_close_box fmt ());
  (* Close the parentheses *)
  if parenthesize then F.pp_print_string fmt ")";
  (* Add the definition end delimiter *)
  if !backend = HOL4 && decl_is_not_last_from_group kind then (
    F.pp_print_space fmt ();
    F.pp_print_string fmt "/\\")
  else if !backend = Coq && decl_is_last_from_group kind then (
    (* This is actually an end of group delimiter. For aesthetic reasons
       we print it here instead of in {!end_fun_decl_group}. *)
    F.pp_print_cut fmt ();
    F.pp_print_string fmt ".");
  (* Close the outer box for the definition *)
  F.pp_close_box fmt ();
  (* Add breaks to insert new lines between definitions *)
  if !backend <> HOL4 || decl_is_not_last_from_group kind then
    F.pp_print_break fmt 0 0

(** Extract an opaque function declaration to HOL4.

    Remark (SH): having to treat this specific case separately is very annoying,
    but I could not find a better way.
 *)
let extract_fun_decl_hol4_opaque (ctx : extraction_ctx) (fmt : F.formatter)
    (def : fun_decl) : unit =
  (* Retrieve the definition name *)
  let with_opaque_pre = false in
  let def_name =
    ctx_get_local_function with_opaque_pre def.def_id def.loop_id def.back_id
      ctx
  in
  assert (def.signature.generics.const_generics = []);
  (* Add the type/const gen parameters - note that we need those bindings
     only for the generation of the type (they are not top-level) *)
  let ctx, _, _, _ = ctx_add_generic_params def.signature.generics ctx in
  (* Add breaks to insert new lines between definitions *)
  F.pp_print_break fmt 0 0;
  (* Open a box for the whole definition *)
  F.pp_open_hvbox fmt ctx.indent_incr;
  (* Print a comment to link the extracted definition to its original rust definition *)
  extract_fun_comment ctx fmt def;
  (* Generate: `val _ = new_constant ("...",` *)
  F.pp_print_string fmt ("val _ = new_constant (\"" ^ def_name ^ "\",");
  F.pp_print_space fmt ();
  (* Open a box for the type *)
  F.pp_open_hovbox fmt 0;
  F.pp_print_string fmt "“:";
  (* Generate the type *)
  extract_fun_input_parameters_types ctx fmt def;
  extract_ty ctx fmt TypeDeclId.Set.empty false def.signature.output;
  (* Close the box for the type *)
  F.pp_print_string fmt "”";
  F.pp_close_box fmt ();
  (* Close the parenthesis opened for the inputs of `new_constant` *)
  F.pp_print_string fmt ")";
  (* Close the box for the definition *)
  F.pp_close_box fmt ();
  (* Add breaks to insert new lines between definitions *)
  F.pp_print_break fmt 0 0

(** Extract a function declaration.

    Note that all the names used for extraction should already have been
    registered.

    We take the definition of the forward translation as parameter (which is
    equal to the definition to extract, if we extract a forward function) because
    it is useful for the decrease clause.

    This function should be inserted between calls to {!start_fun_decl_group}
    and {!end_fun_decl_group}.
 *)
let extract_fun_decl (ctx : extraction_ctx) (fmt : F.formatter)
    (kind : decl_kind) (has_decreases_clause : bool) (def : fun_decl) : unit =
  assert (not def.is_global_decl_body);
  (* We treat HOL4 opaque functions in a specific manner *)
  if !backend = HOL4 && Option.is_none def.body then
    extract_fun_decl_hol4_opaque ctx fmt def
  else extract_fun_decl_gen ctx fmt kind has_decreases_clause def

(** Extract a global declaration body of the shape "QUALIF NAME : TYPE = BODY"
    with a custom body extractor.

    We introduce this helper because every (non opaque) global declaration gets
    extracted to two declarations, and we can actually factor out the generation
    of those declarations. See {!extract_global_decl} for more explanations.
 *)
let extract_global_decl_body_gen (ctx : extraction_ctx) (fmt : F.formatter)
    (kind : decl_kind) (name : string) (ty : ty)
    (extract_body : (F.formatter -> unit) Option.t) : unit =
  let is_opaque = Option.is_none extract_body in

  (* HOL4: Definition wrapper *)
  if !backend = HOL4 then (
    (* Open a vertical box: we *must* break lines *)
    F.pp_open_vbox fmt 0;
    F.pp_print_string fmt ("Definition " ^ name ^ "_def:");
    F.pp_print_space fmt ();
    F.pp_open_vbox fmt ctx.indent_incr;
    F.pp_print_string fmt (String.make ctx.indent_incr ' '));

  (* Open the definition boxes (depth=0) *)
  F.pp_open_hvbox fmt 0;
  F.pp_open_hvbox fmt ctx.indent_incr;

  (* Open "QUALIF NAME : TYPE =" box (depth=1) *)
  F.pp_open_hovbox fmt ctx.indent_incr;
  (* Print "QUALIF NAME " *)
  (match ctx.fmt.fun_decl_kind_to_qualif kind with
  | Some qualif ->
      F.pp_print_string fmt qualif;
      F.pp_print_space fmt ()
  | None -> ());
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
  extract_ty ctx fmt TypeDeclId.Set.empty false ty;
  (* Close "TYPE" box (depth=3) *)
  F.pp_close_box fmt ();

  if not is_opaque then (
    (* Print " =" *)
    F.pp_print_space fmt ();
    let eq = match !backend with FStar | HOL4 -> "=" | Coq | Lean -> ":=" in
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
  if !backend = Coq then (
    F.pp_print_cut fmt ();
    F.pp_print_string fmt ".");

  (* Close the outer definition box (depth=0) *)
  F.pp_close_box fmt ();

  (* HOL4: Definition wrapper *)
  if !backend = HOL4 then (
    F.pp_close_box fmt ();
    F.pp_print_space fmt ();
    F.pp_print_string fmt "End";
    F.pp_close_box fmt ())

(** Extract an opaque global declaration for HOL4.

    Remark (SH): having to treat this specific case separately is very annoying,
    but I could not find a better way.
 *)
let extract_global_decl_hol4_opaque (ctx : extraction_ctx) (fmt : F.formatter)
    (name : string) (ty : ty) : unit =
  (* Open the definition boxe (depth=0) *)
  F.pp_open_hvbox fmt ctx.indent_incr;
  (* [val ..._def = new_constant ("...",] *)
  F.pp_open_hovbox fmt 0;
  F.pp_print_string fmt
    ("val " ^ name ^ "_def = new_constant (\"" ^ name ^ "\", ");
  F.pp_close_box fmt ();
  (* Print the type *)
  F.pp_open_hovbox fmt 0;
  extract_ty ctx fmt TypeDeclId.Set.empty false ty;
  F.pp_close_box fmt ();
  (* Close the definition boxe *) F.pp_close_box fmt ()

(** Extract a global declaration.

    We generate the body which *computes* the global value separately from the
    value declaration itself.

    For example in Rust,
    [static X: u32 = 3;]

    will be translated to the following F*:
    [let x_body : result u32 = Return 3] (* this has type [result u32] *)
    [let x_c : u32 = eval_global x_body] (* this has type [u32] (no [result]!) *)

    This function generates the two declarations.

    Remark: because global declaration groups are always singletons (i.e.,
    there are no groups of mutually recursive global declarations), this function
    doesn't need to be called between calls to functions of the shape
    [{start,end}_gloabl_decl_group], contrary to {!extract_type_decl}
    and {!extract_fun_decl}.
 *)
let extract_global_decl (ctx : extraction_ctx) (fmt : F.formatter)
    (global : A.global_decl) (body : fun_decl) (interface : bool) : unit =
  assert body.is_global_decl_body;
  assert (Option.is_none body.back_id);
  assert (body.signature.inputs = []);
  assert (List.length body.signature.doutputs = 1);
  assert (body.signature.generics = empty_generic_params);

  (* Add a break then the name of the corresponding LLBC declaration *)
  F.pp_print_break fmt 0 0;
  extract_comment fmt [ "[" ^ Print.global_name_to_string global.name ^ "]" ];
  F.pp_print_space fmt ();

  let with_opaque_pre = false in
  let decl_name = ctx_get_global with_opaque_pre global.def_id ctx in
  let body_name =
    ctx_get_function with_opaque_pre
      (FromLlbc (Regular global.body_id, None, None))
      ctx
  in

  let decl_ty, body_ty =
    let ty = body.signature.output in
    if body.signature.info.effect_info.can_fail then (unwrap_result_ty ty, ty)
    else (ty, mk_result_ty ty)
  in
  match body.body with
  | None ->
      (* No body: only generate a [val x_c : u32] declaration *)
      let kind = if interface then Declared else Assumed in
      if !backend = HOL4 then
        extract_global_decl_hol4_opaque ctx fmt decl_name decl_ty
      else extract_global_decl_body_gen ctx fmt kind decl_name decl_ty None
  | Some body ->
      (* There is a body *)
      (* Generate: [let x_body : result u32 = Return 3] *)
      extract_global_decl_body_gen ctx fmt SingleNonRec body_name body_ty
        (Some (fun fmt -> extract_texpression ctx fmt false body.body));
      F.pp_print_break fmt 0 0;
      (* Generate: [let x_c : u32 = eval_global x_body] *)
      extract_global_decl_body_gen ctx fmt SingleNonRec decl_name decl_ty
        (Some
           (fun fmt ->
             let body =
               match !backend with
               | FStar -> "eval_global " ^ body_name
               | Lean -> "eval_global " ^ body_name ^ " (by simp)"
               | Coq -> body_name ^ "%global"
               | HOL4 -> "get_return_value " ^ body_name
             in
             F.pp_print_string fmt body));
      (* Add a break to insert lines between declarations *)
      F.pp_print_break fmt 0 0

(** Extract a trait declaration *)
let extract_trait_decl (ctx : extraction_ctx) (fmt : F.formatter)
    (trait_decl : trait_decl) : unit =
  raise (Failure "TODO")

(** Extract a trait implementation *)
let extract_trait_impl (ctx : extraction_ctx) (fmt : F.formatter)
    (trait_impl : trait_impl) : unit =
  raise (Failure "TODO")

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
    sg.generics = empty_generic_params
    && (sg.inputs = [ mk_unit_ty ] || sg.inputs = [])
    && sg.output = mk_result_ty mk_unit_ty
  then (
    (* Add a break before *)
    F.pp_print_break fmt 0 0;
    (* Print a comment *)
    extract_comment fmt
      [ "Unit test for [" ^ Print.fun_name_to_string def.basename ^ "]" ];
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
        (* Note that if the function is opaque, the unit test will fail
           because the normalizer will get stuck *)
        let with_opaque_pre = ctx.use_opaque_pre in
        let fun_name =
          ctx_get_local_function with_opaque_pre def.def_id def.loop_id
            def.back_id ctx
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
        (* Note that if the function is opaque, the unit test will fail
           because the normalizer will get stuck *)
        let with_opaque_pre = ctx.use_opaque_pre in
        let fun_name =
          ctx_get_local_function with_opaque_pre def.def_id def.loop_id
            def.back_id ctx
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
        (* Note that if the function is opaque, the unit test will fail
           because the normalizer will get stuck *)
        let with_opaque_pre = ctx.use_opaque_pre in
        let fun_name =
          ctx_get_local_function with_opaque_pre def.def_id def.loop_id
            def.back_id ctx
        in
        F.pp_print_string fmt fun_name;
        if sg.inputs <> [] then (
          F.pp_print_space fmt ();
          F.pp_print_string fmt "()");
        F.pp_print_space fmt ();
        F.pp_print_string fmt "==";
        F.pp_print_space fmt ();
        let success = ctx_get_variant (Assumed Result) result_return_id ctx in
        F.pp_print_string fmt ("." ^ success ^ " ())")
    | HOL4 ->
        F.pp_print_string fmt "val _ = assert_return (";
        F.pp_print_string fmt "“";
        (* Note that if the function is opaque, the unit test will fail
           because the normalizer will get stuck *)
        let with_opaque_pre = ctx.use_opaque_pre in
        let fun_name =
          ctx_get_local_function with_opaque_pre def.def_id def.loop_id
            def.back_id ctx
        in
        F.pp_print_string fmt fun_name;
        if sg.inputs <> [] then (
          F.pp_print_space fmt ();
          F.pp_print_string fmt "()");
        F.pp_print_string fmt "”)");
    (* Close the box for the test *)
    F.pp_close_box fmt ();
    (* Add a break after *)
    F.pp_print_break fmt 0 0)
  else (* Do nothing *)
    ()
