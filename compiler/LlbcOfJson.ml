(** Functions to load LLBC ASTs from json.

    Initially, we used [ppx_derive_yojson] to automate this.
    However, [ppx_derive_yojson] expects formatting to be slightly
    different from what [serde_rs] generates (because it uses [Yojson.Safe.t]
    and not [Yojson.Basic.t]).

    TODO: we should check all that the integer values are in the proper range
 *)

open Yojson.Basic
open Names
open OfJsonBasic
open Identifiers
open Meta
module T = Types
module V = Values
module S = Scalars
module E = Expressions
module A = LlbcAst
module TU = TypesUtils
module AU = LlbcAstUtils
module LocalFileId = IdGen ()
module VirtualFileId = IdGen ()

(** The default logger *)
let log = Logging.llbc_of_json_logger

(** A file identifier *)
type file_id = LocalId of LocalFileId.id | VirtualId of VirtualFileId.id
[@@deriving show, ord]

module OrderedIdToFile : Collections.OrderedType with type t = file_id = struct
  type t = file_id

  let compare fid0 fid1 = compare_file_id fid0 fid1

  let to_string id =
    match id with
    | LocalId id -> "Local " ^ LocalFileId.to_string id
    | VirtualId id -> "Virtual " ^ VirtualFileId.to_string id

  let pp_t fmt x = Format.pp_print_string fmt (to_string x)
  let show_t x = to_string x
end

module IdToFile = Collections.MakeMap (OrderedIdToFile)

type id_to_file_map = file_name IdToFile.t

let file_id_of_json (js : json) : (file_id, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("LocalId", id) ] ->
        let* id = LocalFileId.id_of_json id in
        Ok (LocalId id)
    | `Assoc [ ("VirtualId", id) ] ->
        let* id = VirtualFileId.id_of_json id in
        Ok (VirtualId id)
    | _ -> Error "")

let file_name_of_json (js : json) : (file_name, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Virtual", name) ] ->
        let* name = string_of_json name in
        Ok (Virtual name)
    | `Assoc [ ("Local", name) ] ->
        let* name = string_of_json name in
        Ok (Local name)
    | _ -> Error "")

(** Deserialize a map from file id to file name.

    In the serialized LLBC, the files in the loc spans are refered to by their
    ids, in order to save space. In a functional language like OCaml this is
    not necessary: we thus replace the file ids by the file name themselves in
    the AST.
    The "id to file" map is thus only used in the deserialization process.
  *)
let id_to_file_of_json (js : json) : (id_to_file_map, string) result =
  combine_error_msgs js __FUNCTION__
    ((* The map is stored as a list of pairs (key, value): we deserialize
      * this list then convert it to a map *)
     let* key_values =
       list_of_json (pair_of_json file_id_of_json file_name_of_json) js
     in
     Ok (IdToFile.of_list key_values))

let loc_of_json (js : json) : (loc, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("line", line); ("col", col) ] ->
        let* line = int_of_json line in
        let* col = int_of_json col in
        Ok { line; col }
    | _ -> Error "")

let span_of_json (id_to_file : id_to_file_map) (js : json) :
    (span, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("file_id", file_id); ("beg", beg_loc); ("end", end_loc) ] ->
        let* file_id = file_id_of_json file_id in
        let file = IdToFile.find file_id id_to_file in
        let* beg_loc = loc_of_json beg_loc in
        let* end_loc = loc_of_json end_loc in
        Ok { file; beg_loc; end_loc }
    | _ -> Error "")

let meta_of_json (id_to_file : id_to_file_map) (js : json) :
    (meta, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("span", span); ("generated_from_span", generated_from_span) ] ->
        let* span = span_of_json id_to_file span in
        let* generated_from_span =
          option_of_json (span_of_json id_to_file) generated_from_span
        in
        Ok { span; generated_from_span }
    | _ -> Error "")

let path_elem_of_json (js : json) : (path_elem, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Ident", name) ] ->
        let* name = string_of_json name in
        Ok (Ident name)
    | `Assoc [ ("Disambiguator", d) ] ->
        let* d = Disambiguator.id_of_json d in
        Ok (Disambiguator d)
    | _ -> Error "")

let name_of_json (js : json) : (name, string) result =
  combine_error_msgs js __FUNCTION__ (list_of_json path_elem_of_json js)

let fun_name_of_json (js : json) : (fun_name, string) result =
  combine_error_msgs js __FUNCTION__ (name_of_json js)

let type_var_of_json (js : json) : (T.type_var, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("index", index); ("name", name) ] ->
        let* index = T.TypeVarId.id_of_json index in
        let* name = string_of_json name in
        Ok { T.index; name }
    | _ -> Error "")

let region_var_of_json (js : json) : (T.region_var, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("index", index); ("name", name) ] ->
        let* index = T.RegionVarId.id_of_json index in
        let* name = string_option_of_json name in
        Ok { T.index; name }
    | _ -> Error "")

let region_of_json (js : json) : (T.RegionVarId.id T.region, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Static" -> Ok T.Static
    | `Assoc [ ("Var", rid) ] ->
        let* rid = T.RegionVarId.id_of_json rid in
        Ok (T.Var rid)
    | _ -> Error "")

let erased_region_of_json (js : json) : (T.erased_region, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with `String "Erased" -> Ok T.Erased | _ -> Error "")

let integer_type_of_json (js : json) : (T.integer_type, string) result =
  match js with
  | `String "Isize" -> Ok T.Isize
  | `String "I8" -> Ok T.I8
  | `String "I16" -> Ok T.I16
  | `String "I32" -> Ok T.I32
  | `String "I64" -> Ok T.I64
  | `String "I128" -> Ok T.I128
  | `String "Usize" -> Ok T.Usize
  | `String "U8" -> Ok T.U8
  | `String "U16" -> Ok T.U16
  | `String "U32" -> Ok T.U32
  | `String "U64" -> Ok T.U64
  | `String "U128" -> Ok T.U128
  | _ -> Error ("integer_type_of_json failed on: " ^ show js)

let ref_kind_of_json (js : json) : (T.ref_kind, string) result =
  match js with
  | `String "Mut" -> Ok T.Mut
  | `String "Shared" -> Ok T.Shared
  | _ -> Error ("ref_kind_of_json failed on: " ^ show js)

let assumed_ty_of_json (js : json) : (T.assumed_ty, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Box" -> Ok T.Box
    | `String "Vec" -> Ok T.Vec
    | `String "Option" -> Ok T.Option
    | _ -> Error "")

let type_id_of_json (js : json) : (T.type_id, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Adt", id) ] ->
        let* id = T.TypeDeclId.id_of_json id in
        Ok (T.AdtId id)
    | `String "Tuple" -> Ok T.Tuple
    | `Assoc [ ("Assumed", aty) ] ->
        let* aty = assumed_ty_of_json aty in
        Ok (T.Assumed aty)
    | _ -> Error "")

let rec ty_of_json (r_of_json : json -> ('r, string) result) (js : json) :
    ('r T.ty, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Adt", `List [ id; regions; types ]) ] ->
        let* id = type_id_of_json id in
        let* regions = list_of_json r_of_json regions in
        let* types = list_of_json (ty_of_json r_of_json) types in
        (* Sanity check *)
        (match id with T.Tuple -> assert (List.length regions = 0) | _ -> ());
        Ok (T.Adt (id, regions, types))
    | `Assoc [ ("TypeVar", `List [ id ]) ] ->
        let* id = T.TypeVarId.id_of_json id in
        Ok (T.TypeVar id)
    | `String "Bool" -> Ok Bool
    | `String "Char" -> Ok Char
    | `String "`Never" -> Ok Never
    | `Assoc [ ("Integer", `List [ int_ty ]) ] ->
        let* int_ty = integer_type_of_json int_ty in
        Ok (T.Integer int_ty)
    | `String "Str" -> Ok Str
    | `Assoc [ ("Array", `List [ ty ]) ] ->
        let* ty = ty_of_json r_of_json ty in
        Ok (T.Array ty)
    | `Assoc [ ("Slice", `List [ ty ]) ] ->
        let* ty = ty_of_json r_of_json ty in
        Ok (T.Slice ty)
    | `Assoc [ ("Ref", `List [ region; ty; ref_kind ]) ] ->
        let* region = r_of_json region in
        let* ty = ty_of_json r_of_json ty in
        let* ref_kind = ref_kind_of_json ref_kind in
        Ok (T.Ref (region, ty, ref_kind))
    | _ -> Error "")

let sty_of_json (js : json) : (T.sty, string) result =
  combine_error_msgs js __FUNCTION__ (ty_of_json region_of_json js)

let ety_of_json (js : json) : (T.ety, string) result =
  combine_error_msgs js __FUNCTION__ (ty_of_json erased_region_of_json js)

let field_of_json (id_to_file : id_to_file_map) (js : json) :
    (T.field, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("meta", meta); ("name", name); ("ty", ty) ] ->
        let* meta = meta_of_json id_to_file meta in
        let* name = option_of_json string_of_json name in
        let* ty = sty_of_json ty in
        Ok { T.meta; field_name = name; field_ty = ty }
    | _ -> Error "")

let variant_of_json (id_to_file : id_to_file_map) (js : json) :
    (T.variant, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("meta", meta); ("name", name); ("fields", fields) ] ->
        let* meta = meta_of_json id_to_file meta in
        let* name = string_of_json name in
        let* fields = list_of_json (field_of_json id_to_file) fields in
        Ok { T.meta; variant_name = name; fields }
    | _ -> Error "")

let type_decl_kind_of_json (id_to_file : id_to_file_map) (js : json) :
    (T.type_decl_kind, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Struct", fields) ] ->
        let* fields = list_of_json (field_of_json id_to_file) fields in
        Ok (T.Struct fields)
    | `Assoc [ ("Enum", variants) ] ->
        let* variants = list_of_json (variant_of_json id_to_file) variants in
        Ok (T.Enum variants)
    | `String "Opaque" -> Ok T.Opaque
    | _ -> Error "")

let region_var_group_of_json (js : json) : (T.region_var_group, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("id", id); ("regions", regions); ("parents", parents) ] ->
        let* id = T.RegionGroupId.id_of_json id in
        let* regions = list_of_json T.RegionVarId.id_of_json regions in
        let* parents = list_of_json T.RegionGroupId.id_of_json parents in
        Ok { T.id; regions; parents }
    | _ -> Error "")

let region_var_groups_of_json (js : json) : (T.region_var_groups, string) result
    =
  combine_error_msgs js __FUNCTION__ (list_of_json region_var_group_of_json js)

let type_decl_of_json (id_to_file : id_to_file_map) (js : json) :
    (T.type_decl, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("def_id", def_id);
          ("meta", meta);
          ("name", name);
          ("region_params", region_params);
          ("type_params", type_params);
          ("regions_hierarchy", regions_hierarchy);
          ("kind", kind);
        ] ->
        let* def_id = T.TypeDeclId.id_of_json def_id in
        let* meta = meta_of_json id_to_file meta in
        let* name = name_of_json name in
        let* region_params = list_of_json region_var_of_json region_params in
        let* type_params = list_of_json type_var_of_json type_params in
        let* kind = type_decl_kind_of_json id_to_file kind in
        let* regions_hierarchy = region_var_groups_of_json regions_hierarchy in
        Ok
          {
            T.def_id;
            meta;
            name;
            region_params;
            type_params;
            kind;
            regions_hierarchy;
          }
    | _ -> Error "")

let var_of_json (js : json) : (A.var, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("index", index); ("name", name); ("ty", ty) ] ->
        let* index = V.VarId.id_of_json index in
        let* name = string_option_of_json name in
        let* var_ty = ety_of_json ty in
        Ok { A.index; name; var_ty }
    | _ -> Error "")

let big_int_of_json (js : json) : (V.big_int, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Int i -> Ok (Z.of_int i)
    | `String is -> Ok (Z.of_string is)
    | _ -> Error "")

(** Deserialize a {!V.scalar_value} from JSON and **check the ranges**.
    
    Note that in practice we also check that the values are in range
    in the interpreter functions. Still, it doesn't cost much to be
    a bit conservative.
 *)
let scalar_value_of_json (js : json) : (V.scalar_value, string) result =
  let res =
    combine_error_msgs js __FUNCTION__
      (match js with
      | `Assoc [ ("Isize", `List [ bi ]) ] ->
          let* bi = big_int_of_json bi in
          Ok { V.value = bi; int_ty = Isize }
      | `Assoc [ ("I8", `List [ bi ]) ] ->
          let* bi = big_int_of_json bi in
          Ok { V.value = bi; int_ty = I8 }
      | `Assoc [ ("I16", `List [ bi ]) ] ->
          let* bi = big_int_of_json bi in
          Ok { V.value = bi; int_ty = I16 }
      | `Assoc [ ("I32", `List [ bi ]) ] ->
          let* bi = big_int_of_json bi in
          Ok { V.value = bi; int_ty = I32 }
      | `Assoc [ ("I64", `List [ bi ]) ] ->
          let* bi = big_int_of_json bi in
          Ok { V.value = bi; int_ty = I64 }
      | `Assoc [ ("I128", `List [ bi ]) ] ->
          let* bi = big_int_of_json bi in
          Ok { V.value = bi; int_ty = I128 }
      | `Assoc [ ("Usize", `List [ bi ]) ] ->
          let* bi = big_int_of_json bi in
          Ok { V.value = bi; int_ty = Usize }
      | `Assoc [ ("U8", `List [ bi ]) ] ->
          let* bi = big_int_of_json bi in
          Ok { V.value = bi; int_ty = U8 }
      | `Assoc [ ("U16", `List [ bi ]) ] ->
          let* bi = big_int_of_json bi in
          Ok { V.value = bi; int_ty = U16 }
      | `Assoc [ ("U32", `List [ bi ]) ] ->
          let* bi = big_int_of_json bi in
          Ok { V.value = bi; int_ty = U32 }
      | `Assoc [ ("U64", `List [ bi ]) ] ->
          let* bi = big_int_of_json bi in
          Ok { V.value = bi; int_ty = U64 }
      | `Assoc [ ("U128", `List [ bi ]) ] ->
          let* bi = big_int_of_json bi in
          Ok { V.value = bi; int_ty = U128 }
      | _ -> Error "")
  in
  match res with
  | Error _ -> res
  | Ok sv ->
      if not (S.check_scalar_value_in_range sv) then (
        log#serror ("Scalar value not in range: " ^ V.show_scalar_value sv);
        raise (Failure ("Scalar value not in range: " ^ V.show_scalar_value sv)));
      res

let field_proj_kind_of_json (js : json) : (E.field_proj_kind, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("ProjAdt", `List [ def_id; opt_variant_id ]) ] ->
        let* def_id = T.TypeDeclId.id_of_json def_id in
        let* opt_variant_id =
          option_of_json T.VariantId.id_of_json opt_variant_id
        in
        Ok (E.ProjAdt (def_id, opt_variant_id))
    | `Assoc [ ("ProjTuple", i) ] ->
        let* i = int_of_json i in
        Ok (E.ProjTuple i)
    | `Assoc [ ("ProjOption", variant_id) ] ->
        let* variant_id = T.VariantId.id_of_json variant_id in
        Ok (E.ProjOption variant_id)
    | _ -> Error "")

let projection_elem_of_json (js : json) : (E.projection_elem, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "Deref" -> Ok E.Deref
    | `String "DerefBox" -> Ok E.DerefBox
    | `Assoc [ ("Field", `List [ proj_kind; field_id ]) ] ->
        let* proj_kind = field_proj_kind_of_json proj_kind in
        let* field_id = T.FieldId.id_of_json field_id in
        Ok (E.Field (proj_kind, field_id))
    | _ -> Error ("projection_elem_of_json failed on:" ^ show js))

let projection_of_json (js : json) : (E.projection, string) result =
  combine_error_msgs js __FUNCTION__ (list_of_json projection_elem_of_json js)

let place_of_json (js : json) : (E.place, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("var_id", var_id); ("projection", projection) ] ->
        let* var_id = V.VarId.id_of_json var_id in
        let* projection = projection_of_json projection in
        Ok { E.var_id; projection }
    | _ -> Error "")

let borrow_kind_of_json (js : json) : (E.borrow_kind, string) result =
  match js with
  | `String "Shared" -> Ok E.Shared
  | `String "Mut" -> Ok E.Mut
  | `String "TwoPhaseMut" -> Ok E.TwoPhaseMut
  | _ -> Error ("borrow_kind_of_json failed on:" ^ show js)

let unop_of_json (js : json) : (E.unop, string) result =
  match js with
  | `String "Not" -> Ok E.Not
  | `String "Neg" -> Ok E.Neg
  | `Assoc [ ("Cast", `List [ src_ty; tgt_ty ]) ] ->
      let* src_ty = integer_type_of_json src_ty in
      let* tgt_ty = integer_type_of_json tgt_ty in
      Ok (E.Cast (src_ty, tgt_ty))
  | _ -> Error ("unop_of_json failed on:" ^ show js)

let binop_of_json (js : json) : (E.binop, string) result =
  match js with
  | `String "BitXor" -> Ok E.BitXor
  | `String "BitAnd" -> Ok E.BitAnd
  | `String "BitOr" -> Ok E.BitOr
  | `String "Eq" -> Ok E.Eq
  | `String "Lt" -> Ok E.Lt
  | `String "Le" -> Ok E.Le
  | `String "Ne" -> Ok E.Ne
  | `String "Ge" -> Ok E.Ge
  | `String "Gt" -> Ok E.Gt
  | `String "Div" -> Ok E.Div
  | `String "Rem" -> Ok E.Rem
  | `String "Add" -> Ok E.Add
  | `String "Sub" -> Ok E.Sub
  | `String "Mul" -> Ok E.Mul
  | `String "Shl" -> Ok E.Shl
  | `String "Shr" -> Ok E.Shr
  | _ -> Error ("binop_of_json failed on:" ^ show js)

let constant_value_of_json (js : json) : (V.constant_value, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Scalar", scalar_value) ] ->
        let* scalar_value = scalar_value_of_json scalar_value in
        Ok (V.Scalar scalar_value)
    | `Assoc [ ("Bool", v) ] ->
        let* v = bool_of_json v in
        Ok (V.Bool v)
    | `Assoc [ ("Char", v) ] ->
        let* v = char_of_json v in
        Ok (V.Char v)
    | `Assoc [ ("String", v) ] ->
        let* v = string_of_json v in
        Ok (V.String v)
    | _ -> Error "")

let operand_of_json (js : json) : (E.operand, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Copy", place) ] ->
        let* place = place_of_json place in
        Ok (E.Copy place)
    | `Assoc [ ("Move", place) ] ->
        let* place = place_of_json place in
        Ok (E.Move place)
    | `Assoc [ ("Const", `List [ ty; cv ]) ] ->
        let* ty = ety_of_json ty in
        let* cv = constant_value_of_json cv in
        Ok (E.Constant (ty, cv))
    | _ -> Error "")

let aggregate_kind_of_json (js : json) : (E.aggregate_kind, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `String "AggregatedTuple" -> Ok E.AggregatedTuple
    | `Assoc [ ("AggregatedOption", `List [ variant_id; ty ]) ] ->
        let* variant_id = T.VariantId.id_of_json variant_id in
        let* ty = ety_of_json ty in
        Ok (E.AggregatedOption (variant_id, ty))
    | `Assoc [ ("AggregatedAdt", `List [ id; opt_variant_id; regions; tys ]) ]
      ->
        let* id = T.TypeDeclId.id_of_json id in
        let* opt_variant_id =
          option_of_json T.VariantId.id_of_json opt_variant_id
        in
        let* regions = list_of_json erased_region_of_json regions in
        let* tys = list_of_json ety_of_json tys in
        Ok (E.AggregatedAdt (id, opt_variant_id, regions, tys))
    | _ -> Error "")

let rvalue_of_json (js : json) : (E.rvalue, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Use", op) ] ->
        let* op = operand_of_json op in
        Ok (E.Use op)
    | `Assoc [ ("Ref", `List [ place; borrow_kind ]) ] ->
        let* place = place_of_json place in
        let* borrow_kind = borrow_kind_of_json borrow_kind in
        Ok (E.Ref (place, borrow_kind))
    | `Assoc [ ("UnaryOp", `List [ unop; op ]) ] ->
        let* unop = unop_of_json unop in
        let* op = operand_of_json op in
        Ok (E.UnaryOp (unop, op))
    | `Assoc [ ("BinaryOp", `List [ binop; op1; op2 ]) ] ->
        let* binop = binop_of_json binop in
        let* op1 = operand_of_json op1 in
        let* op2 = operand_of_json op2 in
        Ok (E.BinaryOp (binop, op1, op2))
    | `Assoc [ ("Discriminant", place) ] ->
        let* place = place_of_json place in
        Ok (E.Discriminant place)
    | `Assoc [ ("Aggregate", `List [ aggregate_kind; ops ]) ] ->
        let* aggregate_kind = aggregate_kind_of_json aggregate_kind in
        let* ops = list_of_json operand_of_json ops in
        Ok (E.Aggregate (aggregate_kind, ops))
    | _ -> Error "")

let assumed_fun_id_of_json (js : json) : (A.assumed_fun_id, string) result =
  match js with
  | `String "Replace" -> Ok A.Replace
  | `String "BoxNew" -> Ok A.BoxNew
  | `String "BoxDeref" -> Ok A.BoxDeref
  | `String "BoxDerefMut" -> Ok A.BoxDerefMut
  | `String "BoxFree" -> Ok A.BoxFree
  | `String "VecNew" -> Ok A.VecNew
  | `String "VecPush" -> Ok A.VecPush
  | `String "VecInsert" -> Ok A.VecInsert
  | `String "VecLen" -> Ok A.VecLen
  | `String "VecIndex" -> Ok A.VecIndex
  | `String "VecIndexMut" -> Ok A.VecIndexMut
  | _ -> Error ("assumed_fun_id_of_json failed on:" ^ show js)

let fun_id_of_json (js : json) : (A.fun_id, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Regular", id) ] ->
        let* id = A.FunDeclId.id_of_json id in
        Ok (A.Regular id)
    | `Assoc [ ("Assumed", fid) ] ->
        let* fid = assumed_fun_id_of_json fid in
        Ok (A.Assumed fid)
    | _ -> Error "")

let assertion_of_json (js : json) : (A.assertion, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("cond", cond); ("expected", expected) ] ->
        let* cond = operand_of_json cond in
        let* expected = bool_of_json expected in
        Ok { A.cond; expected }
    | _ -> Error "")

let fun_sig_of_json (js : json) : (A.fun_sig, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("region_params", region_params);
          ("num_early_bound_regions", num_early_bound_regions);
          ("regions_hierarchy", regions_hierarchy);
          ("type_params", type_params);
          ("inputs", inputs);
          ("output", output);
        ] ->
        let* region_params = list_of_json region_var_of_json region_params in
        let* num_early_bound_regions = int_of_json num_early_bound_regions in
        let* regions_hierarchy = region_var_groups_of_json regions_hierarchy in
        let* type_params = list_of_json type_var_of_json type_params in
        let* inputs = list_of_json sty_of_json inputs in
        let* output = sty_of_json output in
        Ok
          {
            A.region_params;
            num_early_bound_regions;
            regions_hierarchy;
            type_params;
            inputs;
            output;
          }
    | _ -> Error "")

let call_of_json (js : json) : (A.call, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("func", func);
          ("region_args", region_args);
          ("type_args", type_args);
          ("args", args);
          ("dest", dest);
        ] ->
        let* func = fun_id_of_json func in
        let* region_args = list_of_json erased_region_of_json region_args in
        let* type_args = list_of_json ety_of_json type_args in
        let* args = list_of_json operand_of_json args in
        let* dest = place_of_json dest in
        Ok { A.func; region_args; type_args; args; dest }
    | _ -> Error "")

let rec statement_of_json (id_to_file : id_to_file_map) (js : json) :
    (A.statement, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("meta", meta); ("content", content) ] ->
        let* meta = meta_of_json id_to_file meta in
        let* content = raw_statement_of_json id_to_file content in
        Ok { A.meta; content }
    | _ -> Error "")

and raw_statement_of_json (id_to_file : id_to_file_map) (js : json) :
    (A.raw_statement, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Assign", `List [ place; rvalue ]) ] ->
        let* place = place_of_json place in
        let* rvalue = rvalue_of_json rvalue in
        Ok (A.Assign (place, rvalue))
    | `Assoc [ ("AssignGlobal", `List [ dst; global ]) ] ->
        let* dst = V.VarId.id_of_json dst in
        let* global = A.GlobalDeclId.id_of_json global in
        Ok (A.AssignGlobal { dst; global })
    | `Assoc [ ("FakeRead", place) ] ->
        let* place = place_of_json place in
        Ok (A.FakeRead place)
    | `Assoc [ ("SetDiscriminant", `List [ place; variant_id ]) ] ->
        let* place = place_of_json place in
        let* variant_id = T.VariantId.id_of_json variant_id in
        Ok (A.SetDiscriminant (place, variant_id))
    | `Assoc [ ("Drop", place) ] ->
        let* place = place_of_json place in
        Ok (A.Drop place)
    | `Assoc [ ("Assert", assertion) ] ->
        let* assertion = assertion_of_json assertion in
        Ok (A.Assert assertion)
    | `Assoc [ ("Call", call) ] ->
        let* call = call_of_json call in
        Ok (A.Call call)
    | `String "Panic" -> Ok A.Panic
    | `String "Return" -> Ok A.Return
    | `Assoc [ ("Break", i) ] ->
        let* i = int_of_json i in
        Ok (A.Break i)
    | `Assoc [ ("Continue", i) ] ->
        let* i = int_of_json i in
        Ok (A.Continue i)
    | `String "Nop" -> Ok A.Nop
    | `Assoc [ ("Sequence", `List [ st1; st2 ]) ] ->
        let* st1 = statement_of_json id_to_file st1 in
        let* st2 = statement_of_json id_to_file st2 in
        Ok (A.Sequence (st1, st2))
    | `Assoc [ ("Switch", `List [ op; tgt ]) ] ->
        let* op = operand_of_json op in
        let* tgt = switch_targets_of_json id_to_file tgt in
        Ok (A.Switch (op, tgt))
    | `Assoc [ ("Loop", st) ] ->
        let* st = statement_of_json id_to_file st in
        Ok (A.Loop st)
    | _ -> Error "")

and switch_targets_of_json (id_to_file : id_to_file_map) (js : json) :
    (A.switch_targets, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("If", `List [ st1; st2 ]) ] ->
        let* st1 = statement_of_json id_to_file st1 in
        let* st2 = statement_of_json id_to_file st2 in
        Ok (A.If (st1, st2))
    | `Assoc [ ("SwitchInt", `List [ int_ty; tgts; otherwise ]) ] ->
        let* int_ty = integer_type_of_json int_ty in
        let* tgts =
          list_of_json
            (pair_of_json
               (list_of_json scalar_value_of_json)
               (statement_of_json id_to_file))
            tgts
        in
        let* otherwise = statement_of_json id_to_file otherwise in
        Ok (A.SwitchInt (int_ty, tgts, otherwise))
    | _ -> Error "")

let fun_body_of_json (id_to_file : id_to_file_map) (js : json) :
    (A.fun_body, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("meta", meta);
          ("arg_count", arg_count);
          ("locals", locals);
          ("body", body);
        ] ->
        let* meta = meta_of_json id_to_file meta in
        let* arg_count = int_of_json arg_count in
        let* locals = list_of_json var_of_json locals in
        let* body = statement_of_json id_to_file body in
        Ok { A.meta; arg_count; locals; body }
    | _ -> Error "")

let fun_decl_of_json (id_to_file : id_to_file_map) (js : json) :
    (A.fun_decl, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("def_id", def_id);
          ("meta", meta);
          ("name", name);
          ("signature", signature);
          ("body", body);
        ] ->
        let* def_id = A.FunDeclId.id_of_json def_id in
        let* meta = meta_of_json id_to_file meta in
        let* name = fun_name_of_json name in
        let* signature = fun_sig_of_json signature in
        let* body = option_of_json (fun_body_of_json id_to_file) body in
        Ok
          { A.def_id; meta; name; signature; body; is_global_decl_body = false }
    | _ -> Error "")

(* Strict type for the number of function declarations (see {!global_to_fun_id} below) *)
type global_id_converter = { fun_count : int } [@@deriving show]

(** Converts a global id to its corresponding function id.
    To do so, it adds the global id to the number of function declarations :
    We have the bijection [global_fun_id <=> global_id + fun_id_count].
*)
let global_to_fun_id (conv : global_id_converter) (gid : A.GlobalDeclId.id) :
    A.FunDeclId.id =
  A.FunDeclId.of_int (A.GlobalDeclId.to_int gid + conv.fun_count)

(* Converts a global declaration to a function declaration.
 *)
let global_decl_of_json (id_to_file : id_to_file_map) (js : json)
    (gid_conv : global_id_converter) :
    (A.global_decl * A.fun_decl, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("def_id", def_id);
          ("meta", meta);
          ("name", name);
          ("ty", ty);
          ("body", body);
        ] ->
        let* global_id = A.GlobalDeclId.id_of_json def_id in
        let fun_id = global_to_fun_id gid_conv global_id in
        let* meta = meta_of_json id_to_file meta in
        let* name = fun_name_of_json name in
        let* ty = ety_of_json ty in
        let* body = option_of_json (fun_body_of_json id_to_file) body in
        let signature : A.fun_sig =
          {
            region_params = [];
            num_early_bound_regions = 0;
            regions_hierarchy = [];
            type_params = [];
            inputs = [];
            output = TU.ety_no_regions_to_sty ty;
          }
        in
        Ok
          ( { A.def_id = global_id; meta; body_id = fun_id; name; ty },
            {
              A.def_id = fun_id;
              meta;
              name;
              signature;
              body;
              is_global_decl_body = true;
            } )
    | _ -> Error "")

let g_declaration_group_of_json (id_of_json : json -> ('id, string) result)
    (js : json) : ('id Crates.g_declaration_group, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("NonRec", `List [ id ]) ] ->
        let* id = id_of_json id in
        Ok (Crates.NonRec id)
    | `Assoc [ ("Rec", `List [ ids ]) ] ->
        let* ids = list_of_json id_of_json ids in
        Ok (Crates.Rec ids)
    | _ -> Error "")

let type_declaration_group_of_json (js : json) :
    (Crates.type_declaration_group, string) result =
  combine_error_msgs js __FUNCTION__
    (g_declaration_group_of_json T.TypeDeclId.id_of_json js)

let fun_declaration_group_of_json (js : json) :
    (Crates.fun_declaration_group, string) result =
  combine_error_msgs js __FUNCTION__
    (g_declaration_group_of_json A.FunDeclId.id_of_json js)

let global_declaration_group_of_json (js : json) :
    (A.GlobalDeclId.id, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("NonRec", `List [ id ]) ] ->
        let* id = A.GlobalDeclId.id_of_json id in
        Ok id
    | `Assoc [ ("Rec", `List [ _ ]) ] -> Error "got mutually dependent globals"
    | _ -> Error "")

let declaration_group_of_json (js : json) :
    (Crates.declaration_group, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Type", `List [ decl ]) ] ->
        let* decl = type_declaration_group_of_json decl in
        Ok (Crates.Type decl)
    | `Assoc [ ("Fun", `List [ decl ]) ] ->
        let* decl = fun_declaration_group_of_json decl in
        Ok (Crates.Fun decl)
    | `Assoc [ ("Global", `List [ decl ]) ] ->
        let* id = global_declaration_group_of_json decl in
        Ok (Crates.Global id)
    | _ -> Error "")

let length_of_json_list (js : json) : (int, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `List jsl -> Ok (List.length jsl)
    | _ -> Error ("not a list: " ^ show js))

let llbc_crate_of_json (js : json) : (Crates.llbc_crate, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc
        [
          ("name", name);
          ("id_to_file", id_to_file);
          ("declarations", declarations);
          ("types", types);
          ("functions", functions);
          ("globals", globals);
        ] ->
        (* We first deserialize the declaration groups (which simply contain ids)
         * and all the declarations *butù* the globals *)
        let* name = string_of_json name in
        let* id_to_file = id_to_file_of_json id_to_file in
        let* declarations =
          list_of_json declaration_group_of_json declarations
        in
        let* types = list_of_json (type_decl_of_json id_to_file) types in
        let* functions = list_of_json (fun_decl_of_json id_to_file) functions in
        (* When deserializing the globals, we split the global declarations
         * between the globals themselves and their bodies, which are simply
         * functions with no arguments. We add the global bodies to the list
         * of function declarations: the (fresh) ids we use for those bodies
         * are simply given by: [num_functions + global_id] *)
        let gid_conv = { fun_count = List.length functions } in
        let* globals =
          list_of_json
            (fun js -> global_decl_of_json id_to_file js gid_conv)
            globals
        in
        let globals, global_bodies = List.split globals in
        Ok
          {
            Crates.name;
            declarations;
            types;
            functions = functions @ global_bodies;
            globals;
          }
    | _ -> Error "")
