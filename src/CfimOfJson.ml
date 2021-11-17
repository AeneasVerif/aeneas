(** Functions to load CFIM ASTs from json.

    Initially, we used `ppx_derive_yojson` to automate this.
    However, `ppx_derive_yojson` expects formatting to be slightly
    different from what `serde_rs` generates.

    For instance, if you consider the following rust definition:
    ```
    enum t = | V
    ```
    Serializing `t::V` with `serde_rs` will generate: `"V"`.

    However, if you consider the following OCaml definition:
    ```
    type t = V
    ```
    Serializing `V` will generate: `["V"]`.

    As we consider that the `serde_rs` formatting is more logical, we decided
    to implement our own deserializing functions. Moreover, it allows us to
    generate a friendlier debugging output in case the deserialization functions
    fail.
 *)

open Yojson.Safe
open Identifiers
open Types

type json = t

let ( let* ) o f = match o with Error e -> Error e | Ok x -> f x

let rec of_json_list (a_of_json : json -> ('a, string) result) (jsl : json list)
    : ('a list, string) result =
  match jsl with
  | [] -> Ok []
  | x :: jsl' ->
      let* x = a_of_json x in
      let* jsl' = of_json_list a_of_json jsl' in
      Ok (x :: jsl')

let list_of_json (a_of_json : json -> ('a, string) result) (js : json) :
    ('a list, string) result =
  match js with
  | `List jsl -> of_json_list a_of_json jsl
  | _ -> Error ("list_of_json: not a list: " ^ show js)

let string_of_json (js : json) : (string, string) result =
  match js with
  | `String str -> Ok str
  | _ -> Error ("string_of_json: not a string: " ^ show js)

let option_of_json (a_of_json : json -> ('a, string) result) (js : json) :
    ('a option, string) result =
  match js with
  | `Variant ("Some", Some x) ->
      let* x = a_of_json x in
      Ok (Some x)
  | `Variant ("None", None) -> Ok None
  | _ -> Error ("option_of_json failed on: " ^ show js)

let string_option_of_json (js : json) : (string option, string) result =
  option_of_json string_of_json js

let name_of_json (js : json) : (name, string) result =
  list_of_json string_of_json js

let type_var_of_json (js : json) : (type_var, string) result =
  match js with
  | `Assoc [ ("index", index); ("name", name) ] ->
      let* index = TypeVarId.id_of_json index in
      let* name = string_of_json name in
      Ok { tv_index = index; tv_name = name }
  | _ -> Error ("type_var_of_json failed on:" ^ show js)

let region_var_of_json (js : json) : (region_var, string) result =
  match js with
  | `Assoc [ ("index", index); ("name", name) ] ->
      let* index = RegionVarId.id_of_json index in
      let* name = string_option_of_json name in
      Ok { rv_index = index; rv_name = name }
  | _ -> Error ("region_var_of_json failed on:" ^ show js)

let region_of_json (js : json) : (RegionVarId.id region, string) result =
  match js with
  | `Variant ("Static", None) -> Ok Static
  | `Variant ("Var", Some rid) ->
      let* rid = RegionVarId.id_of_json rid in
      Ok (Var rid)
  | _ -> Error ("region_of_json failed on:" ^ show js)

let erased_region_of_json (js : json) : (erased_region, string) result =
  match js with
  | `Variant ("Erased", None) -> Ok Erased
  | _ -> Error ("erased_region_of_json failed on:" ^ show js)

let integer_type_of_json (js : json) : (integer_type, string) result =
  match js with
  | `Variant ("Isize", None) -> Ok Isize
  | `Variant ("I8", None) -> Ok I8
  | `Variant ("I16", None) -> Ok I16
  | `Variant ("I32", None) -> Ok I32
  | `Variant ("I64", None) -> Ok I64
  | `Variant ("I128", None) -> Ok I128
  | `Variant ("Usize", None) -> Ok Usize
  | `Variant ("U8", None) -> Ok U8
  | `Variant ("U16", None) -> Ok U16
  | `Variant ("U32", None) -> Ok U32
  | `Variant ("U64", None) -> Ok U64
  | `Variant ("U128", None) -> Ok U128
  | _ -> Error ("integer_type_of_json failed on:" ^ show js)

let ref_kind_of_json (js : json) : (ref_kind, string) result =
  match js with
  | `Variant ("Mut", None) -> Ok Mut
  | `Variant ("Shared", None) -> Ok Shared
  | _ -> Error ("ref_kind_of_json failed on:" ^ show js)

let assumed_ty_of_json (js : json) : (assumed_ty, string) result =
  match js with
  | `Variant ("Box", None) -> Ok Box
  | _ -> Error ("assumed_ty_of_json failed on:" ^ show js)

let rec ty_of_json (r_of_json : json -> ('r, string) result) (js : json) :
    ('r ty, string) result =
  match js with
  | `Variant ("Adt", Some (`Tuple [ id; regions; types ])) ->
      let* id = TypeDefId.id_of_json id in
      let* regions = list_of_json r_of_json regions in
      let* types = list_of_json (ty_of_json r_of_json) types in
      Ok (Adt (id, regions, types))
  | `Variant ("TypeVar", Some id) ->
      let* id = TypeVarId.id_of_json id in
      Ok (TypeVar id)
  | `Variant ("Bool", None) -> Ok Bool
  | `Variant ("Char", None) -> Ok Char
  | `Variant ("Never", None) -> Ok Never
  | `Variant ("Integer", Some int_ty) ->
      let* int_ty = integer_type_of_json int_ty in
      Ok (Integer int_ty)
  | `Variant ("Str", None) -> Ok Str
  | `Variant ("Array", Some ty) ->
      let* ty = ty_of_json r_of_json ty in
      Ok (Array ty)
  | `Variant ("Slice", Some ty) ->
      let* ty = ty_of_json r_of_json ty in
      Ok (Slice ty)
  | `Variant ("Ref", Some (`Tuple [ region; ty; ref_kind ])) ->
      let* region = r_of_json region in
      let* ty = ty_of_json r_of_json ty in
      let* ref_kind = ref_kind_of_json ref_kind in
      Ok (Ref (region, ty, ref_kind))
  | `Variant ("Tuple", Some types) ->
      let* types = list_of_json (ty_of_json r_of_json) types in
      Ok (Tuple types)
  | `Variant ("Assumed", Some (`Tuple [ assumed_ty; regions; types ])) ->
      let* assumed_ty = assumed_ty_of_json assumed_ty in
      let* regions = list_of_json r_of_json regions in
      let* types = list_of_json (ty_of_json r_of_json) types in
      Ok (Assumed (assumed_ty, regions, types))
  | _ -> Error ("ty_of_json failed on:" ^ show js)

let rty_of_json (js : json) : (rty, string) result =
  ty_of_json region_of_json js

let ety_of_json (js : json) : (ety, string) result =
  ty_of_json erased_region_of_json js

let field_of_json (js : json) : (field, string) result =
  match js with
  | `Assoc [ ("name", name); ("ty", ty) ] ->
      let* name = string_of_json name in
      let* ty = rty_of_json ty in
      Ok { field_name = name; field_ty = ty }
  | _ -> Error ("field_of_json failed on:" ^ show js)

let variant_of_json (js : json) : (variant, string) result =
  match js with
  | `Assoc [ ("name", name); ("fields", fields) ] ->
      let* name = string_of_json name in
      let* fields = FieldId.vector_of_json field_of_json fields in
      Ok { variant_name = name; fields }
  | _ -> Error ("variant_of_json failed on:" ^ show js)

let type_def_kind_of_json (js : json) : (type_def_kind, string) result =
  match js with
  | `Variant ("Struct", Some fields) ->
      let* fields = FieldId.vector_of_json field_of_json fields in
      Ok (Struct fields)
  | `Variant ("Enum", Some variants) ->
      let* variants = VariantId.vector_of_json variant_of_json variants in
      Ok (Enum variants)
  | _ -> Error ("type_def_kind_of_json failed on:" ^ show js)

let type_def_of_json (js : json) : (type_def, string) result =
  match js with
  | `Assoc
      [
        ("def_id", def_id);
        ("name", name);
        ("region_params", region_params);
        ("type_params", type_params);
        ("kind", kind);
      ] ->
      let* def_id = TypeDefId.id_of_json def_id in
      let* name = name_of_json name in
      let* region_params =
        RegionVarId.vector_of_json region_var_of_json region_params
      in
      let* type_params =
        TypeVarId.vector_of_json type_var_of_json type_params
      in
      let* kind = type_def_kind_of_json kind in
      Ok { def_id; name; region_params; type_params; kind }
  | _ -> Error ("type_def_of_json failed on:" ^ show js)

(*
open Values
open Expressions
open CfimAst*)
