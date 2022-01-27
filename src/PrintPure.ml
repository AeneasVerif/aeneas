(** This module defines printing functions for the types defined in Pure.ml *)

open Identifiers
open Pure
module T = Types
module V = Values
module E = Expressions
module A = CfimAst
module TypeDefId = T.TypeDefId
module TypeVarId = T.TypeVarId
module RegionId = T.RegionId
module VariantId = T.VariantId
module FieldId = T.FieldId
module SymbolicValueId = V.SymbolicValueId
module FunDefId = A.FunDefId

type type_formatter = {
  type_var_id_to_string : T.TypeVarId.id -> string;
  type_def_id_to_string : T.TypeDefId.id -> string;
}

type value_formatter = {
  type_var_id_to_string : T.TypeVarId.id -> string;
  type_def_id_to_string : T.TypeDefId.id -> string;
  adt_variant_to_string : T.TypeDefId.id -> T.VariantId.id -> string;
  adt_field_names :
    T.TypeDefId.id -> T.VariantId.id option -> string list option;
}

let value_to_type_formatter (fmt : value_formatter) : type_formatter =
  {
    type_var_id_to_string = fmt.type_var_id_to_string;
    type_def_id_to_string = fmt.type_def_id_to_string;
  }

type ast_formatter = {
  type_var_id_to_string : T.TypeVarId.id -> string;
  type_def_id_to_string : T.TypeDefId.id -> string;
  adt_variant_to_string : T.TypeDefId.id -> T.VariantId.id -> string;
  adt_field_to_string :
    T.TypeDefId.id -> T.VariantId.id option -> T.FieldId.id -> string;
  adt_field_names :
    T.TypeDefId.id -> T.VariantId.id option -> string list option;
  fun_def_id_to_string : A.FunDefId.id -> string;
}

let ast_to_value_formatter (fmt : ast_formatter) : value_formatter =
  {
    type_var_id_to_string = fmt.type_var_id_to_string;
    type_def_id_to_string = fmt.type_def_id_to_string;
    adt_variant_to_string = fmt.adt_variant_to_string;
    adt_field_names = fmt.adt_field_names;
  }

let ast_to_type_formatter (fmt : ast_formatter) : type_formatter =
  let fmt = ast_to_value_formatter fmt in
  value_to_type_formatter fmt

(* TODO: there is a bit of duplication with Print.fun_def_to_ast_formatter *)
let fun_def_to_ast_formatter (type_defs : T.type_def T.TypeDefId.Map.t)
    (fun_defs : A.fun_def A.FunDefId.Map.t) (fdef : A.fun_def) : ast_formatter =
  let type_var_id_to_string vid =
    let var = T.TypeVarId.nth fdef.signature.type_params vid in
    Print.Types.type_var_to_string var
  in
  let type_def_id_to_string def_id =
    let def = T.TypeDefId.Map.find def_id type_defs in
    Print.name_to_string def.name
  in
  let adt_variant_to_string =
    Print.Contexts.type_ctx_to_adt_variant_to_string_fun type_defs
  in
  let adt_field_names =
    Print.Contexts.type_ctx_to_adt_field_names_fun type_defs
  in
  let adt_field_to_string =
    Print.CfimAst.type_ctx_to_adt_field_to_string_fun type_defs
  in
  let fun_def_id_to_string def_id =
    let def = A.FunDefId.Map.find def_id fun_defs in
    Print.name_to_string def.name
  in
  {
    type_var_id_to_string;
    type_def_id_to_string;
    adt_variant_to_string;
    adt_field_names;
    adt_field_to_string;
    fun_def_id_to_string;
  }

let type_id_to_string (fmt : type_formatter) (id : T.type_id) : string =
  match id with
  | T.AdtId id -> fmt.type_def_id_to_string id
  | T.Tuple -> ""
  | T.Assumed aty -> (
      match aty with
      | Box -> (* Boxes should have been eliminated *) failwith "Unreachable")

let rec ty_to_string (fmt : type_formatter) (ty : ty) : string =
  match ty with
  | Adt (id, tys) -> (
      let tys = List.map (ty_to_string fmt) tys in
      match id with
      | T.Tuple -> "(" ^ String.concat " * " tys ^ ")"
      | T.AdtId _ | T.Assumed _ ->
          let tys = if tys = [] then "" else " " ^ String.concat " " tys in
          type_id_to_string fmt id ^ tys)
  | TypeVar tv -> fmt.type_var_id_to_string tv
  | Bool -> "bool"
  | Char -> "char"
  | Integer int_ty -> Print.Types.integer_type_to_string int_ty
  | Str -> "str"
  | Array aty -> "[" ^ ty_to_string fmt aty ^ "; ?]"
  | Slice sty -> "[" ^ ty_to_string fmt sty ^ "]"
