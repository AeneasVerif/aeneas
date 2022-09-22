(** Printing utilities for symbolic AST.

    We don't put this in [Print] because:
    - [Print] is getting quite big
    - if we do so we have a dependency cycle...
 *)

open Errors
open Identifiers
open FunIdentifier
module T = Types
module TU = TypesUtils
module V = Values
module E = Expressions
module A = LlbcAst
module C = Contexts
module M = Modules
open SymbolicAst
module P = Print
module PT = Print.Types

type formatting_ctx = {
  type_context : C.type_context;
  fun_context : A.fun_decl FunDeclId.Map.t;
  type_vars : T.type_var list;
}

type formatter = P.Values.value_formatter

let formatting_ctx_to_formatter (ctx : formatting_ctx) : formatter =
  (* We shouldn't use [rvar_to_string] *)
  let rvar_to_string _ = failwith "Unexpected use of rvar_to_string" in
  let r_to_string r = PT.region_id_to_string r in

  let type_var_id_to_string vid =
    let v = T.TypeVarId.nth ctx.type_vars vid in
    v.name
  in
  let type_decl_id_to_string def_id =
    let def = T.TypeDeclId.Map.find def_id ctx.type_context.type_decls in
    P.name_to_string def.name
  in
  let adt_variant_to_string =
    P.Contexts.type_ctx_to_adt_variant_to_string_fun ctx.type_context.type_decls
  in
  (* We shouldn't use [var_id_to_string] *)
  let var_id_to_string _ = failwith "Unexpected use of var_id_to_string" in

  let adt_field_names =
    P.Contexts.type_ctx_to_adt_field_names_fun ctx.type_context.type_decls
  in
  {
    rvar_to_string;
    r_to_string;
    type_var_id_to_string;
    type_decl_id_to_string;
    adt_variant_to_string;
    var_id_to_string;
    adt_field_names;
  }
