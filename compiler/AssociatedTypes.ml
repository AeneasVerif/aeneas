(** This file implements utilities to handle trait associated types, in
    particular with normalization helpers.

    When normalizing a type, we simplify the references to the trait associated
    types, and choose a representative when there are equalities between types
    enforced by local clauses (i.e., clauses of the shape [where Trait1::T = Trait2::U]).
 *)

module T = Types
module TU = TypesUtils
module V = Values
module E = Expressions
module A = LlbcAst
module C = Contexts
module Subst = Substitute
module L = Logging

(** The local logger *)
let log = L.associated_types_log

(** Normalize a type by simplyfying the references to trait associated types
    and choosing a representative when there are equalities between types
    enforced by local clauses (i.e., `where Trait1::T = Trait2::U`. *)
let ctx_normalize_type (_ctx : C.eval_ctx) (_ty : 'r T.ty) : 'r T.ty =
  raise (Failure "Unimplemented")

(** Same as [type_decl_get_instantiated_variants_fields_rtypes] but normalizes the types *)
let type_decl_get_inst_norm_variants_fields_rtypes (ctx : C.eval_ctx)
    (def : T.type_decl) (generics : T.rgeneric_args) :
    (T.VariantId.id option * T.rty list) list =
  let res =
    Subst.type_decl_get_instantiated_variants_fields_rtypes def generics
  in
  List.map
    (fun (variant_id, types) ->
      (variant_id, List.map (ctx_normalize_type ctx) types))
    res

(** Same as [type_decl_get_instantiated_field_rtypes] but normalizes the types *)
let type_decl_get_inst_norm_field_rtypes (ctx : C.eval_ctx) (def : T.type_decl)
    (opt_variant_id : T.VariantId.id option) (generics : T.rgeneric_args) :
    T.rty list =
  let types =
    Subst.type_decl_get_instantiated_field_rtypes def opt_variant_id generics
  in
  List.map (ctx_normalize_type ctx) types

(** Same as [ctx_adt_value_get_instantiated_field_rtypes] but normalizes the types *)
let ctx_adt_value_get_inst_norm_field_rtypes (ctx : C.eval_ctx)
    (adt : V.adt_value) (id : T.type_id) (generics : T.rgeneric_args) :
    T.rty list =
  let types =
    Subst.ctx_adt_value_get_instantiated_field_rtypes ctx adt id generics
  in
  List.map (ctx_normalize_type ctx) types

(** Same as [ctx_adt_value_get_instantiated_field_etypes] but normalizes the types *)
let type_decl_get_inst_norm_field_etypes (ctx : C.eval_ctx) (def : T.type_decl)
    (opt_variant_id : T.VariantId.id option) (generics : T.egeneric_args) :
    T.ety list =
  let types =
    Subst.type_decl_get_instantiated_field_etypes def opt_variant_id generics
  in
  List.map (ctx_normalize_type ctx) types

(** Same as [ctx_adt_get_instantiated_field_etypes] but normalizes the types *)
let ctx_adt_get_inst_norm_field_etypes (ctx : C.eval_ctx)
    (def_id : T.TypeDeclId.id) (opt_variant_id : T.VariantId.id option)
    (generics : T.egeneric_args) : T.ety list =
  let types =
    Subst.ctx_adt_get_instantiated_field_etypes ctx def_id opt_variant_id
      generics
  in
  List.map (ctx_normalize_type ctx) types

(** Same as [substitute_signature] but normalizes the types *)
let ctx_subst_norm_signature (ctx : C.eval_ctx)
    (asubst : T.RegionGroupId.id -> V.AbstractionId.id)
    (r_subst : T.RegionVarId.id -> T.RegionId.id)
    (ty_subst : T.TypeVarId.id -> T.rty)
    (cg_subst : T.ConstGenericVarId.id -> T.const_generic)
    (tr_subst : T.TraitClauseId.id -> T.rtrait_instance_id)
    (tr_self : T.rtrait_instance_id) (sg : A.fun_sig) : A.inst_fun_sig =
  let sg =
    Subst.substitute_signature asubst r_subst ty_subst cg_subst tr_subst tr_self
      sg
  in
  let { A.regions_hierarchy; inputs; output } = sg in
  let inputs = List.map (ctx_normalize_type ctx) inputs in
  let output = ctx_normalize_type ctx output in
  { regions_hierarchy; inputs; output }
