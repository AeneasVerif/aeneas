(** This file implements utilities to handle trait associated types, in
    particular with normalization helpers.

    When normalizing a type, we simplify the references to the trait associated
    types, and choose a representative when there are equalities between types
    enforced by local clauses (i.e., clauses of the shape
    [where Trait1::T = Trait2::U]). *)

open Types
open TypesUtils
open Values
open LlbcAst
open Contexts
open Substitute
open Errors

(** The local logger *)
let log = Logging.associated_types_log

(** A trait instance id refers to a local clause if it only uses the variants:
    [Self], [Clause], [ParentClause] *)
let rec trait_instance_id_is_local_clause (id : trait_instance_id) : bool =
  match id with
  | Self | Clause _ -> true
  | ParentClause (tref, _) -> trait_instance_id_is_local_clause tref.trait_id
  | TraitImpl _ | BuiltinOrAuto _ | UnknownTrait _ | Dyn _ -> false

(** Check that it is ok for a trait instance id not to be normalizable.

    We use this in sanity checks. If we can't normalize a trait instance id (and
    in particular one of its associated types) there are two possibilities:
    - either it is a local clause
    - or it is a builtin trait (in particular, [core::marker::DiscriminantKind]
      can never be reduced) *)
let check_non_normalizable_trait_instance_id (trait_id : trait_instance_id) :
    bool =
  trait_instance_id_is_local_clause trait_id
  ||
  match trait_id with
  | BuiltinOrAuto _ -> true
  | _ -> false

let ctx_type_get_inst_norm_variants_fields_rtypes (span : Meta.span)
    (ctx : eval_ctx) (def_id : TypeDeclId.id) (generics : generic_args) :
    (VariantId.id option * ty list) list =
  ctx_type_get_instantiated_variants_fields_types span ctx def_id generics

let ctx_type_get_inst_norm_variants_fields_etypes (span : Meta.span)
    (ctx : eval_ctx) (def_id : TypeDeclId.id) (generics : generic_args) :
    (VariantId.id option * ty list) list =
  let res =
    ctx_type_get_inst_norm_variants_fields_rtypes span ctx def_id generics
  in
  List.map
    (fun (variant_id, types) -> (variant_id, List.map erase_regions types))
    res

(** Same as [type_decl_get_instantiated_field_types] but normalizes the types *)
let type_decl_get_inst_norm_field_rtypes (def : type_decl)
    (opt_variant_id : VariantId.id option) (generics : generic_args) : ty list =
  type_decl_get_instantiated_field_types def opt_variant_id generics

(** Same as [ctx_adt_value_get_instantiated_field_types] but normalizes the
    types and erases the regions. *)
let type_decl_get_inst_norm_field_etypes (def : type_decl)
    (opt_variant_id : VariantId.id option) (generics : generic_args) : ty list =
  let types =
    type_decl_get_instantiated_field_types def opt_variant_id generics
  in
  List.map erase_regions types

(** Same as [ctx_type_get_instantiated_field_types] but normalizes the types. *)
let ctx_type_get_inst_norm_field_rtypes (span : Meta.span) (ctx : eval_ctx)
    (def_id : TypeDeclId.id) (opt_variant_id : VariantId.id option)
    (generics : generic_args) : ty list =
  ctx_type_get_instantiated_field_types span ctx def_id opt_variant_id generics

(** Same as [ctx_type_get_instantiated_field_types] but normalizes the types and
    erases the regions. *)
let ctx_type_get_inst_norm_field_etypes (span : Meta.span) (ctx : eval_ctx)
    (def_id : TypeDeclId.id) (opt_variant_id : VariantId.id option)
    (generics : generic_args) : ty list =
  let types =
    ctx_type_get_inst_norm_field_rtypes span ctx def_id opt_variant_id generics
  in
  List.map erase_regions types
