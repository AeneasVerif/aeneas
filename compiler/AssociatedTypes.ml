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
module UF = UnionFind

(** The local logger *)
let log = L.associated_types_log

let trait_type_ref_substitute (subst : ('r, 'r1) Subst.subst)
    (r : 'r C.trait_type_ref) : 'r1 C.trait_type_ref =
  let { C.trait_ref; type_name } = r in
  let trait_ref = Subst.trait_ref_substitute subst trait_ref in
  { C.trait_ref; type_name }

module RTyOrd = struct
  type t = T.rty

  let compare = T.compare_rty
  let to_string = T.show_rty
  let pp_t = T.pp_rty
  let show_t = T.show_rty
end

module RTyMap = Collections.MakeMap (RTyOrd)

(** Compute the representative classes of trait associated types, for normalization *)
let compute_norm_trait_types_from_preds
    (trait_type_constraints : T.rtrait_type_constraint list) :
    T.ety C.ETraitTypeRefMap.t * T.rty C.RTraitTypeRefMap.t =
  (* Compute a union-find structure by recursively exploring the predicates and clauses *)
  let norm : T.rty UF.elem RTyMap.t ref = ref RTyMap.empty in
  let get_ref (ty : T.rty) : T.rty UF.elem =
    match RTyMap.find_opt ty !norm with
    | Some r -> r
    | None ->
        let r = UF.make ty in
        norm := RTyMap.add ty r !norm;
        r
  in
  let add_trait_type_constraint (c : T.rtrait_type_constraint) =
    let trait_ty = T.TraitType (c.trait_ref, c.generics, c.type_name) in
    let trait_ty_ref = get_ref trait_ty in
    let ty_ref = get_ref c.ty in
    let new_repr = UF.get ty_ref in
    let merged = UF.union trait_ty_ref ty_ref in
    (* Not sure the set operation is necessary, but I want to control which
       representative is chosen *)
    UF.set merged new_repr
  in
  (* Explore the local predicates *)
  List.iter add_trait_type_constraint trait_type_constraints;
  (* TODO: explore the local clauses *)
  (* Compute the norm maps *)
  let rbindings =
    List.map (fun (k, v) -> (k, UF.get v)) (RTyMap.bindings !norm)
  in
  (* Filter the keys to keep only the trait type aliases *)
  let rbindings =
    List.filter_map
      (fun (k, v) ->
        match k with
        | T.TraitType (trait_ref, generics, type_name) ->
            assert (generics = TypesUtils.mk_empty_generic_args);
            Some ({ C.trait_ref; type_name }, v)
        | _ -> None)
      rbindings
  in
  let ebindings =
    List.map
      (fun (k, v) ->
        ( trait_type_ref_substitute Subst.erase_regions_subst k,
          Subst.erase_regions v ))
      rbindings
  in
  (C.ETraitTypeRefMap.of_list ebindings, C.RTraitTypeRefMap.of_list rbindings)

let ctx_add_norm_trait_types_from_preds (ctx : C.eval_ctx)
    (trait_type_constraints : T.rtrait_type_constraint list) : C.eval_ctx =
  let norm_trait_etypes, norm_trait_rtypes =
    compute_norm_trait_types_from_preds trait_type_constraints
  in
  { ctx with C.norm_trait_etypes; norm_trait_rtypes }

(** A trait instance id refers to a local clause if it only uses the variants:
    [Self], [Clause], [ParentClause], [ItemClause] *)
let rec trait_instance_id_is_local_clause (id : 'r T.trait_instance_id) : bool =
  match id with
  | T.Self | Clause _ -> true
  | TraitImpl _ | BuiltinOrAuto _ | TraitRef _ | UnknownTrait _ -> false
  | ParentClause (id, _) | ItemClause (id, _, _) ->
      trait_instance_id_is_local_clause id

(** About the conversion functions: for now we need them (TODO: merge ety, rty, etc.),
    but they should be applied to types without regions.
 *)
type 'r norm_ctx = {
  ctx : C.eval_ctx;
  get_ty_repr : 'r C.trait_type_ref -> 'r T.ty option;
  convert_ety : T.ety -> 'r T.ty;
  convert_etrait_ref : T.etrait_ref -> 'r T.trait_ref;
}

(** Normalize a type by simplyfying the references to trait associated types
    and choosing a representative when there are equalities between types
    enforced by local clauses (i.e., `where Trait1::T = Trait2::U`. *)
let rec ctx_normalize_ty : 'r. 'r norm_ctx -> 'r T.ty -> 'r T.ty =
 fun ctx ty ->
  match ty with
  | T.Adt (id, generics) -> Adt (id, ctx_normalize_generic_args ctx generics)
  | TypeVar _ | Literal _ | Never -> ty
  | Ref (r, ty, rkind) ->
      let ty = ctx_normalize_ty ctx ty in
      T.Ref (r, ty, rkind)
  | TraitType (trait_ref, generics, type_name) -> (
      (* Normalize and attempt to project the type from the trait ref *)
      let trait_ref = ctx_normalize_trait_ref ctx trait_ref in
      let generics = ctx_normalize_generic_args ctx generics in
      let ty : 'r T.ty =
        match trait_ref.trait_id with
        | T.TraitRef { T.trait_id = T.TraitImpl impl_id; generics; _ } ->
            (* Lookup the implementation *)
            let trait_impl = C.ctx_lookup_trait_impl ctx.ctx impl_id in
            (* Lookup the type *)
            let ty = snd (List.assoc type_name trait_impl.types) in
            (* Annoying: convert etype to an stype - TODO: hwo to avoid that? *)
            let ty : T.sty = TypesUtils.ety_no_regions_to_gr_ty ty in
            (* Substitute - annoying: we can't use *)
            let tr_self = T.UnknownTrait __FUNCTION__ in
            let subst =
              Subst.make_subst_from_generics_no_regions trait_impl.generics
                generics tr_self
            in
            let ty = Subst.ty_substitute subst ty in
            (* Reconvert *)
            let ty : 'r T.ty = ctx.convert_ety (Subst.erase_regions ty) in
            (* Normalize *)
            ctx_normalize_ty ctx ty
        | _ ->
            (* We can't project *)
            assert (trait_instance_id_is_local_clause trait_ref.trait_id);
            T.TraitType (trait_ref, generics, type_name)
      in
      let tr : 'r C.trait_type_ref = { C.trait_ref; type_name } in
      (* Lookup the representative, if there is *)
      match ctx.get_ty_repr tr with None -> ty | Some ty -> ty)

(** This returns the normalized trait instance id together with an optional
    reference to a trait **implementation**.

    We need this in particular to simplify the trait instance ids after we
    performed a substitution.

    Example:
    ========
    {[
      trait Trait {
        type S
      }

      impl TraitImpl for Foo {
        type S = usize
      }

      fn f<T : Trait>(...) -> T::S;

      ...
      let x = f<Foo>[TraitImpl](...); // T::S ~~> TraitImpl::S ~~> usize
    ]}

    Several remarks:
    - as we do not allow higher-order types (yet) then local clauses (and
      sub-clauses) can't have generic arguments
    - the [TraitRef] case only happens because of substitution, the role of
      the normalization is in particular to eliminate it. Inside a [TraitRef]
      there is necessarily:
      - an id referencing a local (sub-)clause, that is an id using the variants
        [Self], [Clause], [ItemClause] and [ParentClause] exclusively. We can't
        simplify those cases: all we can do is remove the [TraitRef] wrapper
        by leveraging the fact that the generic arguments must be empty.
      - a [TraitImpl]. Note that the [TraitImpl] is necessarily just a [TraitImpl],
        it can't be for instance a [ParentClause(TraitImpl ...)] because the
        trait resolution would then directly reference the implementation
        designated by [ParentClause(TraitImpl ...)] (and same for the other cases).
        In this case we can lookup the trait implementation and recursively project
        over it.
 *)
and ctx_normalize_trait_instance_id :
      'r.
      'r norm_ctx ->
      'r T.trait_instance_id ->
      'r T.trait_instance_id * 'r T.trait_ref option =
 fun ctx id ->
  match id with
  | Self -> (id, None)
  | TraitImpl _ ->
      (* The [TraitImpl] shouldn't be inside any projection - we check this
         elsewhere by asserting that whenever we return [None] for the impl
         trait ref, then the id actually refers to a local clause. *)
      (id, None)
  | Clause _ -> (id, None)
  | BuiltinOrAuto _ -> (id, None)
  | ParentClause (inst_id, clause_id) -> (
      let inst_id, impl = ctx_normalize_trait_instance_id ctx inst_id in
      (* Check if the inst_id refers to a specific implementation, if yes project *)
      match impl with
      | None ->
          (* This is actually a local clause *)
          assert (trait_instance_id_is_local_clause inst_id);
          (ParentClause (inst_id, clause_id), None)
      | Some impl ->
          (* We figure out the parent clause by doing the following:
             {[
               // The implementation we are looking at
               impl Impl1 : Trait1 { ... }

               // Check the trait it implements
               trait Trait1 : ParentTrait1 + ParentTrait2 { ... }
                              ^^^^^^^^^^^^^^^^^^^^^^^^^^^
                              those are the parent clauses
             ]}

             We can find the parent clauses in the [trait_decl_ref] field, which
             tells us which specific instantiation of [Trait1] is implemented
             by [Impl1].
          *)
          let clause =
            T.TraitClauseId.nth impl.trait_decl_ref.decl_generics.trait_refs
              clause_id
          in
          (* Sanity check: the clause necessarily refers to an impl *)
          let _ = TypesUtils.trait_instance_id_as_trait_impl clause.trait_id in
          (TraitRef clause, Some clause))
  | ItemClause (inst_id, item_name, clause_id) -> (
      let inst_id, impl = ctx_normalize_trait_instance_id ctx inst_id in
      (* Check if the inst_id refers to a specific implementation, if yes project *)
      match impl with
      | None ->
          (* This is actually a local clause *)
          assert (trait_instance_id_is_local_clause inst_id);
          (ParentClause (inst_id, clause_id), None)
      | Some impl ->
          (* We figure out the item clause by doing the following:
             {[
               // The implementation we are looking at
               impl Impl1 : Trait1<R> {
                  type S = ...
                     with Impl2 : Trait2 ... // Instances satisfying the declared bounds
                          ^^^^^^^^^^^^^^^^^^
                      Lookup the clause from here
               }
             ]}
          *)
          (* The referenced instance should be an impl *)
          let impl_id =
            TypesUtils.trait_instance_id_as_trait_impl impl.trait_id
          in
          let trait_impl = C.ctx_lookup_trait_impl ctx.ctx impl_id in
          (* Lookup the clause *)
          let item = List.assoc item_name trait_impl.types in
          let clause = T.TraitClauseId.nth (fst item) clause_id in
          (* Sanity check: the clause necessarily refers to an impl *)
          let _ = TypesUtils.trait_instance_id_as_trait_impl clause.trait_id in
          (* We need to convert the clause type -
             TODO: we have too many problems with those conversions, we should
             merge the types. *)
          let clause = ctx.convert_etrait_ref clause in
          (TraitRef clause, Some clause))
  | TraitRef { T.trait_id = T.TraitImpl trait_id; generics; trait_decl_ref } ->
      (* We can't simplify the id *yet* : we will simplify it when projecting.
         However, we have an implementation to return *)
      (* Normalize the generics *)
      let generics = ctx_normalize_generic_args ctx generics in
      let trait_decl_ref = ctx_normalize_trait_decl_ref ctx trait_decl_ref in
      let trait_ref : 'r T.trait_ref =
        { T.trait_id = T.TraitImpl trait_id; generics; trait_decl_ref }
      in
      (TraitRef trait_ref, Some trait_ref)
  | TraitRef trait_ref ->
      (* The trait instance id necessarily refers to a local sub-clause. We
         can't project over it and can only peel off the [TraitRef] wrapper *)
      assert (trait_instance_id_is_local_clause trait_ref.trait_id);
      assert (trait_ref.generics = TypesUtils.mk_empty_generic_args);
      (trait_ref.trait_id, None)
  | UnknownTrait _ ->
      (* This is actually an error case *)
      (id, None)

and ctx_normalize_generic_args (ctx : 'r norm_ctx)
    (generics : 'r T.generic_args) : 'r T.generic_args =
  let { T.regions; types; const_generics; trait_refs } = generics in
  let types = List.map (ctx_normalize_ty ctx) types in
  let trait_refs = List.map (ctx_normalize_trait_ref ctx) trait_refs in
  { T.regions; types; const_generics; trait_refs }

and ctx_normalize_trait_ref (ctx : 'r norm_ctx) (trait_ref : 'r T.trait_ref) :
    'r T.trait_ref =
  let { T.trait_id; generics; trait_decl_ref } = trait_ref in
  let trait_id, _ = ctx_normalize_trait_instance_id ctx trait_id in
  let generics = ctx_normalize_generic_args ctx generics in
  let trait_decl_ref = ctx_normalize_trait_decl_ref ctx trait_decl_ref in
  { T.trait_id; generics; trait_decl_ref }

(* Not sure this one is really necessary *)
and ctx_normalize_trait_decl_ref (ctx : 'r norm_ctx)
    (trait_decl_ref : 'r T.trait_decl_ref) : 'r T.trait_decl_ref =
  let { T.trait_decl_id; decl_generics } = trait_decl_ref in
  let decl_generics = ctx_normalize_generic_args ctx decl_generics in
  { T.trait_decl_id; decl_generics }

let ctx_normalize_trait_type_constraint (ctx : 'r norm_ctx)
    (ttc : 'r T.trait_type_constraint) : 'r T.trait_type_constraint =
  let { T.trait_ref; generics; type_name; ty } = ttc in
  let trait_ref = ctx_normalize_trait_ref ctx trait_ref in
  let generics = ctx_normalize_generic_args ctx generics in
  let ty = ctx_normalize_ty ctx ty in
  { T.trait_ref; generics; type_name; ty }

let mk_rnorm_ctx (ctx : C.eval_ctx) : T.RegionId.id T.region norm_ctx =
  let get_ty_repr x = C.RTraitTypeRefMap.find_opt x ctx.norm_trait_rtypes in
  {
    ctx;
    get_ty_repr;
    convert_ety = TypesUtils.ety_no_regions_to_rty;
    convert_etrait_ref = TypesUtils.etrait_ref_no_regions_to_gr_trait_ref;
  }

let mk_enorm_ctx (ctx : C.eval_ctx) : T.erased_region norm_ctx =
  let get_ty_repr x = C.ETraitTypeRefMap.find_opt x ctx.norm_trait_etypes in
  {
    ctx;
    get_ty_repr;
    convert_ety = (fun x -> x);
    convert_etrait_ref = (fun x -> x);
  }

let ctx_normalize_rty (ctx : C.eval_ctx) (ty : T.rty) : T.rty =
  ctx_normalize_ty (mk_rnorm_ctx ctx) ty

let ctx_normalize_ety (ctx : C.eval_ctx) (ty : T.ety) : T.ety =
  ctx_normalize_ty (mk_enorm_ctx ctx) ty

let ctx_normalize_rtrait_type_constraint (ctx : C.eval_ctx)
    (ttc : T.rtrait_type_constraint) : T.rtrait_type_constraint =
  ctx_normalize_trait_type_constraint (mk_rnorm_ctx ctx) ttc

(** Same as [type_decl_get_instantiated_variants_fields_rtypes] but normalizes the types *)
let type_decl_get_inst_norm_variants_fields_rtypes (ctx : C.eval_ctx)
    (def : T.type_decl) (generics : T.rgeneric_args) :
    (T.VariantId.id option * T.rty list) list =
  let res =
    Subst.type_decl_get_instantiated_variants_fields_rtypes def generics
  in
  List.map
    (fun (variant_id, types) ->
      (variant_id, List.map (ctx_normalize_rty ctx) types))
    res

(** Same as [type_decl_get_instantiated_field_rtypes] but normalizes the types *)
let type_decl_get_inst_norm_field_rtypes (ctx : C.eval_ctx) (def : T.type_decl)
    (opt_variant_id : T.VariantId.id option) (generics : T.rgeneric_args) :
    T.rty list =
  let types =
    Subst.type_decl_get_instantiated_field_rtypes def opt_variant_id generics
  in
  List.map (ctx_normalize_rty ctx) types

(** Same as [ctx_adt_value_get_instantiated_field_rtypes] but normalizes the types *)
let ctx_adt_value_get_inst_norm_field_rtypes (ctx : C.eval_ctx)
    (adt : V.adt_value) (id : T.type_id) (generics : T.rgeneric_args) :
    T.rty list =
  let types =
    Subst.ctx_adt_value_get_instantiated_field_rtypes ctx adt id generics
  in
  List.map (ctx_normalize_rty ctx) types

(** Same as [ctx_adt_value_get_instantiated_field_etypes] but normalizes the types *)
let type_decl_get_inst_norm_field_etypes (ctx : C.eval_ctx) (def : T.type_decl)
    (opt_variant_id : T.VariantId.id option) (generics : T.egeneric_args) :
    T.ety list =
  let types =
    Subst.type_decl_get_instantiated_field_etypes def opt_variant_id generics
  in
  List.map (ctx_normalize_ety ctx) types

(** Same as [ctx_adt_get_instantiated_field_etypes] but normalizes the types *)
let ctx_adt_get_inst_norm_field_etypes (ctx : C.eval_ctx)
    (def_id : T.TypeDeclId.id) (opt_variant_id : T.VariantId.id option)
    (generics : T.egeneric_args) : T.ety list =
  let types =
    Subst.ctx_adt_get_instantiated_field_etypes ctx def_id opt_variant_id
      generics
  in
  List.map (ctx_normalize_ety ctx) types

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
  let { A.regions_hierarchy; inputs; output; trait_type_constraints } = sg in
  let inputs = List.map (ctx_normalize_rty ctx) inputs in
  let output = ctx_normalize_rty ctx output in
  let trait_type_constraints =
    List.map (ctx_normalize_rtrait_type_constraint ctx) trait_type_constraints
  in
  { regions_hierarchy; inputs; output; trait_type_constraints }
