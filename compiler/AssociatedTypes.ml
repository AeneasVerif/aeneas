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
module PA = Print.EvalCtxLlbcAst

(** The local logger *)
let log = L.associated_types_log

let trait_type_ref_substitute (subst : ('r, 'r1) Subst.subst)
    (r : 'r C.trait_type_ref) : 'r1 C.trait_type_ref =
  let { C.trait_ref; type_name } = r in
  let trait_ref = Subst.trait_ref_substitute subst trait_ref in
  { C.trait_ref; type_name }

(* TODO: how not to duplicate below? *)
module RTyOrd = struct
  type t = T.rty

  let compare = T.compare_rty
  let to_string = T.show_rty
  let pp_t = T.pp_rty
  let show_t = T.show_rty
end

module STyOrd = struct
  type t = T.sty

  let compare = T.compare_sty
  let to_string = T.show_sty
  let pp_t = T.pp_sty
  let show_t = T.show_sty
end

module RTyMap = Collections.MakeMap (RTyOrd)
module STyMap = Collections.MakeMap (STyOrd)

(* TODO: is it possible not to have this? *)
module type TypeWrapper = sig
  type t
end

(* TODO: don't manage to get the syntax right so using a functor *)
module MakeNormalizer
    (R : TypeWrapper)
    (RTyMap : Collections.Map with type key = R.t T.region T.ty)
    (M : Collections.Map with type key = R.t T.region C.trait_type_ref) =
struct
  let compute_norm_trait_types_from_preds
      (trait_type_constraints : R.t T.region T.trait_type_constraint list) :
      R.t T.region T.ty M.t =
    (* Compute a union-find structure by recursively exploring the predicates and clauses *)
    let norm : R.t T.region T.ty UF.elem RTyMap.t ref = ref RTyMap.empty in
    let get_ref (ty : R.t T.region T.ty) : R.t T.region T.ty UF.elem =
      match RTyMap.find_opt ty !norm with
      | Some r -> r
      | None ->
          let r = UF.make ty in
          norm := RTyMap.add ty r !norm;
          r
    in
    let add_trait_type_constraint (c : R.t T.region T.trait_type_constraint) =
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
    M.of_list rbindings
end

(** Compute the representative classes of trait associated types, for normalization *)
let compute_norm_trait_stypes_from_preds
    (trait_type_constraints : T.strait_type_constraint list) :
    T.sty C.STraitTypeRefMap.t =
  (* Compute the normalization map for the types with regions *)
  let module R = struct
    type t = T.region_var_id
  end in
  let module M = C.STraitTypeRefMap in
  let module Norm = MakeNormalizer (R) (STyMap) (M) in
  Norm.compute_norm_trait_types_from_preds trait_type_constraints

(** Compute the representative classes of trait associated types, for normalization *)
let compute_norm_trait_types_from_preds
    (trait_type_constraints : T.rtrait_type_constraint list) :
    T.ety C.ETraitTypeRefMap.t * T.rty C.RTraitTypeRefMap.t =
  (* Compute the normalization map for the types with regions *)
  let module R = struct
    type t = T.region_id
  end in
  let module M = C.RTraitTypeRefMap in
  let module Norm = MakeNormalizer (R) (RTyMap) (M) in
  let rbindings =
    Norm.compute_norm_trait_types_from_preds trait_type_constraints
  in
  (* Compute the normalization map for the types with erased regions *)
  let ebindings =
    List.map
      (fun (k, v) ->
        ( trait_type_ref_substitute Subst.erase_regions_subst k,
          Subst.erase_regions v ))
      (M.bindings rbindings)
  in
  (C.ETraitTypeRefMap.of_list ebindings, rbindings)

let ctx_add_norm_trait_stypes_from_preds (ctx : C.eval_ctx)
    (trait_type_constraints : T.strait_type_constraint list) : C.eval_ctx =
  let norm_trait_stypes =
    compute_norm_trait_stypes_from_preds trait_type_constraints
  in
  { ctx with C.norm_trait_stypes }

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
  | TraitImpl _ | BuiltinOrAuto _ | TraitRef _ | UnknownTrait _ | FnPointer _ ->
      false
  | ParentClause (id, _, _) | ItemClause (id, _, _, _) ->
      trait_instance_id_is_local_clause id

(** About the conversion functions: for now we need them (TODO: merge ety, rty, etc.),
    but they should be applied to types without regions.
 *)
type 'r norm_ctx = {
  ctx : C.eval_ctx;
  get_ty_repr : 'r C.trait_type_ref -> 'r T.ty option;
  convert_ety : T.ety -> 'r T.ty;
  convert_etrait_ref : T.etrait_ref -> 'r T.trait_ref;
  ty_to_string : 'r T.ty -> string;
  trait_ref_to_string : 'r T.trait_ref -> string;
  trait_instance_id_to_string : 'r T.trait_instance_id -> string;
  pp_r : Format.formatter -> 'r -> unit;
}

(** Normalize a type by simplyfying the references to trait associated types
    and choosing a representative when there are equalities between types
    enforced by local clauses (i.e., `where Trait1::T = Trait2::U`. *)
let rec ctx_normalize_ty : 'r. 'r norm_ctx -> 'r T.ty -> 'r T.ty =
 fun ctx ty ->
  log#ldebug (lazy ("ctx_normalize_ty: " ^ ctx.ty_to_string ty));
  match ty with
  | T.Adt (id, generics) -> Adt (id, ctx_normalize_generic_args ctx generics)
  | TypeVar _ | Literal _ | Never -> ty
  | Ref (r, ty, rkind) ->
      let ty = ctx_normalize_ty ctx ty in
      T.Ref (r, ty, rkind)
  | Arrow (inputs, output) ->
      let inputs = List.map (ctx_normalize_ty ctx) inputs in
      let output = ctx_normalize_ty ctx output in
      Arrow (inputs, output)
  | TraitType (trait_ref, generics, type_name) -> (
      log#ldebug
        (lazy
          ("ctx_normalize_ty: trait type: " ^ ctx.ty_to_string ty
         ^ "\n- trait_ref: "
          ^ ctx.trait_ref_to_string trait_ref
          ^ "\n- raw trait ref:\n"
          ^ T.show_trait_ref ctx.pp_r trait_ref));
      (* Normalize and attempt to project the type from the trait ref *)
      let trait_ref = ctx_normalize_trait_ref ctx trait_ref in
      let generics = ctx_normalize_generic_args ctx generics in
      let ty : 'r T.ty =
        match trait_ref.trait_id with
        | T.TraitRef
            { T.trait_id = T.TraitImpl impl_id; generics = ref_generics; _ } ->
            assert (ref_generics = TypesUtils.mk_empty_generic_args);
            log#ldebug
              (lazy
                ("ctx_normalize_ty: trait type: trait ref: "
               ^ ctx.ty_to_string ty));
            (* Lookup the implementation *)
            let trait_impl = C.ctx_lookup_trait_impl ctx.ctx impl_id in
            (* Lookup the type *)
            let ty = snd (List.assoc type_name trait_impl.types) in
            (* Annoying: convert etype to an stype - TODO: hwo to avoid that? *)
            let ty : T.sty = TypesUtils.ety_no_regions_to_gr_ty ty in
            (* Substitute *)
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
        | T.TraitImpl impl_id ->
            (* This happens. This doesn't come from the substituations
               performed by Aeneas (the [TraitImpl] would be wrapped in a
               [TraitRef] but from non-normalized traits translated from
               the Rustc AST.
               TODO: factor out with the branch above.
            *)
            (* Lookup the implementation *)
            let trait_impl = C.ctx_lookup_trait_impl ctx.ctx impl_id in
            (* Lookup the type *)
            let ty = snd (List.assoc type_name trait_impl.types) in
            (* Annoying: convert etype to an stype - TODO: hwo to avoid that? *)
            let ty : T.sty = TypesUtils.ety_no_regions_to_gr_ty ty in
            (* Substitute *)
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
            log#ldebug
              (lazy
                ("ctx_normalize_ty: trait type: not a trait ref: "
               ^ ctx.ty_to_string ty ^ "\n- trait_ref: "
                ^ ctx.trait_ref_to_string trait_ref
                ^ "\n- raw trait ref:\n"
                ^ T.show_trait_ref ctx.pp_r trait_ref));
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
  | ParentClause (inst_id, decl_id, clause_id) -> (
      let inst_id, impl = ctx_normalize_trait_instance_id ctx inst_id in
      (* Check if the inst_id refers to a specific implementation, if yes project *)
      match impl with
      | None ->
          (* This is actually a local clause *)
          assert (trait_instance_id_is_local_clause inst_id);
          (ParentClause (inst_id, decl_id, clause_id), None)
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
  | ItemClause (inst_id, decl_id, item_name, clause_id) -> (
      let inst_id, impl = ctx_normalize_trait_instance_id ctx inst_id in
      (* Check if the inst_id refers to a specific implementation, if yes project *)
      match impl with
      | None ->
          (* This is actually a local clause *)
          assert (trait_instance_id_is_local_clause inst_id);
          (ParentClause (inst_id, decl_id, clause_id), None)
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
  | FnPointer ty ->
      let ty = ctx_normalize_ty ctx ty in
      (* TODO: we might want to return the ref to the function pointer,
         in order to later normalize a call to this function pointer *)
      (FnPointer ty, None)
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
  log#ldebug
    (lazy
      ("ctx_normalize_trait_ref: "
      ^ ctx.trait_ref_to_string trait_ref
      ^ "\n- raw trait ref:\n"
      ^ T.show_trait_ref ctx.pp_r trait_ref));
  let { T.trait_id; generics; trait_decl_ref } = trait_ref in
  (* Check if the id is an impl, otherwise normalize it *)
  let trait_id, norm_trait_ref = ctx_normalize_trait_instance_id ctx trait_id in
  match norm_trait_ref with
  | None ->
      log#ldebug
        (lazy
          ("ctx_normalize_trait_ref: no norm: "
          ^ ctx.trait_instance_id_to_string trait_id));
      let generics = ctx_normalize_generic_args ctx generics in
      let trait_decl_ref = ctx_normalize_trait_decl_ref ctx trait_decl_ref in
      { T.trait_id; generics; trait_decl_ref }
  | Some trait_ref ->
      log#ldebug
        (lazy
          ("ctx_normalize_trait_ref: normalized to: "
          ^ ctx.trait_ref_to_string trait_ref));
      assert (generics = TypesUtils.mk_empty_generic_args);
      trait_ref

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

let mk_snorm_ctx (ctx : C.eval_ctx) : T.RegionVarId.id T.region norm_ctx =
  let get_ty_repr x = C.STraitTypeRefMap.find_opt x ctx.norm_trait_stypes in
  {
    ctx;
    get_ty_repr;
    convert_ety = TypesUtils.ety_no_regions_to_sty;
    convert_etrait_ref = TypesUtils.etrait_ref_no_regions_to_gr_trait_ref;
    ty_to_string = PA.sty_to_string ctx;
    trait_ref_to_string = PA.strait_ref_to_string ctx;
    trait_instance_id_to_string = PA.strait_instance_id_to_string ctx;
    pp_r = T.pp_region T.pp_region_var_id;
  }

let mk_rnorm_ctx (ctx : C.eval_ctx) : T.RegionId.id T.region norm_ctx =
  let get_ty_repr x = C.RTraitTypeRefMap.find_opt x ctx.norm_trait_rtypes in
  {
    ctx;
    get_ty_repr;
    convert_ety = TypesUtils.ety_no_regions_to_rty;
    convert_etrait_ref = TypesUtils.etrait_ref_no_regions_to_gr_trait_ref;
    ty_to_string = PA.rty_to_string ctx;
    trait_ref_to_string = PA.rtrait_ref_to_string ctx;
    trait_instance_id_to_string = PA.rtrait_instance_id_to_string ctx;
    pp_r = T.pp_region T.pp_region_id;
  }

let mk_enorm_ctx (ctx : C.eval_ctx) : T.erased_region norm_ctx =
  let get_ty_repr x = C.ETraitTypeRefMap.find_opt x ctx.norm_trait_etypes in
  {
    ctx;
    get_ty_repr;
    convert_ety = (fun x -> x);
    convert_etrait_ref = (fun x -> x);
    ty_to_string = PA.ety_to_string ctx;
    trait_ref_to_string = PA.etrait_ref_to_string ctx;
    trait_instance_id_to_string = PA.etrait_instance_id_to_string ctx;
    pp_r = T.pp_erased_region;
  }

let ctx_normalize_sty (ctx : C.eval_ctx) (ty : T.sty) : T.sty =
  ctx_normalize_ty (mk_snorm_ctx ctx) ty

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
