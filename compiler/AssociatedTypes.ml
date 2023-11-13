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

let trait_type_ref_substitute (subst : Subst.subst) (r : C.trait_type_ref) :
    C.trait_type_ref =
  let { C.trait_ref; type_name } = r in
  let trait_ref = Subst.trait_ref_substitute subst trait_ref in
  { C.trait_ref; type_name }

module TyOrd = struct
  type t = T.ty

  let compare = T.compare_ty
  let to_string = T.show_ty
  let pp_t = T.pp_ty
  let show_t = T.show_ty
end

module TyMap = Collections.MakeMap (TyOrd)

let compute_norm_trait_types_from_preds
    (trait_type_constraints : T.trait_type_constraint list) :
    T.ty C.TraitTypeRefMap.t =
  (* Compute a union-find structure by recursively exploring the predicates and clauses *)
  let norm : T.ty UF.elem TyMap.t ref = ref TyMap.empty in
  let get_ref (ty : T.ty) : T.ty UF.elem =
    match TyMap.find_opt ty !norm with
    | Some r -> r
    | None ->
        let r = UF.make ty in
        norm := TyMap.add ty r !norm;
        r
  in
  let add_trait_type_constraint (c : T.trait_type_constraint) =
    (* Sanity check: the type constraint can't make use of regions - Remark
       that it would be enough to only visit the field [ty] of the trait type
       constraint, but for safety we visit all the fields *)
    assert (TU.trait_type_constraint_no_regions c);
    let trait_ty = T.TTraitType (c.trait_ref, c.generics, c.type_name) in
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
    List.map (fun (k, v) -> (k, UF.get v)) (TyMap.bindings !norm)
  in
  (* Filter the keys to keep only the trait type aliases *)
  let rbindings =
    List.filter_map
      (fun (k, v) ->
        match k with
        | T.TTraitType (trait_ref, generics, type_name) ->
            assert (generics = TypesUtils.mk_empty_generic_args);
            Some ({ C.trait_ref; type_name }, v)
        | _ -> None)
      rbindings
  in
  C.TraitTypeRefMap.of_list rbindings

let ctx_add_norm_trait_types_from_preds (ctx : C.eval_ctx)
    (trait_type_constraints : T.trait_type_constraint list) : C.eval_ctx =
  let norm_trait_types =
    compute_norm_trait_types_from_preds trait_type_constraints
  in
  { ctx with C.norm_trait_types }

(** A trait instance id refers to a local clause if it only uses the variants:
    [Self], [Clause], [ParentClause], [ItemClause] *)
let rec trait_instance_id_is_local_clause (id : T.trait_instance_id) : bool =
  match id with
  | T.Self | Clause _ -> true
  | TraitImpl _ | BuiltinOrAuto _ | TraitRef _ | UnknownTrait _ | FnPointer _ ->
      false
  | ParentClause (id, _, _) | ItemClause (id, _, _, _) ->
      trait_instance_id_is_local_clause id

(** About the conversion functions: for now we need them (TODO: merge ety, rty, etc.),
    but they should be applied to types without regions.
 *)
type norm_ctx = {
  norm_trait_types : T.ty C.TraitTypeRefMap.t;
  type_decls : T.type_decl T.TypeDeclId.Map.t;
  fun_decls : A.fun_decl A.FunDeclId.Map.t;
  global_decls : A.global_decl A.GlobalDeclId.Map.t;
  trait_decls : A.trait_decl A.TraitDeclId.Map.t;
  trait_impls : A.trait_impl A.TraitImplId.Map.t;
  type_vars : T.type_var list;
  const_generic_vars : T.const_generic_var list;
}

let norm_ctx_to_type_formatter (ctx : norm_ctx) : Print.Types.type_formatter =
  let open Print in
  let region_id_to_string r = PT.region_id_to_string r in

  let type_var_id_to_string vid =
    (* The context may be invalid *)
    match T.TypeVarId.nth_opt ctx.type_vars vid with
    | None -> T.TypeVarId.to_string vid
    | Some v -> v.name
  in
  let const_generic_var_id_to_string vid =
    match T.ConstGenericVarId.nth_opt ctx.const_generic_vars vid with
    | None -> T.ConstGenericVarId.to_string vid
    | Some v -> v.name
  in
  let type_decl_id_to_string def_id =
    let def = T.TypeDeclId.Map.find def_id ctx.type_decls in
    name_to_string def.name
  in
  let global_decl_id_to_string def_id =
    let def = A.GlobalDeclId.Map.find def_id ctx.global_decls in
    name_to_string def.name
  in
  let trait_decl_id_to_string def_id =
    let def = A.TraitDeclId.Map.find def_id ctx.trait_decls in
    name_to_string def.name
  in
  let trait_impl_id_to_string def_id =
    let def = A.TraitImplId.Map.find def_id ctx.trait_impls in
    name_to_string def.name
  in
  let trait_clause_id_to_string id = PT.trait_clause_id_to_pretty_string id in
  {
    region_id_to_string;
    type_var_id_to_string;
    type_decl_id_to_string;
    const_generic_var_id_to_string;
    global_decl_id_to_string;
    trait_decl_id_to_string;
    trait_impl_id_to_string;
    trait_clause_id_to_string;
  }

let norm_ctx_get_ty_repr (ctx : norm_ctx) (x : C.trait_type_ref) : T.ty option =
  C.TraitTypeRefMap.find_opt x ctx.norm_trait_types

let ty_to_string (ctx : norm_ctx) (ty : T.ty) : string =
  let ctx = norm_ctx_to_type_formatter ctx in
  Print.Types.ty_to_string ctx ty

let trait_ref_to_string (ctx : norm_ctx) (x : T.trait_ref) : string =
  let ctx = norm_ctx_to_type_formatter ctx in
  Print.Types.trait_ref_to_string ctx x

let trait_instance_id_to_string (ctx : norm_ctx) (x : T.trait_instance_id) :
    string =
  let ctx = norm_ctx_to_type_formatter ctx in
  Print.Types.trait_instance_id_to_string ctx x

let generic_args_to_string (ctx : norm_ctx) (x : T.generic_args) : string =
  let ctx = norm_ctx_to_type_formatter ctx in
  Print.Types.generic_args_to_string ctx x

let generic_params_to_string (ctx : norm_ctx) (x : T.generic_params) : string =
  let ctx = norm_ctx_to_type_formatter ctx in
  "<"
  ^ String.concat ", " (fst (Print.Types.generic_params_to_strings ctx x))
  ^ ">"

(** Small utility to lookup trait impls, together with a substitution. *)
let norm_ctx_lookup_trait_impl (ctx : norm_ctx) (impl_id : T.TraitImplId.id)
    (generics : T.generic_args) : A.trait_impl * Subst.subst =
  (* Lookup the implementation *)
  let trait_impl = A.TraitImplId.Map.find impl_id ctx.trait_impls in
  (* The substitution *)
  let tr_self = T.UnknownTrait __FUNCTION__ in
  let subst =
    Subst.make_subst_from_generics trait_impl.generics generics tr_self
  in
  (* Return *)
  (trait_impl, subst)

let norm_ctx_lookup_trait_impl_ty (ctx : norm_ctx) (impl_id : T.TraitImplId.id)
    (generics : T.generic_args) (type_name : string) : T.ty =
  (* Lookup the implementation *)
  let trait_impl, subst = norm_ctx_lookup_trait_impl ctx impl_id generics in
  (* Lookup the type *)
  let ty = snd (List.assoc type_name trait_impl.types) in
  (* Substitute *)
  Subst.ty_substitute subst ty

let norm_ctx_lookup_trait_impl_parent_clause (ctx : norm_ctx)
    (impl_id : T.TraitImplId.id) (generics : T.generic_args)
    (clause_id : T.TraitClauseId.id) : T.trait_ref =
  (* Lookup the implementation *)
  let trait_impl, subst = norm_ctx_lookup_trait_impl ctx impl_id generics in
  (* Lookup the clause *)
  let clause = T.TraitClauseId.nth trait_impl.parent_trait_refs clause_id in
  (* Sanity check: the clause necessarily refers to an impl *)
  let _ = TypesUtils.trait_instance_id_as_trait_impl clause.trait_id in
  (* Substitute *)
  Subst.trait_ref_substitute subst clause

let norm_ctx_lookup_trait_impl_item_clause (ctx : norm_ctx)
    (impl_id : T.TraitImplId.id) (generics : T.generic_args)
    (item_name : string) (clause_id : T.TraitClauseId.id) : T.trait_ref =
  (* Lookup the implementation *)
  let trait_impl, subst = norm_ctx_lookup_trait_impl ctx impl_id generics in
  (* Lookup the item then its clause *)
  let item = List.assoc item_name trait_impl.types in
  let clause = T.TraitClauseId.nth (fst item) clause_id in
  (* Sanity check: the clause necessarily refers to an impl *)
  let _ = TypesUtils.trait_instance_id_as_trait_impl clause.trait_id in
  (* Substitute *)
  Subst.trait_ref_substitute subst clause

(** Normalize a type by simplifying the references to trait associated types
    and choosing a representative when there are equalities between types
    enforced by local clauses (i.e., `where Trait1::T = Trait2::U`.

    See the comments for {!norm_ctx_normalize_trait_instance_id}.
  *)
let rec norm_ctx_normalize_ty (ctx : norm_ctx) (ty : T.ty) : T.ty =
  log#ldebug (lazy ("norm_ctx_normalize_ty: " ^ ty_to_string ctx ty));
  match ty with
  | T.TAdt (id, generics) ->
      TAdt (id, norm_ctx_normalize_generic_args ctx generics)
  | TVar _ | TLiteral _ | TNever -> ty
  | TRef (r, ty, rkind) ->
      let ty = norm_ctx_normalize_ty ctx ty in
      T.TRef (r, ty, rkind)
  | TRawPtr (ty, rkind) ->
      let ty = norm_ctx_normalize_ty ctx ty in
      TRawPtr (ty, rkind)
  | TArrow (inputs, output) ->
      let inputs = List.map (norm_ctx_normalize_ty ctx) inputs in
      let output = norm_ctx_normalize_ty ctx output in
      TArrow (inputs, output)
  | TTraitType (trait_ref, generics, type_name) -> (
      log#ldebug
        (lazy
          ("norm_ctx_normalize_ty:\n- trait type: " ^ ty_to_string ctx ty
         ^ "\n- trait_ref: "
          ^ trait_ref_to_string ctx trait_ref
          ^ "\n- raw trait ref:\n" ^ T.show_trait_ref trait_ref
          ^ "\n- generics:\n"
          ^ generic_args_to_string ctx generics));
      (* Normalize and attempt to project the type from the trait ref *)
      let trait_ref = norm_ctx_normalize_trait_ref ctx trait_ref in
      let generics = norm_ctx_normalize_generic_args ctx generics in
      (*  For now, we don't support higher order types *)
      assert (generics = TypesUtils.mk_empty_generic_args);
      let ty : T.ty =
        match trait_ref.trait_id with
        | T.TraitRef
            { T.trait_id = T.TraitImpl impl_id; generics = ref_generics; _ } ->
            assert (ref_generics = TypesUtils.mk_empty_generic_args);
            log#ldebug
              (lazy
                ("norm_ctx_normalize_ty: trait type: trait ref: "
               ^ ty_to_string ctx ty));
            (* Lookup the type *)
            let ty =
              norm_ctx_lookup_trait_impl_ty ctx impl_id trait_ref.generics
                type_name
            in
            (* Normalize *)
            norm_ctx_normalize_ty ctx ty
        | T.TraitImpl impl_id ->
            log#ldebug
              (lazy
                ("norm_ctx_normalize_ty (trait impl):\n- trait type: "
               ^ ty_to_string ctx ty ^ "\n- trait_ref: "
                ^ trait_ref_to_string ctx trait_ref
                ^ "\n- raw trait ref:\n" ^ T.show_trait_ref trait_ref));
            (* This happens. This doesn't come from the substitutions
               performed by Aeneas (the [TraitImpl] would be wrapped in a
               [TraitRef] but from non-normalized traits translated from
               the Rustc AST.
               TODO: factor out with the branch above.
            *)
            (* Lookup the type *)
            let ty =
              norm_ctx_lookup_trait_impl_ty ctx impl_id trait_ref.generics
                type_name
            in
            (* Normalize *)
            norm_ctx_normalize_ty ctx ty
        | _ ->
            log#ldebug
              (lazy
                ("norm_ctx_normalize_ty: trait type: not a trait ref: "
               ^ ty_to_string ctx ty ^ "\n- trait_ref: "
                ^ trait_ref_to_string ctx trait_ref
                ^ "\n- raw trait ref:\n" ^ T.show_trait_ref trait_ref));
            (* We can't project *)
            assert (trait_instance_id_is_local_clause trait_ref.trait_id);
            T.TTraitType (trait_ref, generics, type_name)
      in
      let tr : C.trait_type_ref = { C.trait_ref; type_name } in
      (* Lookup the representative, if there is *)
      match norm_ctx_get_ty_repr ctx tr with None -> ty | Some ty -> ty)

(** This returns the normalized trait instance id together with an optional
    reference to a trait **implementation** (the `trait_ref` we return has
    necessarily for instance id a [TraitImpl]).

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
      let x = f<Foo>[TraitImpl](...);
      (* The return type of the call to f is:
         T::S ~~> TraitImpl::S ~~> usize
       *)
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
and norm_ctx_normalize_trait_instance_id (ctx : norm_ctx)
    (id : T.trait_instance_id) : T.trait_instance_id * T.trait_ref option =
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
      let inst_id, impl = norm_ctx_normalize_trait_instance_id ctx inst_id in
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
          *)
          (* Lookup the clause *)
          let impl_id =
            TypesUtils.trait_instance_id_as_trait_impl impl.trait_id
          in
          let clause =
            norm_ctx_lookup_trait_impl_parent_clause ctx impl_id impl.generics
              clause_id
          in
          (* Normalize the clause *)
          let clause = norm_ctx_normalize_trait_ref ctx clause in
          (TraitRef clause, Some clause))
  | ItemClause (inst_id, decl_id, item_name, clause_id) -> (
      let inst_id, impl = norm_ctx_normalize_trait_instance_id ctx inst_id in
      (* Check if the inst_id refers to a specific implementation, if yes project *)
      match impl with
      | None ->
          (* This is actually a local clause *)
          assert (trait_instance_id_is_local_clause inst_id);
          (ItemClause (inst_id, decl_id, item_name, clause_id), None)
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
          (* Lookup the impl *)
          let impl_id =
            TypesUtils.trait_instance_id_as_trait_impl impl.trait_id
          in
          let clause =
            norm_ctx_lookup_trait_impl_item_clause ctx impl_id impl.generics
              item_name clause_id
          in
          (* Normalize the clause *)
          let clause = norm_ctx_normalize_trait_ref ctx clause in
          (TraitRef clause, Some clause))
  | TraitRef { T.trait_id = T.TraitImpl trait_id; generics; trait_decl_ref } ->
      (* We can't simplify the id *yet* : we will simplify it when projecting.
         However, we have an implementation to return *)
      (* Normalize the generics *)
      let generics = norm_ctx_normalize_generic_args ctx generics in
      let trait_decl_ref =
        norm_ctx_normalize_trait_decl_ref ctx trait_decl_ref
      in
      let trait_ref : T.trait_ref =
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
      let ty = norm_ctx_normalize_ty ctx ty in
      (* TODO: we might want to return the ref to the function pointer,
         in order to later normalize a call to this function pointer *)
      (FnPointer ty, None)
  | UnknownTrait _ ->
      (* This is actually an error case *)
      (id, None)

and norm_ctx_normalize_generic_args (ctx : norm_ctx) (generics : T.generic_args)
    : T.generic_args =
  let { T.regions; types; const_generics; trait_refs } = generics in
  let types = List.map (norm_ctx_normalize_ty ctx) types in
  let trait_refs = List.map (norm_ctx_normalize_trait_ref ctx) trait_refs in
  { T.regions; types; const_generics; trait_refs }

and norm_ctx_normalize_trait_ref (ctx : norm_ctx) (trait_ref : T.trait_ref) :
    T.trait_ref =
  log#ldebug
    (lazy
      ("norm_ctx_normalize_trait_ref: "
      ^ trait_ref_to_string ctx trait_ref
      ^ "\n- raw trait ref:\n" ^ T.show_trait_ref trait_ref));
  let { T.trait_id; generics; trait_decl_ref } = trait_ref in
  (* Check if the id is an impl, otherwise normalize it *)
  let trait_id, norm_trait_ref =
    norm_ctx_normalize_trait_instance_id ctx trait_id
  in
  match norm_trait_ref with
  | None ->
      log#ldebug
        (lazy
          ("norm_ctx_normalize_trait_ref: no norm: "
          ^ trait_instance_id_to_string ctx trait_id));
      let generics = norm_ctx_normalize_generic_args ctx generics in
      let trait_decl_ref =
        norm_ctx_normalize_trait_decl_ref ctx trait_decl_ref
      in
      { T.trait_id; generics; trait_decl_ref }
  | Some trait_ref ->
      log#ldebug
        (lazy
          ("norm_ctx_normalize_trait_ref: normalized to: "
          ^ trait_ref_to_string ctx trait_ref));
      assert (generics = TypesUtils.mk_empty_generic_args);
      trait_ref

(* Not sure this one is really necessary *)
and norm_ctx_normalize_trait_decl_ref (ctx : norm_ctx)
    (trait_decl_ref : T.trait_decl_ref) : T.trait_decl_ref =
  let { T.trait_decl_id; decl_generics } = trait_decl_ref in
  let decl_generics = norm_ctx_normalize_generic_args ctx decl_generics in
  { T.trait_decl_id; decl_generics }

let norm_ctx_normalize_trait_type_constraint (ctx : norm_ctx)
    (ttc : T.trait_type_constraint) : T.trait_type_constraint =
  let { T.trait_ref; generics; type_name; ty } = ttc in
  let trait_ref = norm_ctx_normalize_trait_ref ctx trait_ref in
  let generics = norm_ctx_normalize_generic_args ctx generics in
  let ty = norm_ctx_normalize_ty ctx ty in
  { T.trait_ref; generics; type_name; ty }

let mk_norm_ctx (ctx : C.eval_ctx) : norm_ctx =
  {
    norm_trait_types = ctx.norm_trait_types;
    type_decls = ctx.type_context.type_decls;
    fun_decls = ctx.fun_context.fun_decls;
    global_decls = ctx.global_context.global_decls;
    trait_decls = ctx.trait_decls_context.trait_decls;
    trait_impls = ctx.trait_impls_context.trait_impls;
    type_vars = ctx.type_vars;
    const_generic_vars = ctx.const_generic_vars;
  }

let ctx_normalize_ty (ctx : C.eval_ctx) (ty : T.ty) : T.ty =
  norm_ctx_normalize_ty (mk_norm_ctx ctx) ty

(** Normalize a type and erase the regions at the same time *)
let ctx_normalize_erase_ty (ctx : C.eval_ctx) (ty : T.ty) : T.ty =
  let ty = ctx_normalize_ty ctx ty in
  Subst.erase_regions ty

let ctx_normalize_trait_type_constraint (ctx : C.eval_ctx)
    (ttc : T.trait_type_constraint) : T.trait_type_constraint =
  norm_ctx_normalize_trait_type_constraint (mk_norm_ctx ctx) ttc

(** Same as [type_decl_get_instantiated_variants_fields_types] but normalizes the types *)
let type_decl_get_inst_norm_variants_fields_rtypes (ctx : C.eval_ctx)
    (def : T.type_decl) (generics : T.generic_args) :
    (T.VariantId.id option * T.ty list) list =
  let res =
    Subst.type_decl_get_instantiated_variants_fields_types def generics
  in
  List.map
    (fun (variant_id, types) ->
      (variant_id, List.map (ctx_normalize_ty ctx) types))
    res

(** Same as [type_decl_get_instantiated_field_types] but normalizes the types *)
let type_decl_get_inst_norm_field_rtypes (ctx : C.eval_ctx) (def : T.type_decl)
    (opt_variant_id : T.VariantId.id option) (generics : T.generic_args) :
    T.ty list =
  let types =
    Subst.type_decl_get_instantiated_field_types def opt_variant_id generics
  in
  List.map (ctx_normalize_ty ctx) types

(** Same as [ctx_adt_value_get_instantiated_field_rtypes] but normalizes the types *)
let ctx_adt_value_get_inst_norm_field_rtypes (ctx : C.eval_ctx)
    (adt : V.adt_value) (id : T.type_id) (generics : T.generic_args) : T.ty list
    =
  let types =
    Subst.ctx_adt_value_get_instantiated_field_types ctx adt id generics
  in
  List.map (ctx_normalize_ty ctx) types

(** Same as [ctx_adt_value_get_instantiated_field_types] but normalizes the types
    and erases the regions. *)
let type_decl_get_inst_norm_field_etypes (ctx : C.eval_ctx) (def : T.type_decl)
    (opt_variant_id : T.VariantId.id option) (generics : T.generic_args) :
    T.ty list =
  let types =
    Subst.type_decl_get_instantiated_field_types def opt_variant_id generics
  in
  let types = List.map (ctx_normalize_ty ctx) types in
  List.map Subst.erase_regions types

(** Same as [ctx_adt_get_instantiated_field_types] but normalizes the types and
    erases the regions. *)
let ctx_adt_get_inst_norm_field_etypes (ctx : C.eval_ctx)
    (def_id : T.TypeDeclId.id) (opt_variant_id : T.VariantId.id option)
    (generics : T.generic_args) : T.ty list =
  let types =
    Subst.ctx_adt_get_instantiated_field_types ctx def_id opt_variant_id
      generics
  in
  let types = List.map (ctx_normalize_ty ctx) types in
  List.map Subst.erase_regions types

(** Same as [substitute_signature] but normalizes the types *)
let ctx_subst_norm_signature (ctx : C.eval_ctx)
    (asubst : T.RegionGroupId.id -> V.AbstractionId.id)
    (r_subst : T.RegionId.id -> T.RegionId.id)
    (ty_subst : T.TypeVarId.id -> T.ty)
    (cg_subst : T.ConstGenericVarId.id -> T.const_generic)
    (tr_subst : T.TraitClauseId.id -> T.trait_instance_id)
    (tr_self : T.trait_instance_id) (sg : A.fun_sig)
    (regions_hierarchy : T.region_groups) : A.inst_fun_sig =
  let sg =
    Subst.substitute_signature asubst r_subst ty_subst cg_subst tr_subst tr_self
      sg regions_hierarchy
  in
  let { A.regions_hierarchy; inputs; output; trait_type_constraints } = sg in
  let inputs = List.map (ctx_normalize_ty ctx) inputs in
  let output = ctx_normalize_ty ctx output in
  let trait_type_constraints =
    List.map (ctx_normalize_trait_type_constraint ctx) trait_type_constraints
  in
  { regions_hierarchy; inputs; output; trait_type_constraints }
