(** This file implements utilities to handle trait associated types, in
    particular with normalization helpers.

    When normalizing a type, we simplify the references to the trait associated
    types, and choose a representative when there are equalities between types
    enforced by local clauses (i.e., clauses of the shape [where Trait1::T = Trait2::U]).
 *)

open Types
open TypesUtils
open Values
open LlbcAst
open Contexts
open Errors
module Subst = Substitute

(** The local logger *)
let log = Logging.associated_types_log

let trait_type_ref_substitute (subst : Subst.subst) (r : trait_type_ref) :
    trait_type_ref =
  let { trait_ref; type_name } = r in
  let trait_ref = Subst.trait_ref_substitute subst trait_ref in
  { trait_ref; type_name }

module TyOrd = struct
  type t = ty

  let compare = compare_ty
  let to_string = show_ty
  let pp_t = pp_ty
  let show_t = show_ty
end

module TyMap = Collections.MakeMap (TyOrd)

let compute_norm_trait_types_from_preds (meta : Meta.meta option)
    (trait_type_constraints : trait_type_constraint list) : ty TraitTypeRefMap.t
    =
  (* Compute a union-find structure by recursively exploring the predicates and clauses *)
  let norm : ty UnionFind.elem TyMap.t ref = ref TyMap.empty in
  let get_ref (ty : ty) : ty UnionFind.elem =
    match TyMap.find_opt ty !norm with
    | Some r -> r
    | None ->
        let r = UnionFind.make ty in
        norm := TyMap.add ty r !norm;
        r
  in
  let add_trait_type_constraint (c : trait_type_constraint) =
    (* Sanity check: the type constraint can't make use of regions - Remark
       that it would be enough to only visit the field [ty] of the trait type
       constraint, but for safety we visit all the fields *)
    cassert_opt_meta (trait_type_constraint_no_regions c) meta "TODO: error message";
    let { trait_ref; type_name; ty } : trait_type_constraint = c in
    let trait_ty = TTraitType (trait_ref, type_name) in
    let trait_ty_ref = get_ref trait_ty in
    let ty_ref = get_ref ty in
    let new_repr = UnionFind.get ty_ref in
    let merged = UnionFind.union trait_ty_ref ty_ref in
    (* Not sure the set operation is necessary, but I want to control which
       representative is chosen *)
    UnionFind.set merged new_repr
  in
  (* Explore the local predicates *)
  List.iter add_trait_type_constraint trait_type_constraints;
  (* TODO: explore the local clauses *)
  (* Compute the norm maps *)
  let rbindings =
    List.map (fun (k, v) -> (k, UnionFind.get v)) (TyMap.bindings !norm)
  in
  (* Filter the keys to keep only the trait type aliases *)
  let rbindings =
    List.filter_map
      (fun (k, v) ->
        match k with
        | TTraitType (trait_ref, type_name) -> Some ({ trait_ref; type_name }, v)
        | _ -> None)
      rbindings
  in
  TraitTypeRefMap.of_list rbindings

let ctx_add_norm_trait_types_from_preds (meta : Meta.meta) (ctx : eval_ctx)
    (trait_type_constraints : trait_type_constraint list) : eval_ctx =
  let norm_trait_types =
    compute_norm_trait_types_from_preds (Some meta) trait_type_constraints 
  in
  { ctx with norm_trait_types }

(** A trait instance id refers to a local clause if it only uses the variants:
    [Self], [Clause], [ParentClause], [ItemClause] *)
let rec trait_instance_id_is_local_clause (id : trait_instance_id) : bool =
  match id with
  | Self | Clause _ -> true
  | TraitImpl _ | BuiltinOrAuto _ | TraitRef _ | UnknownTrait _ | FnPointer _
  | Closure _ ->
      false
  | ParentClause (id, _, _) | ItemClause (id, _, _, _) ->
      trait_instance_id_is_local_clause id

(** About the conversion functions: for now we need them (TODO: merge ety, rty, etc.),
    but they should be applied to types without regions.
 *)
type norm_ctx = {
  meta : Meta.meta option;
  norm_trait_types : ty TraitTypeRefMap.t;
  type_decls : type_decl TypeDeclId.Map.t;
  fun_decls : fun_decl FunDeclId.Map.t;
  global_decls : global_decl GlobalDeclId.Map.t;
  trait_decls : trait_decl TraitDeclId.Map.t;
  trait_impls : trait_impl TraitImplId.Map.t;
  type_vars : type_var list;
  const_generic_vars : const_generic_var list;
}

let norm_ctx_to_fmt_env (ctx : norm_ctx) : Print.fmt_env =
  {
    type_decls = ctx.type_decls;
    fun_decls = ctx.fun_decls;
    global_decls = ctx.global_decls;
    trait_decls = ctx.trait_decls;
    trait_impls = ctx.trait_impls;
    types = ctx.type_vars;
    const_generics = ctx.const_generic_vars;
    regions = [];
    trait_clauses = [];
    preds = empty_predicates;
    locals = [];
  }

let norm_ctx_get_ty_repr (ctx : norm_ctx) (x : trait_type_ref) : ty option =
  TraitTypeRefMap.find_opt x ctx.norm_trait_types

let ty_to_string (ctx : norm_ctx) (ty : ty) : string =
  let ctx = norm_ctx_to_fmt_env ctx in
  Print.Types.ty_to_string ctx ty

let trait_ref_to_string (ctx : norm_ctx) (x : trait_ref) : string =
  let ctx = norm_ctx_to_fmt_env ctx in
  Print.Types.trait_ref_to_string ctx x

let trait_instance_id_to_string (ctx : norm_ctx) (x : trait_instance_id) :
    string =
  let ctx = norm_ctx_to_fmt_env ctx in
  Print.Types.trait_instance_id_to_string ctx x

let generic_args_to_string (ctx : norm_ctx) (x : generic_args) : string =
  let ctx = norm_ctx_to_fmt_env ctx in
  Print.Types.generic_args_to_string ctx x

let generic_params_to_string (ctx : norm_ctx) (x : generic_params) : string =
  let ctx = norm_ctx_to_fmt_env ctx in
  "<"
  ^ String.concat ", " (fst (Print.Types.generic_params_to_strings ctx x))
  ^ ">"

(** Small utility to lookup trait impls, together with a substitution. *)
let norm_ctx_lookup_trait_impl (ctx : norm_ctx) (impl_id : TraitImplId.id)
    (generics : generic_args) : trait_impl * Subst.subst =
  (* Lookup the implementation *)
  let trait_impl = TraitImplId.Map.find impl_id ctx.trait_impls in
  (* The substitution *)
  let tr_self = UnknownTrait __FUNCTION__ in
  let subst =
    Subst.make_subst_from_generics trait_impl.generics generics tr_self
  in
  (* Return *)
  (trait_impl, subst)

let norm_ctx_lookup_trait_impl_ty (ctx : norm_ctx) (impl_id : TraitImplId.id)
    (generics : generic_args) (type_name : string) : ty =
  (* Lookup the implementation *)
  let trait_impl, subst = norm_ctx_lookup_trait_impl ctx impl_id generics in
  (* Lookup the type *)
  let ty = snd (List.assoc type_name trait_impl.types) in
  (* Substitute *)
  Subst.ty_substitute subst ty

let norm_ctx_lookup_trait_impl_parent_clause (ctx : norm_ctx)
    (impl_id : TraitImplId.id) (generics : generic_args)
    (clause_id : TraitClauseId.id) : trait_ref =
  (* Lookup the implementation *)
  let trait_impl, subst = norm_ctx_lookup_trait_impl ctx impl_id generics in
  (* Lookup the clause *)
  let clause = TraitClauseId.nth trait_impl.parent_trait_refs clause_id in
  (* Sanity check: the clause necessarily refers to an impl *)
  let _ = TypesUtils.trait_instance_id_as_trait_impl clause.trait_id in
  (* Substitute *)
  Subst.trait_ref_substitute subst clause

let norm_ctx_lookup_trait_impl_item_clause (ctx : norm_ctx)
    (impl_id : TraitImplId.id) (generics : generic_args) (item_name : string)
    (clause_id : TraitClauseId.id) : trait_ref =
  (* Lookup the implementation *)
  let trait_impl, subst = norm_ctx_lookup_trait_impl ctx impl_id generics in
  (* Lookup the item then its clause *)
  let item = List.assoc item_name trait_impl.types in
  let clause = TraitClauseId.nth (fst item) clause_id in
  (* Sanity check: the clause necessarily refers to an impl *)
  let _ = TypesUtils.trait_instance_id_as_trait_impl clause.trait_id in
  (* Substitute *)
  Subst.trait_ref_substitute subst clause

(** Normalize a type by simplifying the references to trait associated types
    and choosing a representative when there are equalities between types
    enforced by local clauses (i.e., `where Trait1::T = Trait2::U`.

    See the comments for {!norm_ctx_normalize_trait_instance_id}.
  *)
let rec norm_ctx_normalize_ty (ctx : norm_ctx) (ty : ty) : ty =
  log#ldebug (lazy ("norm_ctx_normalize_ty: " ^ ty_to_string ctx ty));
  match ty with
  | TAdt (id, generics) ->
      TAdt (id, norm_ctx_normalize_generic_args ctx generics)
  | TVar _ | TLiteral _ | TNever -> ty
  | TRef (r, ty, rkind) ->
      let ty = norm_ctx_normalize_ty ctx ty in
      TRef (r, ty, rkind)
  | TRawPtr (ty, rkind) ->
      let ty = norm_ctx_normalize_ty ctx ty in
      TRawPtr (ty, rkind)
  | TArrow (regions, inputs, output) ->
      (* TODO: for now it works because we don't support predicates with
         bound regions. If we do support them, we probably need to do
         something smarter here. *)
      let inputs = List.map (norm_ctx_normalize_ty ctx) inputs in
      let output = norm_ctx_normalize_ty ctx output in
      TArrow (regions, inputs, output)
  | TTraitType (trait_ref, type_name) -> (
      log#ldebug
        (lazy
          ("norm_ctx_normalize_ty:\n- trait type: " ^ ty_to_string ctx ty
         ^ "\n- trait_ref: "
          ^ trait_ref_to_string ctx trait_ref
          ^ "\n- raw trait ref:\n" ^ show_trait_ref trait_ref));
      (* Normalize and attempt to project the type from the trait ref *)
      let trait_ref = norm_ctx_normalize_trait_ref ctx trait_ref in
      let ty : ty =
        match trait_ref.trait_id with
        | TraitRef { trait_id = TraitImpl impl_id; generics = ref_generics; _ }
          ->
            cassert_opt_meta (ref_generics = empty_generic_args) ctx.meta "Higher order types are not supported yet TODO: error message";
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
        | TraitImpl impl_id ->
            log#ldebug
              (lazy
                ("norm_ctx_normalize_ty (trait impl):\n- trait type: "
               ^ ty_to_string ctx ty ^ "\n- trait_ref: "
                ^ trait_ref_to_string ctx trait_ref
                ^ "\n- raw trait ref:\n" ^ show_trait_ref trait_ref));
            (* This happens. This doesn't come from the substitutions
               performed by Aeneas (the [TraitImpl] would be wrapped in a
               [TraitRef] but from non-normalized traits translated from
               the Rustc AS
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
                ^ "\n- raw trait ref:\n" ^ show_trait_ref trait_ref));
            (* We can't project *)
            cassert_opt_meta (trait_instance_id_is_local_clause trait_ref.trait_id) ctx.meta "TODO: error message";
            TTraitType (trait_ref, type_name)
      in
      let tr : trait_type_ref = { trait_ref; type_name } in
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
    (id : trait_instance_id) : trait_instance_id * trait_ref option =
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
          cassert_opt_meta (trait_instance_id_is_local_clause inst_id) ctx.meta "TODO: error message";
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
          cassert_opt_meta (trait_instance_id_is_local_clause inst_id) ctx.meta "Trait instance id is not a local clause";
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
  | TraitRef { trait_id = TraitImpl trait_id; generics; trait_decl_ref } ->
      (* We can't simplify the id *yet* : we will simplify it when projecting.
         However, we have an implementation to return *)
      (* Normalize the generics *)
      let generics = norm_ctx_normalize_generic_args ctx generics in
      let trait_decl_ref =
        norm_ctx_normalize_trait_decl_ref ctx trait_decl_ref
      in
      let trait_ref : trait_ref =
        { trait_id = TraitImpl trait_id; generics; trait_decl_ref }
      in
      (TraitRef trait_ref, Some trait_ref)
  | TraitRef trait_ref ->
      (* The trait instance id necessarily refers to a local sub-clause. We
         can't project over it and can only peel off the [TraitRef] wrapper *)
(*       let meta = (TraitDeclId.Map.find trait_ref.trait_decl_ref.trait_decl_id ctx.trait_decls).meta in *)
      cassert_opt_meta (trait_instance_id_is_local_clause trait_ref.trait_id) ctx.meta "Trait instance id is not a local sub-clause";
      cassert_opt_meta (trait_ref.generics = empty_generic_args) ctx.meta "TODO: error message";
      (trait_ref.trait_id, None)
  | FnPointer ty ->
      let ty = norm_ctx_normalize_ty ctx ty in
      (* TODO: we might want to return the ref to the function pointer,
         in order to later normalize a call to this function pointer *)
      (FnPointer ty, None)
  | Closure (fid, generics) ->
      let generics = norm_ctx_normalize_generic_args ctx generics in
      (Closure (fid, generics), None)
  | UnknownTrait _ ->
      (* This is actually an error case *)
      (id, None)

and norm_ctx_normalize_generic_args (ctx : norm_ctx) (generics : generic_args) :
    generic_args =
  let { regions; types; const_generics; trait_refs } = generics in
  let types = List.map (norm_ctx_normalize_ty ctx) types in
  let trait_refs = List.map (norm_ctx_normalize_trait_ref ctx) trait_refs in
  { regions; types; const_generics; trait_refs }

and norm_ctx_normalize_trait_ref (ctx : norm_ctx) (trait_ref : trait_ref) :
    trait_ref =
  log#ldebug
    (lazy
      ("norm_ctx_normalize_trait_ref: "
      ^ trait_ref_to_string ctx trait_ref
      ^ "\n- raw trait ref:\n" ^ show_trait_ref trait_ref));
  let { trait_id; generics; trait_decl_ref } = trait_ref in
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
      { trait_id; generics; trait_decl_ref }
  | Some trait_ref ->
      log#ldebug
        (lazy
          ("norm_ctx_normalize_trait_ref: normalized to: "
          ^ trait_ref_to_string ctx trait_ref));
      cassert_opt_meta (generics = empty_generic_args) ctx.meta "TODO: error message";
      trait_ref

(* Not sure this one is really necessary *)
and norm_ctx_normalize_trait_decl_ref (ctx : norm_ctx)
    (trait_decl_ref : trait_decl_ref) : trait_decl_ref =
  let { trait_decl_id; decl_generics } = trait_decl_ref in
  let decl_generics = norm_ctx_normalize_generic_args ctx decl_generics in
  { trait_decl_id; decl_generics }

let norm_ctx_normalize_trait_type_constraint (ctx : norm_ctx)
    (ttc : trait_type_constraint) : trait_type_constraint =
  let { trait_ref; type_name; ty } : trait_type_constraint = ttc in
  let trait_ref = norm_ctx_normalize_trait_ref ctx trait_ref in
  let ty = norm_ctx_normalize_ty ctx ty in
  { trait_ref; type_name; ty }

let mk_norm_ctx (meta : Meta.meta) (ctx : eval_ctx) : norm_ctx =
  {
    meta = Some meta;
    norm_trait_types = ctx.norm_trait_types;
    type_decls = ctx.type_ctx.type_decls;
    fun_decls = ctx.fun_ctx.fun_decls;
    global_decls = ctx.global_ctx.global_decls;
    trait_decls = ctx.trait_decls_ctx.trait_decls;
    trait_impls = ctx.trait_impls_ctx.trait_impls;
    type_vars = ctx.type_vars;
    const_generic_vars = ctx.const_generic_vars;
  }

let ctx_normalize_ty (meta : Meta.meta) (ctx : eval_ctx) (ty : ty) : ty =
  norm_ctx_normalize_ty (mk_norm_ctx meta ctx) ty

(** Normalize a type and erase the regions at the same time *)
let ctx_normalize_erase_ty (meta : Meta.meta) (ctx : eval_ctx) (ty : ty) : ty =
  let ty = ctx_normalize_ty meta ctx ty in
  Subst.erase_regions ty

let ctx_normalize_trait_type_constraint (meta : Meta.meta) (ctx : eval_ctx)
    (ttc : trait_type_constraint) : trait_type_constraint =
  norm_ctx_normalize_trait_type_constraint (mk_norm_ctx meta ctx) ttc

(** Same as [type_decl_get_instantiated_variants_fields_types] but normalizes the types *)
let type_decl_get_inst_norm_variants_fields_rtypes (ctx : eval_ctx)
    (def : type_decl) (generics : generic_args) :
    (VariantId.id option * ty list) list =
  let res =
    Subst.type_decl_get_instantiated_variants_fields_types def generics
  in
  List.map
    (fun (variant_id, types) ->
      (variant_id, List.map (ctx_normalize_ty def.meta ctx) types))
    res

(** Same as [type_decl_get_instantiated_field_types] but normalizes the types *)
let type_decl_get_inst_norm_field_rtypes (ctx : eval_ctx) (def : type_decl)
    (opt_variant_id : VariantId.id option) (generics : generic_args) : ty list =
  let types =
    Subst.type_decl_get_instantiated_field_types def opt_variant_id generics
  in
  List.map (ctx_normalize_ty def.meta ctx) types

(** Same as [ctx_adt_value_get_instantiated_field_rtypes] but normalizes the types *)
let ctx_adt_value_get_inst_norm_field_rtypes (meta : Meta.meta) (ctx : eval_ctx) (adt : adt_value)
    (id : type_id) (generics : generic_args) : ty list =
  let types =
    Subst.ctx_adt_value_get_instantiated_field_types meta ctx adt id generics
  in
  List.map (ctx_normalize_ty meta ctx) types

(** Same as [ctx_adt_value_get_instantiated_field_types] but normalizes the types
    and erases the regions. *)
let type_decl_get_inst_norm_field_etypes (ctx : eval_ctx) (def : type_decl)
    (opt_variant_id : VariantId.id option) (generics : generic_args) : ty list =
  let types =
    Subst.type_decl_get_instantiated_field_types def opt_variant_id generics
  in
  let types = List.map (ctx_normalize_ty def.meta ctx) types in
  List.map Subst.erase_regions types

(** Same as [ctx_adt_get_instantiated_field_types] but normalizes the types and
    erases the regions. *)
let ctx_adt_get_inst_norm_field_etypes (meta : Meta.meta) (ctx : eval_ctx) (def_id : TypeDeclId.id)
    (opt_variant_id : VariantId.id option) (generics : generic_args) : ty list =
  let types =
    Subst.ctx_adt_get_instantiated_field_types ctx def_id opt_variant_id
      generics
  in
  let types = List.map (ctx_normalize_ty meta ctx) types in
  List.map Subst.erase_regions types

(** Same as [substitute_signature] but normalizes the types *)
let ctx_subst_norm_signature (meta : Meta.meta) (ctx : eval_ctx)
    (asubst : RegionGroupId.id -> AbstractionId.id)
    (r_subst : RegionVarId.id -> RegionId.id) (ty_subst : TypeVarId.id -> ty)
    (cg_subst : ConstGenericVarId.id -> const_generic)
    (tr_subst : TraitClauseId.id -> trait_instance_id)
    (tr_self : trait_instance_id) (sg : fun_sig)
    (regions_hierarchy : region_var_groups) : inst_fun_sig =
  let sg =
    Subst.substitute_signature asubst r_subst ty_subst cg_subst tr_subst tr_self
      sg regions_hierarchy
  in
  let { regions_hierarchy; inputs; output; trait_type_constraints } = sg in
  let inputs = List.map (ctx_normalize_ty meta ctx) inputs in
  let output = ctx_normalize_ty meta ctx output in
  let trait_type_constraints =
    List.map (ctx_normalize_trait_type_constraint meta ctx) trait_type_constraints
  in
  { regions_hierarchy; inputs; output; trait_type_constraints }
