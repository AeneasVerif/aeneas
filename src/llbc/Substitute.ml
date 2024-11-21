(** This file implements various substitution utilities to instantiate types,
    function bodies, etc.
 *)

include Charon.Substitute
open Types
open Values
open LlbcAst
open ContextsBase
open Errors

(** Generate fresh regions for region variables.

    Return the list of new regions and appropriate substitutions from the
    original region variables to the fresh regions.
    
    TODO: simplify? we only need the subst [RegionVarId.id -> RegionId.id]
  *)
let fresh_regions_with_substs ~(fail_if_not_found : bool)
    (region_vars : RegionVarId.id list) :
    RegionId.id list
    * (RegionVarId.id -> RegionId.id option)
    * (region -> region) =
  (* Generate fresh regions *)
  let fresh_region_ids = List.map (fun _ -> fresh_region_id ()) region_vars in
  (* Generate the map from region var ids to regions *)
  let ls = List.combine region_vars fresh_region_ids in
  let rid_map = RegionVarId.Map.of_list ls in
  (* Generate the substitution from region var id to region *)
  let rid_subst id = RegionVarId.Map.find_opt id rid_map in
  (* Generate the substitution from region to region *)
  let r_subst (r : region) =
    match r with
    | RStatic | RErased | RFVar _ -> r
    | RBVar (bdid, id) ->
        if bdid = 0 then
          match rid_subst id with
          | None -> if fail_if_not_found then raise Not_found else r
          | Some r -> RFVar r
        else r
  in
  (* Return *)
  (fresh_region_ids, rid_subst, r_subst)

let fresh_regions_with_substs_from_vars ~(fail_if_not_found : bool)
    (region_vars : region_var list) :
    RegionId.id list
    * (RegionVarId.id -> RegionId.id option)
    * (region -> region) =
  fresh_regions_with_substs ~fail_if_not_found
    (List.map (fun (r : region_var) -> r.index) region_vars)

(** Substitute a function signature, together with the regions hierarchy
    associated to that signature.

    **IMPORTANT:** this function doesn't normalize the types.
 *)
let substitute_signature (asubst : RegionGroupId.id -> AbstractionId.id)
    (r_subst : RegionVarId.id -> RegionId.id) (ty_subst : TypeVarId.id -> ty)
    (cg_subst : ConstGenericVarId.id -> const_generic)
    (tr_subst : TraitClauseId.id -> trait_instance_id)
    (tr_self : trait_instance_id) (sg : fun_sig)
    (regions_hierarchy : region_var_groups) : inst_fun_sig =
  let r_subst' (r : region) : region =
    match r with
    | RStatic | RErased | RFVar _ -> r
    | RBVar (bdid, rid) -> if bdid = 0 then RFVar (r_subst rid) else r
  in
  let subst = { r_subst = r_subst'; ty_subst; cg_subst; tr_subst; tr_self } in
  let inputs = List.map (ty_substitute subst) sg.inputs in
  let output = ty_substitute subst sg.output in
  let subst_region_group (rg : region_var_group) : abs_region_group =
    let id = asubst rg.id in
    let regions = List.map r_subst rg.regions in
    let parents = List.map asubst rg.parents in
    ({ id; regions; parents } : abs_region_group)
  in
  let regions_hierarchy = List.map subst_region_group regions_hierarchy in
  let push_region_group (subst : subst) : subst =
    let r_subst (r : region) : region =
      match r with
      | RStatic | RErased | RFVar _ -> r
      | RBVar (bdid, rid) ->
          if bdid = 0 then r else subst.r_subst (RBVar (bdid - 1, rid))
    in
    { subst with r_subst }
  in
  let subst_region_binder :
        'a. (subst -> 'a -> 'a) -> subst -> 'a region_binder -> 'a region_binder
      =
   fun subst_value subst rb ->
    let subst = push_region_group subst in
    let { binder_regions; binder_value } = rb in
    let binder_value = subst_value subst binder_value in
    { binder_regions; binder_value }
  in
  let trait_type_constraints =
    List.map
      (subst_region_binder trait_type_constraint_substitute subst)
      sg.generics.trait_type_constraints
  in
  { inputs; output; regions_hierarchy; trait_type_constraints }

let subst_ids_visitor (r_subst : RegionId.id -> RegionId.id)
    (ty_subst : TypeVarId.id -> TypeVarId.id)
    (cg_subst : ConstGenericVarId.id -> ConstGenericVarId.id)
    (ssubst : SymbolicValueId.id -> SymbolicValueId.id)
    (bsubst : BorrowId.id -> BorrowId.id)
    (asubst : AbstractionId.id -> AbstractionId.id) =
  object (self : 'self)
    inherit [_] map_env
    method! visit_type_var_id _ id = ty_subst id
    method! visit_const_generic_var_id _ id = cg_subst id
    method! visit_region_id _ rid = r_subst rid
    method! visit_borrow_id _ bid = bsubst bid
    method! visit_loan_id _ bid = bsubst bid
    method! visit_symbolic_value_id _ id = ssubst id

    (** We *do* visit meta-values *)
    method! visit_msymbolic_value env sv = self#visit_symbolic_value env sv

    (** We *do* visit meta-values *)
    method! visit_mvalue env v = self#visit_typed_value env v

    method! visit_abstraction_id _ id = asubst id
  end

let typed_value_subst_ids (span : Meta.span)
    (r_subst : RegionId.id -> RegionId.id)
    (ty_subst : TypeVarId.id -> TypeVarId.id)
    (cg_subst : ConstGenericVarId.id -> ConstGenericVarId.id)
    (ssubst : SymbolicValueId.id -> SymbolicValueId.id)
    (bsubst : BorrowId.id -> BorrowId.id) (v : typed_value) : typed_value =
  let asubst _ = craise __FILE__ __LINE__ span "Unreachable" in
  let vis = subst_ids_visitor r_subst ty_subst cg_subst ssubst bsubst asubst in
  vis#visit_typed_value () v

let typed_value_subst_rids (span : Meta.span)
    (r_subst : RegionId.id -> RegionId.id) (v : typed_value) : typed_value =
  typed_value_subst_ids span r_subst
    (fun x -> x)
    (fun x -> x)
    (fun x -> x)
    (fun x -> x)
    v

let typed_avalue_subst_ids (span : Meta.span)
    (r_subst : RegionId.id -> RegionId.id)
    (ty_subst : TypeVarId.id -> TypeVarId.id)
    (cg_subst : ConstGenericVarId.id -> ConstGenericVarId.id)
    (ssubst : SymbolicValueId.id -> SymbolicValueId.id)
    (bsubst : BorrowId.id -> BorrowId.id) (v : typed_avalue) : typed_avalue =
  let asubst _ = craise __FILE__ __LINE__ span "Unreachable" in
  let vis = subst_ids_visitor r_subst ty_subst cg_subst ssubst bsubst asubst in
  vis#visit_typed_avalue () v

let abs_subst_ids (r_subst : RegionId.id -> RegionId.id)
    (ty_subst : TypeVarId.id -> TypeVarId.id)
    (cg_subst : ConstGenericVarId.id -> ConstGenericVarId.id)
    (ssubst : SymbolicValueId.id -> SymbolicValueId.id)
    (bsubst : BorrowId.id -> BorrowId.id)
    (asubst : AbstractionId.id -> AbstractionId.id) (x : abs) : abs =
  let vis = subst_ids_visitor r_subst ty_subst cg_subst ssubst bsubst asubst in
  vis#visit_abs () x

let env_subst_ids (r_subst : RegionId.id -> RegionId.id)
    (ty_subst : TypeVarId.id -> TypeVarId.id)
    (cg_subst : ConstGenericVarId.id -> ConstGenericVarId.id)
    (ssubst : SymbolicValueId.id -> SymbolicValueId.id)
    (bsubst : BorrowId.id -> BorrowId.id)
    (asubst : AbstractionId.id -> AbstractionId.id) (x : env) : env =
  let vis = subst_ids_visitor r_subst ty_subst cg_subst ssubst bsubst asubst in
  vis#visit_env () x

let typed_avalue_subst_rids (span : Meta.span)
    (r_subst : RegionId.id -> RegionId.id) (x : typed_avalue) : typed_avalue =
  let asubst _ = craise __FILE__ __LINE__ span "Unreachable" in
  let vis =
    subst_ids_visitor r_subst
      (fun x -> x)
      (fun x -> x)
      (fun x -> x)
      (fun x -> x)
      asubst
  in
  vis#visit_typed_avalue () x

let env_subst_rids (r_subst : RegionId.id -> RegionId.id) (x : env) : env =
  let vis =
    subst_ids_visitor r_subst
      (fun x -> x)
      (fun x -> x)
      (fun x -> x)
      (fun x -> x)
      (fun x -> x)
  in
  vis#visit_env () x

let generic_args_of_params_erase_regions span (generics : generic_params) :
    generic_args =
  let generics =
    st_substitute_visitor#visit_generic_params erase_regions_subst generics
  in
  (* Note that from here we don't need to perform any susbtitutions actually *)
  let regions = List.map (fun _ -> RErased) generics.regions in
  let types = List.map (fun (v : type_var) -> TVar v.index) generics.types in
  let const_generics =
    List.map
      (fun (v : const_generic_var) -> CgVar v.index)
      generics.const_generics
  in
  let trait_refs =
    List.map
      (fun (c : trait_clause) ->
        sanity_check __FILE__ __LINE__ (c.trait.binder_regions = []) span;
        let { trait_decl_id; decl_generics; _ } = c.trait.binder_value in
        let trait_decl_ref = { trait_decl_id; decl_generics } in
        (* Note that because we directly refer to the clause, we give it
           empty generics *)
        let trait_id = Clause c.clause_id in
        {
          trait_id;
          trait_decl_ref =
            {
              (* Empty list of bound regions: we don't support the other cases for now *)
              binder_regions = [];
              binder_value = trait_decl_ref;
            };
        })
      generics.trait_clauses
  in
  { regions; types; const_generics; trait_refs }
