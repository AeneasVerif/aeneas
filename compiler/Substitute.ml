(** This file implements various substitution utilities to instantiate types,
    function bodies, etc.
 *)

include Charon.Substitute
open Types
open Values
open LlbcAst
open Contexts
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

(** Return the types of the properly instantiated ADT's variant, provided a
    context.

    **IMPORTANT**: this function doesn't normalize the types, you may want to
    use the [AssociatedTypes] equivalent instead.
*)
let ctx_adt_get_instantiated_field_types (ctx : eval_ctx)
    (def_id : TypeDeclId.id) (opt_variant_id : VariantId.id option)
    (generics : generic_args) : ty list =
  let def = ctx_lookup_type_decl ctx def_id in
  type_decl_get_instantiated_field_types def opt_variant_id generics

(** Return the types of the properly instantiated ADT value (note that
    here, ADT is understood in its broad meaning: ADT, assumed value or tuple).

    **IMPORTANT**: this function doesn't normalize the types, you may want to
    use the [AssociatedTypes] equivalent instead.
 *)
let ctx_adt_value_get_instantiated_field_types (meta : Meta.meta) (ctx : eval_ctx)
    (adt : adt_value) (id : type_id) (generics : generic_args) : ty list =
  match id with
  | TAdtId id ->
      (* Retrieve the types of the fields *)
      ctx_adt_get_instantiated_field_types ctx id adt.variant_id generics
  | TTuple ->
      cassert (generics.regions = []) meta "Regions should be empty TODO: error message";
      generics.types
  | TAssumed aty -> (
      match aty with
      | TBox ->
          cassert (generics.regions = []) meta "Regions should be empty TODO: error message";
          cassert (List.length generics.types = 1) meta "Too many types TODO: error message";
          cassert (generics.const_generics = []) meta "const_generics should be empty TODO: error message";
          generics.types
      | TArray | TSlice | TStr ->
          (* Those types don't have fields *)
          craise meta "Unreachable")

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
  let trait_type_constraints =
    List.map
      (trait_type_constraint_substitute subst)
      sg.preds.trait_type_constraints
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

let typed_value_subst_ids (meta : Meta.meta) (r_subst : RegionId.id -> RegionId.id)
    (ty_subst : TypeVarId.id -> TypeVarId.id)
    (cg_subst : ConstGenericVarId.id -> ConstGenericVarId.id)
    (ssubst : SymbolicValueId.id -> SymbolicValueId.id)
    (bsubst : BorrowId.id -> BorrowId.id) (v : typed_value) : typed_value =
  let asubst _ = craise meta "Unreachable" in
  let vis = subst_ids_visitor r_subst ty_subst cg_subst ssubst bsubst asubst in
  vis#visit_typed_value () v

let typed_value_subst_rids (meta : Meta.meta) (r_subst : RegionId.id -> RegionId.id)
    (v : typed_value) : typed_value =
  typed_value_subst_ids meta r_subst
    (fun x -> x)
    (fun x -> x)
    (fun x -> x)
    (fun x -> x)
    v

let typed_avalue_subst_ids (meta : Meta.meta) (r_subst : RegionId.id -> RegionId.id)
    (ty_subst : TypeVarId.id -> TypeVarId.id)
    (cg_subst : ConstGenericVarId.id -> ConstGenericVarId.id)
    (ssubst : SymbolicValueId.id -> SymbolicValueId.id)
    (bsubst : BorrowId.id -> BorrowId.id) (v : typed_avalue) : typed_avalue =
  let asubst _ = craise meta "Unreachable" in
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

let typed_avalue_subst_rids (meta : Meta.meta) (r_subst : RegionId.id -> RegionId.id)
    (x : typed_avalue) : typed_avalue =
  let asubst _ = craise meta "Unreachable" in
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
