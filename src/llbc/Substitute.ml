(** This file implements various substitution utilities to instantiate types,
    function bodies, etc. *)

include Charon.Substitute
open Types
open Values
open LlbcAst

(* Fails if the variable is bound *)
let expect_free_var span (var : 'id de_bruijn_var) : 'id =
  match var with
  | Bound _ -> [%craise_opt_span] span "Found unexpected bound variable"
  | Free id -> id

(** Generate fresh regions for region variables. *)
let fresh_regions_with_substs (region_vars : RegionId.id list)
    (fresh_region_id : unit -> region_id) : RegionId.id -> RegionId.id =
  (* Map each region var id to a fresh region *)
  let rid_map =
    RegionId.Map.of_list
      (List.map (fun var -> (var, fresh_region_id ())) region_vars)
  in
  fun id -> RegionId.Map.find id rid_map

let fresh_regions_with_substs_from_vars (region_vars : region_param list)
    (fresh_region_id : unit -> region_id) : RegionId.id -> RegionId.id =
  fresh_regions_with_substs
    (List.map (fun (r : region_param) -> r.index) region_vars)
    fresh_region_id

(** Substitute a function signature, together with the regions hierarchy
    associated to that signature. *)
let substitute_signature (asubst : RegionGroupId.id -> AbsId.id)
    (r_id_subst : RegionId.id -> RegionId.id) (ty_sb_subst : TypeVarId.id -> ty)
    (cg_sb_subst : ConstGenericVarId.id -> const_generic)
    (tr_sb_subst : TraitClauseId.id -> trait_ref_kind)
    (tr_sb_self : trait_ref_kind) (sg : fun_sig)
    (regions_hierarchy : region_var_groups) : inst_fun_sig =
  let r_sb_subst id = RVar (Free (r_id_subst id)) in
  let subst =
    subst_free_vars
      { r_sb_subst; ty_sb_subst; cg_sb_subst; tr_sb_subst; tr_sb_self }
  in
  let inputs = List.map (ty_substitute subst) sg.inputs in
  let output = ty_substitute subst sg.output in
  let subst_abs_region_group (rg : region_var_group) : abs_region_group =
    let id = asubst rg.id in
    let regions = List.map r_id_subst rg.regions in
    let parents = List.map asubst rg.parents in
    ({ id; regions; parents } : abs_region_group)
  in
  let abs_regions_hierarchy =
    List.map subst_abs_region_group regions_hierarchy
  in
  let subst_region_group (rg : region_var_group) : region_var_group =
    let id = rg.id in
    let regions = List.map r_id_subst rg.regions in
    let parents = rg.parents in
    ({ id; regions; parents } : region_var_group)
  in
  let regions_hierarchy = List.map subst_region_group regions_hierarchy in
  let trait_type_constraints =
    List.map
      (st_substitute_visitor#visit_region_binder
         trait_type_constraint_substitute subst)
      sg.generics.trait_type_constraints
  in
  {
    inputs;
    output;
    regions_hierarchy;
    abs_regions_hierarchy;
    trait_type_constraints;
  }

type id_subst = {
  r_subst : RegionId.id -> RegionId.id;
  ty_subst : TypeVarId.id -> TypeVarId.id;
  cg_subst : ConstGenericVarId.id -> ConstGenericVarId.id;
  ssubst : SymbolicValueId.id -> SymbolicValueId.id;
  bsubst : BorrowId.id -> BorrowId.id;
  sbsubst : SharedBorrowId.id -> SharedBorrowId.id;
  asubst : AbsId.id -> AbsId.id;
}

let empty_id_subst =
  {
    r_subst = (fun x -> x);
    ty_subst = (fun x -> x);
    cg_subst = (fun x -> x);
    ssubst = (fun x -> x);
    bsubst = (fun x -> x);
    sbsubst = (fun x -> x);
    asubst = (fun x -> x);
  }

let no_abs_id_subst span =
  let asubst _ = [%craise] span "Unreachable" in
  { empty_id_subst with asubst }

let subst_ids_visitor (subst : id_subst) =
  object (self : 'self)
    inherit [_] map_env
    method! visit_type_var_id _ id = subst.ty_subst id
    method! visit_const_generic_var_id _ id = subst.cg_subst id
    method! visit_region_id _ rid = subst.r_subst rid
    method! visit_borrow_id _ bid = subst.bsubst bid
    method! visit_shared_borrow_id _ sid = subst.sbsubst sid
    method! visit_loan_id _ bid = subst.bsubst bid
    method! visit_symbolic_value_id _ id = subst.ssubst id

    (** We *do* visit meta-values *)
    method! visit_msymbolic_value env sv = self#visit_symbolic_value env sv

    (** We *do* visit meta-values *)
    method! visit_mvalue env v = self#visit_tvalue env v

    method! visit_abs_id _ id = subst.asubst id
  end

let tvalue_subst_ids (subst : id_subst) (v : tvalue) : tvalue =
  let vis = subst_ids_visitor subst in
  vis#visit_tvalue () v

let tvalue_subst_rids (span : Meta.span) (r_subst : RegionId.id -> RegionId.id)
    (v : tvalue) : tvalue =
  tvalue_subst_ids { (no_abs_id_subst span) with r_subst } v

let abs_subst_ids (subst : id_subst) (x : abs) : abs =
  let vis = subst_ids_visitor subst in
  vis#visit_abs () x

let env_subst_ids (subst : id_subst) (x : env) : env =
  let vis = subst_ids_visitor subst in
  vis#visit_env () x

let tavalue_subst_rids (span : Meta.span) (r_subst : RegionId.id -> RegionId.id)
    (x : tavalue) : tavalue =
  let vis = subst_ids_visitor { (no_abs_id_subst span) with r_subst } in
  vis#visit_tavalue () x

let env_subst_rids (r_subst : RegionId.id -> RegionId.id) (x : env) : env =
  let vis = subst_ids_visitor { empty_id_subst with r_subst } in
  vis#visit_env () x

let generic_args_of_params_erase_regions (span : Meta.span option)
    (generics : generic_params) : generic_args =
  let generics = Charon.TypesUtils.generic_args_of_params span generics in
  (* Note that put aside erasing the regions, we don't need to perform any susbtitutions
     actually, and we only need to erase the regions inside the trait clauses. *)
  let regions = List.map (fun _ -> RErased) generics.regions in
  (* Erase the regions in the trait clauses. *)
  let trait_refs =
    List.map
      (fun (tref : trait_ref) ->
        [%sanity_check_opt_span] span (tref.trait_decl_ref.binder_regions = []);
        st_substitute_visitor#visit_trait_ref erase_regions_subst tref)
      generics.trait_refs
  in
  { generics with regions; trait_refs }
