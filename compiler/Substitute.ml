(** This file implements various substitution utilities to instantiate types,
    function bodies, etc.
 *)

open Types
open TypesUtils
open Values
open Expressions
open LlbcAst
open Contexts

type subst = {
  r_subst : region -> region;
  ty_subst : TypeVarId.id -> ty;
  cg_subst : ConstGenericVarId.id -> const_generic;
      (** Substitution from *local* trait clause to trait instance *)
  tr_subst : TraitClauseId.id -> trait_instance_id;
      (** Substitution for the [Self] trait instance *)
  tr_self : trait_instance_id;
}

let st_substitute_visitor (subst : subst) =
  object
    inherit [_] map_statement
    method! visit_region _ r = subst.r_subst r
    method! visit_TVar _ id = subst.ty_subst id

    method! visit_type_var_id _ _ =
      (* We should never get here because we reimplemented [visit_TypeVar] *)
      raise (Failure "Unexpected")

    method! visit_CGVar _ id = subst.cg_subst id

    method! visit_const_generic_var_id _ _ =
      (* We should never get here because we reimplemented [visit_Var] *)
      raise (Failure "Unexpected")

    method! visit_Clause _ id = subst.tr_subst id
    method! visit_Self _ = subst.tr_self
  end

(** Substitute types variables and regions in a type.

    **IMPORTANT**: this doesn't normalize the types.
 *)
let ty_substitute (subst : subst) (ty : ty) : ty =
  let visitor = st_substitute_visitor subst in
  visitor#visit_ty () ty

(** **IMPORTANT**: this doesn't normalize the types. *)
let trait_ref_substitute (subst : subst) (tr : trait_ref) : trait_ref =
  let visitor = st_substitute_visitor subst in
  visitor#visit_trait_ref () tr

(** **IMPORTANT**: this doesn't normalize the types. *)
let trait_instance_id_substitute (subst : subst) (tr : trait_instance_id) :
    trait_instance_id =
  let visitor = st_substitute_visitor subst in
  visitor#visit_trait_instance_id () tr

(** **IMPORTANT**: this doesn't normalize the types. *)
let generic_args_substitute (subst : subst) (g : generic_args) : generic_args =
  let visitor = st_substitute_visitor subst in
  visitor#visit_generic_args () g

let predicates_substitute (subst : subst) (p : predicates) : predicates =
  let visitor = st_substitute_visitor subst in
  visitor#visit_predicates () p

let erase_regions_subst : subst =
  {
    r_subst = (fun _ -> RErased);
    ty_subst = (fun vid -> TVar vid);
    cg_subst = (fun id -> CGVar id);
    tr_subst = (fun id -> Clause id);
    tr_self = Self;
  }

(** Convert an {!rty} to an {!ety} by erasing the region variables *)
let erase_regions (ty : ty) : ty = ty_substitute erase_regions_subst ty

let trait_ref_erase_regions (tr : trait_ref) : trait_ref =
  trait_ref_substitute erase_regions_subst tr

let trait_instance_id_erase_regions (tr : trait_instance_id) : trait_instance_id
    =
  trait_instance_id_substitute erase_regions_subst tr

let generic_args_erase_regions (tr : generic_args) : generic_args =
  generic_args_substitute erase_regions_subst tr

(** Generate fresh regions for region variables.

    Return the list of new regions and appropriate substitutions from the
    original region variables to the fresh regions.
    
    TODO: simplify? we only need the subst [RegionVarId.id -> RegionId.id]
  *)
let fresh_regions_with_substs (region_vars : region_var list) :
    RegionId.id list * (RegionId.id -> RegionId.id) * (region -> region) =
  (* Generate fresh regions *)
  let fresh_region_ids = List.map (fun _ -> fresh_region_id ()) region_vars in
  (* Generate the map from region var ids to regions *)
  let ls = List.combine region_vars fresh_region_ids in
  let rid_map =
    List.fold_left
      (fun mp ((k : region_var), v) -> RegionId.Map.add k.index v mp)
      RegionId.Map.empty ls
  in
  (* Generate the substitution from region var id to region *)
  let rid_subst id = RegionId.Map.find id rid_map in
  (* Generate the substitution from region to region *)
  let r_subst (r : region) =
    match r with RStatic | RErased -> r | RVar id -> RVar (rid_subst id)
  in
  (* Return *)
  (fresh_region_ids, rid_subst, r_subst)

(** Erase the regions in a type and perform a substitution *)
let erase_regions_substitute_types (ty_subst : TypeVarId.id -> ty)
    (cg_subst : ConstGenericVarId.id -> const_generic)
    (tr_subst : TraitClauseId.id -> trait_instance_id)
    (tr_self : trait_instance_id) (ty : ty) : ty =
  let r_subst (_ : region) : region = RErased in
  let subst = { r_subst; ty_subst; cg_subst; tr_subst; tr_self } in
  ty_substitute subst ty

(** Create a region substitution from a list of region variable ids and a list of
    regions (with which to substitute the region variable ids *)
let make_region_subst (var_ids : RegionId.id list) (regions : region list) :
    region -> region =
  let ls = List.combine var_ids regions in
  let mp =
    List.fold_left
      (fun mp (k, v) -> RegionId.Map.add k v mp)
      RegionId.Map.empty ls
  in
  fun r ->
    match r with RStatic | RErased -> r | RVar id -> RegionId.Map.find id mp

let make_region_subst_from_vars (vars : region_var list) (regions : region list)
    : region -> region =
  make_region_subst (List.map (fun (x : region_var) -> x.index) vars) regions

(** Create a type substitution from a list of type variable ids and a list of
    types (with which to substitute the type variable ids) *)
let make_type_subst (var_ids : TypeVarId.id list) (tys : ty list) :
    TypeVarId.id -> ty =
  let ls = List.combine var_ids tys in
  let mp =
    List.fold_left
      (fun mp (k, v) -> TypeVarId.Map.add k v mp)
      TypeVarId.Map.empty ls
  in
  fun id -> TypeVarId.Map.find id mp

let make_type_subst_from_vars (vars : type_var list) (tys : ty list) :
    TypeVarId.id -> ty =
  make_type_subst (List.map (fun (x : type_var) -> x.index) vars) tys

(** Create a const generic substitution from a list of const generic variable ids and a list of
    const generics (with which to substitute the const generic variable ids) *)
let make_const_generic_subst (var_ids : ConstGenericVarId.id list)
    (cgs : const_generic list) : ConstGenericVarId.id -> const_generic =
  let ls = List.combine var_ids cgs in
  let mp =
    List.fold_left
      (fun mp (k, v) -> ConstGenericVarId.Map.add k v mp)
      ConstGenericVarId.Map.empty ls
  in
  fun id -> ConstGenericVarId.Map.find id mp

let make_const_generic_subst_from_vars (vars : const_generic_var list)
    (cgs : const_generic list) : ConstGenericVarId.id -> const_generic =
  make_const_generic_subst
    (List.map (fun (x : const_generic_var) -> x.index) vars)
    cgs

(** Create a trait substitution from a list of trait clause ids and a list of
    trait refs *)
let make_trait_subst (clause_ids : TraitClauseId.id list) (trs : trait_ref list)
    : TraitClauseId.id -> trait_instance_id =
  let ls = List.combine clause_ids trs in
  let mp =
    List.fold_left
      (fun mp (k, v) -> TraitClauseId.Map.add k (TraitRef v) mp)
      TraitClauseId.Map.empty ls
  in
  fun id -> TraitClauseId.Map.find id mp

let make_trait_subst_from_clauses (clauses : trait_clause list)
    (trs : trait_ref list) : TraitClauseId.id -> trait_instance_id =
  make_trait_subst
    (List.map (fun (x : trait_clause) -> x.clause_id) clauses)
    trs

let make_subst_from_generics (params : generic_params) (args : generic_args)
    (tr_self : trait_instance_id) : subst =
  let r_subst = make_region_subst_from_vars params.regions args.regions in
  let ty_subst = make_type_subst_from_vars params.types args.types in
  let cg_subst =
    make_const_generic_subst_from_vars params.const_generics args.const_generics
  in
  let tr_subst =
    make_trait_subst_from_clauses params.trait_clauses args.trait_refs
  in
  { r_subst; ty_subst; cg_subst; tr_subst; tr_self }

let make_subst_from_generics_erase_regions (params : generic_params)
    (generics : generic_args) (tr_self : trait_instance_id) =
  let generics = generic_args_erase_regions generics in
  let tr_self = trait_instance_id_erase_regions tr_self in
  let subst = make_subst_from_generics params generics tr_self in
  { subst with r_subst = (fun _ -> RErased) }

(** Instantiate the type variables in an ADT definition, and return, for
    every variant, the list of the types of its fields.

    **IMPORTANT**: this function doesn't normalize the types, you may want to
    use the [AssociatedTypes] equivalent instead.
*)
let type_decl_get_instantiated_variants_fields_types (def : type_decl)
    (generics : generic_args) : (VariantId.id option * ty list) list =
  (* There shouldn't be any reference to Self *)
  let tr_self = UnknownTrait __FUNCTION__ in
  let subst = make_subst_from_generics def.generics generics tr_self in
  let (variants_fields : (VariantId.id option * field list) list) =
    match def.kind with
    | Enum variants ->
        List.mapi (fun i v -> (Some (VariantId.of_int i), v.fields)) variants
    | Struct fields -> [ (None, fields) ]
    | Opaque ->
        raise
          (Failure
             ("Can't retrieve the variants of an opaque type: "
            ^ show_name def.name))
  in
  List.map
    (fun (id, fields) ->
      (id, List.map (fun f -> ty_substitute subst f.field_ty) fields))
    variants_fields

(** Instantiate the type variables in an ADT definition, and return the list
    of types of the fields for the chosen variant.

    **IMPORTANT**: this function doesn't normalize the types, you may want to
    use the [AssociatedTypes] equivalent instead.
*)
let type_decl_get_instantiated_field_types (def : type_decl)
    (opt_variant_id : VariantId.id option) (generics : generic_args) : ty list =
  (* For now, check that there are no clauses - otherwise we might need
     to normalize the types *)
  assert (def.generics.trait_clauses = []);
  (* There shouldn't be any reference to Self *)
  let tr_self = UnknownTrait __FUNCTION__ in
  let subst = make_subst_from_generics def.generics generics tr_self in
  let fields = type_decl_get_fields def opt_variant_id in
  List.map (fun f -> ty_substitute subst f.field_ty) fields

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
let ctx_adt_value_get_instantiated_field_types (ctx : eval_ctx)
    (adt : adt_value) (id : type_id) (generics : generic_args) : ty list =
  match id with
  | TAdtId id ->
      (* Retrieve the types of the fields *)
      ctx_adt_get_instantiated_field_types ctx id adt.variant_id generics
  | TTuple ->
      assert (generics.regions = []);
      generics.types
  | TAssumed aty -> (
      match aty with
      | TBox ->
          assert (generics.regions = []);
          assert (List.length generics.types = 1);
          assert (generics.const_generics = []);
          generics.types
      | TArray | TSlice | TStr ->
          (* Those types don't have fields *)
          raise (Failure "Unreachable"))

(** Apply a type substitution to a place *)
let place_substitute (subst : subst) (p : place) : place =
  (* There is in fact nothing to do *)
  (st_substitute_visitor subst)#visit_place () p

(** Apply a type substitution to an operand *)
let operand_substitute (subst : subst) (op : operand) : operand =
  (st_substitute_visitor subst)#visit_operand () op

(** Apply a type substitution to an rvalue *)
let rvalue_substitute (subst : subst) (rv : rvalue) : rvalue =
  (st_substitute_visitor subst)#visit_rvalue () rv

(** Apply a type substitution to an assertion *)
let assertion_substitute (subst : subst) (a : assertion) : assertion =
  (st_substitute_visitor subst)#visit_assertion () a

(** Apply a type substitution to a call *)
let call_substitute (subst : subst) (call : call) : call =
  (st_substitute_visitor subst)#visit_call () call

(** Apply a type substitution to a statement *)
let statement_substitute (subst : subst) (st : statement) : statement =
  (st_substitute_visitor subst)#visit_statement () st

(** Apply a type substitution to a function body. Return the local variables
    and the body. *)
let fun_body_substitute_in_body (subst : subst) (body : fun_body) :
    var list * statement =
  let locals =
    List.map
      (fun (v : var) -> { v with var_ty = ty_substitute subst v.var_ty })
      body.locals
  in
  let body = statement_substitute subst body.body in
  (locals, body)

let trait_type_constraint_substitute (subst : subst)
    (ttc : trait_type_constraint) : trait_type_constraint =
  let { trait_ref; generics; type_name; ty } = ttc in
  let visitor = st_substitute_visitor subst in
  let trait_ref = visitor#visit_trait_ref () trait_ref in
  let generics = visitor#visit_generic_args () generics in
  let ty = visitor#visit_ty () ty in
  { trait_ref; generics; type_name; ty }

(** Substitute a function signature, together with the regions hierarchy
    associated to that signature.

    **IMPORTANT:** this function doesn't normalize the types.
 *)
let substitute_signature (asubst : RegionGroupId.id -> AbstractionId.id)
    (r_subst : RegionId.id -> RegionId.id) (ty_subst : TypeVarId.id -> ty)
    (cg_subst : ConstGenericVarId.id -> const_generic)
    (tr_subst : TraitClauseId.id -> trait_instance_id)
    (tr_self : trait_instance_id) (sg : fun_sig)
    (regions_hierarchy : region_groups) : inst_fun_sig =
  let r_subst' (r : region) : region =
    match r with RStatic | RErased -> r | RVar rid -> RVar (r_subst rid)
  in
  let subst = { r_subst = r_subst'; ty_subst; cg_subst; tr_subst; tr_self } in
  let inputs = List.map (ty_substitute subst) sg.inputs in
  let output = ty_substitute subst sg.output in
  let subst_region_group (rg : region_group) : abs_region_group =
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

(** Substitute variable identifiers in a type *)
let statement_substitute_ids (ty_subst : TypeVarId.id -> TypeVarId.id)
    (cg_subst : ConstGenericVarId.id -> ConstGenericVarId.id) (ty : ty) : ty =
  let visitor =
    object
      inherit [_] map_ty
      method visit_'r _ r = r
      method! visit_type_var_id _ id = ty_subst id
      method! visit_const_generic_var_id _ id = cg_subst id
    end
  in

  visitor#visit_ty () ty

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

let typed_value_subst_ids (r_subst : RegionId.id -> RegionId.id)
    (ty_subst : TypeVarId.id -> TypeVarId.id)
    (cg_subst : ConstGenericVarId.id -> ConstGenericVarId.id)
    (ssubst : SymbolicValueId.id -> SymbolicValueId.id)
    (bsubst : BorrowId.id -> BorrowId.id) (v : typed_value) : typed_value =
  let asubst _ = raise (Failure "Unreachable") in
  let vis = subst_ids_visitor r_subst ty_subst cg_subst ssubst bsubst asubst in
  vis#visit_typed_value () v

let typed_value_subst_rids (r_subst : RegionId.id -> RegionId.id)
    (v : typed_value) : typed_value =
  typed_value_subst_ids r_subst
    (fun x -> x)
    (fun x -> x)
    (fun x -> x)
    (fun x -> x)
    v

let typed_avalue_subst_ids (r_subst : RegionId.id -> RegionId.id)
    (ty_subst : TypeVarId.id -> TypeVarId.id)
    (cg_subst : ConstGenericVarId.id -> ConstGenericVarId.id)
    (ssubst : SymbolicValueId.id -> SymbolicValueId.id)
    (bsubst : BorrowId.id -> BorrowId.id) (v : typed_avalue) : typed_avalue =
  let asubst _ = raise (Failure "Unreachable") in
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

let typed_avalue_subst_rids (r_subst : RegionId.id -> RegionId.id)
    (x : typed_avalue) : typed_avalue =
  let asubst _ = raise (Failure "Unreachable") in
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
