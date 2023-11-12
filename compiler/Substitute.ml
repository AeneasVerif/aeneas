(** This file implements various substitution utilities to instantiate types,
    function bodies, etc.
 *)

module T = Types
module TU = TypesUtils
module V = Values
module E = Expressions
module A = LlbcAst
module C = Contexts

type subst = {
  r_subst : T.region -> T.region;
  ty_subst : T.TypeVarId.id -> T.ty;
  cg_subst : T.ConstGenericVarId.id -> T.const_generic;
      (** Substitution from *local* trait clause to trait instance *)
  tr_subst : T.TraitClauseId.id -> T.trait_instance_id;
      (** Substitution for the [Self] trait instance *)
  tr_self : T.trait_instance_id;
}

let st_substitute_visitor (subst : subst) =
  object
    inherit [_] A.map_statement
    method! visit_region _ r = subst.r_subst r
    method! visit_TypeVar _ id = subst.ty_subst id

    method! visit_type_var_id _ _ =
      (* We should never get here because we reimplemented [visit_TypeVar] *)
      raise (Failure "Unexpected")

    method! visit_ConstGenericVar _ id = subst.cg_subst id

    method! visit_const_generic_var_id _ _ =
      (* We should never get here because we reimplemented [visit_Var] *)
      raise (Failure "Unexpected")

    method! visit_Clause _ id = subst.tr_subst id
    method! visit_Self _ = subst.tr_self
  end

(** Substitute types variables and regions in a type.

    **IMPORTANT**: this doesn't normalize the types.
 *)
let ty_substitute (subst : subst) (ty : T.ty) : T.ty =
  let visitor = st_substitute_visitor subst in
  visitor#visit_ty () ty

(** **IMPORTANT**: this doesn't normalize the types. *)
let trait_ref_substitute (subst : subst) (tr : T.trait_ref) : T.trait_ref =
  let visitor = st_substitute_visitor subst in
  visitor#visit_trait_ref () tr

(** **IMPORTANT**: this doesn't normalize the types. *)
let trait_instance_id_substitute (subst : subst) (tr : T.trait_instance_id) :
    T.trait_instance_id =
  let visitor = st_substitute_visitor subst in
  visitor#visit_trait_instance_id () tr

(** **IMPORTANT**: this doesn't normalize the types. *)
let generic_args_substitute (subst : subst) (g : T.generic_args) :
    T.generic_args =
  let visitor = st_substitute_visitor subst in
  visitor#visit_generic_args () g

let erase_regions_subst : subst =
  {
    r_subst = (fun _ -> T.RErased);
    ty_subst = (fun vid -> T.TypeVar vid);
    cg_subst = (fun id -> T.ConstGenericVar id);
    tr_subst = (fun id -> T.Clause id);
    tr_self = T.Self;
  }

(** Convert an {!T.rty} to an {!T.ety} by erasing the region variables *)
let erase_regions (ty : T.ty) : T.ty = ty_substitute erase_regions_subst ty

let trait_ref_erase_regions (tr : T.trait_ref) : T.trait_ref =
  trait_ref_substitute erase_regions_subst tr

let trait_instance_id_erase_regions (tr : T.trait_instance_id) :
    T.trait_instance_id =
  trait_instance_id_substitute erase_regions_subst tr

let generic_args_erase_regions (tr : T.generic_args) : T.generic_args =
  generic_args_substitute erase_regions_subst tr

(** Generate fresh regions for region variables.

    Return the list of new regions and appropriate substitutions from the
    original region variables to the fresh regions.
    
    TODO: simplify? we only need the subst [T.RegionVarId.id -> T.RegionId.id]
  *)
let fresh_regions_with_substs (region_vars : T.region_var list) :
    T.RegionId.id list
    * (T.RegionId.id -> T.RegionId.id)
    * (T.region -> T.region) =
  (* Generate fresh regions *)
  let fresh_region_ids = List.map (fun _ -> C.fresh_region_id ()) region_vars in
  (* Generate the map from region var ids to regions *)
  let ls = List.combine region_vars fresh_region_ids in
  let rid_map =
    List.fold_left
      (fun mp ((k : T.region_var), v) -> T.RegionId.Map.add k.T.index v mp)
      T.RegionId.Map.empty ls
  in
  (* Generate the substitution from region var id to region *)
  let rid_subst id = T.RegionId.Map.find id rid_map in
  (* Generate the substitution from region to region *)
  let r_subst (r : T.region) =
    match r with
    | T.RStatic | T.RErased -> r
    | T.RVar id -> T.RVar (rid_subst id)
  in
  (* Return *)
  (fresh_region_ids, rid_subst, r_subst)

(** Erase the regions in a type and perform a substitution *)
let erase_regions_substitute_types (ty_subst : T.TypeVarId.id -> T.ty)
    (cg_subst : T.ConstGenericVarId.id -> T.const_generic)
    (tr_subst : T.TraitClauseId.id -> T.trait_instance_id)
    (tr_self : T.trait_instance_id) (ty : T.ty) : T.ty =
  let r_subst (_ : T.region) : T.region = T.RErased in
  let subst = { r_subst; ty_subst; cg_subst; tr_subst; tr_self } in
  ty_substitute subst ty

(** Create a region substitution from a list of region variable ids and a list of
    regions (with which to substitute the region variable ids *)
let make_region_subst (var_ids : T.RegionId.id list) (regions : T.region list) :
    T.region -> T.region =
  let ls = List.combine var_ids regions in
  let mp =
    List.fold_left
      (fun mp (k, v) -> T.RegionId.Map.add k v mp)
      T.RegionId.Map.empty ls
  in
  fun r ->
    match r with
    | T.RStatic | T.RErased -> r
    | T.RVar id -> T.RegionId.Map.find id mp

let make_region_subst_from_vars (vars : T.region_var list)
    (regions : T.region list) : T.region -> T.region =
  make_region_subst
    (List.map (fun (x : T.region_var) -> x.T.index) vars)
    regions

(** Create a type substitution from a list of type variable ids and a list of
    types (with which to substitute the type variable ids) *)
let make_type_subst (var_ids : T.TypeVarId.id list) (tys : T.ty list) :
    T.TypeVarId.id -> T.ty =
  let ls = List.combine var_ids tys in
  let mp =
    List.fold_left
      (fun mp (k, v) -> T.TypeVarId.Map.add k v mp)
      T.TypeVarId.Map.empty ls
  in
  fun id -> T.TypeVarId.Map.find id mp

let make_type_subst_from_vars (vars : T.type_var list) (tys : T.ty list) :
    T.TypeVarId.id -> T.ty =
  make_type_subst (List.map (fun (x : T.type_var) -> x.T.index) vars) tys

(** Create a const generic substitution from a list of const generic variable ids and a list of
    const generics (with which to substitute the const generic variable ids) *)
let make_const_generic_subst (var_ids : T.ConstGenericVarId.id list)
    (cgs : T.const_generic list) : T.ConstGenericVarId.id -> T.const_generic =
  let ls = List.combine var_ids cgs in
  let mp =
    List.fold_left
      (fun mp (k, v) -> T.ConstGenericVarId.Map.add k v mp)
      T.ConstGenericVarId.Map.empty ls
  in
  fun id -> T.ConstGenericVarId.Map.find id mp

let make_const_generic_subst_from_vars (vars : T.const_generic_var list)
    (cgs : T.const_generic list) : T.ConstGenericVarId.id -> T.const_generic =
  make_const_generic_subst
    (List.map (fun (x : T.const_generic_var) -> x.T.index) vars)
    cgs

(** Create a trait substitution from a list of trait clause ids and a list of
    trait refs *)
let make_trait_subst (clause_ids : T.TraitClauseId.id list)
    (trs : T.trait_ref list) : T.TraitClauseId.id -> T.trait_instance_id =
  let ls = List.combine clause_ids trs in
  let mp =
    List.fold_left
      (fun mp (k, v) -> T.TraitClauseId.Map.add k (T.TraitRef v) mp)
      T.TraitClauseId.Map.empty ls
  in
  fun id -> T.TraitClauseId.Map.find id mp

let make_trait_subst_from_clauses (clauses : T.trait_clause list)
    (trs : T.trait_ref list) : T.TraitClauseId.id -> T.trait_instance_id =
  make_trait_subst
    (List.map (fun (x : T.trait_clause) -> x.T.clause_id) clauses)
    trs

let make_subst_from_generics (params : T.generic_params) (args : T.generic_args)
    (tr_self : T.trait_instance_id) : subst =
  let r_subst = make_region_subst_from_vars params.T.regions args.T.regions in
  let ty_subst = make_type_subst_from_vars params.T.types args.T.types in
  let cg_subst =
    make_const_generic_subst_from_vars params.T.const_generics
      args.T.const_generics
  in
  let tr_subst =
    make_trait_subst_from_clauses params.T.trait_clauses args.T.trait_refs
  in
  { r_subst; ty_subst; cg_subst; tr_subst; tr_self }

let make_subst_from_generics_erase_regions (params : T.generic_params)
    (generics : T.generic_args) (tr_self : T.trait_instance_id) =
  let generics = generic_args_erase_regions generics in
  let tr_self = trait_instance_id_erase_regions tr_self in
  let subst = make_subst_from_generics params generics tr_self in
  { subst with r_subst = (fun _ -> T.RErased) }

(** Instantiate the type variables in an ADT definition, and return, for
    every variant, the list of the types of its fields.

    **IMPORTANT**: this function doesn't normalize the types, you may want to
    use the [AssociatedTypes] equivalent instead.
*)
let type_decl_get_instantiated_variants_fields_types (def : T.type_decl)
    (generics : T.generic_args) : (T.VariantId.id option * T.ty list) list =
  (* There shouldn't be any reference to Self *)
  let tr_self = T.UnknownTrait __FUNCTION__ in
  let subst = make_subst_from_generics def.T.generics generics tr_self in
  let (variants_fields : (T.VariantId.id option * T.field list) list) =
    match def.T.kind with
    | T.Enum variants ->
        List.mapi
          (fun i v -> (Some (T.VariantId.of_int i), v.T.fields))
          variants
    | T.Struct fields -> [ (None, fields) ]
    | T.Opaque ->
        raise
          (Failure
             ("Can't retrieve the variants of an opaque type: "
             ^ Names.name_to_string def.name))
  in
  List.map
    (fun (id, fields) ->
      (id, List.map (fun f -> ty_substitute subst f.T.field_ty) fields))
    variants_fields

(** Instantiate the type variables in an ADT definition, and return the list
    of types of the fields for the chosen variant.

    **IMPORTANT**: this function doesn't normalize the types, you may want to
    use the [AssociatedTypes] equivalent instead.
*)
let type_decl_get_instantiated_field_types (def : T.type_decl)
    (opt_variant_id : T.VariantId.id option) (generics : T.generic_args) :
    T.ty list =
  (* For now, check that there are no clauses - otherwise we might need
     to normalize the types *)
  assert (def.generics.trait_clauses = []);
  (* There shouldn't be any reference to Self *)
  let tr_self = T.UnknownTrait __FUNCTION__ in
  let subst = make_subst_from_generics def.T.generics generics tr_self in
  let fields = TU.type_decl_get_fields def opt_variant_id in
  List.map (fun f -> ty_substitute subst f.T.field_ty) fields

(** Return the types of the properly instantiated ADT's variant, provided a
    context.

    **IMPORTANT**: this function doesn't normalize the types, you may want to
    use the [AssociatedTypes] equivalent instead.
*)
let ctx_adt_get_instantiated_field_types (ctx : C.eval_ctx)
    (def_id : T.TypeDeclId.id) (opt_variant_id : T.VariantId.id option)
    (generics : T.generic_args) : T.ty list =
  let def = C.ctx_lookup_type_decl ctx def_id in
  type_decl_get_instantiated_field_types def opt_variant_id generics

(** Return the types of the properly instantiated ADT value (note that
    here, ADT is understood in its broad meaning: ADT, assumed value or tuple).

    **IMPORTANT**: this function doesn't normalize the types, you may want to
    use the [AssociatedTypes] equivalent instead.
 *)
let ctx_adt_value_get_instantiated_field_types (ctx : C.eval_ctx)
    (adt : V.adt_value) (id : T.type_id) (generics : T.generic_args) : T.ty list
    =
  match id with
  | T.AdtId id ->
      (* Retrieve the types of the fields *)
      ctx_adt_get_instantiated_field_types ctx id adt.V.variant_id generics
  | T.Tuple ->
      assert (generics.regions = []);
      generics.types
  | T.TAssumed aty -> (
      match aty with
      | T.TBox ->
          assert (generics.regions = []);
          assert (List.length generics.types = 1);
          assert (generics.const_generics = []);
          generics.types
      | T.TArray | T.TSlice | T.TStr ->
          (* Those types don't have fields *)
          raise (Failure "Unreachable"))

(** Apply a type substitution to a place *)
let place_substitute (subst : subst) (p : E.place) : E.place =
  (* There is in fact nothing to do *)
  (st_substitute_visitor subst)#visit_place () p

(** Apply a type substitution to an operand *)
let operand_substitute (subst : subst) (op : E.operand) : E.operand =
  (st_substitute_visitor subst)#visit_operand () op

(** Apply a type substitution to an rvalue *)
let rvalue_substitute (subst : subst) (rv : E.rvalue) : E.rvalue =
  (st_substitute_visitor subst)#visit_rvalue () rv

(** Apply a type substitution to an assertion *)
let assertion_substitute (subst : subst) (a : A.assertion) : A.assertion =
  (st_substitute_visitor subst)#visit_assertion () a

(** Apply a type substitution to a call *)
let call_substitute (subst : subst) (call : A.call) : A.call =
  (st_substitute_visitor subst)#visit_call () call

(** Apply a type substitution to a statement *)
let statement_substitute (subst : subst) (st : A.statement) : A.statement =
  (st_substitute_visitor subst)#visit_statement () st

(** Apply a type substitution to a function body. Return the local variables
    and the body. *)
let fun_body_substitute_in_body (subst : subst) (body : A.fun_body) :
    A.var list * A.statement =
  let locals =
    List.map
      (fun (v : A.var) -> { v with A.var_ty = ty_substitute subst v.A.var_ty })
      body.A.locals
  in
  let body = statement_substitute subst body.body in
  (locals, body)

let trait_type_constraint_substitute (subst : subst)
    (ttc : T.trait_type_constraint) : T.trait_type_constraint =
  let { T.trait_ref; generics; type_name; ty } = ttc in
  let visitor = st_substitute_visitor subst in
  let trait_ref = visitor#visit_trait_ref () trait_ref in
  let generics = visitor#visit_generic_args () generics in
  let ty = visitor#visit_ty () ty in
  { T.trait_ref; generics; type_name; ty }

(** Substitute a function signature.

    **IMPORTANT:** this function doesn't normalize the types.
 *)
let substitute_signature (asubst : T.RegionGroupId.id -> V.AbstractionId.id)
    (r_subst : T.RegionId.id -> T.RegionId.id)
    (ty_subst : T.TypeVarId.id -> T.ty)
    (cg_subst : T.ConstGenericVarId.id -> T.const_generic)
    (tr_subst : T.TraitClauseId.id -> T.trait_instance_id)
    (tr_self : T.trait_instance_id) (sg : A.fun_sig) : A.inst_fun_sig =
  let r_subst' (r : T.region) : T.region =
    match r with
    | T.RStatic | T.RErased -> r
    | T.RVar rid -> T.RVar (r_subst rid)
  in
  let subst = { r_subst = r_subst'; ty_subst; cg_subst; tr_subst; tr_self } in
  let inputs = List.map (ty_substitute subst) sg.A.inputs in
  let output = ty_substitute subst sg.A.output in
  let subst_region_group (rg : T.region_group) : A.abs_region_group =
    let id = asubst rg.id in
    let regions = List.map r_subst rg.regions in
    let parents = List.map asubst rg.parents in
    ({ id; regions; parents } : A.abs_region_group)
  in
  let regions_hierarchy = List.map subst_region_group sg.A.regions_hierarchy in
  let trait_type_constraints =
    List.map
      (trait_type_constraint_substitute subst)
      sg.preds.trait_type_constraints
  in
  { A.inputs; output; regions_hierarchy; trait_type_constraints }

(** Substitute variable identifiers in a type *)
let statement_substitute_ids (ty_subst : T.TypeVarId.id -> T.TypeVarId.id)
    (cg_subst : T.ConstGenericVarId.id -> T.ConstGenericVarId.id) (ty : T.ty) :
    T.ty =
  let open T in
  let visitor =
    object
      inherit [_] map_ty
      method visit_'r _ r = r
      method! visit_type_var_id _ id = ty_subst id
      method! visit_const_generic_var_id _ id = cg_subst id
    end
  in

  visitor#visit_ty () ty

let subst_ids_visitor (r_subst : T.RegionId.id -> T.RegionId.id)
    (ty_subst : T.TypeVarId.id -> T.TypeVarId.id)
    (cg_subst : T.ConstGenericVarId.id -> T.ConstGenericVarId.id)
    (ssubst : V.SymbolicValueId.id -> V.SymbolicValueId.id)
    (bsubst : V.BorrowId.id -> V.BorrowId.id)
    (asubst : V.AbstractionId.id -> V.AbstractionId.id) =
  object (self : 'self)
    inherit [_] C.map_env
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

let typed_value_subst_ids (r_subst : T.RegionId.id -> T.RegionId.id)
    (ty_subst : T.TypeVarId.id -> T.TypeVarId.id)
    (cg_subst : T.ConstGenericVarId.id -> T.ConstGenericVarId.id)
    (ssubst : V.SymbolicValueId.id -> V.SymbolicValueId.id)
    (bsubst : V.BorrowId.id -> V.BorrowId.id) (v : V.typed_value) :
    V.typed_value =
  let asubst _ = raise (Failure "Unreachable") in
  let vis = subst_ids_visitor r_subst ty_subst cg_subst ssubst bsubst asubst in
  vis#visit_typed_value () v

let typed_value_subst_rids (r_subst : T.RegionId.id -> T.RegionId.id)
    (v : V.typed_value) : V.typed_value =
  typed_value_subst_ids r_subst
    (fun x -> x)
    (fun x -> x)
    (fun x -> x)
    (fun x -> x)
    v

let typed_avalue_subst_ids (r_subst : T.RegionId.id -> T.RegionId.id)
    (ty_subst : T.TypeVarId.id -> T.TypeVarId.id)
    (cg_subst : T.ConstGenericVarId.id -> T.ConstGenericVarId.id)
    (ssubst : V.SymbolicValueId.id -> V.SymbolicValueId.id)
    (bsubst : V.BorrowId.id -> V.BorrowId.id) (v : V.typed_avalue) :
    V.typed_avalue =
  let asubst _ = raise (Failure "Unreachable") in
  let vis = subst_ids_visitor r_subst ty_subst cg_subst ssubst bsubst asubst in
  vis#visit_typed_avalue () v

let abs_subst_ids (r_subst : T.RegionId.id -> T.RegionId.id)
    (ty_subst : T.TypeVarId.id -> T.TypeVarId.id)
    (cg_subst : T.ConstGenericVarId.id -> T.ConstGenericVarId.id)
    (ssubst : V.SymbolicValueId.id -> V.SymbolicValueId.id)
    (bsubst : V.BorrowId.id -> V.BorrowId.id)
    (asubst : V.AbstractionId.id -> V.AbstractionId.id) (x : V.abs) : V.abs =
  let vis = subst_ids_visitor r_subst ty_subst cg_subst ssubst bsubst asubst in
  vis#visit_abs () x

let env_subst_ids (r_subst : T.RegionId.id -> T.RegionId.id)
    (ty_subst : T.TypeVarId.id -> T.TypeVarId.id)
    (cg_subst : T.ConstGenericVarId.id -> T.ConstGenericVarId.id)
    (ssubst : V.SymbolicValueId.id -> V.SymbolicValueId.id)
    (bsubst : V.BorrowId.id -> V.BorrowId.id)
    (asubst : V.AbstractionId.id -> V.AbstractionId.id) (x : C.env) : C.env =
  let vis = subst_ids_visitor r_subst ty_subst cg_subst ssubst bsubst asubst in
  vis#visit_env () x

let typed_avalue_subst_rids (r_subst : T.RegionId.id -> T.RegionId.id)
    (x : V.typed_avalue) : V.typed_avalue =
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

let env_subst_rids (r_subst : T.RegionId.id -> T.RegionId.id) (x : C.env) :
    C.env =
  let vis =
    subst_ids_visitor r_subst
      (fun x -> x)
      (fun x -> x)
      (fun x -> x)
      (fun x -> x)
      (fun x -> x)
  in
  vis#visit_env () x
