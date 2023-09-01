(** This file implements various substitution utilities to instantiate types,
    function bodies, etc.
 *)

module T = Types
module TU = TypesUtils
module V = Values
module E = Expressions
module A = LlbcAst
module C = Contexts

type ('r1, 'r2) subst = {
  r_subst : 'r1 -> 'r2;
  ty_subst : T.TypeVarId.id -> 'r2 T.ty;
  cg_subst : T.ConstGenericVarId.id -> T.const_generic;
      (** Substitution from *local* trait clause to trait instance *)
  tr_subst : T.TraitClauseId.id -> 'r2 T.trait_instance_id;
      (** Substitution for the [Self] trait instance *)
  tr_self : 'r2 T.trait_instance_id;
}

let ty_substitute_visitor (subst : ('r1, 'r2) subst) =
  object
    inherit [_] T.map_ty
    method visit_'r _ r = subst.r_subst r
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
let ty_substitute (subst : ('r1, 'r2) subst) (ty : 'r1 T.ty) : 'r2 T.ty =
  let visitor = ty_substitute_visitor subst in
  visitor#visit_ty () ty

(** **IMPORTANT**: this doesn't normalize the types. *)
let trait_ref_substitute (subst : ('r1, 'r2) subst) (tr : 'r1 T.trait_ref) :
    'r2 T.trait_ref =
  let visitor = ty_substitute_visitor subst in
  visitor#visit_trait_ref () tr

(** **IMPORTANT**: this doesn't normalize the types. *)
let generic_args_substitute (subst : ('r1, 'r2) subst) (g : 'r1 T.generic_args)
    : 'r2 T.generic_args =
  let visitor = ty_substitute_visitor subst in
  visitor#visit_generic_args () g

let erase_regions_subst : ('r, T.erased_region) subst =
  {
    r_subst = (fun _ -> T.Erased);
    ty_subst = (fun vid -> T.TypeVar vid);
    cg_subst = (fun id -> T.ConstGenericVar id);
    tr_subst = (fun id -> T.Clause id);
    tr_self = T.Self;
  }

(** Convert an {!T.rty} to an {!T.ety} by erasing the region variables *)
let erase_regions (ty : 'r T.ty) : T.ety = ty_substitute erase_regions_subst ty

(** Generate fresh regions for region variables.

    Return the list of new regions and appropriate substitutions from the
    original region variables to the fresh regions.
    
    TODO: simplify? we only need the subst [T.RegionVarId.id -> T.RegionId.id]
  *)
let fresh_regions_with_substs (region_vars : T.region_var list) :
    T.RegionId.id list
    * (T.RegionVarId.id -> T.RegionId.id)
    * (T.RegionVarId.id T.region -> T.RegionId.id T.region) =
  (* Generate fresh regions *)
  let fresh_region_ids = List.map (fun _ -> C.fresh_region_id ()) region_vars in
  (* Generate the map from region var ids to regions *)
  let ls = List.combine region_vars fresh_region_ids in
  let rid_map =
    List.fold_left
      (fun mp ((k : T.region_var), v) -> T.RegionVarId.Map.add k.T.index v mp)
      T.RegionVarId.Map.empty ls
  in
  (* Generate the substitution from region var id to region *)
  let rid_subst id = T.RegionVarId.Map.find id rid_map in
  (* Generate the substitution from region to region *)
  let r_subst r =
    match r with T.Static -> T.Static | T.Var id -> T.Var (rid_subst id)
  in
  (* Return *)
  (fresh_region_ids, rid_subst, r_subst)

(** Erase the regions in a type and perform a substitution *)
let erase_regions_substitute_types (ty_subst : T.TypeVarId.id -> T.ety)
    (cg_subst : T.ConstGenericVarId.id -> T.const_generic)
    (tr_subst : T.TraitClauseId.id -> T.etrait_instance_id)
    (tr_self : T.etrait_instance_id) (ty : 'r T.ty) : T.ety =
  let r_subst (_ : 'r) : T.erased_region = T.Erased in
  let subst = { r_subst; ty_subst; cg_subst; tr_subst; tr_self } in
  ty_substitute subst ty

(** Create a region substitution from a list of region variable ids and a list of
    regions (with which to substitute the region variable ids *)
let make_region_subst (var_ids : T.RegionVarId.id list)
    (regions : 'r T.region list) : T.RegionVarId.id T.region -> 'r T.region =
  let ls = List.combine var_ids regions in
  let mp =
    List.fold_left
      (fun mp (k, v) -> T.RegionVarId.Map.add k v mp)
      T.RegionVarId.Map.empty ls
  in
  fun r ->
    match r with
    | T.Static -> T.Static
    | T.Var id -> T.RegionVarId.Map.find id mp

let make_region_subst_from_vars (vars : T.region_var list)
    (regions : 'r T.region list) : T.RegionVarId.id T.region -> 'r T.region =
  make_region_subst
    (List.map (fun (x : T.region_var) -> x.T.index) vars)
    regions

(** Create a type substitution from a list of type variable ids and a list of
    types (with which to substitute the type variable ids) *)
let make_type_subst (var_ids : T.TypeVarId.id list) (tys : 'r T.ty list) :
    T.TypeVarId.id -> 'r T.ty =
  let ls = List.combine var_ids tys in
  let mp =
    List.fold_left
      (fun mp (k, v) -> T.TypeVarId.Map.add k v mp)
      T.TypeVarId.Map.empty ls
  in
  fun id -> T.TypeVarId.Map.find id mp

let make_type_subst_from_vars (vars : T.type_var list) (tys : 'r T.ty list) :
    T.TypeVarId.id -> 'r T.ty =
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
    (trs : 'r T.trait_ref list) : T.TraitClauseId.id -> 'r T.trait_instance_id =
  let ls = List.combine clause_ids trs in
  let mp =
    List.fold_left
      (fun mp (k, v) -> T.TraitClauseId.Map.add k (T.TraitRef v) mp)
      T.TraitClauseId.Map.empty ls
  in
  fun id -> T.TraitClauseId.Map.find id mp

let make_trait_subst_from_clauses (clauses : T.trait_clause list)
    (trs : 'r T.trait_ref list) : T.TraitClauseId.id -> 'r T.trait_instance_id =
  make_trait_subst
    (List.map (fun (x : T.trait_clause) -> x.T.clause_id) clauses)
    trs

let make_subst_from_generics (params : T.generic_params)
    (args : 'r T.region T.generic_args)
    (tr_self : 'r T.region T.trait_instance_id) :
    (T.region_var_id T.region, 'r T.region) subst =
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

let make_subst_from_generics_no_regions :
      'r.
      T.generic_params ->
      'r T.generic_args ->
      'r T.trait_instance_id ->
      (T.region_var_id T.region, 'r) subst =
 fun params args tr_self ->
  let r_subst _ = raise (Failure "Unexpected region") in
  let ty_subst = make_type_subst_from_vars params.T.types args.T.types in
  let cg_subst =
    make_const_generic_subst_from_vars params.T.const_generics
      args.T.const_generics
  in
  let tr_subst =
    make_trait_subst_from_clauses params.T.trait_clauses args.T.trait_refs
  in
  { r_subst; ty_subst; cg_subst; tr_subst; tr_self }

let make_esubst_from_generics (params : T.generic_params)
    (generics : T.egeneric_args) (tr_self : T.etrait_instance_id) =
  let r_subst _ = T.Erased in
  let ty_subst = make_type_subst_from_vars params.types generics.T.types in
  let cg_subst =
    make_const_generic_subst_from_vars params.const_generics
      generics.T.const_generics
  in
  let tr_subst =
    make_trait_subst_from_clauses params.trait_clauses generics.T.trait_refs
  in
  { r_subst; ty_subst; cg_subst; tr_subst; tr_self }

(** Instantiate the type variables in an ADT definition, and return, for
    every variant, the list of the types of its fields.

    **IMPORTANT**: this function doesn't normalize the types, you may want to
    use the [AssociatedTypes] equivalent instead.
*)
let type_decl_get_instantiated_variants_fields_rtypes (def : T.type_decl)
    (generics : T.rgeneric_args) : (T.VariantId.id option * T.rty list) list =
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
let type_decl_get_instantiated_field_rtypes (def : T.type_decl)
    (opt_variant_id : T.VariantId.id option) (generics : T.rgeneric_args) :
    T.rty list =
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
let ctx_adt_get_instantiated_field_rtypes (ctx : C.eval_ctx)
    (def_id : T.TypeDeclId.id) (opt_variant_id : T.VariantId.id option)
    (generics : T.rgeneric_args) : T.rty list =
  let def = C.ctx_lookup_type_decl ctx def_id in
  type_decl_get_instantiated_field_rtypes def opt_variant_id generics

(** Return the types of the properly instantiated ADT value (note that
    here, ADT is understood in its broad meaning: ADT, assumed value or tuple).

    **IMPORTANT**: this function doesn't normalize the types, you may want to
    use the [AssociatedTypes] equivalent instead.
 *)
let ctx_adt_value_get_instantiated_field_rtypes (ctx : C.eval_ctx)
    (adt : V.adt_value) (id : T.type_id) (generics : T.rgeneric_args) :
    T.rty list =
  match id with
  | T.AdtId id ->
      (* Retrieve the types of the fields *)
      ctx_adt_get_instantiated_field_rtypes ctx id adt.V.variant_id generics
  | T.Tuple ->
      assert (generics.regions = []);
      generics.types
  | T.Assumed aty -> (
      match aty with
      | T.Box | T.Vec ->
          assert (generics.regions = []);
          assert (List.length generics.types = 1);
          assert (generics.const_generics = []);
          generics.types
      | T.Option ->
          assert (generics.regions = []);
          assert (List.length generics.types = 1);
          assert (generics.const_generics = []);
          if adt.V.variant_id = Some T.option_some_id then generics.types
          else if adt.V.variant_id = Some T.option_none_id then []
          else raise (Failure "Unreachable")
      | T.Range ->
          assert (generics.regions = []);
          assert (List.length generics.types = 1);
          assert (generics.const_generics = []);
          generics.types
      | T.Array | T.Slice | T.Str ->
          (* Those types don't have fields *)
          raise (Failure "Unreachable"))

(** Instantiate the type variables in an ADT definition, and return the list
    of types of the fields for the chosen variant.

    **IMPORTANT**: this function doesn't normalize the types, you may want to
    use the [AssociatedTypes] equivalent instead.
*)
let type_decl_get_instantiated_field_etypes (def : T.type_decl)
    (opt_variant_id : T.VariantId.id option) (generics : T.egeneric_args) :
    T.ety list =
  (* For now, check that there are no clauses - otherwise we might need
     to normalize the types *)
  assert (def.generics.trait_clauses = []);
  (* There shouldn't be any reference to Self *)
  let tr_self : T.erased_region T.trait_instance_id =
    T.UnknownTrait __FUNCTION__
  in
  let { r_subst = _; ty_subst; cg_subst; tr_subst; tr_self } =
    make_esubst_from_generics def.T.generics generics tr_self
  in
  let fields = TU.type_decl_get_fields def opt_variant_id in
  List.map
    (fun (f : T.field) ->
      erase_regions_substitute_types ty_subst cg_subst tr_subst tr_self
        f.T.field_ty)
    fields

(** Return the types of the properly instantiated ADT's variant, provided a
    context.

    **IMPORTANT**: this function doesn't normalize the types, you may want to
    use the [AssociatedTypes] equivalent instead.
 *)
let ctx_adt_get_instantiated_field_etypes (ctx : C.eval_ctx)
    (def_id : T.TypeDeclId.id) (opt_variant_id : T.VariantId.id option)
    (generics : T.egeneric_args) : T.ety list =
  let def = C.ctx_lookup_type_decl ctx def_id in
  type_decl_get_instantiated_field_etypes def opt_variant_id generics

let statement_substitute_visitor
    (subst : (T.erased_region, T.erased_region) subst) =
  (* Keep in synch with [ty_substitute_visitor] *)
  object
    inherit [_] A.map_statement
    method! visit_'r _ r = subst.r_subst r
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

(** Apply a type substitution to a place *)
let place_substitute (subst : (T.erased_region, T.erased_region) subst)
    (p : E.place) : E.place =
  (* There is in fact nothing to do *)
  (statement_substitute_visitor subst)#visit_place () p

(** Apply a type substitution to an operand *)
let operand_substitute (subst : (T.erased_region, T.erased_region) subst)
    (op : E.operand) : E.operand =
  (statement_substitute_visitor subst)#visit_operand () op

(** Apply a type substitution to an rvalue *)
let rvalue_substitute (subst : (T.erased_region, T.erased_region) subst)
    (rv : E.rvalue) : E.rvalue =
  (statement_substitute_visitor subst)#visit_rvalue () rv

(** Apply a type substitution to an assertion *)
let assertion_substitute (subst : (T.erased_region, T.erased_region) subst)
    (a : A.assertion) : A.assertion =
  (statement_substitute_visitor subst)#visit_assertion () a

(** Apply a type substitution to a call *)
let call_substitute (subst : (T.erased_region, T.erased_region) subst)
    (call : A.call) : A.call =
  (statement_substitute_visitor subst)#visit_call () call

(** Apply a type substitution to a statement *)
let statement_substitute (subst : (T.erased_region, T.erased_region) subst)
    (st : A.statement) : A.statement =
  (statement_substitute_visitor subst)#visit_statement () st

(** Apply a type substitution to a function body. Return the local variables
    and the body. *)
let fun_body_substitute_in_body
    (subst : (T.erased_region, T.erased_region) subst) (body : A.fun_body) :
    A.var list * A.statement =
  let locals =
    List.map
      (fun (v : A.var) -> { v with A.var_ty = ty_substitute subst v.A.var_ty })
      body.A.locals
  in
  let body = statement_substitute subst body.body in
  (locals, body)

let trait_type_constraint_substitute (subst : ('r1, 'r2) subst)
    (ttc : 'r1 T.trait_type_constraint) : 'r2 T.trait_type_constraint =
  let { T.trait_ref; generics; type_name; ty } = ttc in
  let visitor = ty_substitute_visitor subst in
  let trait_ref = visitor#visit_trait_ref () trait_ref in
  let generics = visitor#visit_generic_args () generics in
  let ty = visitor#visit_ty () ty in
  { T.trait_ref; generics; type_name; ty }

(** Substitute a function signature.

    **IMPORTANT:** this function doesn't normalize the types.
 *)
let substitute_signature (asubst : T.RegionGroupId.id -> V.AbstractionId.id)
    (r_subst : T.RegionVarId.id -> T.RegionId.id)
    (ty_subst : T.TypeVarId.id -> T.rty)
    (cg_subst : T.ConstGenericVarId.id -> T.const_generic)
    (tr_subst : T.TraitClauseId.id -> T.rtrait_instance_id)
    (tr_self : T.rtrait_instance_id) (sg : A.fun_sig) : A.inst_fun_sig =
  let r_subst' (r : T.RegionVarId.id T.region) : T.RegionId.id T.region =
    match r with T.Static -> T.Static | T.Var rid -> T.Var (r_subst rid)
  in
  let subst = { r_subst = r_subst'; ty_subst; cg_subst; tr_subst; tr_self } in
  let inputs = List.map (ty_substitute subst) sg.A.inputs in
  let output = ty_substitute subst sg.A.output in
  let subst_region_group (rg : T.region_var_group) : A.abs_region_group =
    let id = asubst rg.id in
    let regions = List.map r_subst rg.regions in
    let parents = List.map asubst rg.parents in
    { id; regions; parents }
  in
  let regions_hierarchy = List.map subst_region_group sg.A.regions_hierarchy in
  let trait_type_constraints =
    List.map
      (trait_type_constraint_substitute subst)
      sg.preds.trait_type_constraints
  in
  { A.inputs; output; regions_hierarchy; trait_type_constraints }

(** Substitute variable identifiers in a type *)
let ty_substitute_ids (ty_subst : T.TypeVarId.id -> T.TypeVarId.id)
    (cg_subst : T.ConstGenericVarId.id -> T.ConstGenericVarId.id) (ty : 'r T.ty)
    : 'r T.ty =
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

(* This visitor is a mess...

   We want to write a class which visits abstractions, values, etc. *and their
   types* to substitute identifiers.

   The issue is that we derive two specialized types (ety and rty) from a
   polymorphic type (ty). Because of this, there are typing issues with
   [visit_'r] if we define a class which visits objects of types [ety] and [rty]
   while inheriting a class which visit [ty]...
*)
let subst_ids_visitor (r_subst : T.RegionId.id -> T.RegionId.id)
    (rvsubst : T.RegionVarId.id -> T.RegionVarId.id)
    (ty_subst : T.TypeVarId.id -> T.TypeVarId.id)
    (cg_subst : T.ConstGenericVarId.id -> T.ConstGenericVarId.id)
    (ssubst : V.SymbolicValueId.id -> V.SymbolicValueId.id)
    (bsubst : V.BorrowId.id -> V.BorrowId.id)
    (asubst : V.AbstractionId.id -> V.AbstractionId.id) =
  let subst_rty =
    object
      inherit [_] T.map_ty

      method visit_'r _ r =
        match r with T.Static -> T.Static | T.Var rid -> T.Var (r_subst rid)

      method! visit_type_var_id _ id = ty_subst id
      method! visit_const_generic_var_id _ id = cg_subst id
    end
  in

  let visitor =
    object (self : 'self)
      inherit [_] C.map_env
      method! visit_borrow_id _ bid = bsubst bid
      method! visit_loan_id _ bid = bsubst bid
      method! visit_ety _ ty = ty_substitute_ids ty_subst cg_subst ty
      method! visit_rty env ty = subst_rty#visit_ty env ty
      method! visit_symbolic_value_id _ id = ssubst id

      (** We *do* visit meta-values *)
      method! visit_msymbolic_value env sv = self#visit_symbolic_value env sv

      (** We *do* visit meta-values *)
      method! visit_mvalue env v = self#visit_typed_value env v

      method! visit_region_id _ id = r_subst id
      method! visit_region_var_id _ id = rvsubst id
      method! visit_abstraction_id _ id = asubst id
    end
  in

  object
    method visit_ety (x : T.ety) : T.ety = visitor#visit_ety () x
    method visit_rty (x : T.rty) : T.rty = visitor#visit_rty () x

    method visit_typed_value (x : V.typed_value) : V.typed_value =
      visitor#visit_typed_value () x

    method visit_typed_avalue (x : V.typed_avalue) : V.typed_avalue =
      visitor#visit_typed_avalue () x

    method visit_abs (x : V.abs) : V.abs = visitor#visit_abs () x
    method visit_env (env : C.env) : C.env = visitor#visit_env () env
  end

let typed_value_subst_ids (r_subst : T.RegionId.id -> T.RegionId.id)
    (rvsubst : T.RegionVarId.id -> T.RegionVarId.id)
    (ty_subst : T.TypeVarId.id -> T.TypeVarId.id)
    (cg_subst : T.ConstGenericVarId.id -> T.ConstGenericVarId.id)
    (ssubst : V.SymbolicValueId.id -> V.SymbolicValueId.id)
    (bsubst : V.BorrowId.id -> V.BorrowId.id) (v : V.typed_value) :
    V.typed_value =
  let asubst _ = raise (Failure "Unreachable") in
  (subst_ids_visitor r_subst rvsubst ty_subst cg_subst ssubst bsubst asubst)
    #visit_typed_value v

let typed_value_subst_rids (r_subst : T.RegionId.id -> T.RegionId.id)
    (v : V.typed_value) : V.typed_value =
  typed_value_subst_ids r_subst
    (fun x -> x)
    (fun x -> x)
    (fun x -> x)
    (fun x -> x)
    (fun x -> x)
    v

let typed_avalue_subst_ids (r_subst : T.RegionId.id -> T.RegionId.id)
    (rvsubst : T.RegionVarId.id -> T.RegionVarId.id)
    (ty_subst : T.TypeVarId.id -> T.TypeVarId.id)
    (cg_subst : T.ConstGenericVarId.id -> T.ConstGenericVarId.id)
    (ssubst : V.SymbolicValueId.id -> V.SymbolicValueId.id)
    (bsubst : V.BorrowId.id -> V.BorrowId.id) (v : V.typed_avalue) :
    V.typed_avalue =
  let asubst _ = raise (Failure "Unreachable") in
  (subst_ids_visitor r_subst rvsubst ty_subst cg_subst ssubst bsubst asubst)
    #visit_typed_avalue v

let abs_subst_ids (r_subst : T.RegionId.id -> T.RegionId.id)
    (rvsubst : T.RegionVarId.id -> T.RegionVarId.id)
    (ty_subst : T.TypeVarId.id -> T.TypeVarId.id)
    (cg_subst : T.ConstGenericVarId.id -> T.ConstGenericVarId.id)
    (ssubst : V.SymbolicValueId.id -> V.SymbolicValueId.id)
    (bsubst : V.BorrowId.id -> V.BorrowId.id)
    (asubst : V.AbstractionId.id -> V.AbstractionId.id) (x : V.abs) : V.abs =
  (subst_ids_visitor r_subst rvsubst ty_subst cg_subst ssubst bsubst asubst)
    #visit_abs x

let env_subst_ids (r_subst : T.RegionId.id -> T.RegionId.id)
    (rvsubst : T.RegionVarId.id -> T.RegionVarId.id)
    (ty_subst : T.TypeVarId.id -> T.TypeVarId.id)
    (cg_subst : T.ConstGenericVarId.id -> T.ConstGenericVarId.id)
    (ssubst : V.SymbolicValueId.id -> V.SymbolicValueId.id)
    (bsubst : V.BorrowId.id -> V.BorrowId.id)
    (asubst : V.AbstractionId.id -> V.AbstractionId.id) (x : C.env) : C.env =
  (subst_ids_visitor r_subst rvsubst ty_subst cg_subst ssubst bsubst asubst)
    #visit_env x

let typed_avalue_subst_rids (r_subst : T.RegionId.id -> T.RegionId.id)
    (x : V.typed_avalue) : V.typed_avalue =
  let asubst _ = raise (Failure "Unreachable") in
  (subst_ids_visitor r_subst
     (fun x -> x)
     (fun x -> x)
     (fun x -> x)
     (fun x -> x)
     (fun x -> x)
     asubst)
    #visit_typed_avalue
    x

let env_subst_rids (r_subst : T.RegionId.id -> T.RegionId.id) (x : C.env) :
    C.env =
  (subst_ids_visitor r_subst
     (fun x -> x)
     (fun x -> x)
     (fun x -> x)
     (fun x -> x)
     (fun x -> x)
     (fun x -> x))
    #visit_env
    x
