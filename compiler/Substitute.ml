(** This file implements various substitution utilities to instantiate types,
    function bodies, etc.
 *)

module T = Types
module TU = TypesUtils
module V = Values
module E = Expressions
module A = LlbcAst
module C = Contexts

(** Substitute types variables and regions in a type. *)
let ty_substitute (rsubst : 'r1 -> 'r2) (tsubst : T.TypeVarId.id -> 'r2 T.ty)
    (cgsubst : T.ConstGenericVarId.id -> T.const_generic) (ty : 'r1 T.ty) :
    'r2 T.ty =
  let open T in
  let visitor =
    object
      inherit [_] map_ty
      method visit_'r _ r = rsubst r
      method! visit_TypeVar _ id = tsubst id

      method! visit_type_var_id _ _ =
        (* We should never get here because we reimplemented [visit_TypeVar] *)
        raise (Failure "Unexpected")

      method! visit_ConstGenericVar _ id = cgsubst id

      method! visit_const_generic_var_id _ _ =
        (* We should never get here because we reimplemented [visit_Var] *)
        raise (Failure "Unexpected")
    end
  in

  visitor#visit_ty () ty

let rty_substitute (rsubst : T.RegionId.id -> T.RegionId.id)
    (tsubst : T.TypeVarId.id -> T.rty)
    (cgsubst : T.ConstGenericVarId.id -> T.const_generic) (ty : T.rty) : T.rty =
  let rsubst r =
    match r with T.Static -> T.Static | T.Var rid -> T.Var (rsubst rid)
  in
  ty_substitute rsubst tsubst cgsubst ty

let ety_substitute (tsubst : T.TypeVarId.id -> T.ety)
    (cgsubst : T.ConstGenericVarId.id -> T.const_generic) (ty : T.ety) : T.ety =
  let rsubst r = r in
  ty_substitute rsubst tsubst cgsubst ty

(** Convert an {!T.rty} to an {!T.ety} by erasing the region variables *)
let erase_regions (ty : T.rty) : T.ety =
  ty_substitute
    (fun _ -> T.Erased)
    (fun vid -> T.TypeVar vid)
    (fun id -> T.ConstGenericVar id)
    ty

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
  let rsubst r =
    match r with T.Static -> T.Static | T.Var id -> T.Var (rid_subst id)
  in
  (* Return *)
  (fresh_region_ids, rid_subst, rsubst)

(** Erase the regions in a type and substitute the type variables *)
let erase_regions_substitute_types (tsubst : T.TypeVarId.id -> T.ety)
    (cgsubst : T.ConstGenericVarId.id -> T.const_generic)
    (ty : 'r T.region T.ty) : T.ety =
  let rsubst (_ : 'r T.region) : T.erased_region = T.Erased in
  ty_substitute rsubst tsubst cgsubst ty

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

(** Instantiate the type variables in an ADT definition, and return, for
    every variant, the list of the types of its fields *)
let type_decl_get_instantiated_variants_fields_rtypes (def : T.type_decl)
    (regions : T.RegionId.id T.region list) (types : T.rty list)
    (cgs : T.const_generic list) : (T.VariantId.id option * T.rty list) list =
  let r_subst = make_region_subst_from_vars def.T.region_params regions in
  let ty_subst = make_type_subst_from_vars def.T.type_params types in
  let cg_subst =
    make_const_generic_subst_from_vars def.T.const_generic_params cgs
  in
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
      ( id,
        List.map
          (fun f -> ty_substitute r_subst ty_subst cg_subst f.T.field_ty)
          fields ))
    variants_fields

(** Instantiate the type variables in an ADT definition, and return the list
    of types of the fields for the chosen variant *)
let type_decl_get_instantiated_field_rtypes (def : T.type_decl)
    (opt_variant_id : T.VariantId.id option)
    (regions : T.RegionId.id T.region list) (types : T.rty list)
    (cgs : T.const_generic list) : T.rty list =
  let r_subst = make_region_subst_from_vars def.T.region_params regions in
  let ty_subst = make_type_subst_from_vars def.T.type_params types in
  let cg_subst =
    make_const_generic_subst_from_vars def.T.const_generic_params cgs
  in
  let fields = TU.type_decl_get_fields def opt_variant_id in
  List.map
    (fun f -> ty_substitute r_subst ty_subst cg_subst f.T.field_ty)
    fields

(** Return the types of the properly instantiated ADT's variant, provided a
    context *)
let ctx_adt_get_instantiated_field_rtypes (ctx : C.eval_ctx)
    (def_id : T.TypeDeclId.id) (opt_variant_id : T.VariantId.id option)
    (regions : T.RegionId.id T.region list) (types : T.rty list)
    (cgs : T.const_generic list) : T.rty list =
  let def = C.ctx_lookup_type_decl ctx def_id in
  type_decl_get_instantiated_field_rtypes def opt_variant_id regions types cgs

(** Return the types of the properly instantiated ADT value (note that
    here, ADT is understood in its broad meaning: ADT, assumed value or tuple) *)
let ctx_adt_value_get_instantiated_field_rtypes (ctx : C.eval_ctx)
    (adt : V.adt_value) (id : T.type_id)
    (region_params : T.RegionId.id T.region list) (type_params : T.rty list)
    (cg_params : T.const_generic list) : T.rty list =
  match id with
  | T.AdtId id ->
      (* Retrieve the types of the fields *)
      ctx_adt_get_instantiated_field_rtypes ctx id adt.V.variant_id
        region_params type_params cg_params
  | T.Tuple ->
      assert (List.length region_params = 0);
      type_params
  | T.Assumed aty -> (
      match aty with
      | T.Box | T.Vec ->
          assert (List.length region_params = 0);
          assert (List.length type_params = 1);
          assert (List.length cg_params = 0);
          type_params
      | T.Option ->
          assert (List.length region_params = 0);
          assert (List.length type_params = 1);
          assert (List.length cg_params = 0);
          if adt.V.variant_id = Some T.option_some_id then type_params
          else if adt.V.variant_id = Some T.option_none_id then []
          else raise (Failure "Unreachable")
      | T.Range ->
          assert (List.length region_params = 0);
          assert (List.length type_params = 1);
          assert (List.length cg_params = 0);
          type_params
      | T.Array | T.Slice | T.Str ->
          (* Those types don't have fields *)
          raise (Failure "Unreachable"))

(** Instantiate the type variables in an ADT definition, and return the list
    of types of the fields for the chosen variant *)
let type_decl_get_instantiated_field_etypes (def : T.type_decl)
    (opt_variant_id : T.VariantId.id option) (types : T.ety list)
    (cgs : T.const_generic list) : T.ety list =
  let ty_subst = make_type_subst_from_vars def.T.type_params types in
  let cg_subst =
    make_const_generic_subst_from_vars def.T.const_generic_params cgs
  in
  let fields = TU.type_decl_get_fields def opt_variant_id in
  List.map
    (fun f -> erase_regions_substitute_types ty_subst cg_subst f.T.field_ty)
    fields

(** Return the types of the properly instantiated ADT's variant, provided a
    context *)
let ctx_adt_get_instantiated_field_etypes (ctx : C.eval_ctx)
    (def_id : T.TypeDeclId.id) (opt_variant_id : T.VariantId.id option)
    (types : T.ety list) (cgs : T.const_generic list) : T.ety list =
  let def = C.ctx_lookup_type_decl ctx def_id in
  type_decl_get_instantiated_field_etypes def opt_variant_id types cgs

let statement_substitute_visitor (tsubst : T.TypeVarId.id -> T.ety)
    (cgsubst : T.ConstGenericVarId.id -> T.const_generic) =
  object
    inherit [_] A.map_statement
    method! visit_ety _ ty = ety_substitute tsubst cgsubst ty
    method! visit_ConstGenericVar _ id = cgsubst id

    method! visit_const_generic_var_id _ _ =
      (* We should never get here because we reimplemented [visit_Var] *)
      raise (Failure "Unexpected")
  end

(** Apply a type substitution to a place *)
let place_substitute (tsubst : T.TypeVarId.id -> T.ety)
    (cgsubst : T.ConstGenericVarId.id -> T.const_generic) (p : E.place) :
    E.place =
  (* There is in fact nothing to do *)
  (statement_substitute_visitor tsubst cgsubst)#visit_place () p

(** Apply a type substitution to an operand *)
let operand_substitute (tsubst : T.TypeVarId.id -> T.ety)
    (cgsubst : T.ConstGenericVarId.id -> T.const_generic) (op : E.operand) :
    E.operand =
  (statement_substitute_visitor tsubst cgsubst)#visit_operand () op

(** Apply a type substitution to an rvalue *)
let rvalue_substitute (tsubst : T.TypeVarId.id -> T.ety)
    (cgsubst : T.ConstGenericVarId.id -> T.const_generic) (rv : E.rvalue) :
    E.rvalue =
  (statement_substitute_visitor tsubst cgsubst)#visit_rvalue () rv

(** Apply a type substitution to an assertion *)
let assertion_substitute (tsubst : T.TypeVarId.id -> T.ety)
    (cgsubst : T.ConstGenericVarId.id -> T.const_generic) (a : A.assertion) :
    A.assertion =
  (statement_substitute_visitor tsubst cgsubst)#visit_assertion () a

(** Apply a type substitution to a call *)
let call_substitute (tsubst : T.TypeVarId.id -> T.ety)
    (cgsubst : T.ConstGenericVarId.id -> T.const_generic) (call : A.call) :
    A.call =
  (statement_substitute_visitor tsubst cgsubst)#visit_call () call

(** Apply a type substitution to a statement *)
let statement_substitute (tsubst : T.TypeVarId.id -> T.ety)
    (cgsubst : T.ConstGenericVarId.id -> T.const_generic) (st : A.statement) :
    A.statement =
  (statement_substitute_visitor tsubst cgsubst)#visit_statement () st

(** Apply a type substitution to a function body. Return the local variables
    and the body. *)
let fun_body_substitute_in_body (tsubst : T.TypeVarId.id -> T.ety)
    (cgsubst : T.ConstGenericVarId.id -> T.const_generic) (body : A.fun_body) :
    A.var list * A.statement =
  let rsubst r = r in
  let locals =
    List.map
      (fun (v : A.var) ->
        { v with A.var_ty = ty_substitute rsubst tsubst cgsubst v.A.var_ty })
      body.A.locals
  in
  let body = statement_substitute tsubst cgsubst body.body in
  (locals, body)

(** Substitute a function signature *)
let substitute_signature (asubst : T.RegionGroupId.id -> V.AbstractionId.id)
    (rsubst : T.RegionVarId.id -> T.RegionId.id)
    (tsubst : T.TypeVarId.id -> T.rty)
    (cgsubst : T.ConstGenericVarId.id -> T.const_generic) (sg : A.fun_sig) :
    A.inst_fun_sig =
  let rsubst' (r : T.RegionVarId.id T.region) : T.RegionId.id T.region =
    match r with T.Static -> T.Static | T.Var rid -> T.Var (rsubst rid)
  in
  let inputs = List.map (ty_substitute rsubst' tsubst cgsubst) sg.A.inputs in
  let output = ty_substitute rsubst' tsubst cgsubst sg.A.output in
  let subst_region_group (rg : T.region_var_group) : A.abs_region_group =
    let id = asubst rg.id in
    let regions = List.map rsubst rg.regions in
    let parents = List.map asubst rg.parents in
    { id; regions; parents }
  in
  let regions_hierarchy = List.map subst_region_group sg.A.regions_hierarchy in
  { A.regions_hierarchy; inputs; output }

(** Substitute type variable identifiers in a type *)
let ty_substitute_ids (tsubst : T.TypeVarId.id -> T.TypeVarId.id)
    (cgsubst : T.ConstGenericVarId.id -> T.ConstGenericVarId.id) (ty : 'r T.ty)
    : 'r T.ty =
  let open T in
  let visitor =
    object
      inherit [_] map_ty
      method visit_'r _ r = r
      method! visit_type_var_id _ id = tsubst id
      method! visit_const_generic_var_id _ id = cgsubst id
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
let subst_ids_visitor (rsubst : T.RegionId.id -> T.RegionId.id)
    (rvsubst : T.RegionVarId.id -> T.RegionVarId.id)
    (tsubst : T.TypeVarId.id -> T.TypeVarId.id)
    (cgsubst : T.ConstGenericVarId.id -> T.ConstGenericVarId.id)
    (ssubst : V.SymbolicValueId.id -> V.SymbolicValueId.id)
    (bsubst : V.BorrowId.id -> V.BorrowId.id)
    (asubst : V.AbstractionId.id -> V.AbstractionId.id) =
  let subst_rty =
    object
      inherit [_] T.map_ty

      method visit_'r _ r =
        match r with T.Static -> T.Static | T.Var rid -> T.Var (rsubst rid)

      method! visit_type_var_id _ id = tsubst id
      method! visit_const_generic_var_id _ id = cgsubst id
    end
  in

  let visitor =
    object (self : 'self)
      inherit [_] C.map_env
      method! visit_borrow_id _ bid = bsubst bid
      method! visit_loan_id _ bid = bsubst bid
      method! visit_ety _ ty = ty_substitute_ids tsubst cgsubst ty
      method! visit_rty env ty = subst_rty#visit_ty env ty
      method! visit_symbolic_value_id _ id = ssubst id

      (** We *do* visit meta-values *)
      method! visit_msymbolic_value env sv = self#visit_symbolic_value env sv

      (** We *do* visit meta-values *)
      method! visit_mvalue env v = self#visit_typed_value env v

      method! visit_region_id _ id = rsubst id
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

let typed_value_subst_ids (rsubst : T.RegionId.id -> T.RegionId.id)
    (rvsubst : T.RegionVarId.id -> T.RegionVarId.id)
    (tsubst : T.TypeVarId.id -> T.TypeVarId.id)
    (cgsubst : T.ConstGenericVarId.id -> T.ConstGenericVarId.id)
    (ssubst : V.SymbolicValueId.id -> V.SymbolicValueId.id)
    (bsubst : V.BorrowId.id -> V.BorrowId.id) (v : V.typed_value) :
    V.typed_value =
  let asubst _ = raise (Failure "Unreachable") in
  (subst_ids_visitor rsubst rvsubst tsubst cgsubst ssubst bsubst asubst)
    #visit_typed_value v

let typed_value_subst_rids (rsubst : T.RegionId.id -> T.RegionId.id)
    (v : V.typed_value) : V.typed_value =
  typed_value_subst_ids rsubst
    (fun x -> x)
    (fun x -> x)
    (fun x -> x)
    (fun x -> x)
    (fun x -> x)
    v

let typed_avalue_subst_ids (rsubst : T.RegionId.id -> T.RegionId.id)
    (rvsubst : T.RegionVarId.id -> T.RegionVarId.id)
    (tsubst : T.TypeVarId.id -> T.TypeVarId.id)
    (cgsubst : T.ConstGenericVarId.id -> T.ConstGenericVarId.id)
    (ssubst : V.SymbolicValueId.id -> V.SymbolicValueId.id)
    (bsubst : V.BorrowId.id -> V.BorrowId.id) (v : V.typed_avalue) :
    V.typed_avalue =
  let asubst _ = raise (Failure "Unreachable") in
  (subst_ids_visitor rsubst rvsubst tsubst cgsubst ssubst bsubst asubst)
    #visit_typed_avalue v

let abs_subst_ids (rsubst : T.RegionId.id -> T.RegionId.id)
    (rvsubst : T.RegionVarId.id -> T.RegionVarId.id)
    (tsubst : T.TypeVarId.id -> T.TypeVarId.id)
    (cgsubst : T.ConstGenericVarId.id -> T.ConstGenericVarId.id)
    (ssubst : V.SymbolicValueId.id -> V.SymbolicValueId.id)
    (bsubst : V.BorrowId.id -> V.BorrowId.id)
    (asubst : V.AbstractionId.id -> V.AbstractionId.id) (x : V.abs) : V.abs =
  (subst_ids_visitor rsubst rvsubst tsubst cgsubst ssubst bsubst asubst)
    #visit_abs x

let env_subst_ids (rsubst : T.RegionId.id -> T.RegionId.id)
    (rvsubst : T.RegionVarId.id -> T.RegionVarId.id)
    (tsubst : T.TypeVarId.id -> T.TypeVarId.id)
    (cgsubst : T.ConstGenericVarId.id -> T.ConstGenericVarId.id)
    (ssubst : V.SymbolicValueId.id -> V.SymbolicValueId.id)
    (bsubst : V.BorrowId.id -> V.BorrowId.id)
    (asubst : V.AbstractionId.id -> V.AbstractionId.id) (x : C.env) : C.env =
  (subst_ids_visitor rsubst rvsubst tsubst cgsubst ssubst bsubst asubst)
    #visit_env x

let typed_avalue_subst_rids (rsubst : T.RegionId.id -> T.RegionId.id)
    (x : V.typed_avalue) : V.typed_avalue =
  let asubst _ = raise (Failure "Unreachable") in
  (subst_ids_visitor rsubst
     (fun x -> x)
     (fun x -> x)
     (fun x -> x)
     (fun x -> x)
     (fun x -> x)
     asubst)
    #visit_typed_avalue
    x

let env_subst_rids (rsubst : T.RegionId.id -> T.RegionId.id) (x : C.env) : C.env
    =
  (subst_ids_visitor rsubst
     (fun x -> x)
     (fun x -> x)
     (fun x -> x)
     (fun x -> x)
     (fun x -> x)
     (fun x -> x))
    #visit_env
    x
