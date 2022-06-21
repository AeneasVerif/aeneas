(** This file implements various substitution utilities to instantiate types,
    function bodies, etc.
 *)

module T = Types
module TU = TypesUtils
module V = Values
module E = Expressions
module A = LlbcAst
module C = Contexts

(** Substitute types variables and regions in a type.

    TODO: we can reimplement that with visitors.
 *)
let rec ty_substitute (rsubst : 'r1 -> 'r2)
    (tsubst : T.TypeVarId.id -> 'r2 T.ty) (ty : 'r1 T.ty) : 'r2 T.ty =
  let open T in
  let subst = ty_substitute rsubst tsubst in
  (* helper *)
  match ty with
  | Adt (def_id, regions, tys) ->
      Adt (def_id, List.map rsubst regions, List.map subst tys)
  | Array aty -> Array (subst aty)
  | Slice sty -> Slice (subst sty)
  | Ref (r, ref_ty, ref_kind) -> Ref (rsubst r, subst ref_ty, ref_kind)
  (* Below variants: we technically return the same value, but because
     one has type ['r1 ty] and the other has type ['r2 ty], we need to
     deconstruct then reconstruct *)
  | Bool -> Bool
  | Char -> Char
  | Never -> Never
  | Integer int_ty -> Integer int_ty
  | Str -> Str
  | TypeVar vid -> tsubst vid

(** Convert an [rty] to an [ety] by erasing the region variables *)
let erase_regions (ty : T.rty) : T.ety =
  ty_substitute (fun _ -> T.Erased) (fun vid -> T.TypeVar vid) ty

(** Generate fresh regions for region variables.

    Return the list of new regions and appropriate substitutions from the
    original region variables to the fresh regions.
    
    TODO: simplify? we only need the subst `T.RegionVarId.id -> T.RegionId.id`
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
      (fun mp (k, v) -> T.RegionVarId.Map.add k.T.index v mp)
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
    (ty : 'r T.region T.ty) : T.ety =
  let rsubst (_ : 'r T.region) : T.erased_region = T.Erased in
  ty_substitute rsubst tsubst ty

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

(** Instantiate the type variables in an ADT definition, and return, for
    every variant, the list of the types of its fields *)
let type_decl_get_instantiated_variants_fields_rtypes (def : T.type_decl)
    (regions : T.RegionId.id T.region list) (types : T.rty list) :
    (T.VariantId.id option * T.rty list) list =
  let r_subst =
    make_region_subst
      (List.map (fun x -> x.T.index) def.T.region_params)
      regions
  in
  let ty_subst =
    make_type_subst (List.map (fun x -> x.T.index) def.T.type_params) types
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
        List.map (fun f -> ty_substitute r_subst ty_subst f.T.field_ty) fields
      ))
    variants_fields

(** Instantiate the type variables in an ADT definition, and return the list
    of types of the fields for the chosen variant *)
let type_decl_get_instantiated_field_rtypes (def : T.type_decl)
    (opt_variant_id : T.VariantId.id option)
    (regions : T.RegionId.id T.region list) (types : T.rty list) : T.rty list =
  let r_subst =
    make_region_subst
      (List.map (fun x -> x.T.index) def.T.region_params)
      regions
  in
  let ty_subst =
    make_type_subst (List.map (fun x -> x.T.index) def.T.type_params) types
  in
  let fields = TU.type_decl_get_fields def opt_variant_id in
  List.map (fun f -> ty_substitute r_subst ty_subst f.T.field_ty) fields

(** Return the types of the properly instantiated ADT's variant, provided a
    context *)
let ctx_adt_get_instantiated_field_rtypes (ctx : C.eval_ctx)
    (def_id : T.TypeDeclId.id) (opt_variant_id : T.VariantId.id option)
    (regions : T.RegionId.id T.region list) (types : T.rty list) : T.rty list =
  let def = C.ctx_lookup_type_decl ctx def_id in
  type_decl_get_instantiated_field_rtypes def opt_variant_id regions types

(** Return the types of the properly instantiated ADT value (note that
    here, ADT is understood in its broad meaning: ADT, assumed value or tuple) *)
let ctx_adt_value_get_instantiated_field_rtypes (ctx : C.eval_ctx)
    (adt : V.adt_value) (id : T.type_id)
    (region_params : T.RegionId.id T.region list) (type_params : T.rty list) :
    T.rty list =
  match id with
  | T.AdtId id ->
      (* Retrieve the types of the fields *)
      ctx_adt_get_instantiated_field_rtypes ctx id adt.V.variant_id
        region_params type_params
  | T.Tuple ->
      assert (List.length region_params = 0);
      type_params
  | T.Assumed aty -> (
      match aty with
      | T.Box | T.Vec ->
          assert (List.length region_params = 0);
          assert (List.length type_params = 1);
          type_params
      | T.Option ->
          assert (List.length region_params = 0);
          assert (List.length type_params = 1);
          if adt.V.variant_id = Some T.option_some_id then type_params
          else if adt.V.variant_id = Some T.option_none_id then []
          else failwith "Unrechable")

(** Instantiate the type variables in an ADT definition, and return the list
    of types of the fields for the chosen variant *)
let type_decl_get_instantiated_field_etypes (def : T.type_decl)
    (opt_variant_id : T.VariantId.id option) (types : T.ety list) : T.ety list =
  let ty_subst =
    make_type_subst (List.map (fun x -> x.T.index) def.T.type_params) types
  in
  let fields = TU.type_decl_get_fields def opt_variant_id in
  List.map
    (fun f -> erase_regions_substitute_types ty_subst f.T.field_ty)
    fields

(** Return the types of the properly instantiated ADT's variant, provided a
    context *)
let ctx_adt_get_instantiated_field_etypes (ctx : C.eval_ctx)
    (def_id : T.TypeDeclId.id) (opt_variant_id : T.VariantId.id option)
    (types : T.ety list) : T.ety list =
  let def = C.ctx_lookup_type_decl ctx def_id in
  type_decl_get_instantiated_field_etypes def opt_variant_id types

(** Apply a type substitution to a place *)
let place_substitute (_tsubst : T.TypeVarId.id -> T.ety) (p : E.place) : E.place
    =
  (* There is nothing to do *)
  p

(** Apply a type substitution to an operand *)
let operand_substitute (tsubst : T.TypeVarId.id -> T.ety) (op : E.operand) :
    E.operand =
  let p_subst = place_substitute tsubst in
  match op with
  | E.Copy p -> E.Copy (p_subst p)
  | E.Move p -> E.Move (p_subst p)
  | E.Constant (ety, cv) ->
      let rsubst x = x in
      E.Constant ( ty_substitute rsubst tsubst ety, cv )

(** Apply a type substitution to an rvalue *)
let rvalue_substitute (tsubst : T.TypeVarId.id -> T.ety) (rv : E.rvalue) :
    E.rvalue =
  let op_subst = operand_substitute tsubst in
  let p_subst = place_substitute tsubst in
  match rv with
  | E.Use op -> E.Use (op_subst op)
  | E.Ref (p, bkind) -> E.Ref (p_subst p, bkind)
  | E.UnaryOp (unop, op) -> E.UnaryOp (unop, op_subst op)
  | E.BinaryOp (binop, op1, op2) ->
      E.BinaryOp (binop, op_subst op1, op_subst op2)
  | E.Discriminant p -> E.Discriminant (p_subst p)
  | E.Aggregate (kind, ops) ->
      let ops = List.map op_subst ops in
      let kind =
        match kind with
        | E.AggregatedTuple -> E.AggregatedTuple
        | E.AggregatedOption (variant_id, ty) ->
            let rsubst r = r in
            E.AggregatedOption (variant_id, ty_substitute rsubst tsubst ty)
        | E.AggregatedAdt (def_id, variant_id, regions, tys) ->
            let rsubst r = r in
            E.AggregatedAdt
              ( def_id,
                variant_id,
                regions,
                List.map (ty_substitute rsubst tsubst) tys )
      in
      E.Aggregate (kind, ops)

(** Apply a type substitution to an assertion *)
let assertion_substitute (tsubst : T.TypeVarId.id -> T.ety) (a : A.assertion) :
    A.assertion =
  { A.cond = operand_substitute tsubst a.A.cond; A.expected = a.A.expected }

(** Apply a type substitution to a call *)
let call_substitute (tsubst : T.TypeVarId.id -> T.ety) (call : A.call) : A.call
    =
  let rsubst x = x in
  let type_args = List.map (ty_substitute rsubst tsubst) call.A.type_args in
  let args = List.map (operand_substitute tsubst) call.A.args in
  let dest = place_substitute tsubst call.A.dest in
  (* Putting all the paramters on purpose: we want to get a compiler error if
     something moves - we may add a field on which we need to apply a substitution *)
  {
    func = call.A.func;
    region_args = call.A.region_args;
    A.type_args;
    args;
    dest;
  }

(** Apply a type substitution to a statement *)
let rec statement_substitute (tsubst : T.TypeVarId.id -> T.ety)
    (st : A.statement) : A.statement =
  match st with
  | A.Assign (p, rvalue) ->
      let p = place_substitute tsubst p in
      let rvalue = rvalue_substitute tsubst rvalue in
      A.Assign (p, rvalue)
  | A.AssignGlobal g -> A.AssignGlobal g
  | A.FakeRead p ->
      let p = place_substitute tsubst p in
      A.FakeRead p
  | A.SetDiscriminant (p, vid) ->
      let p = place_substitute tsubst p in
      A.SetDiscriminant (p, vid)
  | A.Drop p ->
      let p = place_substitute tsubst p in
      A.Drop p
  | A.Assert assertion ->
      let assertion = assertion_substitute tsubst assertion in
      A.Assert assertion
  | A.Call call ->
      let call = call_substitute tsubst call in
      A.Call call
  | A.Panic | A.Return | A.Break _ | A.Continue _ | A.Nop -> st
  | A.Sequence (st1, st2) ->
      A.Sequence
        (statement_substitute tsubst st1, statement_substitute tsubst st2)
  | A.Switch (op, tgts) ->
      A.Switch
        (operand_substitute tsubst op, switch_targets_substitute tsubst tgts)
  | A.Loop le -> A.Loop (statement_substitute tsubst le)

(** Apply a type substitution to switch targets *)
and switch_targets_substitute (tsubst : T.TypeVarId.id -> T.ety)
    (tgts : A.switch_targets) : A.switch_targets =
  match tgts with
  | A.If (st1, st2) ->
      A.If (statement_substitute tsubst st1, statement_substitute tsubst st2)
  | A.SwitchInt (int_ty, tgts, otherwise) ->
      let tgts =
        List.map (fun (sv, st) -> (sv, statement_substitute tsubst st)) tgts
      in
      let otherwise = statement_substitute tsubst otherwise in
      A.SwitchInt (int_ty, tgts, otherwise)

(** Apply a type substitution to a function body. Return the local variables
    and the body. *)
let fun_body_substitute_in_body (tsubst : T.TypeVarId.id -> T.ety)
    (body : A.fun_body) : A.var list * A.statement =
  let rsubst r = r in
  let locals =
    List.map
      (fun v -> { v with A.var_ty = ty_substitute rsubst tsubst v.A.var_ty })
      body.A.locals
  in
  let body = statement_substitute tsubst body.body in
  (locals, body)

(** Substitute a function signature *)
let substitute_signature (asubst : T.RegionGroupId.id -> V.AbstractionId.id)
    (rsubst : T.RegionVarId.id -> T.RegionId.id)
    (tsubst : T.TypeVarId.id -> T.rty) (sg : A.fun_sig) : A.inst_fun_sig =
  let rsubst' (r : T.RegionVarId.id T.region) : T.RegionId.id T.region =
    match r with T.Static -> T.Static | T.Var rid -> T.Var (rsubst rid)
  in
  let inputs = List.map (ty_substitute rsubst' tsubst) sg.A.inputs in
  let output = ty_substitute rsubst' tsubst sg.A.output in
  let subst_region_group (rg : T.region_var_group) : A.abs_region_group =
    let id = asubst rg.id in
    let regions = List.map rsubst rg.regions in
    let parents = List.map asubst rg.parents in
    { id; regions; parents }
  in
  let regions_hierarchy = List.map subst_region_group sg.A.regions_hierarchy in
  { A.regions_hierarchy; inputs; output }
