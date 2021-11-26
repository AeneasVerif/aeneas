(** This file implements various substitution utilities to instantiate types,
    function bodies, etc.
 *)

module T = Types
module V = Values
module E = Expressions
module A = CfimAst
module C = Contexts

(** Substitute types variables and regions in a type *)
let rec ty_substitute (rsubst : 'r1 -> 'r2)
    (tsubst : T.TypeVarId.id -> 'r2 T.ty) (ty : 'r1 T.ty) : 'r2 T.ty =
  let open T in
  let subst = ty_substitute rsubst tsubst in
  (* helper *)
  match ty with
  | Adt (def_id, regions, tys) ->
      Adt (def_id, List.map rsubst regions, List.map subst tys)
  | Tuple tys -> Tuple (List.map subst tys)
  | Array aty -> Array (subst aty)
  | Slice sty -> Slice (subst sty)
  | Ref (r, ref_ty, ref_kind) -> Ref (rsubst r, subst ref_ty, ref_kind)
  | Assumed (aty, regions, tys) ->
      Assumed (aty, List.map rsubst regions, List.map subst tys)
      (* Below variants: we technically return the same value, but because
         one has type ['r1 ty] and the other has type ['r2 ty] we need to
         deconstruct then reconstruct *)
  | Bool -> Bool
  | Char -> Char
  | Never -> Never
  | Integer int_ty -> Integer int_ty
  | Str -> Str
  | TypeVar vid -> tsubst vid

(** Erase the regions in a type and substitute the type variables *)
let erase_regions_substitute_types (tsubst : T.TypeVarId.id -> T.ety)
    (ty : T.rty) : T.ety =
  let rsubst (r : T.RegionVarId.id T.region) : T.erased_region = T.Erased in
  ty_substitute rsubst tsubst ty

(** Create a type substitution from a list of type variable ids and a list of
    types (with which to substitute the type variable ids *)
let make_type_subst (var_ids : T.TypeVarId.id list) (tys : 'r T.ty list) :
    T.TypeVarId.id -> 'r T.ty =
  let ls = List.combine var_ids tys in
  let mp =
    List.fold_left
      (fun mp (k, v) -> T.TypeVarId.Map.add k v mp)
      T.TypeVarId.Map.empty ls
  in
  fun id -> T.TypeVarId.Map.find id mp

(** Retrieve the list of fields for the given variant of a [type_def].

    Raises [Invalid_argument] if the arguments are incorrect.

    TODO: move
 *)
let type_def_get_fields (def : T.type_def)
    (opt_variant_id : T.VariantId.id option) : T.field T.FieldId.vector =
  match (def.kind, opt_variant_id) with
  | Enum variants, Some variant_id ->
      (T.VariantId.nth variants variant_id).fields
  | Struct fields, None -> fields
  | _ ->
      raise
        (Invalid_argument
           "The variant id should be [Some] if and only if the definition is \
            an enumeration")

(** Instantiate the type variables in an ADT definition, and return the list
    of types of the fields for the chosen variant *)
let type_def_get_instantiated_field_type (def : T.type_def)
    (opt_variant_id : T.VariantId.id option) (types : T.ety list) :
    T.ety T.FieldId.vector =
  let ty_subst =
    make_type_subst
      (List.map
         (fun x -> x.T.tv_index)
         (T.TypeVarId.vector_to_list def.T.type_params))
      types
  in
  let fields = type_def_get_fields def opt_variant_id in
  T.FieldId.map
    (fun f -> erase_regions_substitute_types ty_subst f.T.field_ty)
    fields

(** Return the types of the properly instantiated ADT's variant, provided a
    context *)
let ctx_adt_get_instantiated_field_types (ctx : C.eval_ctx)
    (def_id : T.TypeDefId.id) (opt_variant_id : T.VariantId.id option)
    (types : T.ety list) : T.ety T.FieldId.vector =
  let def = C.ctx_lookup_type_def ctx def_id in
  type_def_get_instantiated_field_type def opt_variant_id types

(** Apply a type substitution to a place *)
let place_substitute (_tsubst : T.TypeVarId.id -> T.ety) (p : E.place) : E.place
    =
  (* There is nothing to do *)
  p

(** Apply a type substitution to an operand constant value *)
let operand_constant_value_substitute (_tsubst : T.TypeVarId.id -> T.ety)
    (op : E.operand_constant_value) : E.operand_constant_value =
  (* There is nothing to do *)
  op

(** Apply a type substitution to an operand *)
let operand_substitute (tsubst : T.TypeVarId.id -> T.ety) (op : E.operand) :
    E.operand =
  let p_subst = place_substitute tsubst in
  match op with
  | E.Copy p -> E.Copy (p_subst p)
  | E.Move p -> E.Move (p_subst p)
  | E.Constant (ety, cv) ->
      let rsubst x = x in
      E.Constant
        ( ty_substitute rsubst tsubst ety,
          operand_constant_value_substitute tsubst cv )

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
        | E.AggregatedAdt (def_id, variant_id, regions, tys) ->
            let rsubst x = x in
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
  let type_params = List.map (ty_substitute rsubst tsubst) call.A.type_params in
  let args = List.map (operand_substitute tsubst) call.A.args in
  let dest = place_substitute tsubst call.A.dest in
  (* Putting all the paramters on purpose: we want to get a compiler error if
     something moves - we may add a field on which we need to apply a substitution *)
  {
    func = call.A.func;
    region_params = call.A.region_params;
    A.type_params;
    args;
    dest;
  }

(** Apply a type substitution to a statement *)
let statement_substitute (tsubst : T.TypeVarId.id -> T.ety) (st : A.statement) :
    A.statement =
  match st with
  | A.Assign (p, rvalue) ->
      let p = place_substitute tsubst p in
      let rvalue = rvalue_substitute tsubst rvalue in
      A.Assign (p, rvalue)
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

(** Apply a type substitution to an expression *)
let rec expression_substitute (tsubst : T.TypeVarId.id -> T.ety)
    (e : A.expression) : A.expression =
  match e with
  | A.Statement st -> A.Statement (statement_substitute tsubst st)
  | A.Sequence (e1, e2) ->
      A.Sequence
        (expression_substitute tsubst e1, expression_substitute tsubst e2)
  | A.Switch (op, tgts) ->
      A.Switch
        (operand_substitute tsubst op, switch_targets_substitute tsubst tgts)
  | A.Loop le -> A.Loop (expression_substitute tsubst le)

(** Apply a type substitution to switch targets *)
and switch_targets_substitute (tsubst : T.TypeVarId.id -> T.ety)
    (tgts : A.switch_targets) : A.switch_targets =
  match tgts with
  | A.If (e1, e2) ->
      A.If (expression_substitute tsubst e1, expression_substitute tsubst e2)
  | A.SwitchInt (int_ty, tgts, otherwise) ->
      let tgts =
        List.map (fun (sv, e) -> (sv, expression_substitute tsubst e)) tgts
      in
      let otherwise = expression_substitute tsubst otherwise in
      A.SwitchInt (int_ty, tgts, otherwise)

(** Apply a type substitution to a function body. Return the local variables
    and the body. *)
let fun_def_substitute_in_body (tsubst : T.TypeVarId.id -> T.ety)
    (def : A.fun_def) : V.var V.VarId.vector * A.expression =
  let rsubst r = r in
  let locals =
    V.VarId.map
      (fun v -> { v with V.var_ty = ty_substitute rsubst tsubst v.V.var_ty })
      def.A.locals
  in
  let body = expression_substitute tsubst def.body in
  (locals, body)
