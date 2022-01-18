module T = Types
module V = Values
open Scalars
module E = Expressions
open Errors
module C = Contexts
module Subst = Substitute
module L = Logging
open TypesUtils
open ValuesUtils
module Inv = Invariants
module S = Synthesis
open InterpreterUtils
open InterpreterExpansion
open InterpreterPaths

(** The local logger *)
let log = L.expressions_log

(** TODO: change the name *)
type eval_error = Panic

type 'a eval_result = ('a, eval_error) result

(** As long as there are symbolic values at a given place (potentially in subalues)
    which contain borrows and are primitively copyable, expand them.
    
    We use this function before copying values.
    
    Note that the place should have been prepared so that there are no remaining
    loans.
*)
let expand_primitively_copyable_at_place (config : C.config)
    (access : access_kind) (p : E.place) (ctx : C.eval_ctx) : C.eval_ctx =
  (* Small helper *)
  let rec expand ctx =
    let v = read_place_unwrap config access p ctx in
    match
      find_first_primitively_copyable_sv_with_borrows
        ctx.type_context.type_infos v
    with
    | None -> ctx
    | Some sv ->
        let ctx = expand_symbolic_value_no_branching config sv ctx in
        expand ctx
  in
  (* Apply *)
  expand ctx

(** Small utility.

    [expand_prim_copy]: if true, expand the symbolic values which are primitively
    copyable and contain borrows.
 *)
let prepare_rplace (config : C.config) (expand_prim_copy : bool)
    (access : access_kind) (p : E.place) (ctx : C.eval_ctx) :
    C.eval_ctx * V.typed_value =
  let ctx = update_ctx_along_read_place config access p ctx in
  let ctx = end_loans_at_place config access p ctx in
  let ctx =
    if expand_prim_copy then
      expand_primitively_copyable_at_place config access p ctx
    else ctx
  in
  let v = read_place_unwrap config access p ctx in
  (ctx, v)

(** Convert a constant operand value to a typed value *)
let constant_value_to_typed_value (ctx : C.eval_ctx) (ty : T.ety)
    (cv : E.operand_constant_value) : V.typed_value =
  (* Check the type while converting *)
  match (ty, cv) with
  (* Unit *)
  | T.Adt (T.Tuple, [], []), Unit -> mk_unit_value
  (* Adt with one variant and no fields *)
  | T.Adt (T.AdtId def_id, [], []), ConstantAdt def_id' ->
      assert (def_id = def_id');
      (* Check that the adt definition only has one variant with no fields,
         compute the variant id at the same time. *)
      let def = C.ctx_lookup_type_def ctx def_id in
      assert (List.length def.region_params = 0);
      assert (List.length def.type_params = 0);
      let variant_id =
        match def.kind with
        | Struct fields ->
            assert (List.length fields = 0);
            None
        | Enum variants ->
            assert (List.length variants = 1);
            let variant_id = T.VariantId.zero in
            let variant = T.VariantId.nth variants variant_id in
            assert (List.length variant.fields = 0);
            Some variant_id
      in
      let value = V.Adt { variant_id; field_values = [] } in
      { value; ty }
  (* Scalar, boolean... *)
  | T.Bool, ConstantValue (Bool v) -> { V.value = V.Concrete (Bool v); ty }
  | T.Char, ConstantValue (Char v) -> { V.value = V.Concrete (Char v); ty }
  | T.Str, ConstantValue (String v) -> { V.value = V.Concrete (String v); ty }
  | T.Integer int_ty, ConstantValue (V.Scalar v) ->
      (* Check the type and the ranges *)
      assert (int_ty == v.int_ty);
      assert (check_scalar_value_in_range v);
      { V.value = V.Concrete (V.Scalar v); ty }
  (* Remaining cases (invalid) - listing as much as we can on purpose
     (allows to catch errors at compilation if the definitions change) *)
  | _, Unit | _, ConstantAdt _ | _, ConstantValue _ ->
      failwith "Improperly typed constant value"

(** Prepare the evaluation of an operand.

    Evaluating an operand requires updating the context to get access to a
    given place (by ending borrows, expanding symbolic values...) then
    applying the operand operation (move, copy, etc.).
    
    Sometimes, we want to decouple the two operations.
    Consider the following example:
    ```
    context = {
      x -> shared_borrow l0
      y -> shared_loan {l0} v
    }
    
    dest <- f(move x, move y);
    ...
    ```
    Because of the way end_borrow is implemented, when giving back the borrow
    `l0` upon evaluating `move y`, we won't notice that `shared_borrow l0` has
    disappeared from the environment (it has been moved and not assigned yet,
    and so is hanging in "thin air").
    
    By first "preparing" the operands evaluation, we make sure no such thing
    happens. To be more precise, we make sure all the updates to borrows triggered
    by access *and* move operations have already been applied.
    
    As a side note: doing this is actually not completely necessary because when
    generating MIR, rustc introduces intermediate assignments for all the function
    parameters. Still, it is better for soundness purposes, and corresponds to
    what we do in the formal semantics.
 *)
let eval_operand_prepare (config : C.config) (ctx : C.eval_ctx) (op : E.operand)
    : C.eval_ctx * V.typed_value =
  let ctx, v =
    match op with
    | Expressions.Constant (ty, cv) ->
        let v = constant_value_to_typed_value ctx ty cv in
        (ctx, v)
    | Expressions.Copy p ->
        (* Access the value *)
        let access = Read in
        (* Expand the symbolic values, if necessary *)
        let expand_prim_copy = true in
        prepare_rplace config expand_prim_copy access p ctx
    | Expressions.Move p ->
        (* Access the value *)
        let access = Move in
        let expand_prim_copy = false in
        prepare_rplace config expand_prim_copy access p ctx
  in
  assert (not (bottom_in_value ctx.ended_regions v));
  (ctx, v)

(** Evaluate an operand. *)
let eval_operand (config : C.config) (ctx : C.eval_ctx) (op : E.operand) :
    C.eval_ctx * V.typed_value =
  (* Debug *)
  log#ldebug
    (lazy
      ("eval_operand: op: " ^ operand_to_string ctx op ^ "\n- ctx:\n"
     ^ eval_ctx_to_string ctx ^ "\n"));
  (* Evaluate *)
  match op with
  | Expressions.Constant (ty, cv) ->
      let v = constant_value_to_typed_value ctx ty cv in
      (ctx, v)
  | Expressions.Copy p ->
      (* Access the value *)
      let access = Read in
      let expand_prim_copy = true in
      let ctx, v = prepare_rplace config expand_prim_copy access p ctx in
      (* Copy the value *)
      assert (not (bottom_in_value ctx.ended_regions v));
      assert (
        Option.is_none
          (find_first_primitively_copyable_sv_with_borrows
             ctx.type_context.type_infos v));
      let allow_adt_copy = false in
      copy_value allow_adt_copy config ctx v
  | Expressions.Move p -> (
      (* Access the value *)
      let access = Move in
      let expand_prim_copy = false in
      let ctx, v = prepare_rplace config expand_prim_copy access p ctx in
      (* Move the value *)
      assert (not (bottom_in_value ctx.ended_regions v));
      let bottom : V.typed_value = { V.value = Bottom; ty = v.ty } in
      match write_place config access p bottom ctx with
      | Error _ -> failwith "Unreachable"
      | Ok ctx -> (ctx, v))

(** Small utility.

    See [eval_operand_prepare].
 *)
let eval_operands_prepare (config : C.config) (ctx : C.eval_ctx)
    (ops : E.operand list) : C.eval_ctx * V.typed_value list =
  List.fold_left_map (fun ctx op -> eval_operand_prepare config ctx op) ctx ops

(** Evaluate several operands. *)
let eval_operands (config : C.config) (ctx : C.eval_ctx) (ops : E.operand list)
    : C.eval_ctx * V.typed_value list =
  let ctx, _ = eval_operands_prepare config ctx ops in
  List.fold_left_map (fun ctx op -> eval_operand config ctx op) ctx ops

let eval_two_operands (config : C.config) (ctx : C.eval_ctx) (op1 : E.operand)
    (op2 : E.operand) : C.eval_ctx * V.typed_value * V.typed_value =
  match eval_operands config ctx [ op1; op2 ] with
  | ctx, [ v1; v2 ] -> (ctx, v1, v2)
  | _ -> failwith "Unreachable"

let eval_unary_op_concrete (config : C.config) (ctx : C.eval_ctx)
    (unop : E.unop) (op : E.operand) : (C.eval_ctx * V.typed_value) eval_result
    =
  (* Evaluate the operand *)
  let ctx, v = eval_operand config ctx op in
  (* Apply the unop *)
  match (unop, v.V.value) with
  | E.Not, V.Concrete (Bool b) ->
      Ok (ctx, { v with V.value = V.Concrete (Bool (not b)) })
  | E.Neg, V.Concrete (V.Scalar sv) -> (
      let i = Z.neg sv.V.value in
      match mk_scalar sv.int_ty i with
      | Error _ -> Error Panic
      | Ok sv -> Ok (ctx, { v with V.value = V.Concrete (V.Scalar sv) }))
  | _ -> failwith "Invalid input for unop"

let eval_unary_op_symbolic (config : C.config) (ctx : C.eval_ctx)
    (unop : E.unop) (op : E.operand) : (C.eval_ctx * V.typed_value) eval_result
    =
  (* Evaluate the operand *)
  let ctx, v = eval_operand config ctx op in
  (* Generate a fresh symbolic value to store the result *)
  let res_sv_id = C.fresh_symbolic_value_id () in
  let res_sv_ty =
    match (unop, v.V.ty) with
    | E.Not, T.Bool -> T.Bool
    | E.Neg, T.Integer int_ty -> T.Integer int_ty
    | _ -> failwith "Invalid input for unop"
  in
  let res_sv =
    { V.sv_kind = V.FunCallRet; V.sv_id = res_sv_id; sv_ty = res_sv_ty }
  in
  (* Synthesize *)
  S.synthesize_unary_op unop v res_sv;
  (* Return *)
  Ok (ctx, mk_typed_value_from_symbolic_value res_sv)

let eval_unary_op (config : C.config) (ctx : C.eval_ctx) (unop : E.unop)
    (op : E.operand) : (C.eval_ctx * V.typed_value) eval_result =
  match config.mode with
  | C.ConcreteMode -> eval_unary_op_concrete config ctx unop op
  | C.SymbolicMode -> eval_unary_op_symbolic config ctx unop op

let eval_binary_op_concrete (config : C.config) (ctx : C.eval_ctx)
    (binop : E.binop) (op1 : E.operand) (op2 : E.operand) :
    (C.eval_ctx * V.typed_value) eval_result =
  (* Evaluate the operands *)
  let ctx, v1, v2 = eval_two_operands config ctx op1 op2 in
  (* Equality check binops (Eq, Ne) accept values from a wide variety of types.
   * The remaining binops only operate on scalars. *)
  if binop = Eq || binop = Ne then (
    (* Equality operations *)
    assert (v1.ty = v2.ty);
    (* Equality/inequality check is primitive only for a subset of types *)
    assert (ty_is_primitively_copyable v1.ty);
    let b = v1 = v2 in
    Ok (ctx, { V.value = V.Concrete (Bool b); ty = T.Bool }))
  else
    (* For the non-equality operations, the input values are necessarily scalars *)
    match (v1.V.value, v2.V.value) with
    | V.Concrete (V.Scalar sv1), V.Concrete (V.Scalar sv2) -> (
        let res =
          (* There are binops which require the two operands to have the same
             type, and binops for which it is not the case.
             There are also binops which return booleans, and binops which
             return integers.
          *)
          match binop with
          | E.Lt | E.Le | E.Ge | E.Gt ->
              (* The two operands must have the same type and the result is a boolean *)
              assert (sv1.int_ty = sv2.int_ty);
              let b =
                match binop with
                | E.Lt -> Z.lt sv1.V.value sv2.V.value
                | E.Le -> Z.leq sv1.V.value sv2.V.value
                | E.Ge -> Z.geq sv1.V.value sv2.V.value
                | E.Gt -> Z.gt sv1.V.value sv2.V.value
                | E.Div | E.Rem | E.Add | E.Sub | E.Mul | E.BitXor | E.BitAnd
                | E.BitOr | E.Shl | E.Shr | E.Ne | E.Eq ->
                    failwith "Unreachable"
              in
              Ok
                ({ V.value = V.Concrete (Bool b); ty = T.Bool } : V.typed_value)
          | E.Div | E.Rem | E.Add | E.Sub | E.Mul | E.BitXor | E.BitAnd
          | E.BitOr -> (
              (* The two operands must have the same type and the result is an integer *)
              assert (sv1.int_ty = sv2.int_ty);
              let res =
                match binop with
                | E.Div ->
                    if sv2.V.value = Z.zero then Error ()
                    else mk_scalar sv1.int_ty (Z.div sv1.V.value sv2.V.value)
                | E.Rem ->
                    (* See [https://github.com/ocaml/Zarith/blob/master/z.mli] *)
                    if sv2.V.value = Z.zero then Error ()
                    else mk_scalar sv1.int_ty (Z.rem sv1.V.value sv2.V.value)
                | E.Add -> mk_scalar sv1.int_ty (Z.add sv1.V.value sv2.V.value)
                | E.Sub -> mk_scalar sv1.int_ty (Z.sub sv1.V.value sv2.V.value)
                | E.Mul -> mk_scalar sv1.int_ty (Z.mul sv1.V.value sv2.V.value)
                | E.BitXor -> raise Unimplemented
                | E.BitAnd -> raise Unimplemented
                | E.BitOr -> raise Unimplemented
                | E.Lt | E.Le | E.Ge | E.Gt | E.Shl | E.Shr | E.Ne | E.Eq ->
                    failwith "Unreachable"
              in
              match res with
              | Error err -> Error err
              | Ok sv ->
                  Ok
                    {
                      V.value = V.Concrete (V.Scalar sv);
                      ty = Integer sv1.int_ty;
                    })
          | E.Shl | E.Shr -> raise Unimplemented
          | E.Ne | E.Eq -> failwith "Unreachable"
        in
        match res with Error _ -> Error Panic | Ok v -> Ok (ctx, v))
    | _ -> failwith "Invalid inputs for binop"

let eval_binary_op_symbolic (config : C.config) (ctx : C.eval_ctx)
    (binop : E.binop) (op1 : E.operand) (op2 : E.operand) :
    (C.eval_ctx * V.typed_value) eval_result =
  (* Evaluate the operands *)
  let ctx, v1, v2 = eval_two_operands config ctx op1 op2 in
  (* Generate a fresh symbolic value to store the result *)
  let res_sv_id = C.fresh_symbolic_value_id () in
  let res_sv_ty =
    if binop = Eq || binop = Ne then (
      (* Equality operations *)
      assert (v1.ty = v2.ty);
      (* Equality/inequality check is primitive only for a subset of types *)
      assert (ty_is_primitively_copyable v1.ty);
      T.Bool)
    else
      (* Other operations: input types are integers *)
      match (v1.V.ty, v2.V.ty) with
      | T.Integer int_ty1, T.Integer int_ty2 -> (
          match binop with
          | E.Lt | E.Le | E.Ge | E.Gt ->
              assert (int_ty1 = int_ty2);
              T.Bool
          | E.Div | E.Rem | E.Add | E.Sub | E.Mul | E.BitXor | E.BitAnd
          | E.BitOr ->
              assert (int_ty1 = int_ty2);
              T.Integer int_ty1
          | E.Shl | E.Shr -> raise Unimplemented
          | E.Ne | E.Eq -> failwith "Unreachable")
      | _ -> failwith "Invalid inputs for binop"
  in
  let res_sv =
    { V.sv_kind = V.FunCallRet; V.sv_id = res_sv_id; sv_ty = res_sv_ty }
  in
  (* Synthesize *)
  S.synthesize_binary_op binop v1 v2 res_sv;
  (* Return *)
  Ok (ctx, mk_typed_value_from_symbolic_value res_sv)

let eval_binary_op (config : C.config) (ctx : C.eval_ctx) (binop : E.binop)
    (op1 : E.operand) (op2 : E.operand) :
    (C.eval_ctx * V.typed_value) eval_result =
  match config.mode with
  | C.ConcreteMode -> eval_binary_op_concrete config ctx binop op1 op2
  | C.SymbolicMode -> eval_binary_op_symbolic config ctx binop op1 op2

(** Evaluate the discriminant of a concrete (i.e., non symbolic) ADT value *)
let eval_rvalue_discriminant_concrete (config : C.config) (p : E.place)
    (ctx : C.eval_ctx) : C.eval_ctx * V.typed_value =
  (* Note that discriminant values have type `isize` *)
  (* Access the value *)
  let access = Read in
  let expand_prim_copy = false in
  let ctx, v = prepare_rplace config expand_prim_copy access p ctx in
  match v.V.value with
  | Adt av -> (
      match av.variant_id with
      | None ->
          failwith "Invalid input for `discriminant`: structure instead of enum"
      | Some variant_id -> (
          let id = Z.of_int (T.VariantId.to_int variant_id) in
          match mk_scalar Isize id with
          | Error _ ->
              failwith "Disciminant id out of range"
              (* Should really never happen *)
          | Ok sv ->
              (ctx, { V.value = V.Concrete (V.Scalar sv); ty = Integer Isize }))
      )
  | _ -> failwith "Invalid input for `discriminant`"

let eval_rvalue_discriminant (config : C.config) (p : E.place)
    (ctx : C.eval_ctx) : (C.eval_ctx * V.typed_value) list =
  S.synthesize_eval_rvalue_discriminant p;
  (* Note that discriminant values have type `isize` *)
  (* Access the value *)
  let access = Read in
  let expand_prim_copy = false in
  let ctx, v = prepare_rplace config expand_prim_copy access p ctx in
  match v.V.value with
  | Adt _ -> [ eval_rvalue_discriminant_concrete config p ctx ]
  | Symbolic sv ->
      (* Expand the symbolic value - may lead to branching *)
      let ctxl = expand_symbolic_enum_value config sv ctx in
      (* This time the value is concrete: reevaluate *)
      List.map (eval_rvalue_discriminant_concrete config p) ctxl
  | _ -> failwith "Invalid input for `discriminant`"

let eval_rvalue_ref (config : C.config) (ctx : C.eval_ctx) (p : E.place)
    (bkind : E.borrow_kind) : C.eval_ctx * V.typed_value =
  S.synthesize_eval_rvalue_ref p bkind;
  match bkind with
  | E.Shared | E.TwoPhaseMut ->
      (* Access the value *)
      let access = if bkind = E.Shared then Read else Write in
      let expand_prim_copy = false in
      let ctx, v = prepare_rplace config expand_prim_copy access p ctx in
      (* Compute the rvalue - simply a shared borrow with a fresh id *)
      let bid = C.fresh_borrow_id () in
      (* Note that the reference is *mutable* if we do a two-phase borrow *)
      let rv_ty =
        T.Ref (T.Erased, v.ty, if bkind = E.Shared then Shared else Mut)
      in
      let bc =
        if bkind = E.Shared then V.SharedBorrow bid
        else V.InactivatedMutBorrow bid
      in
      let rv : V.typed_value = { V.value = V.Borrow bc; ty = rv_ty } in
      (* Compute the value with which to replace the value at place p *)
      let nv =
        match v.V.value with
        | V.Loan (V.SharedLoan (bids, sv)) ->
            (* Shared loan: insert the new borrow id *)
            let bids1 = V.BorrowId.Set.add bid bids in
            { v with V.value = V.Loan (V.SharedLoan (bids1, sv)) }
        | _ ->
            (* Not a shared loan: add a wrapper *)
            let v' = V.Loan (V.SharedLoan (V.BorrowId.Set.singleton bid, v)) in
            { v with V.value = v' }
      in
      (* Update the value in the context *)
      let ctx = write_place_unwrap config access p nv ctx in
      (* Return *)
      (ctx, rv)
  | E.Mut ->
      (* Access the value *)
      let access = Write in
      let expand_prim_copy = false in
      let ctx, v = prepare_rplace config expand_prim_copy access p ctx in
      (* Compute the rvalue - wrap the value in a mutable borrow with a fresh id *)
      let bid = C.fresh_borrow_id () in
      let rv_ty = T.Ref (T.Erased, v.ty, Mut) in
      let rv : V.typed_value =
        { V.value = V.Borrow (V.MutBorrow (bid, v)); ty = rv_ty }
      in
      (* Compute the value with which to replace the value at place p *)
      let nv = { v with V.value = V.Loan (V.MutLoan bid) } in
      (* Update the value in the context *)
      let ctx = write_place_unwrap config access p nv ctx in
      (* Return *)
      (ctx, rv)

let eval_rvalue_aggregate (config : C.config) (ctx : C.eval_ctx)
    (aggregate_kind : E.aggregate_kind) (ops : E.operand list) :
    C.eval_ctx * V.typed_value =
  S.synthesize_eval_rvalue_aggregate aggregate_kind ops;
  (* Evaluate the operands *)
  let ctx, values = eval_operands config ctx ops in
  (* Match on the aggregate kind *)
  match aggregate_kind with
  | E.AggregatedTuple ->
      let tys = List.map (fun (v : V.typed_value) -> v.V.ty) values in
      let v = V.Adt { variant_id = None; field_values = values } in
      let ty = T.Adt (T.Tuple, [], tys) in
      (ctx, { V.value = v; ty })
  | E.AggregatedAdt (def_id, opt_variant_id, regions, types) ->
      (* Sanity checks *)
      let type_def = C.ctx_lookup_type_def ctx def_id in
      assert (List.length type_def.region_params = List.length regions);
      let expected_field_types =
        Subst.ctx_adt_get_instantiated_field_etypes ctx def_id opt_variant_id
          types
      in
      assert (
        expected_field_types
        = List.map (fun (v : V.typed_value) -> v.V.ty) values);
      (* Construct the value *)
      let av : V.adt_value =
        { V.variant_id = opt_variant_id; V.field_values = values }
      in
      let aty = T.Adt (T.AdtId def_id, regions, types) in
      (ctx, { V.value = Adt av; ty = aty })

(** Evaluate an rvalue which is not a discriminant.

    We define a function for this specific case, because evaluating
    a discriminant might lead to branching (if we evaluate the discriminant
    of a symbolic enumeration value), while it is not the case for the
    other rvalues.
 *)
let eval_rvalue_non_discriminant (config : C.config) (ctx : C.eval_ctx)
    (rvalue : E.rvalue) : (C.eval_ctx * V.typed_value) eval_result =
  match rvalue with
  | E.Use op -> Ok (eval_operand config ctx op)
  | E.Ref (p, bkind) -> Ok (eval_rvalue_ref config ctx p bkind)
  | E.UnaryOp (unop, op) -> eval_unary_op config ctx unop op
  | E.BinaryOp (binop, op1, op2) -> eval_binary_op config ctx binop op1 op2
  | E.Aggregate (aggregate_kind, ops) ->
      Ok (eval_rvalue_aggregate config ctx aggregate_kind ops)
  | E.Discriminant _ -> failwith "Unreachable"

(** Evaluate an rvalue in a given context: return the updated context and
    the computed value.

    Returns a list of pairs (new context, computed rvalue) because
    `discriminant` might lead to a branching in case it is applied
    on a symbolic enumeration value.
*)
let eval_rvalue (config : C.config) (ctx : C.eval_ctx) (rvalue : E.rvalue) :
    (C.eval_ctx * V.typed_value) list eval_result =
  match rvalue with
  | E.Discriminant p -> Ok (eval_rvalue_discriminant config p ctx)
  | _ -> (
      match eval_rvalue_non_discriminant config ctx rvalue with
      | Error e -> Error e
      | Ok res -> Ok [ res ])
