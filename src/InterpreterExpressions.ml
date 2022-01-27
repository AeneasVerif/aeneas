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
module S = SynthesizeSymbolic
open Cps
open InterpreterUtils
open InterpreterExpansion
open InterpreterPaths

(** The local logger *)
let log = L.expressions_log

(** As long as there are symbolic values at a given place (potentially in subvalues)
    which contain borrows and are primitively copyable, expand them.
    
    We use this function before copying values.
    
    Note that the place should have been prepared so that there are no remaining
    loans.
*)
let expand_primitively_copyable_at_place (config : C.config)
    (access : access_kind) (p : E.place) : cm_fun =
 fun cf ctx ->
  (* Small helper *)
  let rec expand : cm_fun =
   fun cf ctx ->
    let v = read_place_unwrap config access p ctx in
    match
      find_first_primitively_copyable_sv_with_borrows
        ctx.type_context.type_infos v
    with
    | None -> cf ctx
    | Some sv ->
        let cc =
          expand_symbolic_value_no_branching config sv
            (Some (S.mk_mplace p ctx))
        in
        comp cc expand cf ctx
  in
  (* Apply *)
  expand cf ctx

(** Small utility.

    [expand_prim_copy]: if true, expand the symbolic values which are primitively
    copyable and contain borrows.
 *)
let prepare_rplace (config : C.config) (expand_prim_copy : bool)
    (access : access_kind) (p : E.place) (cf : V.typed_value -> m_fun) : m_fun =
 fun ctx ->
  let cc = update_ctx_along_read_place config access p in
  let cc = comp cc (end_loans_at_place config access p) in
  let cc =
    if expand_prim_copy then
      comp cc (expand_primitively_copyable_at_place config access p)
    else cc
  in
  let read_place cf : m_fun =
   fun ctx ->
    let v = read_place_unwrap config access p ctx in
    cf v ctx
  in
  comp cc read_place cf ctx

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
let eval_operand_prepare (config : C.config) (op : E.operand)
    (cf : V.typed_value -> m_fun) : m_fun =
 fun ctx ->
  let prepare (cf : V.typed_value -> m_fun) : m_fun =
   fun ctx ->
    match op with
    | Expressions.Constant (ty, cv) ->
        let v = constant_value_to_typed_value ctx ty cv in
        cf v ctx
    | Expressions.Copy p ->
        (* Access the value *)
        let access = Read in
        (* Expand the symbolic values, if necessary *)
        let expand_prim_copy = true in
        prepare_rplace config expand_prim_copy access p cf ctx
    | Expressions.Move p ->
        (* Access the value *)
        let access = Move in
        let expand_prim_copy = false in
        prepare_rplace config expand_prim_copy access p cf ctx
  in
  (* Sanity check *)
  let check cf v : m_fun =
   fun ctx ->
    assert (not (bottom_in_value ctx.ended_regions v));
    cf v ctx
  in
  (* Compose and apply *)
  comp prepare check cf ctx

(** Evaluate an operand. *)
let eval_operand (config : C.config) (op : E.operand)
    (cf : V.typed_value -> m_fun) : m_fun =
 fun ctx ->
  (* Debug *)
  log#ldebug
    (lazy
      ("eval_operand: op: " ^ operand_to_string ctx op ^ "\n- ctx:\n"
     ^ eval_ctx_to_string ctx ^ "\n"));
  (* Evaluate *)
  match op with
  | Expressions.Constant (ty, cv) ->
      let v = constant_value_to_typed_value ctx ty cv in
      cf v ctx
  | Expressions.Copy p ->
      (* Access the value *)
      let access = Read in
      let expand_prim_copy = true in
      let cc = prepare_rplace config expand_prim_copy access p in
      (* Copy the value *)
      let copy cf v : m_fun =
       fun ctx ->
        (* Sanity checks *)
        assert (not (bottom_in_value ctx.ended_regions v));
        assert (
          Option.is_none
            (find_first_primitively_copyable_sv_with_borrows
               ctx.type_context.type_infos v));
        let allow_adt_copy = false in
        (* Actually perform the copy *)
        let ctx, v = copy_value allow_adt_copy config ctx v in
        (* Continue *)
        cf v ctx
      in
      (* Compose and apply *)
      comp cc copy cf ctx
  | Expressions.Move p ->
      (* Access the value *)
      let access = Move in
      let expand_prim_copy = false in
      let cc = prepare_rplace config expand_prim_copy access p in
      (* Move the value *)
      let move cf v : m_fun =
       fun ctx ->
        assert (not (bottom_in_value ctx.ended_regions v));
        let bottom : V.typed_value = { V.value = Bottom; ty = v.ty } in
        match write_place config access p bottom ctx with
        | Error _ -> failwith "Unreachable"
        | Ok ctx -> cf v ctx
      in
      (* Compose and apply *)
      comp cc move cf ctx

(** Small utility.

    See [eval_operand_prepare].
 *)
let eval_operands_prepare (config : C.config) (ops : E.operand list)
    (cf : V.typed_value list -> m_fun) : m_fun =
  fold_left_apply_continuation (eval_operand_prepare config) ops cf

(** Evaluate several operands. *)
let eval_operands (config : C.config) (ops : E.operand list)
    (cf : V.typed_value list -> m_fun) : m_fun =
 fun ctx ->
  (* Prepare the operands *)
  let prepare = eval_operands_prepare config ops in
  (* Evaluate the operands *)
  let eval = fold_left_apply_continuation (eval_operand config) ops in
  (* Compose and apply *)
  comp prepare (fun cf (_ : V.typed_value list) -> eval cf) cf ctx

let eval_two_operands (config : C.config) (op1 : E.operand) (op2 : E.operand)
    (cf : V.typed_value * V.typed_value -> m_fun) : m_fun =
  let eval_op = eval_operands config [ op1; op2 ] in
  let use_res cf res =
    match res with [ v1; v2 ] -> cf (v1, v2) | _ -> failwith "Unreachable"
  in
  comp eval_op use_res cf

let eval_unary_op_concrete (config : C.config) (unop : E.unop) (op : E.operand)
    (cf : (V.typed_value, eval_error) result -> m_fun) : m_fun =
  (* Evaluate the operand *)
  let eval_op = eval_operand config op in
  (* Apply the unop *)
  let apply cf (v : V.typed_value) : m_fun =
    match (unop, v.V.value) with
    | E.Not, V.Concrete (Bool b) ->
        cf (Ok { v with V.value = V.Concrete (Bool (not b)) })
    | E.Neg, V.Concrete (V.Scalar sv) -> (
        let i = Z.neg sv.V.value in
        match mk_scalar sv.int_ty i with
        | Error _ -> cf (Error EPanic)
        | Ok sv -> cf (Ok { v with V.value = V.Concrete (V.Scalar sv) }))
    | _ -> failwith "Invalid input for unop"
  in
  comp eval_op apply cf

let eval_unary_op_symbolic (config : C.config) (unop : E.unop) (op : E.operand)
    (cf : (V.typed_value, eval_error) result -> m_fun) : m_fun =
 fun ctx ->
  (* Evaluate the operand *)
  let eval_op = eval_operand config op in
  (* Generate a fresh symbolic value to store the result *)
  let apply cf (v : V.typed_value) : m_fun =
   fun ctx ->
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
    (* Call the continuation *)
    let expr = cf (Ok (mk_typed_value_from_symbolic_value res_sv)) ctx in
    (* Synthesize the symbolic AST *)
    S.synthesize_unary_op unop v
      (S.mk_opt_place_from_op op ctx)
      res_sv None expr
  in
  (* Compose and apply *)
  comp eval_op apply cf ctx

let eval_unary_op (config : C.config) (unop : E.unop) (op : E.operand)
    (cf : (V.typed_value, eval_error) result -> m_fun) : m_fun =
  match config.mode with
  | C.ConcreteMode -> eval_unary_op_concrete config unop op cf
  | C.SymbolicMode -> eval_unary_op_symbolic config unop op cf

(** Small helper for [eval_binary_op_concrete]: computes the result of applying
    the binop *after* the operands have been successfully evaluated
 *)
let eval_binary_op_concrete_compute (binop : E.binop) (v1 : V.typed_value)
    (v2 : V.typed_value) : (V.typed_value, eval_error) result =
  (* Equality check binops (Eq, Ne) accept values from a wide variety of types.
   * The remaining binops only operate on scalars. *)
  if binop = Eq || binop = Ne then (
    (* Equality operations *)
    assert (v1.ty = v2.ty);
    (* Equality/inequality check is primitive only for a subset of types *)
    assert (ty_is_primitively_copyable v1.ty);
    let b = v1 = v2 in
    Ok { V.value = V.Concrete (Bool b); ty = T.Bool })
  else
    (* For the non-equality operations, the input values are necessarily scalars *)
    match (v1.V.value, v2.V.value) with
    | V.Concrete (V.Scalar sv1), V.Concrete (V.Scalar sv2) -> (
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
            Ok ({ V.value = V.Concrete (Bool b); ty = T.Bool } : V.typed_value)
        | E.Div | E.Rem | E.Add | E.Sub | E.Mul | E.BitXor | E.BitAnd | E.BitOr
          -> (
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
            | Error _ -> Error EPanic
            | Ok sv ->
                Ok
                  {
                    V.value = V.Concrete (V.Scalar sv);
                    ty = Integer sv1.int_ty;
                  })
        | E.Shl | E.Shr -> raise Unimplemented
        | E.Ne | E.Eq -> failwith "Unreachable")
    | _ -> failwith "Invalid inputs for binop"

let eval_binary_op_concrete (config : C.config) (binop : E.binop)
    (op1 : E.operand) (op2 : E.operand)
    (cf : (V.typed_value, eval_error) result -> m_fun) : m_fun =
  (* Evaluate the operands *)
  let eval_ops = eval_two_operands config op1 op2 in
  (* Compute the result of the binop *)
  let compute cf (res : V.typed_value * V.typed_value) =
    let v1, v2 = res in
    cf (eval_binary_op_concrete_compute binop v1 v2)
  in
  (* Compose and apply *)
  comp eval_ops compute cf

let eval_binary_op_symbolic (config : C.config) (binop : E.binop)
    (op1 : E.operand) (op2 : E.operand)
    (cf : (V.typed_value, eval_error) result -> m_fun) : m_fun =
 fun ctx ->
  (* Evaluate the operands *)
  let eval_ops = eval_two_operands config op1 op2 in
  (* Compute the result of applying the binop *)
  let compute cf ((v1, v2) : V.typed_value * V.typed_value) : m_fun =
   fun ctx ->
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
    (* Call the continuattion *)
    let v = mk_typed_value_from_symbolic_value res_sv in
    let expr = cf (Ok v) ctx in
    (* Synthesize the symbolic AST *)
    let p1 = S.mk_opt_place_from_op op1 ctx in
    let p2 = S.mk_opt_place_from_op op2 ctx in
    S.synthesize_binary_op binop v1 p1 v2 p2 res_sv None expr
  in
  (* Compose and apply *)
  comp eval_ops compute cf ctx

let eval_binary_op (config : C.config) (binop : E.binop) (op1 : E.operand)
    (op2 : E.operand) (cf : (V.typed_value, eval_error) result -> m_fun) : m_fun
    =
  match config.mode with
  | C.ConcreteMode -> eval_binary_op_concrete config binop op1 op2 cf
  | C.SymbolicMode -> eval_binary_op_symbolic config binop op1 op2 cf

(** Evaluate the discriminant of a concrete (i.e., non symbolic) ADT value *)
let eval_rvalue_discriminant_concrete (config : C.config) (p : E.place)
    (cf : V.typed_value -> m_fun) : m_fun =
  (* Note that discriminant values have type `isize` *)
  (* Access the value *)
  let access = Read in
  let expand_prim_copy = false in
  let prepare = prepare_rplace config expand_prim_copy access p in
  (* Read the value *)
  let read (cf : V.typed_value -> m_fun) (v : V.typed_value) : m_fun =
    match v.V.value with
    | Adt av -> (
        match av.variant_id with
        | None ->
            failwith
              "Invalid input for `discriminant`: structure instead of enum"
        | Some variant_id -> (
            let id = Z.of_int (T.VariantId.to_int variant_id) in
            match mk_scalar Isize id with
            | Error _ -> failwith "Disciminant id out of range"
            (* Should really never happen *)
            | Ok sv ->
                cf { V.value = V.Concrete (V.Scalar sv); ty = Integer Isize }))
    | _ -> failwith "Invalid input for `discriminant`"
  in
  (* Compose and apply *)
  comp prepare read cf

(** Evaluate the discriminant of an ADT value.

    Might lead to branching, if the value is symbolic.
 *)
let eval_rvalue_discriminant (config : C.config) (p : E.place)
    (cf : V.typed_value -> m_fun) : m_fun =
 fun ctx ->
  log#ldebug (lazy "eval_rvalue_discriminant");
  (* Note that discriminant values have type `isize` *)
  (* Access the value *)
  let access = Read in
  let expand_prim_copy = false in
  let prepare = prepare_rplace config expand_prim_copy access p in
  (* Read the value *)
  let read (cf : V.typed_value -> m_fun) (v : V.typed_value) : m_fun =
   fun ctx ->
    match v.V.value with
    | Adt _ -> eval_rvalue_discriminant_concrete config p cf ctx
    | Symbolic sv ->
        (* Expand the symbolic value - may lead to branching *)
        let allow_branching = true in
        let cc =
          expand_symbolic_value config allow_branching sv
            (Some (S.mk_mplace p ctx))
        in
        (* This time the value is concrete: reevaluate *)
        comp cc (eval_rvalue_discriminant_concrete config p) cf ctx
    | _ -> failwith "Invalid input for `discriminant`"
  in
  (* Compose and apply *)
  comp prepare read cf ctx

let eval_rvalue_ref (config : C.config) (p : E.place) (bkind : E.borrow_kind)
    (cf : V.typed_value -> m_fun) : m_fun =
 fun ctx ->
  match bkind with
  | E.Shared | E.TwoPhaseMut ->
      (* Access the value *)
      let access = if bkind = E.Shared then Read else Write in
      let expand_prim_copy = false in
      let prepare = prepare_rplace config expand_prim_copy access p in
      (* Evaluate the borrowing operation *)
      let eval (cf : V.typed_value -> m_fun) (v : V.typed_value) : m_fun =
       fun ctx ->
        (* Generate the fresh borrow id *)
        let bid = C.fresh_borrow_id () in
        (* Compute the loan value, with which to replace the value at place p *)
        let nv, shared_mvalue =
          match v.V.value with
          | V.Loan (V.SharedLoan (bids, sv)) ->
              (* Shared loan: insert the new borrow id *)
              let bids1 = V.BorrowId.Set.add bid bids in
              ({ v with V.value = V.Loan (V.SharedLoan (bids1, sv)) }, sv)
          | _ ->
              (* Not a shared loan: add a wrapper *)
              let v' =
                V.Loan (V.SharedLoan (V.BorrowId.Set.singleton bid, v))
              in
              ({ v with V.value = v' }, v)
        in
        (* Update the borrowed value in the context *)
        let ctx = write_place_unwrap config access p nv ctx in
        (* Compute the rvalue - simply a shared borrow with a the fresh id.
         * Note that the reference is *mutable* if we do a two-phase borrow *)
        let rv_ty =
          T.Ref (T.Erased, v.ty, if bkind = E.Shared then Shared else Mut)
        in
        let bc =
          if bkind = E.Shared then V.SharedBorrow (shared_mvalue, bid)
          else V.InactivatedMutBorrow bid
        in
        let rv : V.typed_value = { V.value = V.Borrow bc; ty = rv_ty } in
        (* Continue *)
        cf rv ctx
      in
      (* Compose and apply *)
      comp prepare eval cf ctx
  | E.Mut ->
      (* Access the value *)
      let access = Write in
      let expand_prim_copy = false in
      let prepare = prepare_rplace config expand_prim_copy access p in
      (* Evaluate the borrowing operation *)
      let eval (cf : V.typed_value -> m_fun) (v : V.typed_value) : m_fun =
       fun ctx ->
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
        (* Continue *)
        cf rv ctx
      in
      (* Compose and apply *)
      comp prepare eval cf ctx

let eval_rvalue_aggregate (config : C.config)
    (aggregate_kind : E.aggregate_kind) (ops : E.operand list)
    (cf : V.typed_value -> m_fun) : m_fun =
  (* Evaluate the operands *)
  let eval_ops = eval_operands config ops in
  (* Compute the value *)
  let compute (cf : V.typed_value -> m_fun) (values : V.typed_value list) :
      m_fun =
   fun ctx ->
    (* Match on the aggregate kind *)
    match aggregate_kind with
    | E.AggregatedTuple ->
        let tys = List.map (fun (v : V.typed_value) -> v.V.ty) values in
        let v = V.Adt { variant_id = None; field_values = values } in
        let ty = T.Adt (T.Tuple, [], tys) in
        let aggregated : V.typed_value = { V.value = v; ty } in
        (* Call the continuation *)
        cf aggregated ctx
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
        let aggregated : V.typed_value = { V.value = Adt av; ty = aty } in
        (* Call the continuation *)
        cf aggregated ctx
  in
  (* Compose and apply *)
  comp eval_ops compute cf

(** Evaluate an rvalue.

    Transmits the computed rvalue to the received continuation.
 *)
let eval_rvalue (config : C.config) (rvalue : E.rvalue)
    (cf : (V.typed_value, eval_error) result -> m_fun) : m_fun =
 fun ctx ->
  log#ldebug (lazy "eval_rvalue");
  (* Small helpers *)
  let wrap_in_result (cf : (V.typed_value, eval_error) result -> m_fun)
      (v : V.typed_value) : m_fun =
    cf (Ok v)
  in
  let comp_wrap f = comp f wrap_in_result cf in
  (* Delegate to the proper auxiliary function *)
  match rvalue with
  | E.Use op -> comp_wrap (eval_operand config op) ctx
  | E.Ref (p, bkind) -> comp_wrap (eval_rvalue_ref config p bkind) ctx
  | E.UnaryOp (unop, op) -> eval_unary_op config unop op cf ctx
  | E.BinaryOp (binop, op1, op2) -> eval_binary_op config binop op1 op2 cf ctx
  | E.Aggregate (aggregate_kind, ops) ->
      comp_wrap (eval_rvalue_aggregate config aggregate_kind ops) ctx
  | E.Discriminant p -> comp_wrap (eval_rvalue_discriminant config p) ctx
