open Types
open Values
open LlbcAst
open Scalars
open Expressions
open Utils
open Contexts
open TypesUtils
open ValuesUtils
open SynthesizeSymbolic
open Cps
open InterpreterUtils
open InterpreterExpansion
open InterpreterPaths

(** The local logger *)
let log = Logging.expressions_log

(** As long as there are symbolic values at a given place (potentially in subvalues)
    which contain borrows and are primitively copyable, expand them.
    
    We use this function before copying values.
    
    Note that the place should have been prepared so that there are no remaining
    loans.
*)
let expand_primitively_copyable_at_place (config : config)
    (access : access_kind) (p : place) : cm_fun =
 fun cf ctx ->
  (* Small helper *)
  let rec expand : cm_fun =
   fun cf ctx ->
    let v = read_place access p ctx in
    match
      find_first_primitively_copyable_sv_with_borrows
        ctx.type_context.type_infos v
    with
    | None -> cf ctx
    | Some sv ->
        let cc =
          expand_symbolic_value_no_branching config sv (Some (mk_mplace p ctx))
        in
        comp cc expand cf ctx
  in
  (* Apply *)
  expand cf ctx

(** Read a place (CPS-style function).

    We also check that the value *doesn't contain bottoms or reserved
    borrows*.
 *)
let read_place (access : access_kind) (p : place) (cf : typed_value -> m_fun) :
    m_fun =
 fun ctx ->
  let v = read_place access p ctx in
  (* Check that there are no bottoms in the value *)
  assert (not (bottom_in_value ctx.ended_regions v));
  (* Check that there are no reserved borrows in the value *)
  assert (not (reserved_in_value v));
  (* Call the continuation *)
  cf v ctx

let access_rplace_reorganize_and_read (config : config)
    (expand_prim_copy : bool) (access : access_kind) (p : place)
    (cf : typed_value -> m_fun) : m_fun =
 fun ctx ->
  (* Make sure we can evaluate the path *)
  let cc = update_ctx_along_read_place config access p in
  (* End the proper loans at the place itself *)
  let cc = comp cc (end_loans_at_place config access p) in
  (* Expand the copyable values which contain borrows (which are necessarily shared
   * borrows) *)
  let cc =
    if expand_prim_copy then
      comp cc (expand_primitively_copyable_at_place config access p)
    else cc
  in
  (* Read the place - note that this checks that the value doesn't contain bottoms *)
  let read_place = read_place access p in
  (* Compose *)
  comp cc read_place cf ctx

let access_rplace_reorganize (config : config) (expand_prim_copy : bool)
    (access : access_kind) (p : place) : cm_fun =
 fun cf ctx ->
  access_rplace_reorganize_and_read config expand_prim_copy access p
    (fun _v -> cf)
    ctx

(** Convert an operand constant operand value to a typed value *)
let literal_to_typed_value (ty : literal_type) (cv : literal) : typed_value =
  (* Check the type while converting - we actually need some information
     * contained in the type *)
  log#ldebug
    (lazy
      ("literal_to_typed_value:" ^ "\n- cv: "
      ^ Print.Values.literal_to_string cv));
  match (ty, cv) with
  (* Scalar, boolean... *)
  | TBool, VBool v -> { value = VLiteral (VBool v); ty = TLiteral ty }
  | TChar, VChar v -> { value = VLiteral (VChar v); ty = TLiteral ty }
  | TInteger int_ty, VScalar v ->
      (* Check the type and the ranges *)
      assert (int_ty = v.int_ty);
      assert (check_scalar_value_in_range v);
      { value = VLiteral (VScalar v); ty = TLiteral ty }
  (* Remaining cases (invalid) *)
  | _, _ -> raise (Failure "Improperly typed constant value")

(** Copy a value, and return the resulting value.

    Note that copying values might update the context. For instance, when
    copying shared borrows, we need to insert new shared borrows in the context.

    Also, this function is actually more general than it should be: it can be
    used to copy concrete ADT values, while ADT copy should be done through the
    Copy trait (i.e., by calling a dedicated function). This is why we added a
    parameter to control this copy ([allow_adt_copy]). Note that here by ADT we
    mean the user-defined ADTs (not tuples or assumed types).
 *)
let rec copy_value (allow_adt_copy : bool) (config : config) (ctx : eval_ctx)
    (v : typed_value) : eval_ctx * typed_value =
  log#ldebug
    (lazy
      ("copy_value: "
      ^ typed_value_to_string ctx v
      ^ "\n- context:\n" ^ eval_ctx_to_string ctx));
  (* Remark: at some point we rewrote this function to use iterators, but then
   * we reverted the changes: the result was less clear actually. In particular,
   * the fact that we have exhaustive matches below makes very obvious the cases
   * in which we need to fail *)
  match v.value with
  | VLiteral _ -> (ctx, v)
  | VAdt av ->
      (* Sanity check *)
      (match v.ty with
      | TAdt (TAssumed TBox, _) ->
          raise (Failure "Can't copy an assumed value other than Option")
      | TAdt (TAdtId _, _) as ty ->
          assert (allow_adt_copy || ty_is_primitively_copyable ty)
      | TAdt (TTuple, _) -> () (* Ok *)
      | TAdt
          ( TAssumed (TSlice | TArray),
            {
              regions = [];
              types = [ ty ];
              const_generics = [];
              trait_refs = [];
            } ) ->
          assert (ty_is_primitively_copyable ty)
      | _ -> raise (Failure "Unreachable"));
      let ctx, fields =
        List.fold_left_map
          (copy_value allow_adt_copy config)
          ctx av.field_values
      in
      (ctx, { v with value = VAdt { av with field_values = fields } })
  | VBottom -> raise (Failure "Can't copy ⊥")
  | VBorrow bc -> (
      (* We can only copy shared borrows *)
      match bc with
      | VSharedBorrow bid ->
          (* We need to create a new borrow id for the copied borrow, and
           * update the context accordingly *)
          let bid' = fresh_borrow_id () in
          let ctx = InterpreterBorrows.reborrow_shared bid bid' ctx in
          (ctx, { v with value = VBorrow (VSharedBorrow bid') })
      | VMutBorrow (_, _) -> raise (Failure "Can't copy a mutable borrow")
      | VReservedMutBorrow _ ->
          raise (Failure "Can't copy a reserved mut borrow"))
  | VLoan lc -> (
      (* We can only copy shared loans *)
      match lc with
      | VMutLoan _ -> raise (Failure "Can't copy a mutable loan")
      | VSharedLoan (_, sv) ->
          (* We don't copy the shared loan: only the shared value inside *)
          copy_value allow_adt_copy config ctx sv)
  | VSymbolic sp ->
      (* We can copy only if the type is "primitively" copyable.
       * Note that in the general case, copy is a trait: copying values
       * thus requires calling the proper function. Here, we copy values
       * for very simple types such as integers, shared borrows, etc. *)
      assert (ty_is_primitively_copyable (Substitute.erase_regions sp.sv_ty));
      (* If the type is copyable, we simply return the current value. Side
       * remark: what is important to look at when copying symbolic values
       * is symbolic expansion. The important subcase is the expansion of shared
       * borrows: when doing so, every occurrence of the same symbolic value
       * must use a fresh borrow id. *)
      (ctx, v)

(** Reorganize the environment in preparation for the evaluation of an operand.

    Evaluating an operand requires reorganizing the environment to get access
    to a given place (by ending borrows, expanding symbolic values...) then
    applying the operand operation (move, copy, etc.).
    
    Sometimes, we want to decouple the two operations.
    Consider the following example:
    {[
      context = {
        x -> shared_borrow l0
        y -> shared_loan {l0} v
      }

      dest <- f(move x, move y);
      ...
    ]}
    Because of the way {!end_borrow} is implemented, when giving back the borrow
    [l0] upon evaluating [move y], we won't notice that [shared_borrow l0] has
    disappeared from the environment (it has been moved and not assigned yet,
    and so is hanging in "thin air").
    
    By first "preparing" the operands evaluation, we make sure no such thing
    happens. To be more precise, we make sure all the updates to borrows triggered
    by access *and* move operations have already been applied.

    Rk.: in the formalization, we always have an explicit "reorganization" step
    in the rule premises, before the actual operand evaluation, that allows to
    reorganize the environment so that it satisfies the proper conditions. This
    function's role is to do the reorganization.
    
    Rk.: doing this is actually not completely necessary because when
    generating MIR, rustc introduces intermediate assignments for all the function
    parameters. Still, it is better for soundness purposes, and corresponds to
    what we do in the formalization (because we don't enforce the same constraints
    as MIR in the formalization).
 *)
let prepare_eval_operand_reorganize (config : config) (op : operand) : cm_fun =
 fun cf ctx ->
  let prepare : cm_fun =
   fun cf ctx ->
    match op with
    | Constant _ ->
        (* No need to reorganize the context *)
        cf ctx
    | Copy p ->
        (* Access the value *)
        let access = Read in
        (* Expand the symbolic values, if necessary *)
        let expand_prim_copy = true in
        access_rplace_reorganize config expand_prim_copy access p cf ctx
    | Move p ->
        (* Access the value *)
        let access = Move in
        let expand_prim_copy = false in
        access_rplace_reorganize config expand_prim_copy access p cf ctx
  in
  (* Apply *)
  prepare cf ctx

(** Evaluate an operand, without reorganizing the context before *)
let eval_operand_no_reorganize (config : config) (op : operand)
    (cf : typed_value -> m_fun) : m_fun =
 fun ctx ->
  (* Debug *)
  log#ldebug
    (lazy
      ("eval_operand_no_reorganize: op: " ^ operand_to_string ctx op
     ^ "\n- ctx:\n" ^ eval_ctx_to_string ctx ^ "\n"));
  (* Evaluate *)
  match op with
  | Constant cv -> (
      match cv.value with
      | CLiteral lit ->
          cf (literal_to_typed_value (ty_as_literal cv.ty) lit) ctx
      | CTraitConst (trait_ref, generics, const_name) -> (
          assert (generics = empty_generic_args);
          match trait_ref.trait_id with
          | TraitImpl _ ->
              (* This shouldn't happen: if we refer to a concrete implementation, we
                 should directly refer to the top-level constant *)
              raise (Failure "Unreachable")
          | _ -> (
              (* We refer to a constant defined in a local clause: simply
                 introduce a fresh symbolic value *)
              let ctx0 = ctx in
              (* Lookup the trait declaration to retrieve the type of the symbolic value *)
              let trait_decl =
                ctx_lookup_trait_decl ctx trait_ref.trait_decl_ref.trait_decl_id
              in
              let _, (ty, _) =
                List.find (fun (name, _) -> name = const_name) trait_decl.consts
              in
              (* Introduce a fresh symbolic value *)
              let v = mk_fresh_symbolic_typed_value TraitConst ty in
              (* Continue the evaluation *)
              let e = cf v ctx in
              (* We have to wrap the generated expression *)
              match e with
              | None -> None
              | Some e ->
                  Some
                    (SymbolicAst.IntroSymbolic
                       ( ctx0,
                         None,
                         value_as_symbolic v.value,
                         SymbolicAst.VaTraitConstValue
                           (trait_ref, generics, const_name),
                         e ))))
      | CVar vid -> (
          let ctx0 = ctx in
          (* Lookup the const generic value *)
          let cv = ctx_lookup_const_generic_value ctx vid in
          (* Copy the value *)
          let allow_adt_copy = false in
          let ctx, v = copy_value allow_adt_copy config ctx cv in
          (* Continue *)
          let e = cf v ctx in
          (* We have to wrap the generated expression *)
          match e with
          | None -> None
          | Some e ->
              (* If we are synthesizing a symbolic AST, it means that we are in symbolic
                 mode: the value of the const generic is necessarily symbolic. *)
              assert (is_symbolic cv.value);
              (* *)
              Some
                (SymbolicAst.IntroSymbolic
                   ( ctx0,
                     None,
                     value_as_symbolic v.value,
                     SymbolicAst.VaCgValue vid,
                     e )))
      | CFnPtr _ -> raise (Failure "TODO"))
  | Copy p ->
      (* Access the value *)
      let access = Read in
      let cc = read_place access p in
      (* Copy the value *)
      let copy cf v : m_fun =
       fun ctx ->
        (* Sanity checks *)
        assert (not (bottom_in_value ctx.ended_regions v));
        assert (
          Option.is_none
            (find_first_primitively_copyable_sv_with_borrows
               ctx.type_context.type_infos v));
        (* Actually perform the copy *)
        let allow_adt_copy = false in
        let ctx, v = copy_value allow_adt_copy config ctx v in
        (* Continue *)
        cf v ctx
      in
      (* Compose and apply *)
      comp cc copy cf ctx
  | Move p ->
      (* Access the value *)
      let access = Move in
      let cc = read_place access p in
      (* Move the value *)
      let move cf v : m_fun =
       fun ctx ->
        (* Check that there are no bottoms in the value we are about to move *)
        assert (not (bottom_in_value ctx.ended_regions v));
        let bottom : typed_value = { value = VBottom; ty = v.ty } in
        let ctx = write_place access p bottom ctx in
        cf v ctx
      in
      (* Compose and apply *)
      comp cc move cf ctx

let eval_operand (config : config) (op : operand) (cf : typed_value -> m_fun) :
    m_fun =
 fun ctx ->
  (* Debug *)
  log#ldebug
    (lazy
      ("eval_operand: op: " ^ operand_to_string ctx op ^ "\n- ctx:\n"
     ^ eval_ctx_to_string ctx ^ "\n"));
  (* We reorganize the context, then evaluate the operand *)
  comp
    (prepare_eval_operand_reorganize config op)
    (eval_operand_no_reorganize config op)
    cf ctx

(** Small utility.

    See [prepare_eval_operand_reorganize].
 *)
let prepare_eval_operands_reorganize (config : config) (ops : operand list) :
    cm_fun =
  fold_left_apply_continuation (prepare_eval_operand_reorganize config) ops

(** Evaluate several operands. *)
let eval_operands (config : config) (ops : operand list)
    (cf : typed_value list -> m_fun) : m_fun =
 fun ctx ->
  (* Prepare the operands *)
  let prepare = prepare_eval_operands_reorganize config ops in
  (* Evaluate the operands *)
  let eval =
    fold_left_list_apply_continuation (eval_operand_no_reorganize config) ops
  in
  (* Compose and apply *)
  comp prepare eval cf ctx

let eval_two_operands (config : config) (op1 : operand) (op2 : operand)
    (cf : typed_value * typed_value -> m_fun) : m_fun =
  let eval_op = eval_operands config [ op1; op2 ] in
  let use_res cf res =
    match res with
    | [ v1; v2 ] -> cf (v1, v2)
    | _ -> raise (Failure "Unreachable")
  in
  comp eval_op use_res cf

let eval_unary_op_concrete (config : config) (unop : unop) (op : operand)
    (cf : (typed_value, eval_error) result -> m_fun) : m_fun =
  (* Evaluate the operand *)
  let eval_op = eval_operand config op in
  (* Apply the unop *)
  let apply cf (v : typed_value) : m_fun =
    match (unop, v.value) with
    | Not, VLiteral (VBool b) ->
        cf (Ok { v with value = VLiteral (VBool (not b)) })
    | Neg, VLiteral (VScalar sv) -> (
        let i = Z.neg sv.value in
        match mk_scalar sv.int_ty i with
        | Error _ -> cf (Error EPanic)
        | Ok sv -> cf (Ok { v with value = VLiteral (VScalar sv) }))
    | Cast (CastInteger (src_ty, tgt_ty)), VLiteral (VScalar sv) -> (
        assert (src_ty = sv.int_ty);
        let i = sv.value in
        match mk_scalar tgt_ty i with
        | Error _ -> cf (Error EPanic)
        | Ok sv ->
            let ty = TLiteral (TInteger tgt_ty) in
            let value = VLiteral (VScalar sv) in
            cf (Ok { ty; value }))
    | _ -> raise (Failure "Invalid input for unop")
  in
  comp eval_op apply cf

let eval_unary_op_symbolic (config : config) (unop : unop) (op : operand)
    (cf : (typed_value, eval_error) result -> m_fun) : m_fun =
 fun ctx ->
  (* Evaluate the operand *)
  let eval_op = eval_operand config op in
  (* Generate a fresh symbolic value to store the result *)
  let apply cf (v : typed_value) : m_fun =
   fun ctx ->
    let res_sv_id = fresh_symbolic_value_id () in
    let res_sv_ty =
      match (unop, v.ty) with
      | Not, (TLiteral TBool as lty) -> lty
      | Neg, (TLiteral (TInteger _) as lty) -> lty
      | Cast (CastInteger (_, tgt_ty)), _ -> TLiteral (TInteger tgt_ty)
      | _ -> raise (Failure "Invalid input for unop")
    in
    let res_sv =
      { sv_kind = FunCallRet; sv_id = res_sv_id; sv_ty = res_sv_ty }
    in
    (* Call the continuation *)
    let expr = cf (Ok (mk_typed_value_from_symbolic_value res_sv)) ctx in
    (* Synthesize the symbolic AST *)
    synthesize_unary_op ctx unop v
      (mk_opt_place_from_op op ctx)
      res_sv None expr
  in
  (* Compose and apply *)
  comp eval_op apply cf ctx

let eval_unary_op (config : config) (unop : unop) (op : operand)
    (cf : (typed_value, eval_error) result -> m_fun) : m_fun =
  match config.mode with
  | ConcreteMode -> eval_unary_op_concrete config unop op cf
  | SymbolicMode -> eval_unary_op_symbolic config unop op cf

(** Small helper for [eval_binary_op_concrete]: computes the result of applying
    the binop *after* the operands have been successfully evaluated
 *)
let eval_binary_op_concrete_compute (binop : binop) (v1 : typed_value)
    (v2 : typed_value) : (typed_value, eval_error) result =
  (* Equality check binops (Eq, Ne) accept values from a wide variety of types.
   * The remaining binops only operate on scalars. *)
  if binop = Eq || binop = Ne then (
    (* Equality operations *)
    assert (v1.ty = v2.ty);
    (* Equality/inequality check is primitive only for a subset of types *)
    assert (ty_is_primitively_copyable v1.ty);
    let b = v1 = v2 in
    Ok { value = VLiteral (VBool b); ty = TLiteral TBool })
  else
    (* For the non-equality operations, the input values are necessarily scalars *)
    match (v1.value, v2.value) with
    | VLiteral (VScalar sv1), VLiteral (VScalar sv2) -> (
        (* There are binops which require the two operands to have the same
           type, and binops for which it is not the case.
           There are also binops which return booleans, and binops which
           return integers.
        *)
        match binop with
        | Lt | Le | Ge | Gt ->
            (* The two operands must have the same type and the result is a boolean *)
            assert (sv1.int_ty = sv2.int_ty);
            let b =
              match binop with
              | Lt -> Z.lt sv1.value sv2.value
              | Le -> Z.leq sv1.value sv2.value
              | Ge -> Z.geq sv1.value sv2.value
              | Gt -> Z.gt sv1.value sv2.value
              | Div | Rem | Add | Sub | Mul | BitXor | BitAnd | BitOr | Shl
              | Shr | Ne | Eq ->
                  raise (Failure "Unreachable")
            in
            Ok
              ({ value = VLiteral (VBool b); ty = TLiteral TBool }
                : typed_value)
        | Div | Rem | Add | Sub | Mul | BitXor | BitAnd | BitOr -> (
            (* The two operands must have the same type and the result is an integer *)
            assert (sv1.int_ty = sv2.int_ty);
            let res =
              match binop with
              | Div ->
                  if sv2.value = Z.zero then Error ()
                  else mk_scalar sv1.int_ty (Z.div sv1.value sv2.value)
              | Rem ->
                  (* See [https://github.com/ocaml/Zarith/blob/master/z.mli] *)
                  if sv2.value = Z.zero then Error ()
                  else mk_scalar sv1.int_ty (Z.rem sv1.value sv2.value)
              | Add -> mk_scalar sv1.int_ty (Z.add sv1.value sv2.value)
              | Sub -> mk_scalar sv1.int_ty (Z.sub sv1.value sv2.value)
              | Mul -> mk_scalar sv1.int_ty (Z.mul sv1.value sv2.value)
              | BitXor -> raise Unimplemented
              | BitAnd -> raise Unimplemented
              | BitOr -> raise Unimplemented
              | Lt | Le | Ge | Gt | Shl | Shr | Ne | Eq ->
                  raise (Failure "Unreachable")
            in
            match res with
            | Error _ -> Error EPanic
            | Ok sv ->
                Ok
                  {
                    value = VLiteral (VScalar sv);
                    ty = TLiteral (TInteger sv1.int_ty);
                  })
        | Shl | Shr -> raise Unimplemented
        | Ne | Eq -> raise (Failure "Unreachable"))
    | _ -> raise (Failure "Invalid inputs for binop")

let eval_binary_op_concrete (config : config) (binop : binop) (op1 : operand)
    (op2 : operand) (cf : (typed_value, eval_error) result -> m_fun) : m_fun =
  (* Evaluate the operands *)
  let eval_ops = eval_two_operands config op1 op2 in
  (* Compute the result of the binop *)
  let compute cf (res : typed_value * typed_value) =
    let v1, v2 = res in
    cf (eval_binary_op_concrete_compute binop v1 v2)
  in
  (* Compose and apply *)
  comp eval_ops compute cf

let eval_binary_op_symbolic (config : config) (binop : binop) (op1 : operand)
    (op2 : operand) (cf : (typed_value, eval_error) result -> m_fun) : m_fun =
 fun ctx ->
  (* Evaluate the operands *)
  let eval_ops = eval_two_operands config op1 op2 in
  (* Compute the result of applying the binop *)
  let compute cf ((v1, v2) : typed_value * typed_value) : m_fun =
   fun ctx ->
    (* Generate a fresh symbolic value to store the result *)
    let res_sv_id = fresh_symbolic_value_id () in
    let res_sv_ty =
      if binop = Eq || binop = Ne then (
        (* Equality operations *)
        assert (v1.ty = v2.ty);
        (* Equality/inequality check is primitive only for a subset of types *)
        assert (ty_is_primitively_copyable v1.ty);
        TLiteral TBool)
      else
        (* Other operations: input types are integers *)
        match (v1.ty, v2.ty) with
        | TLiteral (TInteger int_ty1), TLiteral (TInteger int_ty2) -> (
            match binop with
            | Lt | Le | Ge | Gt ->
                assert (int_ty1 = int_ty2);
                TLiteral TBool
            | Div | Rem | Add | Sub | Mul | BitXor | BitAnd | BitOr ->
                assert (int_ty1 = int_ty2);
                TLiteral (TInteger int_ty1)
            | Shl | Shr -> raise Unimplemented
            | Ne | Eq -> raise (Failure "Unreachable"))
        | _ -> raise (Failure "Invalid inputs for binop")
    in
    let res_sv =
      { sv_kind = FunCallRet; sv_id = res_sv_id; sv_ty = res_sv_ty }
    in
    (* Call the continuattion *)
    let v = mk_typed_value_from_symbolic_value res_sv in
    let expr = cf (Ok v) ctx in
    (* Synthesize the symbolic AST *)
    let p1 = mk_opt_place_from_op op1 ctx in
    let p2 = mk_opt_place_from_op op2 ctx in
    synthesize_binary_op ctx binop v1 p1 v2 p2 res_sv None expr
  in
  (* Compose and apply *)
  comp eval_ops compute cf ctx

let eval_binary_op (config : config) (binop : binop) (op1 : operand)
    (op2 : operand) (cf : (typed_value, eval_error) result -> m_fun) : m_fun =
  match config.mode with
  | ConcreteMode -> eval_binary_op_concrete config binop op1 op2 cf
  | SymbolicMode -> eval_binary_op_symbolic config binop op1 op2 cf

let eval_rvalue_ref (config : config) (p : place) (bkind : borrow_kind)
    (cf : typed_value -> m_fun) : m_fun =
 fun ctx ->
  match bkind with
  | BShared | BTwoPhaseMut | BShallow ->
      (* **REMARK**: we initially treated shallow borrows like shared borrows.
         In practice this restricted the behaviour too much, so for now we
         forbid them.
      *)
      assert (bkind <> BShallow);

      (* Access the value *)
      let access =
        match bkind with
        | BShared | BShallow -> Read
        | BTwoPhaseMut -> Write
        | _ -> raise (Failure "Unreachable")
      in

      let expand_prim_copy = false in
      let prepare =
        access_rplace_reorganize_and_read config expand_prim_copy access p
      in
      (* Evaluate the borrowing operation *)
      let eval (cf : typed_value -> m_fun) (v : typed_value) : m_fun =
       fun ctx ->
        (* Generate the fresh borrow id *)
        let bid = fresh_borrow_id () in
        (* Compute the loan value, with which to replace the value at place p *)
        let nv =
          match v.value with
          | VLoan (VSharedLoan (bids, sv)) ->
              (* Shared loan: insert the new borrow id *)
              let bids1 = BorrowId.Set.add bid bids in
              { v with value = VLoan (VSharedLoan (bids1, sv)) }
          | _ ->
              (* Not a shared loan: add a wrapper *)
              let v' = VLoan (VSharedLoan (BorrowId.Set.singleton bid, v)) in
              { v with value = v' }
        in
        (* Update the borrowed value in the context *)
        let ctx = write_place access p nv ctx in
        (* Compute the rvalue - simply a shared borrow with a the fresh id.
         * Note that the reference is *mutable* if we do a two-phase borrow *)
        let ref_kind =
          match bkind with
          | BShared | BShallow -> RShared
          | BTwoPhaseMut -> RMut
          | _ -> raise (Failure "Unreachable")
        in
        let rv_ty = TRef (RErased, v.ty, ref_kind) in
        let bc =
          match bkind with
          | BShared | BShallow ->
              (* See the remark at the beginning of the match branch: we
                 handle shallow borrows like shared borrows *)
              VSharedBorrow bid
          | BTwoPhaseMut -> VReservedMutBorrow bid
          | _ -> raise (Failure "Unreachable")
        in
        let rv : typed_value = { value = VBorrow bc; ty = rv_ty } in
        (* Continue *)
        cf rv ctx
      in
      (* Compose and apply *)
      comp prepare eval cf ctx
  | BMut ->
      (* Access the value *)
      let access = Write in
      let expand_prim_copy = false in
      let prepare =
        access_rplace_reorganize_and_read config expand_prim_copy access p
      in
      (* Evaluate the borrowing operation *)
      let eval (cf : typed_value -> m_fun) (v : typed_value) : m_fun =
       fun ctx ->
        (* Compute the rvalue - wrap the value in a mutable borrow with a fresh id *)
        let bid = fresh_borrow_id () in
        let rv_ty = TRef (RErased, v.ty, RMut) in
        let rv : typed_value =
          { value = VBorrow (VMutBorrow (bid, v)); ty = rv_ty }
        in
        (* Compute the value with which to replace the value at place p *)
        let nv = { v with value = VLoan (VMutLoan bid) } in
        (* Update the value in the context *)
        let ctx = write_place access p nv ctx in
        (* Continue *)
        cf rv ctx
      in
      (* Compose and apply *)
      comp prepare eval cf ctx

let eval_rvalue_aggregate (config : config) (aggregate_kind : aggregate_kind)
    (ops : operand list) (cf : typed_value -> m_fun) : m_fun =
  (* Evaluate the operands *)
  let eval_ops = eval_operands config ops in
  (* Compute the value *)
  let compute (cf : typed_value -> m_fun) (values : typed_value list) : m_fun =
   fun ctx ->
    (* Match on the aggregate kind *)
    match aggregate_kind with
    | AggregatedAdt (type_id, opt_variant_id, generics) -> (
        match type_id with
        | TTuple ->
            let tys = List.map (fun (v : typed_value) -> v.ty) values in
            let v = VAdt { variant_id = None; field_values = values } in
            let generics = mk_generic_args [] tys [] [] in
            let ty = TAdt (TTuple, generics) in
            let aggregated : typed_value = { value = v; ty } in
            (* Call the continuation *)
            cf aggregated ctx
        | TAdtId def_id ->
            (* Sanity checks *)
            let type_decl = ctx_lookup_type_decl ctx def_id in
            assert (
              List.length type_decl.generics.regions
              = List.length generics.regions);
            let expected_field_types =
              AssociatedTypes.ctx_adt_get_inst_norm_field_etypes ctx def_id
                opt_variant_id generics
            in
            assert (
              expected_field_types
              = List.map (fun (v : typed_value) -> v.ty) values);
            (* Construct the value *)
            let av : adt_value =
              { variant_id = opt_variant_id; field_values = values }
            in
            let aty = TAdt (TAdtId def_id, generics) in
            let aggregated : typed_value = { value = VAdt av; ty = aty } in
            (* Call the continuation *)
            cf aggregated ctx
        | TAssumed _ -> raise (Failure "Unreachable"))
    | AggregatedArray (ety, cg) -> (
        (* Sanity check: all the values have the proper type *)
        assert (List.for_all (fun (v : typed_value) -> v.ty = ety) values);
        (* Sanity check: the number of values is consistent with the length *)
        let len = (literal_as_scalar (const_generic_as_literal cg)).value in
        assert (len = Z.of_int (List.length values));
        let generics = TypesUtils.mk_generic_args [] [ ety ] [ cg ] [] in
        let ty = TAdt (TAssumed TArray, generics) in
        (* In order to generate a better AST, we introduce a symbolic
           value equal to the array. The reason is that otherwise, the
           array we introduce here might be duplicated in the generated
           code: by introducing a symbolic value we introduce a let-binding
           in the generated code. *)
        let saggregated = mk_fresh_symbolic_typed_value Aggregate ty in
        (* Call the continuation *)
        match cf saggregated ctx with
        | None -> None
        | Some e ->
            (* Introduce the symbolic value in the AST *)
            let sv = ValuesUtils.value_as_symbolic saggregated.value in
            Some (SymbolicAst.IntroSymbolic (ctx, None, sv, VaArray values, e)))
  in
  (* Compose and apply *)
  comp eval_ops compute cf

let eval_rvalue_not_global (config : config) (rvalue : rvalue)
    (cf : (typed_value, eval_error) result -> m_fun) : m_fun =
 fun ctx ->
  log#ldebug (lazy "eval_rvalue");
  (* Small helpers *)
  let wrap_in_result (cf : (typed_value, eval_error) result -> m_fun)
      (v : typed_value) : m_fun =
    cf (Ok v)
  in
  let comp_wrap f = comp f wrap_in_result cf in
  (* Delegate to the proper auxiliary function *)
  match rvalue with
  | Use op -> comp_wrap (eval_operand config op) ctx
  | RvRef (p, bkind) -> comp_wrap (eval_rvalue_ref config p bkind) ctx
  | UnaryOp (unop, op) -> eval_unary_op config unop op cf ctx
  | BinaryOp (binop, op1, op2) -> eval_binary_op config binop op1 op2 cf ctx
  | Aggregate (aggregate_kind, ops) ->
      comp_wrap (eval_rvalue_aggregate config aggregate_kind ops) ctx
  | Discriminant _ ->
      raise
        (Failure
           "Unreachable: discriminant reads should have been eliminated from \
            the AST")
  | Global _ -> raise (Failure "Unreachable")

let eval_fake_read (config : config) (p : place) : cm_fun =
 fun cf ctx ->
  let expand_prim_copy = false in
  let cf_prepare cf =
    access_rplace_reorganize_and_read config expand_prim_copy Read p cf
  in
  let cf_continue cf v : m_fun =
   fun ctx ->
    assert (not (bottom_in_value ctx.ended_regions v));
    cf ctx
  in
  comp cf_prepare cf_continue cf ctx
