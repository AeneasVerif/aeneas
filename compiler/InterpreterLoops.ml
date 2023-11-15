open Types
open Values
open Contexts
open ValuesUtils
module S = SynthesizeSymbolic
open Cps
open InterpreterUtils
open InterpreterLoopsCore
open InterpreterLoopsMatchCtxs
open InterpreterLoopsFixedPoint

(** The local logger *)
let log = Logging.loops_log

(** Evaluate a loop in concrete mode *)
let eval_loop_concrete (eval_loop_body : st_cm_fun) : st_cm_fun =
 fun cf ctx ->
  (* We need a loop id for the [LoopReturn]. In practice it won't be used
     (it is useful only for the symbolic execution *)
  let loop_id = fresh_loop_id () in
  (* Continuation for after we evaluate the loop body: depending the result
     of doing one loop iteration:
     - redoes a loop iteration
     - exits the loop
     - other...

     We need a specific function because of the {!Continue} case: in case we
     continue, we might have to reevaluate the current loop body with the
     new context (and repeat this an indefinite number of times).
  *)
  let rec reeval_loop_body (res : statement_eval_res) : m_fun =
    match res with
    | Return -> cf (LoopReturn loop_id)
    | Panic -> cf Panic
    | Break i ->
        (* Break out of the loop by calling the continuation *)
        let res = if i = 0 then Unit else Break (i - 1) in
        cf res
    | Continue 0 ->
        (* Re-evaluate the loop body *)
        eval_loop_body reeval_loop_body
    | Continue i ->
        (* Continue to an outer loop *)
        cf (Continue (i - 1))
    | Unit ->
        (* We can't get there.
         * Note that if we decide not to fail here but rather do
         * the same thing as for [Continue 0], we could make the
         * code slightly simpler: calling {!reeval_loop_body} with
         * {!Unit} would account for the first iteration of the loop.
         * We prefer to write it this way for consistency and sanity,
         * though. *)
        raise (Failure "Unreachable")
    | LoopReturn _ | EndEnterLoop _ | EndContinue _ ->
        (* We can't get there: this is only used in symbolic mode *)
        raise (Failure "Unreachable")
  in

  (* Apply *)
  eval_loop_body reeval_loop_body ctx

(** Evaluate a loop in symbolic mode *)
let eval_loop_symbolic (config : config) (eval_loop_body : st_cm_fun) :
    st_cm_fun =
 fun cf ctx ->
  (* Debug *)
  log#ldebug
    (lazy ("eval_loop_symbolic:\nContext:\n" ^ eval_ctx_to_string ctx ^ "\n\n"));

  (* Generate a fresh loop id *)
  let loop_id = fresh_loop_id () in

  (* Compute the fixed point at the loop entrance *)
  let fp_ctx, fixed_ids, rg_to_abs =
    compute_loop_entry_fixed_point config loop_id eval_loop_body ctx
  in

  (* Debug *)
  log#ldebug
    (lazy
      ("eval_loop_symbolic:\nInitial context:\n" ^ eval_ctx_to_string ctx
     ^ "\n\nFixed point:\n" ^ eval_ctx_to_string fp_ctx));

  (* Compute the loop input parameters *)
  let fresh_sids, input_svalues = compute_fp_ctx_symbolic_values ctx fp_ctx in
  let fp_input_svalues = List.map (fun sv -> sv.sv_id) input_svalues in

  (* Synthesize the end of the function - we simply match the context at the
     loop entry with the fixed point: in the synthesized code, the function
     will end with a call to the loop translation
  *)
  let fp_bl_corresp =
    compute_fixed_point_id_correspondance fixed_ids ctx fp_ctx
  in
  let end_expr =
    match_ctx_with_target config loop_id true fp_bl_corresp fp_input_svalues
      fixed_ids fp_ctx cf ctx
  in

  (* Synthesize the loop body by evaluating it, with the continuation for
     after the loop starting at the *fixed point*, but with a special
     treatment for the [Break] and [Continue] cases *)
  let cf_loop : st_m_fun =
   fun res ctx ->
    match res with
    | Return ->
        (* We replace the [Return] with a [LoopReturn] *)
        cf (LoopReturn loop_id) ctx
    | Panic -> cf res ctx
    | Break i ->
        (* Break out of the loop by calling the continuation *)
        let res = if i = 0 then Unit else Break (i - 1) in
        cf res ctx
    | Continue i ->
        (* We don't support nested loops for now *)
        assert (i = 0);
        let cc =
          match_ctx_with_target config loop_id false fp_bl_corresp
            fp_input_svalues fixed_ids fp_ctx
        in
        cc cf ctx
    | Unit | LoopReturn _ | EndEnterLoop _ | EndContinue _ ->
        (* For why we can't get [Unit], see the comments inside {!eval_loop_concrete}.
           For [EndEnterLoop] and [EndContinue]: we don't support nested loops for now.
        *)
        raise (Failure "Unreachable")
  in
  let loop_expr = eval_loop_body cf_loop fp_ctx in

  log#ldebug
    (lazy
      ("eval_loop_symbolic: result:" ^ "\n- src context:\n"
      ^ eval_ctx_to_string_no_filter ctx
      ^ "\n- fixed point:\n"
      ^ eval_ctx_to_string_no_filter fp_ctx
      ^ "\n- fixed_sids: "
      ^ SymbolicValueId.Set.show fixed_ids.sids
      ^ "\n- fresh_sids: "
      ^ SymbolicValueId.Set.show fresh_sids
      ^ "\n- input_svalues: "
      ^ Print.list_to_string (symbolic_value_to_string ctx) input_svalues
      ^ "\n\n"));

  (* For every abstraction introduced by the fixed-point, compute the
     types of the given back values.

     We need to explore the abstractions, looking for the mutable borrows.
     Moreover, we list the borrows in the same order as the loans (this
     is important in {!SymbolicToPure}, where we expect the given back
     values to have a specific order.
  *)
  let compute_abs_given_back_tys (abs : abs) : RegionId.Set.t * rty list =
    let is_borrow (av : typed_avalue) : bool =
      match av.value with
      | ABorrow _ -> true
      | ALoan _ -> false
      | _ -> raise (Failure "Unreachable")
    in
    let borrows, loans = List.partition is_borrow abs.avalues in

    let borrows =
      List.filter_map
        (fun (av : typed_avalue) ->
          match av.value with
          | ABorrow (AMutBorrow (bid, child_av)) ->
              assert (is_aignored child_av.value);
              Some (bid, child_av.ty)
          | ABorrow (ASharedBorrow _) -> None
          | _ -> raise (Failure "Unreachable"))
        borrows
    in
    let borrows = ref (BorrowId.Map.of_list borrows) in

    let loan_ids =
      List.filter_map
        (fun (av : typed_avalue) ->
          match av.value with
          | ALoan (AMutLoan (bid, child_av)) ->
              assert (is_aignored child_av.value);
              Some bid
          | ALoan (ASharedLoan _) -> None
          | _ -> raise (Failure "Unreachable"))
        loans
    in

    (* List the given back types, in the order given by the loans *)
    let given_back_tys =
      List.map
        (fun lid ->
          let bid =
            BorrowId.InjSubst.find lid fp_bl_corresp.loan_to_borrow_id_map
          in
          let ty = BorrowId.Map.find bid !borrows in
          borrows := BorrowId.Map.remove bid !borrows;
          ty)
        loan_ids
    in
    assert (BorrowId.Map.is_empty !borrows);

    (abs.regions, given_back_tys)
  in
  let rg_to_given_back =
    RegionGroupId.Map.map compute_abs_given_back_tys rg_to_abs
  in

  (* Put together *)
  S.synthesize_loop loop_id input_svalues fresh_sids rg_to_given_back end_expr
    loop_expr

let eval_loop (config : config) (eval_loop_body : st_cm_fun) : st_cm_fun =
 fun cf ctx ->
  match config.mode with
  | ConcreteMode -> eval_loop_concrete eval_loop_body cf ctx
  | SymbolicMode ->
      (* We want to make sure the loop will *not* manipulate shared avalues
         containing themselves shared loans (i.e., nested shared loans in
         the abstractions), because it complexifies the matches between values
         (when joining environments, or checking that two environments are
         equivalent).

         We thus call {!prepare_ashared_loans} once *before* diving into
         the loop, to make sure the shared values are deconstructed.

         Note that we will call this function again inside {!eval_loop_symbolic},
         to introduce fresh, non-fixed abstractions containing the shared values
         which can be manipulated (and thus borrowed, expanded, etc.) so
         that the fixed abstractions are never modified.

         This is important to understand: we call this function once here to
         introduce *fixed* abstractions, and again later to introduce
         *non-fixed* abstractions.
      *)
      let cc = prepare_ashared_loans None in
      comp cc (eval_loop_symbolic config eval_loop_body) cf ctx
