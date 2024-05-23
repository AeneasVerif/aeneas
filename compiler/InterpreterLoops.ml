open Types
open Values
open Contexts
open ValuesUtils
open Meta
module S = SynthesizeSymbolic
open Cps
open InterpreterUtils
open InterpreterLoopsCore
open InterpreterLoopsMatchCtxs
open InterpreterLoopsFixedPoint
open Errors

(** The local logger *)
let log = Logging.loops_log

(** Evaluate a loop in concrete mode *)
let eval_loop_concrete (meta : Meta.meta) (eval_loop_body : stl_cm_fun) :
    stl_cm_fun =
 fun ctx ->
  (* We need a loop id for the [LoopReturn]. In practice it won't be used
     (it is useful only for the symbolic execution *)
  let loop_id = fresh_loop_id () in
  (* Function to recursively evaluate the loop

     We need a specific function because of the {!Continue} case: in case we
     continue, we might have to reevaluate the current loop body with the
     new context (and repeat this an indefinite number of times).
  *)
  let rec rec_eval_loop_body (ctx : eval_ctx) (res : statement_eval_res) =
    log#ldebug (lazy "eval_loop_concrete: reeval_loop_body");
    match res with
    | Return -> [ (ctx, LoopReturn loop_id) ]
    | Panic -> [ (ctx, Panic) ]
    | Break i ->
        (* Break out of the loop *)
        let res = if i = 0 then Unit else Break (i - 1) in
        [ (ctx, res) ]
    | Continue 0 ->
        (* Re-evaluate the loop body *)
        let ctx_resl, _ = eval_loop_body ctx in
        let ctx_res_cfl =
          List.map (fun (ctx, res) -> rec_eval_loop_body ctx res) ctx_resl
        in
        List.flatten ctx_res_cfl
    | Continue i ->
        (* Continue to an outer loop *)
        [ (ctx, Continue (i - 1)) ]
    | Unit ->
        (* We can't get there.
         * Note that if we decide not to fail here but rather do
         * the same thing as for [Continue 0], we could make the
         * code slightly simpler: calling {!reeval_loop_body} with
         * {!Unit} would account for the first iteration of the loop.
         * We prefer to write it this way for consistency and sanity,
         * though. *)
        craise __FILE__ __LINE__ meta "Unreachable"
    | LoopReturn _ | EndEnterLoop _ | EndContinue _ ->
        (* We can't get there: this is only used in symbolic mode *)
        craise __FILE__ __LINE__ meta "Unreachable"
  in

  (* Apply - for the first iteration, we use the result `Continue 0` to evaluate
     the loop body at least once *)
  let ctx_resl = rec_eval_loop_body ctx (Continue 0) in
  (* If we evaluate in concrete mode, we shouldn't have to generate any symbolic expression *)
  let cf el =
    sanity_check __FILE__ __LINE__ (el = None) meta;
    None
  in
  (ctx_resl, cf)

(** Evaluate a loop in symbolic mode *)
let eval_loop_symbolic (config : config) (meta : meta)
    (eval_loop_body : stl_cm_fun) : stl_cm_fun =
 fun ctx ->
  (* Debug *)
  log#ldebug
    (lazy
      ("eval_loop_symbolic:\nContext:\n"
      ^ eval_ctx_to_string ~meta:(Some meta) ctx
      ^ "\n\n"));

  (* Generate a fresh loop id *)
  let loop_id = fresh_loop_id () in

  (* Compute the fixed point at the loop entrance *)
  let fp_ctx, fixed_ids, rg_to_abs =
    compute_loop_entry_fixed_point config meta loop_id eval_loop_body ctx
  in

  (* Debug *)
  log#ldebug
    (lazy
      ("eval_loop_symbolic:\nInitial context:\n"
      ^ eval_ctx_to_string ~meta:(Some meta) ctx
      ^ "\n\nFixed point:\n"
      ^ eval_ctx_to_string ~meta:(Some meta) fp_ctx));

  (* Compute the loop input parameters *)
  let fresh_sids, input_svalues =
    compute_fp_ctx_symbolic_values meta ctx fp_ctx
  in
  let fp_input_svalues = List.map (fun sv -> sv.sv_id) input_svalues in

  (* Synthesize the end of the function - we simply match the context at the
     loop entry with the fixed point: in the synthesized code, the function
     will end with a call to the loop translation
  *)
  let ((res_fun_end, cf_fun_end), fp_bl_corresp) :
      ((eval_ctx * statement_eval_res) * (eval_result -> eval_result)) * _ =
    (* First, preemptively end borrows/move values by matching the current
       context with the target context *)
    let ctx, cf_prepare =
      log#ldebug
        (lazy
          ("eval_loop_symbolic: about to reorganize the original context to \
            match the fixed-point ctx with it:\n\
            - src ctx (fixed-point ctx):\n" ^ eval_ctx_to_string fp_ctx
         ^ "\n\n-tgt ctx (original context):\n" ^ eval_ctx_to_string ctx));

      prepare_match_ctx_with_target config meta loop_id fixed_ids fp_ctx ctx
    in

    (* Actually match *)
    log#ldebug
      (lazy
        ("eval_loop_symbolic: about to compute the id correspondance between \
          the fixed-point ctx and the original ctx:\n\
          - src ctx (fixed-point ctx)" ^ eval_ctx_to_string fp_ctx
       ^ "\n\n-tgt ctx (original context):\n" ^ eval_ctx_to_string ctx));

    (* Compute the id correspondance between the contexts *)
    let fp_bl_corresp =
      compute_fixed_point_id_correspondance meta fixed_ids ctx fp_ctx
    in
    log#ldebug
      (lazy
        ("eval_loop_symbolic: about to match the fixed-point context with the \
          original context:\n\
          - src ctx (fixed-point ctx)"
        ^ eval_ctx_to_string ~meta:(Some meta) fp_ctx
        ^ "\n\n-tgt ctx (original context):\n"
        ^ eval_ctx_to_string ~meta:(Some meta) ctx));

    (* Compute the end expression, that is the expresion corresponding to the
       end of the functin where we call the loop (for now, when calling a loop
       we never get out) *)
    let res_fun_end =
      comp cf_prepare
        (match_ctx_with_target config meta loop_id true fp_bl_corresp
           fp_input_svalues fixed_ids fp_ctx ctx)
    in
    (res_fun_end, fp_bl_corresp)
  in
  log#ldebug
    (lazy
      "eval_loop_symbolic: matched the fixed-point context with the original \
       context");

  (* Synthesize the loop body *)
  let (resl_loop_body, cf_loop_body) :
      (eval_ctx * statement_eval_res) list
      * (SymbolicAst.expression list option -> eval_result) =
    (* First, evaluate the loop body starting from the **fixed-point** context *)
    let ctx_resl, cf_loop = eval_loop_body fp_ctx in

    (* Then, do a special treatment of the break and continue cases.
       For now, we forbid having breaks in loops (and eliminate breaks
       in the prepasses) *)
    let eval_after_loop_iter (ctx, res) =
      log#ldebug (lazy "eval_loop_symbolic: eval_after_loop_iter");
      match res with
      | Return ->
          (* We replace the [Return] with a [LoopReturn] *)
          ((ctx, LoopReturn loop_id), fun e -> e)
      | Panic -> ((ctx, res), fun e -> e)
      | Break _ ->
          (* Breaks should have been eliminated in the prepasses *)
          craise __FILE__ __LINE__ meta "Unexpected break"
      | Continue i ->
          (* We don't support nested loops for now *)
          cassert __FILE__ __LINE__ (i = 0) meta
            "Nested loops are not supported yet";
          log#ldebug
            (lazy
              ("eval_loop_symbolic: about to match the fixed-point context \
                with the context at a continue:\n\
                - src ctx (fixed-point ctx)"
              ^ eval_ctx_to_string ~meta:(Some meta) fp_ctx
              ^ "\n\n-tgt ctx (ctx at continue):\n"
              ^ eval_ctx_to_string ~meta:(Some meta) ctx));
          match_ctx_with_target config meta loop_id false fp_bl_corresp
            fp_input_svalues fixed_ids fp_ctx ctx
      | Unit | LoopReturn _ | EndEnterLoop _ | EndContinue _ ->
          (* For why we can't get [Unit], see the comments inside {!eval_loop_concrete}.
             For [EndEnterLoop] and [EndContinue]: we don't support nested loops for now.
          *)
          craise __FILE__ __LINE__ meta "Unreachable"
    in

    (* Apply and compose *)
    let ctx_resl, cfl = List.split (List.map eval_after_loop_iter ctx_resl) in
    let cc (el : SymbolicAst.expression list option) : eval_result =
      match el with
      | None -> None
      | Some el ->
          let el =
            List.map
              (fun (cf, e) -> Option.get (cf (Some e)))
              (List.combine cfl el)
          in
          cf_loop (Some el)
    in

    (ctx_resl, cc)
  in

  log#ldebug
    (lazy
      ("eval_loop_symbolic: result:" ^ "\n- src context:\n"
      ^ eval_ctx_to_string_no_filter ~meta:(Some meta) ctx
      ^ "\n- fixed point:\n"
      ^ eval_ctx_to_string_no_filter ~meta:(Some meta) fp_ctx
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

     Also, we filter the backward functions which and
     return nothing.
  *)
  let rg_to_given_back =
    let compute_abs_given_back_tys (abs : abs) : rty list =
      let is_borrow (av : typed_avalue) : bool =
        match av.value with
        | ABorrow _ -> true
        | ALoan _ -> false
        | _ -> craise __FILE__ __LINE__ meta "Unreachable"
      in
      let borrows, loans = List.partition is_borrow abs.avalues in

      let borrows =
        List.filter_map
          (fun (av : typed_avalue) ->
            match av.value with
            | ABorrow (AMutBorrow (bid, child_av)) ->
                sanity_check __FILE__ __LINE__ (is_aignored child_av.value) meta;
                Some (bid, child_av.ty)
            | ABorrow (ASharedBorrow _) -> None
            | _ -> craise __FILE__ __LINE__ meta "Unreachable")
          borrows
      in
      let borrows = ref (BorrowId.Map.of_list borrows) in

      let loan_ids =
        List.filter_map
          (fun (av : typed_avalue) ->
            match av.value with
            | ALoan (AMutLoan (bid, child_av)) ->
                sanity_check __FILE__ __LINE__ (is_aignored child_av.value) meta;
                Some bid
            | ALoan (ASharedLoan _) -> None
            | _ -> craise __FILE__ __LINE__ meta "Unreachable")
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
      sanity_check __FILE__ __LINE__ (BorrowId.Map.is_empty !borrows) meta;

      given_back_tys
    in
    RegionGroupId.Map.map compute_abs_given_back_tys rg_to_abs
  in

  (* Put everything together *)
  let cc (el : SymbolicAst.expression list option) =
    match el with
    | None -> None
    | Some el -> (
        match el with
        | [] -> internal_error __FILE__ __LINE__ meta
        | e :: el ->
            let fun_end_expr = cf_fun_end (Some e) in
            let loop_expr = cf_loop_body (Some el) in
            S.synthesize_loop loop_id input_svalues fresh_sids rg_to_given_back
              fun_end_expr loop_expr meta)
  in
  (res_fun_end :: resl_loop_body, cc)

let eval_loop (config : config) (meta : meta) (eval_loop_body : stl_cm_fun) :
    stl_cm_fun =
 fun ctx ->
  match config.mode with
  | ConcreteMode -> (eval_loop_concrete meta eval_loop_body) ctx
  | SymbolicMode ->
      (* Simplify the context by ending the unnecessary borrows/loans and getting
         rid of the useless symbolic values (which are in anonymous variables) *)
      let ctx, cc =
        cleanup_fresh_values_and_abs config meta empty_ids_set ctx
      in

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
      let ctx, cc = comp cc (prepare_ashared_loans meta None ctx) in
      comp cc (eval_loop_symbolic config meta eval_loop_body ctx)
