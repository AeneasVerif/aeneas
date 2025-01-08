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
let eval_loop_concrete (span : Meta.span) (eval_loop_body : stl_cm_fun) :
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
    log#ltrace (lazy "eval_loop_concrete: reeval_loop_body");
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
        craise __FILE__ __LINE__ span "Unreachable"
    | LoopReturn _ | EndEnterLoop _ | EndContinue _ ->
        (* We can't get there: this is only used in symbolic mode *)
        craise __FILE__ __LINE__ span "Unreachable"
  in

  (* Apply - for the first iteration, we use the result `Continue 0` to evaluate
     the loop body at least once *)
  let ctx_resl = rec_eval_loop_body ctx (Continue 0) in
  (* If we evaluate in concrete mode, we shouldn't have to generate any symbolic expression *)
  let cf _ = internal_error __FILE__ __LINE__ span in
  (ctx_resl, cf)

(** Auxiliary function for {!eval_loop_symbolic}.

    Match the context upon entering the loop with the loop fixed-point to
    compute how to "apply" the fixed-point. Compute the correspondance from
    the borrow ids in the current context to the loans which appear in the
    loop context (we need this in order to know how to introduce the region
    abstractions of the loop).

    We check the fixed-point at the same time to make sure the loans and borrows
    inside the region abstractions are properly ordered (this is necessary for the
    synthesis).
    Ex.: if in the fixed point we have:
    {[
      abs { MB l0, MB l1, ML l2, ML l3 }
    ]}
    we want to make sure that borrow l0 actually corresponds to loan l2, and
    borrow l1 to loan l3.
 *)
let eval_loop_symbolic_synthesize_fun_end (config : config) (span : span)
    (loop_id : LoopId.id) (init_ctx : eval_ctx) (fixed_ids : ids_sets)
    (fp_ctx : eval_ctx) (fp_input_svalues : SymbolicValueId.id list)
    (rg_to_abs : AbstractionId.id RegionGroupId.Map.t) :
    ((eval_ctx * statement_eval_res)
    * (SymbolicAst.expression -> SymbolicAst.expression))
    * borrow_loan_corresp =
  log#ltrace
    (lazy
      (__FUNCTION__
     ^ ": about to reorganize the original context to match the fixed-point \
        ctx with it:\n\
        - src ctx (fixed-point ctx):\n" ^ eval_ctx_to_string fp_ctx
     ^ "\n\n-tgt ctx (original context):\n"
      ^ eval_ctx_to_string init_ctx));

  let ctx = init_ctx in

  (* Preemptively end borrows/move values by matching the current
     context with the target context *)
  let ctx, cf_prepare =
    prepare_loop_match_ctx_with_target config span loop_id fixed_ids fp_ctx ctx
  in

  (* Actually match *)
  log#ltrace
    (lazy
      (__FUNCTION__
     ^ ": about to compute the id correspondance between the fixed-point ctx \
        and the original ctx:\n\
        - src ctx (fixed-point ctx)\n" ^ eval_ctx_to_string fp_ctx
     ^ "\n\n-tgt ctx (original context):\n" ^ eval_ctx_to_string ctx));

  (* Compute the id correspondance between the contexts *)
  let fp_bl_corresp =
    compute_fixed_point_id_correspondance span fixed_ids ctx fp_ctx
  in
  log#ltrace
    (lazy
      (__FUNCTION__
     ^ ": about to match the fixed-point context with the original context:\n\
        - src ctx (fixed-point ctx)"
      ^ eval_ctx_to_string ~span:(Some span) fp_ctx
      ^ "\n\n-tgt ctx (original context):\n"
      ^ eval_ctx_to_string ~span:(Some span) ctx
      ^ "\n\n- fp_bl_corresp:\n"
      ^ show_borrow_loan_corresp fp_bl_corresp
      ^ "\n"));

  (* Compute the end expression, that is the expresion corresponding to the
     end of the function where we call the loop (for now, when calling a loop
     we never get out) *)
  let res_fun_end =
    comp cf_prepare
      (loop_match_ctx_with_target config span loop_id true fp_bl_corresp
         fp_input_svalues fixed_ids fp_ctx ctx)
  in

  (* Sanity check: the mutable borrows/loans are properly ordered.
     TODO: it seems that the way the fixed points are computed makes this check
     always succeed. If it happens to fail we can reorder the borrows/loans
     inside the region abstractions. *)
  let check_abs (abs_id : AbstractionId.id) =
    let abs = ctx_lookup_abs fp_ctx abs_id in
    log#ltrace
      (lazy
        (__FUNCTION__ ^ ": checking abs:\n" ^ abs_to_string span ctx abs ^ "\n"));

    let is_borrow (av : typed_avalue) : bool =
      match av.value with
      | ABorrow _ | ASymbolic (_, AProjBorrows _) -> true
      | ALoan _ | ASymbolic (_, AProjLoans _) -> false
      | _ -> craise __FILE__ __LINE__ span "Unreachable"
    in
    let borrows, loans = List.partition is_borrow abs.avalues in

    let mut_borrows =
      List.filter_map
        (fun (av : typed_avalue) ->
          match av.value with
          | ABorrow (AMutBorrow (pm, bid, child_av)) ->
              sanity_check __FILE__ __LINE__ (pm = PNone) span;
              sanity_check __FILE__ __LINE__ (is_aignored child_av.value) span;
              Some bid
          | ABorrow (ASharedBorrow (pm, _)) ->
              sanity_check __FILE__ __LINE__ (pm = PNone) span;
              None
          | ASymbolic (_, (AProjBorrows _ | AProjLoans _)) -> None
          | _ -> craise __FILE__ __LINE__ span "Unreachable")
        borrows
    in

    let borrow_projs =
      List.filter_map
        (fun (av : typed_avalue) ->
          match av.value with
          | ASymbolic (pm, AProjBorrows (sv, _proj_ty, children)) ->
              sanity_check __FILE__ __LINE__ (pm = PNone) span;
              sanity_check __FILE__ __LINE__ (children = []) span;
              Some sv.sv_id
          | _ -> None)
        borrows
    in

    let mut_loans =
      List.filter_map
        (fun (av : typed_avalue) ->
          match av.value with
          | ALoan (AMutLoan (pm, bid, child_av)) ->
              sanity_check __FILE__ __LINE__ (pm = PNone) span;
              sanity_check __FILE__ __LINE__ (is_aignored child_av.value) span;
              Some bid
          | ALoan (ASharedLoan (pm, _, _, _)) ->
              sanity_check __FILE__ __LINE__ (pm = PNone) span;
              None
          | ASymbolic (_, (AProjBorrows _ | AProjLoans _)) -> None
          | _ -> craise __FILE__ __LINE__ span "Unreachable")
        loans
    in

    let loan_projs =
      List.filter_map
        (fun (av : typed_avalue) ->
          match av.value with
          | ASymbolic (pm, AProjLoans (sv, _proj_ty, children)) ->
              sanity_check __FILE__ __LINE__ (pm = PNone) span;
              sanity_check __FILE__ __LINE__ (children = []) span;
              Some sv.sv_id
          | _ -> None)
        loans
    in

    sanity_check __FILE__ __LINE__
      (List.length mut_borrows = List.length mut_loans)
      span;
    sanity_check __FILE__ __LINE__
      (List.length borrow_projs = List.length loan_projs)
      span;

    let borrows_loans = List.combine mut_borrows mut_loans in
    List.iter
      (fun (bid, lid) ->
        let lid_of_bid =
          BorrowId.InjSubst.find bid fp_bl_corresp.borrow_to_loan_id_map
        in
        sanity_check __FILE__ __LINE__ (lid_of_bid = lid) span)
      borrows_loans;

    let borrow_loan_projs = List.combine borrow_projs loan_projs in
    List.iter
      (fun (bid, lid) ->
        let lid_of_bid =
          SymbolicValueId.InjSubst.find bid
            fp_bl_corresp.borrow_to_loan_proj_map
        in
        sanity_check __FILE__ __LINE__ (lid_of_bid = lid) span)
      borrow_loan_projs
  in
  List.iter check_abs (RegionGroupId.Map.values rg_to_abs);

  (* Return *)
  (res_fun_end, fp_bl_corresp)

(** Auxiliary function for {!eval_loop_symbolic}.

    Synthesize the body of the loop.
 *)
let eval_loop_symbolic_synthesize_loop_body (config : config) (span : span)
    (eval_loop_body : stl_cm_fun) (loop_id : LoopId.id) (fixed_ids : ids_sets)
    (fp_ctx : eval_ctx) (fp_input_svalues : SymbolicValueId.id list)
    (fp_bl_corresp : borrow_loan_corresp) :
    (eval_ctx * statement_eval_res) list
    * (SymbolicAst.expression list -> SymbolicAst.expression) =
  (* First, evaluate the loop body starting from the **fixed-point** context *)
  let ctx_resl, cf_loop = eval_loop_body fp_ctx in

  (* Then, do a special treatment of the break and continue cases.
     For now, we forbid having breaks in loops (and eliminate breaks
     in the prepasses) *)
  let eval_after_loop_iter (ctx, res) =
    log#ltrace (lazy "eval_loop_symbolic: eval_after_loop_iter");
    match res with
    | Return ->
        (* We replace the [Return] with a [LoopReturn] *)
        ((ctx, LoopReturn loop_id), fun e -> e)
    | Panic -> ((ctx, res), fun e -> e)
    | Break _ ->
        (* Breaks should have been eliminated in the prepasses *)
        craise __FILE__ __LINE__ span "Unexpected break"
    | Continue i ->
        (* We don't support nested loops for now *)
        cassert __FILE__ __LINE__ (i = 0) span
          "Nested loops are not supported yet";
        log#ltrace
          (lazy
            ("eval_loop_symbolic: about to match the fixed-point context with \
              the context at a continue:\n\
              - src ctx (fixed-point ctx)"
            ^ eval_ctx_to_string ~span:(Some span) fp_ctx
            ^ "\n\n-tgt ctx (ctx at continue):\n"
            ^ eval_ctx_to_string ~span:(Some span) ctx));
        loop_match_ctx_with_target config span loop_id false fp_bl_corresp
          fp_input_svalues fixed_ids fp_ctx ctx
    | Unit | LoopReturn _ | EndEnterLoop _ | EndContinue _ ->
        (* For why we can't get [Unit], see the comments inside {!eval_loop_concrete}.
           For [EndEnterLoop] and [EndContinue]: we don't support nested loops for now.
        *)
        craise __FILE__ __LINE__ span "Unreachable"
  in

  (* Apply and compose *)
  let ctx_resl, cfl = List.split (List.map eval_after_loop_iter ctx_resl) in
  let cc (el : SymbolicAst.expression list) : SymbolicAst.expression =
    let el = List.map (fun (cf, e) -> cf e) (List.combine cfl el) in
    cf_loop el
  in

  (ctx_resl, cc)

(** Evaluate a loop in symbolic mode *)
let eval_loop_symbolic (config : config) (span : span)
    (eval_loop_body : stl_cm_fun) : stl_cm_fun =
 fun ctx ->
  (* Debug *)
  log#ltrace
    (lazy
      (__FUNCTION__ ^ ":\nContext:\n"
      ^ eval_ctx_to_string ~span:(Some span) ctx
      ^ "\n\n"));

  (* Generate a fresh loop id *)
  let loop_id = fresh_loop_id () in

  (* Compute the fixed point at the loop entrance *)
  let fp_ctx, fixed_ids, rg_to_abs =
    compute_loop_entry_fixed_point config span loop_id eval_loop_body ctx
  in

  (* Debug *)
  log#ltrace
    (lazy
      (__FUNCTION__ ^ ":\nInitial context:\n"
      ^ eval_ctx_to_string ~span:(Some span) ctx
      ^ "\n\nFixed point:\n"
      ^ eval_ctx_to_string ~span:(Some span) fp_ctx));

  (* Compute the loop input parameters *)
  let fresh_sids, input_svalues =
    compute_fp_ctx_symbolic_values span ctx fp_ctx
  in
  let fp_input_svalues = List.map (fun sv -> sv.sv_id) input_svalues in

  (* Synthesize the end of the function - we simply match the context at the
     loop entry with the fixed point: in the synthesized code, the function
     will end with a call to the loop translation.

     We update the loop fixed point at the same time by reordering the borrows/
     loans which appear inside it.
  *)
  let (res_fun_end, cf_fun_end), fp_bl_corresp =
    eval_loop_symbolic_synthesize_fun_end config span loop_id ctx fixed_ids
      fp_ctx fp_input_svalues rg_to_abs
  in

  log#ltrace
    (lazy
      (__FUNCTION__
     ^ ": matched the fixed-point context with the original context."));

  (* Synthesize the loop body *)
  let resl_loop_body, cf_loop_body =
    eval_loop_symbolic_synthesize_loop_body config span eval_loop_body loop_id
      fixed_ids fp_ctx fp_input_svalues fp_bl_corresp
  in

  log#ltrace
    (lazy
      (__FUNCTION__ ^ ": result:" ^ "\n- src context:\n"
      ^ eval_ctx_to_string ~span:(Some span) ~filter:false ctx
      ^ "\n- fixed point:\n"
      ^ eval_ctx_to_string ~span:(Some span) ~filter:false fp_ctx
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
    let compute_abs_given_back_tys (abs_id : AbstractionId.id) : Pure.ty list =
      let abs = ctx_lookup_abs fp_ctx abs_id in
      log#ltrace
        (lazy
          (__FUNCTION__ ^ ": compute_abs_given_back_tys:\n- abs:\n"
          ^ abs_to_string span ~with_ended:true ctx abs
          ^ "\n"));

      let is_borrow (av : typed_avalue) : bool =
        match av.value with
        | ABorrow _ | ASymbolic (_, AProjBorrows _) -> true
        | ALoan _ | ASymbolic (_, AProjLoans _) -> false
        | _ -> craise __FILE__ __LINE__ span "Unreachable"
      in
      let borrows, _ = List.partition is_borrow abs.avalues in

      List.filter_map
        (fun (av : typed_avalue) ->
          SymbolicToPure.translate_back_ty (Some span) ctx.type_ctx.type_infos
            (function
              | RVar (Free rid) -> RegionId.Set.mem rid abs.regions.owned
              | _ -> false)
            false av.ty)
        borrows
    in
    RegionGroupId.Map.map compute_abs_given_back_tys rg_to_abs
  in

  (* Put everything together *)
  let cc (el : SymbolicAst.expression list) =
    match el with
    | [] -> internal_error __FILE__ __LINE__ span
    | e :: el ->
        let fun_end_expr = cf_fun_end e in
        let loop_expr = cf_loop_body el in
        SymbolicAst.Loop
          {
            loop_id;
            input_svalues;
            fresh_svalues = fresh_sids;
            rg_to_given_back_tys = rg_to_given_back;
            end_expr = fun_end_expr;
            loop_expr;
            span;
          }
  in
  (res_fun_end :: resl_loop_body, cc)

let eval_loop (config : config) (span : span) (eval_loop_body : stl_cm_fun) :
    stl_cm_fun =
 fun ctx ->
  match config.mode with
  | ConcreteMode -> (eval_loop_concrete span eval_loop_body) ctx
  | SymbolicMode ->
      (* Preemptively simplify the context by ending the unnecessary borrows/loans and getting
         rid of the useless symbolic values (which are in anonymous variables) *)
      let ctx, cc =
        InterpreterBorrows.simplify_dummy_values_useless_abs config span
          ~simplify_abs:false AbstractionId.Set.empty ctx
      in

      (* We want to make sure the loop will *not* manipulate shared avalues
         themselves containing shared loans (i.e., nested shared loans in
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
      let ctx, cc = comp cc (prepare_ashared_loans span None ctx) in
      comp cc (eval_loop_symbolic config span eval_loop_body ctx)
