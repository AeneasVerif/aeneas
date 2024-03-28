open Types
open Values
open Contexts
open Meta
module S = SynthesizeSymbolic
open Cps
open InterpreterUtils
open InterpreterBorrows
open InterpreterLoopsCore
open InterpreterLoopsMatchCtxs
open InterpreterLoopsJoinCtxs
open InterpreterLoopsFixedPoint
module SA = SymbolicAst

(** The local logger *)
let log = Logging.loops_log

(** Evaluate a loop in concrete mode *)
let eval_loop_concrete (eval_loop_body : st_cm_fun) : st_cm_fun =
 fun cf ctx ->
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
    log#ldebug (lazy "eval_loop_concrete: reeval_loop_body");
    match res with
    | Return -> cf Return
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
  in

  (* Apply *)
  eval_loop_body reeval_loop_body ctx

(** Compute the loop output context (the context resulting from calling the
    loop).

    For now, this is just the context that we get upon reaching the [return].
  *)
let compute_loop_output_contexts (config : config) (loop_id : LoopId.id)
    (eval_loop_body : st_cm_fun) (fp_ctx : eval_ctx) (fixed_ids : ids_sets) :
    eval_ctx option * eval_ctx option =
  log#ldebug (lazy "compute_loop_output_context:\n");
  (* The environments at returns *)
  let return_ctxs = ref [] in
  let register_return_ctx ctx = return_ctxs := ctx :: !return_ctxs in
  (* The environments at breaks *)
  let break_ctxs = ref [] in
  let register_break_ctx ctx = break_ctxs := ctx :: !break_ctxs in
  let cf_loop : st_m_fun =
   fun res ctx ->
    log#ldebug (lazy "eval_loop_symbolic: cf_loop");
    match res with
    | Return ->
        (* Register the context *)
        let _ =
          cleanup_fresh_values_and_abs config fixed_ids
            (fun ctx ->
              register_return_ctx ctx;
              None)
            ctx
        in
        None
    | Panic ->
        (* Nothing to do *)
        None
    | Break i ->
        (* Register the context *)
        if i <> 0 then raise (Failure "Breaks to outer loops not supported yet");
        register_break_ctx ctx;
        None
    | Continue i ->
        (* We don't support nested loops for now *)
        assert (i = 0);
        (* Nothing to do: we already computed the fixed-point *)
        None
    | Unit ->
        (* For why we can't get [Unit], see the comments inside {!eval_loop_concrete}. *)
        raise (Failure "Unreachable")
  in
  let _ = eval_loop_body cf_loop fp_ctx in

  (* A small utility to compute joined environments *)
  let compute_joined (kind : string) (ctxs : eval_ctx list) : eval_ctx option =
    match ctxs with
    | [] ->
        log#ldebug
          (lazy ("compute_loop_output_context: no " ^ kind ^ " context\n"));
        None
    | ctx :: ctxl ->
        let _, joined_ctx =
          loop_join_with_ctxs config loop_id fixed_ids ctx ctxl
        in
        log#ldebug
          (lazy
            ("compute_loop_output_context: " ^ kind ^ " context:"
           ^ "\n\n- fp_ctx:\n"
            ^ eval_ctx_to_string_no_filter fp_ctx
            ^ "\n\n- " ^ kind ^ "_ctx:\n"
            ^ eval_ctx_to_string_no_filter joined_ctx
            ^ "\n\n"));
        Some joined_ctx
  in

  (* Compute the joined environment at the return *)
  let return_ctx = compute_joined "return" !return_ctxs in

  (* Compute the joined environment at the break *)
  let break_ctx = compute_joined "break" !break_ctxs in

  (return_ctx, break_ctx)

type loop_output_ctx_info = {
  ctx : eval_ctx;
  fresh_svalues : symbolic_value list;
  fresh_abs : abs AbstractionId.Map.t;
}

type loop_match_info = {
  input_values : typed_value SymbolicValueId.Map.t;
  fresh_svalues : symbolic_value list;
  return_info : loop_output_ctx_info option;
  break_info : loop_output_ctx_info option;
}

(** The loop "signature" - TODO: add the joined environments at the breaks,
    continues, returns so that we truely have a signature *)
type loop_sig = {
  fp_ctx : eval_ctx;
  fixed_ids : ids_sets;  (** The sets of fixed ids *)
  input_svalues : symbolic_value list;  (** The input symbolic values *)
  body : SymbolicAst.expression option;  (** The body of the loop *)
}

let loop_sig_to_string (sg : loop_sig) : string =
  let { fp_ctx; fixed_ids; input_svalues = _; body; _ } = sg in
  "{" ^ "\n-fp_ctx\n" ^ eval_ctx_to_string fp_ctx ^ "\n\n- fixed_sids: "
  ^ SymbolicValueId.Set.show fixed_ids.sids
  ^ "\n\n- body:\n"
  ^ Print.option_to_string SA.show_expression body
  ^ "\n}"

(** Small helper.

    End the loop input abstractions to synthesize the end of a function.
 *)
let eval_loop_end (config : config) (loop_id : LoopId.id) (ctx : eval_ctx)
    (cf : m_fun) : (RegionGroupId.id * SA.expression option) list =
  log#ldebug
    (lazy
      ("eval_loop_end:" ^ "\n- loop_id: " ^ LoopId.to_string loop_id
     ^ "\n- ctx:\n"
      ^ Print.Contexts.eval_ctx_to_string ctx));

  (* List all the input abstractions of the current loop *)
  let abs_ids =
    let abs_ids = ref AbstractionId.Map.empty in
    let visitor =
      object
        inherit [_] iter_eval_ctx

        method! visit_abs _ abs =
          match abs.kind with
          | Loop (loop_id', rg_id, LoopSynthInput) ->
              (* Check if this is for the current loop *)
              if loop_id' = loop_id then
                abs_ids :=
                  AbstractionId.Map.add abs.abs_id (Option.get rg_id) !abs_ids
              else ()
          | _ ->
              (* Other abstractions *)
              ()
      end
    in
    visitor#visit_eval_ctx () ctx;
    AbstractionId.Map.bindings !abs_ids
  in

  (* End the region abstractions one by one *)
  let end_one ((abs_id, rg_id) : AbstractionId.id * RegionGroupId.id) :
      RegionGroupId.id * SA.expression option =
    (* Set the proper abstractions as endable *)
    let ctx =
      let visit_loop_abs =
        object
          inherit [_] map_eval_ctx

          method! visit_abs _ abs =
            match abs.kind with
            | Loop (loop_id', _, LoopSynthInput) ->
                if loop_id' = loop_id then { abs with can_end = true } else abs
            | Loop (loop_id', _, LoopCall) ->
                (* We can end all the loop call abstractions *)
                assert (loop_id' = loop_id);
                { abs with can_end = true }
            | _ ->
                (* Other abstractions *)
                abs
        end
      in
      visit_loop_abs#visit_eval_ctx () ctx
    in

    (* End the input abstraction *)
    (rg_id, end_abstraction config abs_id cf ctx)
  in
  List.map end_one abs_ids

let compute_loop_output_ctx_info (old_ctx : eval_ctx) (new_ctx : eval_ctx) :
    loop_output_ctx_info =
  (* Compute the set of fresh ids *)
  let old_ids, _ = compute_ctx_ids old_ctx in
  let new_ids, new_sids_to_values = compute_ctx_ids new_ctx in

  (* Compute the list of fresh symbolic values *)
  let fresh_sids = SymbolicValueId.Set.diff new_ids.sids old_ids.sids in
  let fresh_svalues = SymbolicValueId.Set.elements fresh_sids in
  let fresh_svalues =
    List.map
      (fun id -> SymbolicValueId.Map.find id new_sids_to_values.sids_to_values)
      fresh_svalues
  in

  (* Compute the list of fresh region abstractions *)
  let fresh_sabs =
    AbstractionId.Set.elements
      (AbstractionId.Set.diff new_ids.aids old_ids.aids)
  in
  let fresh_abs =
    AbstractionId.Map.of_list
      (List.map
         (fun abs_id ->
           let abs = ctx_lookup_abs new_ctx abs_id in
           (abs_id, abs))
         fresh_sabs)
  in

  (* Return *)
  { ctx = new_ctx; fresh_svalues; fresh_abs }

let compute_opt_loop_output_ctx_info (old_ctx : eval_ctx)
    (new_ctx : eval_ctx option) : loop_output_ctx_info option =
  Option.map (compute_loop_output_ctx_info old_ctx) new_ctx

(* Match a loop fixed-point context with a target, compute the resulting joined
   contexts at the breaks and continue, and call the continuation from there.
*)
let match_loop_fp_ctx_with_target (config : config) (loop_id : LoopId.id)
    (eval_loop_body : st_cm_fun) (fp_bl_maps : borrow_loan_corresp)
    (fp_input_svalues : symbolic_value list) (fixed_ids : ids_sets)
    (fp_ctx : eval_ctx) (cf : loop_match_info -> eval_result)
    (tgt_ctx : eval_ctx) : eval_result =
  (* The continuation for after matching the contexts. *)
  let cf_after_match (input_values : typed_value SymbolicValueId.Map.t) _
      (ctx_after_match : eval_ctx) : eval_result =
    (* Compute the joined contexts at the break and the return *)
    let return_ctx, break_ctx =
      compute_loop_output_contexts config loop_id eval_loop_body ctx_after_match
        fixed_ids
    in

    let compute_info = compute_opt_loop_output_ctx_info tgt_ctx in
    let return_info = compute_info return_ctx in
    let break_info = compute_info break_ctx in
    cf
      {
        input_values;
        fresh_svalues = fp_input_svalues;
        return_info;
        break_info;
      }
  in

  let abs_kind = LoopCall in
  let can_end = true in
  let fp_input_svalues = List.map (fun sv -> sv.sv_id) fp_input_svalues in
  match_ctx_with_target config loop_id fp_bl_maps fp_input_svalues fixed_ids
    fp_ctx abs_kind can_end cf_after_match tgt_ctx

(** Set all the regions introduced by a loop as endable *)
let set_loop_regions_as_endable (loop_id : LoopId.id) (ctx : eval_ctx) :
    eval_ctx =
  let visitor =
    object
      inherit [_] map_eval_ctx

      method! visit_abs _ abs =
        match abs.kind with
        | Loop (loop_id', _, _) when loop_id' = loop_id ->
            { abs with can_end = true }
        | _ ->
            (* Ignore *)
            abs
    end
  in
  visitor#visit_eval_ctx () ctx

let compute_loop_body (config : config) (loop_id : LoopId.id)
    (eval_loop_body : st_cm_fun) (fp_ctx : eval_ctx) (fixed_ids : ids_sets)
    (fp_input_svalues : symbolic_value list) (return_ctx : eval_ctx option)
    (break_ctx : eval_ctx option) : SA.expression option =
  (* Helper *)
  let compute_end_expr (fresh_svalues : symbolic_value list)
      (fresh_abs : abs AbstractionId.Map.t) (ctx : eval_ctx) :
      SA.expr_call option =
    (* Compute the backward functions *)
    let back_exprs =
      eval_loop_end config loop_id ctx (fun ctx -> Some (SA.Return (ctx, None)))
    in
    if List.exists (fun (_, e) -> Option.is_none e) back_exprs then None
    else
      let back_exprs =
        List.map (fun (rg_id, expr) -> (rg_id, Option.get expr)) back_exprs
      in
      let back_exprs = RegionGroupId.Map.of_list back_exprs in
      Some { SA.fresh_svalues; fresh_abs; back_exprs }
  in
  (* Helper *)
  let cf_match_with_return_break_ctx (ctx : eval_ctx)
      (tgt_ctx : eval_ctx option) (fresh_abs_kind : loop_abs_kind)
      (finish :
        LoopId.id ->
        typed_value SymbolicValueId.Map.t ->
        abs AbstractionId.Map.t ->
        SA.expr_call ->
        SA.expression option) =
    (* Simplify the context *)
    let cf_cleanup = cleanup_fresh_values_and_abs config fixed_ids in
    (* The target context must be present *)
    let tgt_ctx = Option.get tgt_ctx in
    (* Match the target context *)
    let fp_bl_corresp =
      compute_fixed_point_id_correspondance fixed_ids ctx tgt_ctx
    in
    (* The continuation for after the match *)
    let cf (input_values : typed_value SymbolicValueId.Map.t)
        (fresh_absl : abs AbstractionId.Map.t) (ctx : eval_ctx) =
      (* Compute the end expressions for the [return] tags *)
      let fresh_svalues = SymbolicValueId.Map.keys input_values in
      let _, sids_to_values = compute_ctx_ids ctx in
      let fresh_svalues =
        List.map
          (fun id -> SymbolicValueId.Map.find id sids_to_values.sids_to_values)
          fresh_svalues
      in
      let loop_end = compute_end_expr fresh_svalues fresh_absl ctx in
      let loop_end = Option.get loop_end in
      finish loop_id input_values fresh_absl loop_end
    in
    (* Match *)
    let can_end = true in
    let fp_input_svalues_ids = List.map (fun sv -> sv.sv_id) fp_input_svalues in
    let cf_match =
      match_ctx_with_target config loop_id fp_bl_corresp fp_input_svalues_ids
        fixed_ids tgt_ctx fresh_abs_kind can_end cf
    in
    cf_cleanup cf_match ctx
  in
  let cf_loop : st_m_fun =
   fun res ctx ->
    log#ldebug (lazy "compute_loop_body: cf_loop");
    match res with
    | Return ->
        cf_match_with_return_break_ctx ctx return_ctx LoopReturn
          (fun loop_id input_values _ loop_return ->
            Some (SA.LoopReturn (loop_id, input_values, loop_return)))
    | Panic ->
        (* Nothing to do *)
        None
    | Break i ->
        (* We don't support breaks to outer loops for now *)
        if i <> 0 then raise (Failure "Breaks to outer loops not supported yet");
        (* Match with the return context *)
        cf_match_with_return_break_ctx ctx break_ctx LoopBreak
          (fun loop_id input_values _ loop_return ->
            Some (SA.LoopBreak (loop_id, input_values, loop_return)))
    | Continue i ->
        (* We don't support continues to outer loops for now *)
        if i <> 0 then raise (Failure "Breaks to outer loops not supported yet");
        (* Simplify the context *)
        let cf_cleanup = cleanup_fresh_values_and_abs config fixed_ids in
        (* Match with the loop entry context *)
        let fp_bl_corresp =
          compute_fixed_point_id_correspondance fixed_ids ctx fp_ctx
        in
        (* The continuation for after the match: we receive the (optional) joined
           contexts computed at the break/return statements that we reach.
           We then need to resume the evaluation from there by propagating those
           break/return statements. For now, all we have to do is to compute
           the backward functions starting from those statements by ending the
           input synthesis functions one by one.
        *)
        let cf (loop_match_info : loop_match_info) : eval_result =
          let compute_opt_end_expr (ctx_info : loop_output_ctx_info option) :
              SA.expr_call option option =
            match ctx_info with
            | None -> None
            | Some ctx_info ->
                (* There is a break/return *inside* the loop: we have to continue
                   the execution from the joined environment resulting from reaching
                   a break/return.

                   First set the region abstraction introduced by
                   this loop as endable: we might need to end them. *)
                let ctx_info =
                  {
                    ctx_info with
                    ctx = set_loop_regions_as_endable loop_id ctx_info.ctx;
                  }
                in

                (* Compute the end expression by ending the input abstractions
                   of the loop *)
                Some
                  (compute_end_expr ctx_info.fresh_svalues ctx_info.fresh_abs
                     ctx_info.ctx)
          in
          (* Compute the end expressions for the [return] and [break] tags *)
          let loop_return = compute_opt_end_expr loop_match_info.return_info in
          let loop_break = compute_opt_end_expr loop_match_info.break_info in
          (* Do we need to generate an expression or not? *)
          let compute_expr e =
            match e with None | Some (Some _) -> true | Some None -> false
          in
          let compute_expr =
            compute_expr loop_return && compute_expr loop_break
          in
          if compute_expr then
            let get_expr e =
              match e with Some e -> Some (Option.get e) | None -> None
            in
            let continue_return = get_expr loop_return in
            let continue_break = get_expr loop_break in
            Some
              (SA.LoopContinue
                 {
                   loop_id;
                   continue_input_values = loop_match_info.input_values;
                   continue_return;
                   continue_break;
                 })
          else None
        in
        (* Match *)
        let cf_match =
          match_loop_fp_ctx_with_target config loop_id eval_loop_body
            fp_bl_corresp fp_input_svalues fixed_ids fp_ctx cf
        in
        cf_cleanup cf_match ctx
    | Unit ->
        (* For why we can't get [Unit], see the comments inside {!eval_loop_concrete}. *)
        raise (Failure "Unreachable")
  in
  eval_loop_body cf_loop fp_ctx

let compute_loop_sig (config : config) (loop_id : LoopId.id)
    (eval_loop_body : st_cm_fun) (ctx0 : eval_ctx) : loop_sig =
  (* TODO: we recompute several times the same things below (in particular,
     we re-evaluate several times the loop body, and in particular
     recompute the fixed-points of the inner loops every time we evaluate
     this loop body - this is super inefficient)
  *)
  (* Compute the input context (the loop entry fixed-point) *)
  let fp_ctx, fixed_ids, _ =
    compute_loop_entry_fixed_point config loop_id eval_loop_body ctx0
  in

  (* Compute the output contexts (the joined environments at breaks and returns) *)
  let return_ctx, break_ctx =
    compute_loop_output_contexts config loop_id eval_loop_body fp_ctx fixed_ids
  in

  (* Compute the loop input parameters *)
  let _, input_svalues = compute_fp_ctx_symbolic_values ctx0 fp_ctx in

  (* Compute the loop body *)
  let body =
    compute_loop_body config loop_id eval_loop_body fp_ctx fixed_ids
      input_svalues return_ctx break_ctx
  in

  (* Return *)
  { fp_ctx; fixed_ids; input_svalues; body }

(** Evaluate a loop in symbolic mode *)
let eval_loop_symbolic (config : config) (meta : meta)
    (llbc_loop_id : LlbcAst.LoopId.id) (eval_loop_body : st_cm_fun) : st_cm_fun
    =
 fun cf ctx ->
  (* Debug *)
  log#ldebug
    (lazy ("eval_loop_symbolic:\nContext:\n" ^ eval_ctx_to_string ctx ^ "\n\n"));

  (* Generate a fresh loop id *)
  let loop_id = fresh_loop_id () in

  (* Compute the input context (the fixed point at the loop entrance) and the
     loop body. *)
  let loop_sig = compute_loop_sig config loop_id eval_loop_body ctx in
  log#ldebug
    (lazy
      ("eval_loop_symbolic:\n- loop_sig:\n"
      ^ loop_sig_to_string loop_sig
      ^ "\n\n"));

  (* Match with the loop entry context and apply the substitution
     to the joined contexts for the break and the return *)
  let fp_bl_corresp =
    compute_fixed_point_id_correspondance loop_sig.fixed_ids ctx loop_sig.fp_ctx
  in

  (* The continuation for after the loop *)
  let cf_after_loop (match_info : loop_match_info) : eval_result =
    (* Call the continuation: we call it with [Return] starting with the
       joined return state and [Unit] starting with the joined break state,
       if there are.
    *)
    let compute_return_break_expr (res : statement_eval_res)
        (ctx_info : loop_output_ctx_info option) :
        (symbolic_value list * abs AbstractionId.Map.t * SA.expression) option =
      match ctx_info with
      | None -> None
      | Some info ->
          let e = cf res info.ctx in
          Some (info.fresh_svalues, info.fresh_abs, Option.get e)
    in
    let loop_return = compute_return_break_expr Return match_info.return_info in
    let loop_break =
      compute_return_break_expr (Break 0) match_info.break_info
    in

    (* Synthesize *)
    Some
      (SA.Loop
         {
           llbc_loop_id;
           id = loop_id;
           loop_input_values = match_info.input_values;
           loop_fresh_svalues = match_info.fresh_svalues;
           loop_body = Option.get loop_sig.body;
           loan_to_borrow_id_map = fp_bl_corresp.loan_to_borrow_id_map;
           loop_return;
           loop_break;
           meta;
         })
  in
  (* Match *)
  match_loop_fp_ctx_with_target config loop_id eval_loop_body fp_bl_corresp
    loop_sig.input_svalues loop_sig.fixed_ids loop_sig.fp_ctx cf_after_loop ctx

let eval_loop (config : config) (meta : meta) (loop_id : LlbcAst.LoopId.id)
    (eval_loop_body : st_cm_fun) : st_cm_fun =
 fun cf ctx ->
  match config.mode with
  | ConcreteMode -> eval_loop_concrete eval_loop_body cf ctx
  | SymbolicMode ->
      (* Simplify the context by ending the unnecessary borrows/loans and getting
         rid of the useless symbolic values inside anonymous variables. *)
      let cc = cleanup_fresh_values_and_abs config empty_ids_set in

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
      let cc = comp cc (prepare_ashared_loans None) in
      comp cc (eval_loop_symbolic config meta loop_id eval_loop_body) cf ctx
