open Values
open Contexts
open Meta
module S = SynthesizeSymbolic
module SA = SymbolicAst
open Cps
open InterpreterUtils
open InterpreterMatchCtxs
open InterpreterJoin
open InterpreterLoopsFixedPoint

(** The local logger *)
let log = Logging.loops_log

(** Evaluate a loop in concrete mode *)
let eval_loop_concrete (span : Meta.span) (eval_loop_body : stl_cm_fun) :
    stl_cm_fun =
 fun ctx ->
  (* Function to recursively evaluate the loop

     We need a specific function because of the {!Continue} case: in case we
     continue, we might have to reevaluate the current loop body with the
     new context (and repeat this an indefinite number of times).
  *)
  let rec rec_eval_loop_body (ctx : eval_ctx) (res : statement_eval_res) =
    [%ltrace ""];
    match res with
    | Return -> [ (ctx, Return) ]
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
        [%craise] span "Unreachable"
  in

  (* Apply - for the first iteration, we use the result `Continue 0` to evaluate
     the loop body at least once *)
  let ctx_resl = rec_eval_loop_body ctx (Continue 0) in
  (* If we evaluate in concrete mode, we shouldn't have to generate any symbolic expression *)
  let cf _ = [%internal_error] span in
  (ctx_resl, cf)

(** Auxiliary function for {!eval_loop_symbolic}.

    Match the context upon entering the loop with the loop fixed-point to
    compute how to "apply" the fixed-point. Compute the correspondance from the
    borrow ids in the current context to the loans which appear in the loop
    context (we need this in order to know how to introduce the region
    abstractions of the loop).

    We check the fixed-point at the same time to make sure the loans and borrows
    inside the region abstractions are properly ordered (this is necessary for
    the synthesis). Ex.: if in the fixed point we have:
    {[
      abs { MB l0, MB l1, ML l2, ML l3 }
    ]}
    we want to make sure that borrow l0 actually corresponds to loan l2, and
    borrow l1 to loan l3. *)
let eval_loop_symbolic_apply_loop (config : config) (span : span)
    (loop_id : LoopId.id) (init_ctx : eval_ctx) (fp_ctx : eval_ctx)
    (fp_input_abs : AbsId.id list) (fp_input_svalues : SymbolicValueId.id list)
    :
    (eval_ctx * eval_ctx * tvalue SymbolicValueId.Map.t * abs AbsId.Map.t)
    * (SymbolicAst.expr -> SymbolicAst.expr) =
  [%ltrace
    "about to reorganize the original context to match the fixed-point ctx \
     with it:\n\
     - src ctx (fixed-point ctx):\n" ^ eval_ctx_to_string fp_ctx
    ^ "\n\n-tgt ctx (original context):\n"
    ^ eval_ctx_to_string init_ctx];

  let ctx = init_ctx in

  (* Preemptively end borrows/move values by matching the current
     context with the target context *)
  let ctx, cf_prepare =
    prepare_match_ctx_with_target config span (Loop loop_id) fp_ctx ctx
  in

  (* Actually match *)
  [%ltrace
    "about to compute the id correspondance between the fixed-point ctx and \
     the original ctx:\n\
     - src ctx (fixed-point ctx)\n" ^ eval_ctx_to_string fp_ctx
    ^ "\n\n-tgt ctx (original context):\n" ^ eval_ctx_to_string ctx];

  (* Compute the end expression, that is the expresion corresponding to the
     end of the function where we call the loop (for now, when calling a loop
     we never get out) *)
  let fixed_aids = InterpreterJoinCore.compute_fixed_abs_ids init_ctx fp_ctx in
  let fixed_dids = ctx_get_dummy_var_ids init_ctx in
  let (ctx, tgt_ctx, input_values, input_abs), cc =
    comp cf_prepare
      (match_ctx_with_target config span WithCont fixed_aids fixed_dids
         fp_input_abs fp_input_svalues fp_ctx ctx)
  in

  [%ltrace "Resulting context:\n- ctx" ^ eval_ctx_to_string ctx];

  ((ctx, tgt_ctx, input_values, input_abs), cc)

(** Auxiliary function for {!eval_loop_symbolic}.

    Synthesize the body of the loop. *)
let eval_loop_symbolic_synthesize_loop_body (config : config) (span : span)
    (eval_loop_body : stl_cm_fun) (loop_id : LoopId.id) (fp_ctx : eval_ctx)
    (fp_input_abs : AbsId.id list) (fp_input_svalues : SymbolicValueId.id list)
    (fixed_aids : AbsId.Set.t) (fixed_dids : DummyVarId.Set.t)
    (break_ctx : eval_ctx) (break_input_abs : AbsId.id list)
    (break_input_svalues : SymbolicValueId.id list) : SA.expr =
  [%ldebug "fp_ctx:\n" ^ eval_ctx_to_string fp_ctx];

  (* Save a snapshot of the context as meta-information: it is useful to
     compute pretty names at extraction time *)
  let cc = SynthesizeSymbolic.save_snapshot fp_ctx in

  (* First, evaluate the loop body starting from the **fixed-point** context *)
  let ctx_resl, cf_loop = comp cc (eval_loop_body fp_ctx) in

  (* Small helpers *)
  let reorder_input_abs (map : abs AbsId.Map.t) (absl : abs_id list) : abs list
      =
    List.map (fun id -> AbsId.Map.find id map) absl
  in
  let reorder_input_values (map : tvalue SymbolicValueId.Map.t)
      (values : symbolic_value_id list) : tvalue list =
    List.map (fun id -> SymbolicValueId.Map.find id map) values
  in

  (* Then, do a special treatment of the break and continue cases.
     For now, we forbid having breaks in loops (and eliminate breaks
     in the prepasses) *)
  let eval_after_loop_iter (ctx, res) : SA.expr =
    [%ltrace ""];
    match res with
    | Return ->
        (* We don't support early returns *)
        [%craise] span "Unexpected return"
    | Panic -> SA.Panic
    | Break i ->
        (* We don't support nested loops for now *)
        [%cassert] span (i = 0) "Nested loops are not supported yet";

        [%ltrace
          "about to match the break context with the context at a break:\n\
           - src ctx (break ctx):\n"
          ^ eval_ctx_to_string ~span:(Some span) break_ctx
          ^ "\n\n-tgt ctx (ctx at this break):\n"
          ^ eval_ctx_to_string ~span:(Some span) ctx];
        let (_ctx, tgt_ctx, input_values, input_abs), cc =
          loop_match_break_ctx_with_target config span loop_id fixed_aids
            fixed_dids break_input_abs break_input_svalues break_ctx ctx
        in
        [%ldebug
          "after matching the break context with the context at a break:\n\
           - src ctx (break ctx):\n"
          ^ eval_ctx_to_string ~span:(Some span) break_ctx
          ^ "\n\n-tgt ctx (ctx at this break):\n"
          ^ eval_ctx_to_string ~span:(Some span) ctx
          ^ "\n\n-input_abs:\n"
          ^ AbsId.Map.to_string None
              (fun abs -> AbsId.to_string abs.abs_id)
              input_abs
          ^ "\n\n-break_input_abs:\n"
          ^ Print.list_to_string AbsId.to_string break_input_abs];
        let input_values =
          reorder_input_values input_values break_input_svalues
        in
        let input_abs = reorder_input_abs input_abs break_input_abs in
        (* Reorder the input values and the abstractions *)
        cc (SA.LoopBreak (tgt_ctx, loop_id, input_values, input_abs))
    | Continue i ->
        (* We don't support nested loops for now *)
        [%cassert] span (i = 0) "Nested loops are not supported yet";
        [%ltrace
          "about to match the fixed-point context with the context at a \
           continue:" ^ "\n- fixed_aids: "
          ^ AbsId.Set.to_string None fixed_aids
          ^ "\n- src ctx (fixed-point ctx):\n"
          ^ eval_ctx_to_string ~span:(Some span) fp_ctx
          ^ "\n\n-tgt ctx (ctx at continue):\n"
          ^ eval_ctx_to_string ~span:(Some span) ctx];

        let (_ctx, tgt_ctx, input_values, input_abs), cc =
          match_ctx_with_target config span WithCont fixed_aids fixed_dids
            fp_input_abs fp_input_svalues fp_ctx ctx
        in
        let input_values = reorder_input_values input_values fp_input_svalues in
        let input_abs = reorder_input_abs input_abs fp_input_abs in
        let e =
          cc (SA.LoopContinue (tgt_ctx, loop_id, input_values, input_abs))
        in
        [%ldebug
          let ctx = Print.Contexts.eval_ctx_to_fmt_env ctx in
          PrintSymbolicAst.expr_to_string ctx "" "  " e];
        e
    | Unit ->
        (* For why we can't get [Unit], see the comments inside {!eval_loop_concrete}. *)
        [%craise] span "Unreachable"
  in

  (* Apply and compose *)
  let el = List.map eval_after_loop_iter ctx_resl in
  cf_loop el

(** Evaluate a loop in symbolic mode *)
let eval_loop_symbolic (config : config) (span : span)
    (eval_loop_body : stl_cm_fun) : st_cm_fun =
 fun ctx ->
  (* Debug *)
  [%ltrace "Context:\n" ^ eval_ctx_to_string ~span:(Some span) ctx ^ "\n"];

  (* Generate a fresh loop id *)
  let loop_id = ctx.fresh_loop_id () in

  (* Compute the fixed point at the loop entrance *)
  let fp_ctx, fixed_ids =
    compute_loop_entry_fixed_point config span loop_id eval_loop_body ctx
  in
  let input_abs_list =
    List.rev
      (env_filter_map_abs
         (fun abs ->
           match abs.kind with
           | Loop id when id = loop_id -> Some abs
           | _ -> None)
         fp_ctx.env)
  in
  let input_abs_ids_list =
    List.map (fun (abs : abs) -> abs.abs_id) input_abs_list
  in
  [%ltrace
    "fixed point:\n- fp:\n" ^ eval_ctx_to_string ~span:(Some span) fp_ctx];

  (* Compute the context at the breaks *)
  let fixed_aids = InterpreterJoinCore.compute_fixed_abs_ids ctx fp_ctx in
  let fixed_dids = ctx_get_dummy_var_ids ctx in
  let break_info =
    compute_loop_break_context config span loop_id eval_loop_body fp_ctx
      fixed_aids fixed_dids
  in
  [%cassert] span
    (Option.is_some break_info)
    "(Infinite) loops which do not contain breaks are not supported yet";
  let break_ctx, break_abs = Option.get break_info in
  let break_input_abs_ids = List.map (fun (a : abs) -> a.abs_id) break_abs in

  (* Debug *)
  [%ltrace
    "- Initial context:\n"
    ^ eval_ctx_to_string ~span:(Some span) ctx
    ^ "\n\n- Fixed point:\n"
    ^ eval_ctx_to_string ~span:(Some span) ~filter:false fp_ctx
    ^ "\n\n- break_ctx:\n"
    ^ eval_ctx_to_string ~span:(Some span) break_ctx];

  (* Compute the loop input parameters *)
  let fp_input_svalues =
    compute_ctx_fresh_ordered_symbolic_values span ~only_modified_svalues:false
      ctx fp_ctx
  in
  let fp_input_svalue_ids =
    List.map (fun (sv : symbolic_value) -> sv.sv_id) fp_input_svalues
  in

  let break_input_svalues =
    compute_ctx_fresh_ordered_symbolic_values span ~only_modified_svalues:false
      ctx break_ctx
  in
  let break_input_svalue_ids =
    List.map (fun (sv : symbolic_value) -> sv.sv_id) break_input_svalues
  in

  [%ltrace
    "\n- fp_input_svalues: "
    ^ String.concat ", "
        (List.map (symbolic_value_to_string ctx) fp_input_svalues)
    ^ "\n- break_input_svalues: "
    ^ String.concat ", "
        (List.map (symbolic_value_to_string ctx) break_input_svalues)];

  (* "Call" the loop *)
  let (_ctx_after_loop, entry_loop_ctx, input_values, input_abs), cf_before_loop
      =
    eval_loop_symbolic_apply_loop config span loop_id ctx fp_ctx
      input_abs_ids_list fp_input_svalue_ids
  in

  [%ltrace "matched the fixed-point context with the original context."];

  (* Synthesize the loop body *)
  let loop_body =
    let fixed_aids = InterpreterJoinCore.compute_fixed_abs_ids ctx fp_ctx in
    let fixed_dids = ctx_get_dummy_var_ids ctx in
    eval_loop_symbolic_synthesize_loop_body config span eval_loop_body loop_id
      fp_ctx input_abs_ids_list fp_input_svalue_ids fixed_aids fixed_dids
      break_ctx break_input_abs_ids break_input_svalue_ids
  in

  [%ltrace
    "result:" ^ "\n- src context:\n"
    ^ eval_ctx_to_string ~span:(Some span) ~filter:false ctx
    ^ "\n- fixed point:\n"
    ^ eval_ctx_to_string ~span:(Some span) ~filter:false fp_ctx
    ^ "\n- fixed_sids: "
    ^ SymbolicValueId.Set.show fixed_ids.sids
    ^ "\n- fp_input_abs: "
    ^ Print.list_to_string AbsId.to_string input_abs_ids_list
    ^ "\n- fp_input_svalues: "
    ^ Print.list_to_string (symbolic_value_to_string ctx) fp_input_svalues
    ^ "\n\n- break ctx:\n"
    ^ eval_ctx_to_string ~span:(Some span) ~filter:false break_ctx
    ^ "\n\n- break_input_svalues: "
    ^ Print.list_to_string (symbolic_value_to_string ctx) break_input_svalues
    ^ "\n"];

  (* Put everything together *)
  let cc (next_expr : SA.expr) : SA.expr =
    let loop_expr =
      SymbolicAst.Loop
        {
          loop_id;
          input_svalues = fp_input_svalues;
          input_abs = input_abs_list;
          input_value_to_value = input_values;
          input_abs_to_abs = input_abs;
          break_svalues = break_input_svalues;
          break_abs;
          loop_expr = loop_body;
          next_expr;
          span;
          ctx = entry_loop_ctx;
        }
    in
    cf_before_loop loop_expr
  in
  ((break_ctx, Unit), cc)

let eval_loop (config : config) (span : span) (eval_loop_body : stl_cm_fun) :
    stl_cm_fun =
 fun ctx ->
  match config.mode with
  | ConcreteMode -> (eval_loop_concrete span eval_loop_body) ctx
  | SymbolicMode ->
      (* Preemptively simplify the context by ending the unnecessary borrows/loans and getting
         rid of the useless symbolic values (which are in anonymous variables) *)
      let ctx, cc =
        InterpreterBorrows.simplify_dummy_values_useless_abs config span ctx
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
      let ctx, cc =
        comp cc (prepare_ashared_loans span None ~with_abs_conts:true ctx)
      in
      let (ctx, res), cc =
        comp cc (eval_loop_symbolic config span eval_loop_body ctx)
      in
      let cf (el : SymbolicAst.expr list) : SymbolicAst.expr =
        match el with
        | [ e ] -> cc e
        | _ -> [%internal_error] span
      in
      ([ (ctx, res) ], cf)
