open Values
open Contexts
module S = SynthesizeSymbolic
open Cps
open InterpUtils
open InterpAbs
open InterpMatchCtxs
open InterpJoin

(** The local logger *)
let log = Logging.loops_fixed_point_log

type loop_entry_result =
  | CurrentLoopReentry
  | PropagatedContinueToOuter of int
  | NonReentryExit
  | UnitResult

(** Classify a loop-body result for fixed-point entry computation.

    Only [Continue 0] is a re-entry of the loop currently being analyzed.
    [Continue i] for [i > 0] exits this loop and targets an enclosing loop after
    one depth decrement. If a nested loop has already propagated that exit to the
    current loop as [Continue 0], this classifier treats it as a local re-entry. *)
let classify_loop_entry_result (res : statement_eval_res) : loop_entry_result =
  match res with
  | Continue i ->
      if i < 0 then invalid_arg "classify_loop_entry_result";
      if i = 0 then CurrentLoopReentry
      else PropagatedContinueToOuter (i - 1)
  | Break _ | Return | Panic -> NonReentryExit
  | Unit -> UnitResult

type loop_exit_result =
  | CurrentLoopBreak
  | PropagatedLoopBreak of int
  | PropagatedLoopContinue of int
  | PropagatedLoopReturn
  | NotLoopExit
  | UnitLoopResult

(** Classify a loop-body result for exit-context collection.

    [Break 0] is the normal break consumed by the current loop. Other structured
    exits leave the current loop and carry one fewer relative depth if they
    target an enclosing loop. *)
let classify_loop_exit_result (res : statement_eval_res) : loop_exit_result =
  match res with
  | Break i ->
      if i < 0 then invalid_arg "classify_loop_exit_result";
      if i = 0 then CurrentLoopBreak else PropagatedLoopBreak (i - 1)
  | Continue i ->
      if i < 0 then invalid_arg "classify_loop_exit_result";
      if i = 0 then NotLoopExit else PropagatedLoopContinue (i - 1)
  | Return -> PropagatedLoopReturn
  | Panic -> NotLoopExit
  | Unit -> UnitLoopResult

(** Update the abstractions introduced by a loop with additional information,
    such as region group ids, continuation expressions, etc. *)
let loop_abs_reorder_and_add_info (span : Meta.span) (fixed_ids : ids_sets)
    (ctx : eval_ctx) : eval_ctx =
  (* Reorder the fresh abstractions in the fixed-point *)
  let fp = reorder_fresh_abs span false fixed_ids.aids ctx in

  (* Introduce continuation expressions. *)
  let add_abs_cont_to_abs (abs : abs) (loop_id : loop_id) : abs =
    InterpAbs.add_abs_cont_to_abs span ctx abs (ELoop (abs.abs_id, loop_id))
  in
  let add_abs_conts ctx =
    let visitor =
      object
        inherit [_] map_eval_ctx

        method! visit_abs _ abs =
          match abs.kind with
          | Loop loop_id -> add_abs_cont_to_abs abs loop_id
          | _ -> abs
      end
    in
    visitor#visit_eval_ctx () ctx
  in

  let fp = add_abs_conts fp in

  (* Return *)
  fp

(* TODO: remove the output ids_sets *)
let compute_loop_entry_fixed_point (config : config) (span : Meta.span)
    (loop_id : LoopId.id) (eval_loop_body : stl_cm_fun) (ctx0 : eval_ctx) :
    eval_ctx * ids_sets =
  (* Introduce "reborrows" for the shared values in the abstractions, so that
     the shared values in the fixed abstractions never get modified (technically,
     they are immutable, but in practice we can introduce more shared loans, or
     expand symbolic values).

     For more details, see the comments for {!reborrow_ashared_loans_symbolic_mutable_borrows}
  *)
  let ctx =
    InterpJoin.reborrow_ashared_loans_symbolic_borrows_no_synth span loop_id
      ~with_abs_conts:false ctx0
  in

  (* Debug *)
  [%ltrace
    "after reborrow_ashared_loans_symbolic_mutable_borrows:" ^ "\n\n- ctx0:\n"
    ^ eval_ctx_to_string ~span:(Some span) ~filter:false ctx0
    ^ "\n\n- ctx1:\n"
    ^ eval_ctx_to_string ~span:(Some span) ~filter:false ctx
    ^ "\n"];

  (* The fixed ids - TODO: remove *)
  let fixed_ids, _ = compute_ctx_ids ctx0 in
  let fixed_ids = ref fixed_ids in

  (* Update the set of fixed ids - for the symbolic and abstraction ids, we
     compute the intersection of ids between the original environment and the
     list of new environments *)
  let update_fixed_ids (ctxl : eval_ctx list) =
    let {
      aids;
      blids;
      borrow_ids;
      unique_borrow_ids;
      shared_borrow_ids;
      non_unique_shared_borrow_ids;
      loan_ids;
      shared_loans_to_values;
      dids;
      rids;
      sids;
    } =
      !fixed_ids
    in
    let sids = ref sids in
    let aids = ref aids in
    List.iter
      (fun ctx ->
        let fixed_ids, _ = compute_ctx_ids ctx in
        sids := SymbolicValueId.Set.inter !sids fixed_ids.sids;
        aids := AbsId.Set.inter !aids fixed_ids.aids)
      ctxl;
    fixed_ids :=
      {
        aids = !aids;
        blids;
        borrow_ids;
        unique_borrow_ids;
        shared_borrow_ids;
        non_unique_shared_borrow_ids;
        loan_ids;
        shared_loans_to_values;
        dids;
        rids;
        sids = !sids;
      }
  in

  (* Join the contexts at the loop entry - ctx1 is the current joined
     context (the context at the loop entry, after we called
     {!reborrow_ashared_loans_symbolic_mutable_borrows}, if this is the first iteration) *)
  let join_ctxs (ctx1 : eval_ctx) (ctxs : eval_ctx list) : eval_ctx =
    [%ltrace "join_ctxs"];
    (* Join the context with the context at the loop entry *)
    update_fixed_ids ctxs;
    let (_, _), ctx2 =
      loop_join_origin_with_continue_ctxs config span loop_id ctx1 ctxs
    in
    ctx2
  in

  (* Check if two contexts are equivalent - modulo alpha conversion on the
     existentially quantified borrows/abstractions/symbolic values.
  *)
  let equiv_ctxs (i : int) (ctx1 : eval_ctx) (ctx2 : eval_ctx) : bool =
    [%ltrace "equiv_ctx:"];
    update_fixed_ids [ ctx2 ];
    let lookup_shared_value _ = [%craise] span "Unreachable" in
    (* If there is just a single iteration left it means we *should* have reached
       a fixed point (otherwise we will fail). In case the fail hard option is on,
       we directly call [match_ctxs]: this way exceptions will not be caught and
       the user will see a full call stack, which eases deboguing. *)
    if i = 1 && !Config.fail_hard then
      let _ =
        match_ctxs span ~check_equiv:true ~recoverable:false !fixed_ids
          lookup_shared_value lookup_shared_value ctx1 ctx2
      in
      true
    else
      Option.is_some
        (try_match_ctxs span ~check_equiv:true !fixed_ids lookup_shared_value
           lookup_shared_value ctx1 ctx2)
  in
  let max_num_iter = Config.loop_fixed_point_max_num_iters in
  (* Keep a trace of the subsequent contexts we computed *)
  let joined_ctxs = ref [ ctx ] in
  let rec compute_fixed_point (ctx : eval_ctx) (i0 : int) (i : int) : eval_ctx =
    if i = 0 then (
      [%ltrace
        "Joined contexts:\n"
        ^ String.concat "\n\n"
            (List.map eval_ctx_to_string (List.rev !joined_ctxs))];
      [%craise] span
        ("Could not compute a loop fixed point in " ^ string_of_int i0
       ^ " iterations"))
    else
      (* Evaluate the loop body to register the different contexts upon reentry *)
      let ctx_resl, _ = eval_loop_body ctx in
      (* Keep only the contexts which reached a `continue`. *)
      let keep_continue_ctx (ctx, res) =
        [%ltrace "register_continue_ctx"];
        match classify_loop_entry_result res with
        | CurrentLoopReentry -> Some ctx
        | PropagatedContinueToOuter depth ->
            [%ltrace
              "propagating continue to outer loop at remaining depth "
              ^ string_of_int depth];
            None
        | NonReentryExit -> None
        | UnitResult ->
            (* See the comment in {!eval_loop} *)
            [%craise] span "Unreachable"
      in
      let continue_ctxs = List.filter_map keep_continue_ctx ctx_resl in
      if continue_ctxs = [] then
        [%ltrace
          "no local continue contexts reached this loop entry; propagated \
           continues, breaks, returns, and panics are excluded from the current \
           fixed point"];

      [%ltrace
        "about to join with continue_ctx" ^ "\n\n- ctx0:\n"
        ^ eval_ctx_to_string ~span:(Some span) ~filter:false ctx
        ^ "\n\n"
        ^ String.concat "\n\n"
            (List.map
               (fun ctx ->
                 "- continue_ctx:\n"
                 ^ eval_ctx_to_string ~span:(Some span) ~filter:false ctx)
               continue_ctxs)
        ^ "\n"];

      (* Compute the join between the original contexts and the contexts computed
         upon reentry *)
      let ctx1 = join_ctxs ctx continue_ctxs in

      (* Debug *)
      [%ltrace
        "after joining continue ctxs" ^ "\n\n- ctx0:\n"
        ^ eval_ctx_to_string ~span:(Some span) ~filter:false ctx
        ^ "\n\n- ctx1:\n"
        ^ eval_ctx_to_string ~span:(Some span) ~filter:false ctx1
        ^ "\n"];

      (* Reduce the context in order to reach a fixed-point *)
      let fixed_aids = InterpJoinCore.compute_fixed_abs_ids ctx0 ctx1 in
      let fixed_dids = ctx_get_dummy_var_ids ctx0 in
      let ctx1 =
        InterpReduceCollapse.reduce_ctx config span ~with_abs_conts:false
          (Loop loop_id) fixed_aids fixed_dids ctx1
      in
      (* Debug *)
      [%ltrace
        "after reducing the joined context (fixed_aids: "
        ^ AbsId.Set.to_string None fixed_aids
        ^ "):" ^ "\n- ctx1:\n"
        ^ eval_ctx_to_string ~span:(Some span) ~filter:false ctx1
        ^ "\n"];

      (* Check if we reached a fixed point: if not, iterate *)
      if equiv_ctxs i ctx ctx1 then ctx1
      else (
        joined_ctxs := ctx1 :: !joined_ctxs;
        compute_fixed_point ctx1 i0 (i - 1))
  in
  let fp = compute_fixed_point ctx max_num_iter max_num_iter in

  [%ltrace
    "- fixed point:\n" ^ eval_ctx_to_string ~span:(Some span) ~filter:false fp];

  (* Update the region abstractions to introduce continuation expressions, etc. *)
  update_fixed_ids [ fp ];
  let fp = loop_abs_reorder_and_add_info span !fixed_ids fp in

  [%ltrace
    "- fixed point:\n" ^ eval_ctx_to_string ~span:(Some span) ~filter:false fp];

  (* Return *)
  (fp, !fixed_ids)

type break_ctx =
  | NoBreak  (** The loop doesn't contain any break *)
  | Single
      (** There is a single break statement, so we don't join the break contexts
      *)
  | Multiple of (eval_ctx * abs list)  (** We joined multiple break contexts *)

type propagated_exit_kind =
  | PropagatedBreakExit of int
  | PropagatedContinueExit of int
  | PropagatedReturnExit

type propagated_exit_ctx = {
  exit_kind : propagated_exit_kind;
  exit_ctx : eval_ctx;
  exit_abs : abs list;
}

type loop_exit_contexts = {
  normal_break : break_ctx;
  propagated_exits : propagated_exit_ctx list;
}

let same_propagated_exit_kind (kind0 : propagated_exit_kind)
    (kind1 : propagated_exit_kind) : bool =
  match (kind0, kind1) with
  | PropagatedBreakExit d0, PropagatedBreakExit d1
  | PropagatedContinueExit d0, PropagatedContinueExit d1 ->
      d0 = d1
  | PropagatedReturnExit, PropagatedReturnExit -> true
  | _ -> false

let group_by_propagated_exit_kind
    (items : (propagated_exit_kind * 'a) list) :
    (propagated_exit_kind * 'a list) list =
  let add_group groups (kind, item) =
    let rec add = function
      | [] -> [ (kind, [ item ]) ]
      | (group_kind, group_items) :: groups ->
          if same_propagated_exit_kind kind group_kind then
            (group_kind, item :: group_items) :: groups
          else (group_kind, group_items) :: add groups
    in
    add groups
  in
  List.map
    (fun (kind, items) -> (kind, List.rev items))
    (List.fold_left add_group [] items)

let finalize_loop_exit_ctx (config : config) (span : Meta.span)
    (loop_id : LoopId.id) (fixed_aids : AbsId.Set.t)
    (fixed_dids : DummyVarId.Set.t) (ctx : eval_ctx) : eval_ctx * abs list =
  let ctx =
    InterpReduceCollapse.reduce_ctx config span ~with_abs_conts:true
      (Loop loop_id) fixed_aids fixed_dids ctx
  in
  [%ltrace "exit ctx after reduce:\n" ^ eval_ctx_to_string ~span:(Some span) ctx];
  if !Config.sanity_checks then Invariants.check_invariants span ctx;

  let ctx = reorder_fresh_abs span false fixed_aids ctx in

  let add_abs_cont_to_abs (abs : abs) (loop_id : loop_id) : abs =
    InterpAbs.add_abs_cont_to_abs span ctx abs (ELoop (abs.abs_id, loop_id))
  in
  let add_abs_conts ctx =
    let visitor =
      object
        inherit [_] map_eval_ctx

        method! visit_abs _ abs =
          match abs.kind with
          | Loop loop_id ->
              let abs = add_abs_cont_to_abs abs loop_id in
              InterpBorrows.destructure_abs span abs.kind ~can_end:true
                ~destructure_shared_values:true ctx abs
          | _ -> abs
      end
    in
    visitor#visit_eval_ctx () ctx
  in
  let ctx = add_abs_conts ctx in

  let get_fresh_abs (e : env_elem) : abs option =
    match e with
    | EAbs abs ->
        if not (AbsId.Set.mem abs.abs_id fixed_aids) then Some abs else None
    | EBinding _ | EFrame -> None
  in
  (* Pay attention to the fact that the elements are stored in reverse order *)
  let abs = List.rev (List.filter_map get_fresh_abs ctx.env) in
  (ctx, abs)

let compute_loop_exit_contexts (config : config) (span : Meta.span)
    (loop_id : LoopId.id) (eval_loop_body : stl_cm_fun) (fp_ctx : eval_ctx)
    (fixed_aids : AbsId.Set.t) (fixed_dids : DummyVarId.Set.t) :
    loop_exit_contexts =
  [%ltrace
    "Initial fixed-point context:\n"
    ^ eval_ctx_to_string ~span:(Some span) ~filter:false fp_ctx];

  (* Update the fixed-point context to remove the continuation expressions from
     the abstractions introduced by the fixed-point *)
  let fp_ctx =
    let update (e : env_elem) : env_elem =
      match (e : env_elem) with
      | EAbs abs -> (
          match abs.kind with
          | Loop loop_id' ->
              if loop_id' = loop_id then
                EAbs { abs with cont = None; kind = Loop loop_id }
              else e
          | _ -> e)
      | EBinding _ | EFrame -> e
    in
    { fp_ctx with env = List.map update fp_ctx.env }
  in

  (* Evaluate the loop body to register the different exit contexts. *)
  let ctx_resl, _ = eval_loop_body fp_ctx in
  let classify_exit_ctx (ctx, res) :
      [ `NormalBreak of eval_ctx
      | `PropagatedExit of propagated_exit_kind * eval_ctx
      | `Ignore ] =
    [%ltrace "register_exit_ctx"];
    match classify_loop_exit_result res with
    | CurrentLoopBreak -> `NormalBreak ctx
    | PropagatedLoopBreak depth ->
        `PropagatedExit (PropagatedBreakExit depth, ctx)
    | PropagatedLoopContinue depth ->
        `PropagatedExit (PropagatedContinueExit depth, ctx)
    | PropagatedLoopReturn -> `PropagatedExit (PropagatedReturnExit, ctx)
    | NotLoopExit -> `Ignore
    | UnitLoopResult ->
        (* See the comment in {!eval_loop} *)
        [%craise] span "Unreachable"
  in
  let normal_break_ctxs = ref [] in
  let propagated_exit_ctxs = ref [] in
  List.iter
    (fun ctx_res ->
      match classify_exit_ctx ctx_res with
      | `NormalBreak ctx -> normal_break_ctxs := ctx :: !normal_break_ctxs
      | `PropagatedExit exit -> propagated_exit_ctxs := exit :: !propagated_exit_ctxs
      | `Ignore -> ())
    ctx_resl;
  let break_ctxs = List.rev !normal_break_ctxs in
  let propagated_exit_ctxs = List.rev !propagated_exit_ctxs in

  [%ltrace
    "about to join the contexts at the breaks:\n"
    ^ String.concat "\n\n"
        (List.map
           (fun ctx ->
             "- continue_ctx:\n"
             ^ eval_ctx_to_string ~span:(Some span) ~filter:false ctx)
           break_ctxs)
    ^ "\n"];

  (* Compute the join *)
  let normal_break =
    match break_ctxs with
    | [] ->
        (* There is no break! *)
        NoBreak
    | [ _ ] ->
        (* Single break context *)
        Single
    | ctxs ->
        (* Join the contexts *)
        let break_ctx =
          loop_join_break_ctxs config span loop_id fixed_aids fixed_dids ctxs
        in
        (* Debug *)
        [%ltrace
          "after joining break ctxs" ^ "\n\n- ctx0:\n"
          ^ eval_ctx_to_string ~span:(Some span) ~filter:false break_ctx];

        let break_ctx, abs =
          finalize_loop_exit_ctx config span loop_id fixed_aids fixed_dids
            break_ctx
        in
        Multiple (break_ctx, abs)
  in

  let join_propagated_exit_ctxs (kind, ctxs) : propagated_exit_ctx =
    (* Propagated exits always use the joined/finalized path, including
       singleton groups: unlike normal breaks, synthesis cannot reconstruct a
       legacy Single fast path for them. *)
    let ctx =
      loop_join_break_ctxs config span loop_id fixed_aids fixed_dids ctxs
    in
    [%ltrace
      "after joining propagated exit ctxs" ^ "\n\n- ctx0:\n"
      ^ eval_ctx_to_string ~span:(Some span) ~filter:false ctx];
    let ctx, abs =
      finalize_loop_exit_ctx config span loop_id fixed_aids fixed_dids ctx
    in
    { exit_kind = kind; exit_ctx = ctx; exit_abs = abs }
  in
  let propagated_exits =
    List.map join_propagated_exit_ctxs
      (group_by_propagated_exit_kind propagated_exit_ctxs)
  in
  { normal_break; propagated_exits }
