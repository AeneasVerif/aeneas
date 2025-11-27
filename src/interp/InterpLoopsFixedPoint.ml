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

     For more details, see the comments for {!prepare_ashared_loans}
  *)
  let ctx =
    InterpJoin.prepare_ashared_loans_no_synth span loop_id ~with_abs_conts:false
      ctx0
  in

  (* Debug *)
  [%ltrace
    "after prepare_ashared_loans:" ^ "\n\n- ctx0:\n"
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
     {!prepare_ashared_loans}, if this is the first iteration) *)
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
  let equiv_ctxs (ctx1 : eval_ctx) (ctx2 : eval_ctx) : bool =
    [%ltrace "equiv_ctx:"];
    update_fixed_ids [ ctx2 ];
    let lookup_shared_value _ = [%craise] span "Unreachable" in
    Option.is_some
      (match_ctxs span ~check_equiv:true !fixed_ids lookup_shared_value
         lookup_shared_value ctx1 ctx2)
  in
  let max_num_iter = Config.loop_fixed_point_max_num_iters in
  let rec compute_fixed_point (ctx : eval_ctx) (i0 : int) (i : int) : eval_ctx =
    if i = 0 then
      [%craise] span
        ("Could not compute a loop fixed point in " ^ string_of_int i0
       ^ " iterations")
    else
      (* Evaluate the loop body to register the different contexts upon reentry *)
      let ctx_resl, _ = eval_loop_body ctx in
      (* Keep only the contexts which reached a `continue`. *)
      let keep_continue_ctx (ctx, res) =
        [%ltrace "register_continue_ctx"];
        match res with
        | Return | Panic | Break _ -> None
        | Unit ->
            (* See the comment in {!eval_loop} *)
            [%craise] span "Unreachable"
        | Continue i ->
            (* For now we don't support continues to outer loops *)
            [%cassert] span (i = 0) "Continues to outer loops not supported yet";
            Some ctx
      in
      let continue_ctxs = List.filter_map keep_continue_ctx ctx_resl in

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
      if equiv_ctxs ctx ctx1 then ctx1 else compute_fixed_point ctx1 i0 (i - 1)
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

let compute_loop_break_context (config : config) (span : Meta.span)
    (loop_id : LoopId.id) (eval_loop_body : stl_cm_fun) (fp_ctx : eval_ctx)
    (fixed_aids : AbsId.Set.t) (fixed_dids : DummyVarId.Set.t) : break_ctx =
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

  (* Evaluate the loop body to register the different contexts upon reentry *)
  let ctx_resl, _ = eval_loop_body fp_ctx in
  (* Keep only the contexts which reached a `continue`. *)
  let keep_break_ctx (ctx, res) : eval_ctx option =
    [%ltrace "register_continue_ctx"];
    match res with
    | Return | Panic | Continue _ -> None
    | Unit ->
        (* See the comment in {!eval_loop} *)
        [%craise] span "Unreachable"
    | Break i ->
        (* We don't support breaks to outer loops *)
        (* For now we don't support continues to outer loops *)
        [%cassert] span (i = 0) "Continues to outer loops not supported yet";
        Some ctx
  in
  let break_ctxs = List.filter_map keep_break_ctx ctx_resl in

  [%ltrace
    "about to join the contexts at the breaks:"
    ^ String.concat "\n\n"
        (List.map
           (fun ctx ->
             "- continue_ctx:\n"
             ^ eval_ctx_to_string ~span:(Some span) ~filter:false ctx)
           break_ctxs)
    ^ "\n"];

  (* Compute the join *)
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

      (* Reduce the context - TODO: generalize so that we don't have to do this *)
      let break_ctx =
        InterpReduceCollapse.reduce_ctx config span ~with_abs_conts:true
          (Loop loop_id) fixed_aids fixed_dids break_ctx
      in
      [%ltrace
        "break_ctx after reduce:\n"
        ^ eval_ctx_to_string ~span:(Some span) break_ctx];
      (* Sanity check *)
      if !Config.sanity_checks then Invariants.check_invariants span break_ctx;

      (* Reorder the fresh abstractions *)
      let break_ctx = reorder_fresh_abs span false fixed_aids break_ctx in

      (* Introduce continuation expressions and destructure the region abstractions. *)
      let add_abs_cont_to_abs (abs : abs) (loop_id : loop_id) : abs =
        InterpAbs.add_abs_cont_to_abs span break_ctx abs
          (ELoop (abs.abs_id, loop_id))
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
      let break_ctx = add_abs_conts break_ctx in

      let get_fresh_abs (e : env_elem) : abs option =
        match e with
        | EAbs abs ->
            if not (AbsId.Set.mem abs.abs_id fixed_aids) then Some abs else None
        | EBinding _ | EFrame -> None
      in
      (* Pay attention to the fact that the elements are stored in reverse order *)
      let abs = List.rev (List.filter_map get_fresh_abs break_ctx.env) in

      Multiple (break_ctx, abs)
