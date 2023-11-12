module T = Types
module PV = PrimitiveValues
module V = Values
module E = Expressions
module C = Contexts
module Subst = Substitute
module A = LlbcAst
module L = Logging
open TypesUtils
open ValuesUtils
module Inv = Invariants
module S = SynthesizeSymbolic
open Cps
open InterpreterUtils
open InterpreterLoopsCore
open InterpreterLoopsMatchCtxs
open InterpreterLoopsJoinCtxs

(** The local logger *)
let log = L.loops_fixed_point_log

(** Reorder the loans and borrows in the fresh abstractions.

    We do this in order to enforce some structure in the environments: this
    allows us to find fixed-points. Note that this function needs to be
    called typically after we merge abstractions together (see {!collapse_ctx}
    for instance).
 *)
let reorder_loans_borrows_in_fresh_abs (old_abs_ids : V.AbstractionId.Set.t)
    (ctx : C.eval_ctx) : C.eval_ctx =
  let reorder_in_fresh_abs (abs : V.abs) : V.abs =
    (* Split between the loans and borrows *)
    let is_borrow (av : V.typed_avalue) : bool =
      match av.V.value with
      | ABorrow _ -> true
      | ALoan _ -> false
      | _ -> raise (Failure "Unexpected")
    in
    let aborrows, aloans = List.partition is_borrow abs.V.avalues in

    (* Reoder the borrows, and the loans.

       After experimenting, it seems that a good way of reordering the loans
       and the borrows to find fixed points is simply to sort them by increasing
       order of id (taking the smallest id of a set of ids, in case of sets).
    *)
    let get_borrow_id (av : V.typed_avalue) : V.BorrowId.id =
      match av.V.value with
      | V.ABorrow (V.AMutBorrow (bid, _) | V.ASharedBorrow bid) -> bid
      | _ -> raise (Failure "Unexpected")
    in
    let get_loan_id (av : V.typed_avalue) : V.BorrowId.id =
      match av.V.value with
      | V.ALoan (V.AMutLoan (lid, _)) -> lid
      | V.ALoan (V.ASharedLoan (lids, _, _)) -> V.BorrowId.Set.min_elt lids
      | _ -> raise (Failure "Unexpected")
    in
    (* We use ordered maps to reorder the borrows and loans *)
    let reorder (get_bid : V.typed_avalue -> V.BorrowId.id)
        (values : V.typed_avalue list) : V.typed_avalue list =
      List.map snd
        (V.BorrowId.Map.bindings
           (V.BorrowId.Map.of_list (List.map (fun v -> (get_bid v, v)) values)))
    in
    let aborrows = reorder get_borrow_id aborrows in
    let aloans = reorder get_loan_id aloans in
    let avalues = List.append aborrows aloans in
    { abs with V.avalues }
  in

  let reorder_in_abs (abs : V.abs) =
    if V.AbstractionId.Set.mem abs.abs_id old_abs_ids then abs
    else reorder_in_fresh_abs abs
  in

  let env = C.env_map_abs reorder_in_abs ctx.env in

  { ctx with C.env }

let prepare_ashared_loans (loop_id : V.LoopId.id option) : cm_fun =
 fun cf ctx0 ->
  let ctx = ctx0 in
  (* Compute the set of borrows which appear in the abstractions, so that
     we can filter the borrows that we reborrow.
  *)
  let absl =
    List.filter_map
      (function C.EBinding _ | C.EFrame -> None | C.EAbs abs -> Some abs)
      ctx.env
  in
  let absl_ids, absl_id_maps = compute_absl_ids absl in
  let abs_borrow_ids = absl_ids.borrow_ids in

  (* Map from the fresh sids to the original symbolic values *)
  let sid_subst = ref [] in

  (* Return the same value but where:
     - the shared loans have been removed
     - the symbolic values have been replaced with fresh symbolic values
     - the region ids found in the value and belonging to the set [rids] have
       been substituted with [nrid]
  *)
  let mk_value_with_fresh_sids_no_shared_loans (rids : T.RegionId.Set.t)
      (nrid : T.RegionId.id) (v : V.typed_value) : V.typed_value =
    (* Remove the shared loans *)
    let v = value_remove_shared_loans v in
    (* Substitute the symbolic values and the region *)
    Subst.typed_value_subst_ids
      (fun r -> if T.RegionId.Set.mem r rids then nrid else r)
      (fun x -> x)
      (fun x -> x)
      (fun id ->
        let nid = C.fresh_symbolic_value_id () in
        let sv = V.SymbolicValueId.Map.find id absl_id_maps.sids_to_values in
        sid_subst := (nid, sv) :: !sid_subst;
        nid)
      (fun x -> x)
      v
  in

  let borrow_substs = ref [] in
  let fresh_absl = ref [] in

  (* Auxiliary function to create a new abstraction for a shared value found in
     an abstraction.

     Example:
     ========
     When exploring:
     {[
       abs'0 { SL {l0, l1} s0 }
     ]}

     we find the shared value:

     {[
       SL {l0, l1} s0
     ]}

     and introduce the corresponding abstraction:
     {[
       abs'2 { SB l0, SL {l2} s2 }
     ]}
  *)
  let push_abs_for_shared_value (abs : V.abs) (sv : V.typed_value)
      (lid : V.BorrowId.id) : unit =
    (* Create a fresh borrow (for the reborrow) *)
    let nlid = C.fresh_borrow_id () in

    (* We need a fresh region for the new abstraction *)
    let nrid = C.fresh_region_id () in

    (* Prepare the shared value *)
    let nsv = mk_value_with_fresh_sids_no_shared_loans abs.regions nrid sv in

    (* Save the borrow substitution, to apply it to the context later *)
    borrow_substs := (lid, nlid) :: !borrow_substs;

    (* Rem.: the below sanity checks are not really necessary *)
    assert (V.AbstractionId.Set.is_empty abs.parents);
    assert (abs.original_parents = []);
    assert (T.RegionId.Set.is_empty abs.ancestors_regions);

    (* Introduce the new abstraction for the shared values *)
    assert (ty_no_regions sv.V.ty);
    let rty = sv.V.ty in

    (* Create the shared loan child *)
    let child_rty = rty in
    let child_av = mk_aignored child_rty in

    (* Create the shared loan *)
    let loan_rty = T.TRef (T.RVar nrid, rty, T.Shared) in
    let loan_value =
      V.ALoan (V.ASharedLoan (V.BorrowId.Set.singleton nlid, nsv, child_av))
    in
    let loan_value = mk_typed_avalue loan_rty loan_value in

    (* Create the shared borrow *)
    let borrow_rty = loan_rty in
    let borrow_value = V.ABorrow (V.ASharedBorrow lid) in
    let borrow_value = mk_typed_avalue borrow_rty borrow_value in

    (* Create the abstraction *)
    let avalues = [ borrow_value; loan_value ] in
    let kind =
      match loop_id with
      | Some loop_id -> V.Loop (loop_id, None, V.LoopSynthInput)
      | None -> V.Identity
    in
    let can_end = true in
    let fresh_abs =
      {
        V.abs_id = C.fresh_abstraction_id ();
        kind;
        can_end;
        parents = V.AbstractionId.Set.empty;
        original_parents = [];
        regions = T.RegionId.Set.singleton nrid;
        ancestors_regions = T.RegionId.Set.empty;
        avalues;
      }
    in
    fresh_absl := fresh_abs :: !fresh_absl
  in

  (* Explore the shared values in the context abstractions, and introduce
     fresh abstractions with reborrows for those shared values.

     We simply explore the context and call {!push_abs_for_shared_value}
     when necessary.
  *)
  let collect_shared_values_in_abs (abs : V.abs) : unit =
    let collect_shared_value lids (sv : V.typed_value) =
      (* Sanity check: we don't support nested borrows for now *)
      assert (not (value_has_borrows ctx sv.V.value));

      (* Filter the loan ids whose corresponding borrows appear in abstractions
         (see the documentation of the function) *)
      let lids = V.BorrowId.Set.diff lids abs_borrow_ids in

      (* Generate fresh borrows and values *)
      V.BorrowId.Set.iter (push_abs_for_shared_value abs sv) lids
    in

    let visit_avalue =
      object
        inherit [_] V.iter_typed_avalue as super

        method! visit_VSharedLoan env lids sv =
          collect_shared_value lids sv;

          (* Continue the exploration *)
          super#visit_VSharedLoan env lids sv

        method! visit_ASharedLoan env lids sv av =
          collect_shared_value lids sv;

          (* Continue the exploration *)
          super#visit_ASharedLoan env lids sv av

        (** Check that there are no symbolic values with *borrows* inside the
            abstraction - shouldn't happen if the symbolic values are greedily
            expanded.
            We do this because those values could contain shared borrows:
            if it is the case, we need to duplicate them too.
            TODO: implement this more general behavior.
         *)
        method! visit_symbolic_value env sv =
          assert (not (symbolic_value_has_borrows ctx sv));
          super#visit_symbolic_value env sv
      end
    in
    List.iter (visit_avalue#visit_typed_avalue None) abs.avalues
  in
  C.env_iter_abs collect_shared_values_in_abs ctx.env;

  (* Update the borrow ids in the environment.

     Example:
     ========
     If we start with environment:
     {[
       abs'0 { SL {l0, l1} s0 }
       l0 -> SB l0
       l1 -> SB l1
     ]}

     We introduce the following abstractions:
     {[
       abs'2 { SB l0, SL {l2} s2 }
       abs'3 { SB l1, SL {l3} s3 }
     ]}

     While doing so, we registered the fact that we introduced [l2] for [l0]
     and [l3] for [l1]: we now need to perform the proper substitutions in
     the values [l0] and [l1]. This gives:

     {[
       l0 -> SB l0
       l1 -> SB l1

         ~~>

       l0 -> SB l2
       l1 -> SB l3
     ]}
  *)
  let env =
    let bmap = V.BorrowId.Map.of_list !borrow_substs in
    let bsusbt bid =
      match V.BorrowId.Map.find_opt bid bmap with
      | None -> bid
      | Some bid -> bid
    in

    let visitor =
      object
        inherit [_] C.map_env
        method! visit_borrow_id _ bid = bsusbt bid
      end
    in
    visitor#visit_env () ctx.env
  in

  (* Add the abstractions *)
  let fresh_absl = List.map (fun abs -> C.EAbs abs) !fresh_absl in
  let env = List.append fresh_absl env in
  let ctx = { ctx with env } in

  let _, new_ctx_ids_map = compute_context_ids ctx in

  (* Synthesize *)
  match cf ctx with
  | None -> None
  | Some e ->
      (* Add the let-bindings which introduce the fresh symbolic values *)
      Some
        (List.fold_left
           (fun e (sid, v) ->
             let v = mk_typed_value_from_symbolic_value v in
             let sv =
               V.SymbolicValueId.Map.find sid new_ctx_ids_map.sids_to_values
             in
             SymbolicAst.IntroSymbolic (ctx, None, sv, VaSingleValue v, e))
           e !sid_subst)

let prepare_ashared_loans_no_synth (loop_id : V.LoopId.id) (ctx : C.eval_ctx) :
    C.eval_ctx =
  get_cf_ctx_no_synth (prepare_ashared_loans (Some loop_id)) ctx

let compute_loop_entry_fixed_point (config : C.config) (loop_id : V.LoopId.id)
    (eval_loop_body : st_cm_fun) (ctx0 : C.eval_ctx) :
    C.eval_ctx * ids_sets * V.abs T.RegionGroupId.Map.t =
  (* The continuation for when we exit the loop - we register the
     environments upon loop *reentry*, and synthesize nothing by
     returning [None]
  *)
  let ctxs = ref [] in
  let register_ctx ctx = ctxs := ctx :: !ctxs in

  (* Introduce "reborrows" for the shared values in the abstractions, so that
     the shared values in the fixed abstractions never get modified (technically,
     they are immutable, but in practice we can introduce more shared loans, or
     expand symbolic values).

     For more details, see the comments for {!prepare_ashared_loans}
  *)
  let ctx = prepare_ashared_loans_no_synth loop_id ctx0 in

  (* Debug *)
  log#ldebug
    (lazy
      ("compute_loop_entry_fixed_point: after prepare_ashared_loans:"
     ^ "\n\n- ctx0:\n"
      ^ eval_ctx_to_string_no_filter ctx0
      ^ "\n\n- ctx1:\n"
      ^ eval_ctx_to_string_no_filter ctx
      ^ "\n\n"));

  let cf_exit_loop_body (res : statement_eval_res) : m_fun =
   fun ctx ->
    match res with
    | Return | Panic | Break _ -> None
    | Unit ->
        (* See the comment in {!eval_loop} *)
        raise (Failure "Unreachable")
    | Continue i ->
        (* For now we don't support continues to outer loops *)
        assert (i = 0);
        register_ctx ctx;
        None
    | LoopReturn _ | EndEnterLoop _ | EndContinue _ ->
        (* We don't support nested loops for now *)
        raise (Failure "Nested loops are not supported for now")
  in

  (* The fixed ids. They are the ids of the original ctx, after we ended
     the borrows/loans which end during the first loop iteration (we do
     one loop iteration, then set it to [Some].
  *)
  let fixed_ids : ids_sets option ref = ref None in

  (* Join the contexts at the loop entry - ctx1 is the current joined
     context (the context at the loop entry, after we called
     {!prepare_ashared_loans}, if this is the first iteration) *)
  let join_ctxs (ctx1 : C.eval_ctx) : C.eval_ctx =
    (* If this is the first iteration, end the borrows/loans/abs which
       appear in ctx1 and not in the other contexts, then compute the
       set of fixed ids. This means those borrows/loans have to end
       in the loop, and we rather end them *before* the loop. *)
    let ctx1 =
      match !fixed_ids with
      | Some _ -> ctx1
      | None ->
          let old_ids, _ = compute_context_ids ctx1 in
          let new_ids, _ = compute_contexts_ids !ctxs in
          let blids = V.BorrowId.Set.diff old_ids.blids new_ids.blids in
          let aids = V.AbstractionId.Set.diff old_ids.aids new_ids.aids in
          (* End those borrows and abstractions *)
          let end_borrows_abs blids aids ctx =
            let ctx =
              InterpreterBorrows.end_borrows_no_synth config blids ctx
            in
            let ctx =
              InterpreterBorrows.end_abstractions_no_synth config aids ctx
            in
            ctx
          in
          (* End the borrows/abs in [ctx1] *)
          let ctx1 = end_borrows_abs blids aids ctx1 in
          (* We can also do the same in the contexts [ctxs]: if there are
             several contexts, maybe one of them ended some borrows and some
             others didn't. As we need to end those borrows anyway (the join
             will detect them and ask to end them) we do it preemptively.
          *)
          ctxs := List.map (end_borrows_abs blids aids) !ctxs;
          (* Note that the fixed ids are given by the original context, from *before*
             we introduce fresh abstractions/reborrows for the shared values *)
          fixed_ids := Some (fst (compute_context_ids ctx0));
          ctx1
    in

    let fixed_ids = Option.get !fixed_ids in
    let (_, _), ctx2 =
      loop_join_origin_with_continue_ctxs config loop_id fixed_ids ctx1 !ctxs
    in
    ctxs := [];
    ctx2
  in
  (* Compute the set of fixed ids - for the symbolic ids, we compute the
     intersection of ids between the original environment and the list
     of new environments *)
  let compute_fixed_ids (ctxl : C.eval_ctx list) : ids_sets =
    let fixed_ids, _ = compute_context_ids ctx0 in
    let { aids; blids; borrow_ids; loan_ids; dids; rids; sids } = fixed_ids in
    let sids = ref sids in
    List.iter
      (fun ctx ->
        let fixed_ids, _ = compute_context_ids ctx in
        sids := V.SymbolicValueId.Set.inter !sids fixed_ids.sids)
      ctxl;
    let sids = !sids in
    let fixed_ids = { aids; blids; borrow_ids; loan_ids; dids; rids; sids } in
    fixed_ids
  in
  (* Check if two contexts are equivalent - modulo alpha conversion on the
     existentially quantified borrows/abstractions/symbolic values.
  *)
  let equiv_ctxs (ctx1 : C.eval_ctx) (ctx2 : C.eval_ctx) : bool =
    let fixed_ids = compute_fixed_ids [ ctx1; ctx2 ] in
    let check_equivalent = true in
    let lookup_shared_value _ = raise (Failure "Unreachable") in
    Option.is_some
      (match_ctxs check_equivalent fixed_ids lookup_shared_value
         lookup_shared_value ctx1 ctx2)
  in
  let max_num_iter = Config.loop_fixed_point_max_num_iters in
  let rec compute_fixed_point (ctx : C.eval_ctx) (i0 : int) (i : int) :
      C.eval_ctx =
    if i = 0 then
      raise
        (Failure
           ("Could not compute a loop fixed point in " ^ string_of_int i0
          ^ " iterations"))
    else
      (* Evaluate the loop body to register the different contexts upon reentry *)
      let _ = eval_loop_body cf_exit_loop_body ctx in
      (* Compute the join between the original contexts and the contexts computed
         upon reentry *)
      let ctx1 = join_ctxs ctx in

      (* Debug *)
      log#ldebug
        (lazy
          ("compute_fixed_point:" ^ "\n\n- ctx0:\n"
          ^ eval_ctx_to_string_no_filter ctx
          ^ "\n\n- ctx1:\n"
          ^ eval_ctx_to_string_no_filter ctx1
          ^ "\n\n"));

      (* Check if we reached a fixed point: if not, iterate *)
      if equiv_ctxs ctx ctx1 then ctx1 else compute_fixed_point ctx1 i0 (i - 1)
  in
  let fp = compute_fixed_point ctx max_num_iter max_num_iter in

  (* Debug *)
  log#ldebug
    (lazy
      ("compute_fixed_point: fixed point computed before matching with input \
        region groups:" ^ "\n\n- fp:\n"
      ^ eval_ctx_to_string_no_filter fp
      ^ "\n\n"));

  (* Make sure we have exactly one loop abstraction per function region (merge
     abstractions accordingly).

     Rem.: this shouldn't impact the set of symbolic value ids (because we
     already merged abstractions "vertically" and are now merging them
     "horizontally": the symbolic values contained in the abstractions (typically
     the shared values) will be preserved.
  *)
  let fp, rg_to_abs =
    (* List the loop abstractions in the fixed-point *)
    let fp_aids, add_aid, _mem_aid = V.AbstractionId.Set.mk_stateful_set () in

    let list_loop_abstractions =
      object
        inherit [_] C.map_eval_ctx

        method! visit_abs _ abs =
          match abs.kind with
          | Loop (loop_id', _, kind) ->
              assert (loop_id' = loop_id);
              assert (kind = V.LoopSynthInput);
              (* The abstractions introduced so far should be endable *)
              assert (abs.can_end = true);
              add_aid abs.abs_id;
              abs
          | _ -> abs
      end
    in
    let fp = list_loop_abstractions#visit_eval_ctx () fp in

    (* For every input region group:
     * - evaluate until we get to a [return]
     * - end the input abstraction corresponding to the input region group
     * - find which loop abstractions end at that moment
     *
     * [fp_ended_aids] links region groups to sets of ended abstractions.
     *)
    let fp_ended_aids = ref T.RegionGroupId.Map.empty in
    let add_ended_aids (rg_id : T.RegionGroupId.id)
        (aids : V.AbstractionId.Set.t) : unit =
      match T.RegionGroupId.Map.find_opt rg_id !fp_ended_aids with
      | None ->
          fp_ended_aids := T.RegionGroupId.Map.add rg_id aids !fp_ended_aids
      | Some aids' ->
          let aids = V.AbstractionId.Set.union aids aids' in
          fp_ended_aids := T.RegionGroupId.Map.add rg_id aids !fp_ended_aids
    in
    let cf_loop : st_m_fun =
     fun res ctx ->
      match res with
      | Continue _ | Panic ->
          (* We don't want to generate anything *)
          None
      | Break _ ->
          (* We enforce that we can't get there: see {!PrePasses.remove_loop_breaks} *)
          raise (Failure "Unreachable")
      | Unit | LoopReturn _ | EndEnterLoop _ | EndContinue _ ->
          (* For why we can't get [Unit], see the comments inside {!eval_loop_concrete}.
             For [EndEnterLoop] and [EndContinue]: we don't support nested loops for now.
          *)
          raise (Failure "Unreachable")
      | Return ->
          (* Should we consume the return value and pop the frame?
           * If we check in [Interpreter] that the loop abstraction we end is
           * indeed the correct one, I think it is sound to under-approximate here
           * (and it shouldn't make any difference).
           *)
          let _ =
            List.iter
              (fun rg_id ->
                (* Lookup the input abstraction - we use the fact that the
                   abstractions should have been introduced in a specific
                   order (and we check that it is indeed the case) *)
                let abs_id =
                  V.AbstractionId.of_int (T.RegionGroupId.to_int rg_id)
                in
                (* By default, the [SynthInput] abs can't end *)
                let ctx = C.ctx_set_abs_can_end ctx abs_id true in
                assert (
                  let abs = C.ctx_lookup_abs ctx abs_id in
                  abs.kind = V.SynthInput rg_id);
                (* End this abstraction *)
                let ctx =
                  InterpreterBorrows.end_abstraction_no_synth config abs_id ctx
                in
                (* Explore the context, and check which abstractions are not there anymore *)
                let ids, _ = compute_context_ids ctx in
                let ended_ids = V.AbstractionId.Set.diff !fp_aids ids.aids in
                add_ended_aids rg_id ended_ids)
              ctx.region_groups
          in
          (* We don't want to generate anything *)
          None
    in
    let _ = eval_loop_body cf_loop fp in

    (* Check that the sets of abstractions we need to end per region group are pairwise
     * disjoint *)
    let aids_union = ref V.AbstractionId.Set.empty in
    let _ =
      T.RegionGroupId.Map.iter
        (fun _ ids ->
          assert (V.AbstractionId.Set.disjoint !aids_union ids);
          aids_union := V.AbstractionId.Set.union ids !aids_union)
        !fp_ended_aids
    in

    (* We also check that all the regions need to end - this is not necessary per
       se, but if it doesn't happen it is bizarre and worth investigating... *)
    assert (V.AbstractionId.Set.equal !aids_union !fp_aids);

    (* Merge the abstractions which need to be merged, and compute the map from
       region id to abstraction id *)
    let fp = ref fp in
    let rg_to_abs = ref T.RegionGroupId.Map.empty in
    let _ =
      T.RegionGroupId.Map.iter
        (fun rg_id ids ->
          let ids = V.AbstractionId.Set.elements ids in
          (* Retrieve the first id of the group *)
          match ids with
          | [] ->
              (* We shouldn't get there: we actually introduce reborrows with
                 {!prepare_ashared_loans} and in the [match_mut_borrows] function
                 of {!MakeJoinMatcher} to introduce some fresh abstractions for
                 this purpose.
              *)
              raise (Failure "Unexpected")
          | id0 :: ids ->
              let id0 = ref id0 in
              (* Add the proper region group into the abstraction *)
              let abs_kind = V.Loop (loop_id, Some rg_id, V.LoopSynthInput) in
              let abs = C.ctx_lookup_abs !fp !id0 in
              let abs = { abs with V.kind = abs_kind } in
              let fp', _ = C.ctx_subst_abs !fp !id0 abs in
              fp := fp';
              (* Merge all the abstractions into this one *)
              List.iter
                (fun id ->
                  try
                    log#ldebug
                      (lazy
                        ("compute_loop_entry_fixed_point: merge FP \
                          abstraction: "
                        ^ V.AbstractionId.to_string id
                        ^ " into "
                        ^ V.AbstractionId.to_string !id0));
                    (* Note that we merge *into* [id0] *)
                    let fp', id0' =
                      merge_into_abstraction loop_id abs_kind false !fp id !id0
                    in
                    fp := fp';
                    id0 := id0';
                    ()
                  with ValueMatchFailure _ -> raise (Failure "Unexpected"))
                ids;
              (* Register the mapping *)
              let abs = C.ctx_lookup_abs !fp !id0 in
              rg_to_abs := T.RegionGroupId.Map.add_strict rg_id abs !rg_to_abs)
        !fp_ended_aids
    in
    let rg_to_abs = !rg_to_abs in

    (* Reorder the loans and borrows in the fresh abstractions in the fixed-point *)
    let fp =
      reorder_loans_borrows_in_fresh_abs (Option.get !fixed_ids).aids !fp
    in

    (* Update the abstraction's [can_end] field and their kinds.

       Note that if [remove_rg_id] is [true], we set the region id to [None]
       and set the abstractions as endable: this is so that we can check that
       we have a fixed point (so far in the fixed point the loop abstractions had
       no region group, and we set them as endable just above).

       If [remove_rg_id] is [false], we simply set the abstractions as non-endable
       to freeze them (we will use the fixed point as starting point for the
       symbolic execution of the loop body, and we have to make sure the input
       abstractions are frozen).
    *)
    let update_loop_abstractions (remove_rg_id : bool) =
      object
        inherit [_] C.map_eval_ctx

        method! visit_abs _ abs =
          match abs.kind with
          | Loop (loop_id', _, kind) ->
              assert (loop_id' = loop_id);
              assert (kind = V.LoopSynthInput);
              let kind =
                if remove_rg_id then V.Loop (loop_id, None, V.LoopSynthInput)
                else abs.kind
              in
              { abs with can_end = remove_rg_id; kind }
          | _ -> abs
      end
    in
    let update_kinds_can_end (remove_rg_id : bool) ctx =
      (update_loop_abstractions remove_rg_id)#visit_eval_ctx () ctx
    in
    let fp = update_kinds_can_end false fp in

    (* Sanity check: we still have a fixed point - we simply call [compute_fixed_point]
       while allowing exactly one iteration to see if it fails *)
    let _ =
      let fp_test = update_kinds_can_end true fp in
      log#ldebug
        (lazy
          ("compute_fixed_point: fixed point after matching with the function \
            region groups:\n"
          ^ eval_ctx_to_string_no_filter fp_test));
      compute_fixed_point fp_test 1 1
    in

    (* Return *)
    (fp, rg_to_abs)
  in
  let fixed_ids = compute_fixed_ids [ fp ] in

  (* Return *)
  (fp, fixed_ids, rg_to_abs)

let compute_fixed_point_id_correspondance (fixed_ids : ids_sets)
    (src_ctx : C.eval_ctx) (tgt_ctx : C.eval_ctx) : borrow_loan_corresp =
  log#ldebug
    (lazy
      ("compute_fixed_point_id_correspondance:\n\n- fixed_ids:\n"
     ^ show_ids_sets fixed_ids ^ "\n\n- src_ctx:\n" ^ eval_ctx_to_string src_ctx
     ^ "\n\n- tgt_ctx:\n" ^ eval_ctx_to_string tgt_ctx ^ "\n\n"));

  let filt_src_env, _, _ = ctx_split_fixed_new fixed_ids src_ctx in
  let filt_src_ctx = { src_ctx with env = filt_src_env } in
  let filt_tgt_env, new_absl, _ = ctx_split_fixed_new fixed_ids tgt_ctx in
  let filt_tgt_ctx = { tgt_ctx with env = filt_tgt_env } in

  log#ldebug
    (lazy
      ("compute_fixed_point_id_correspondance:\n\n- fixed_ids:\n"
     ^ show_ids_sets fixed_ids ^ "\n\n- filt_src_ctx:\n"
      ^ eval_ctx_to_string filt_src_ctx
      ^ "\n\n- filt_tgt_ctx:\n"
      ^ eval_ctx_to_string filt_tgt_ctx
      ^ "\n\n"));

  (* Match the source context and the filtered target context *)
  let maps =
    let check_equiv = false in
    let fixed_ids = ids_sets_empty_borrows_loans fixed_ids in
    let open InterpreterBorrowsCore in
    let lookup_shared_loan lid ctx : V.typed_value =
      match snd (lookup_loan ek_all lid ctx) with
      | Concrete (VSharedLoan (_, v)) -> v
      | Abstract (ASharedLoan (_, v, _)) -> v
      | _ -> raise (Failure "Unreachable")
    in
    let lookup_in_tgt id = lookup_shared_loan id tgt_ctx in
    let lookup_in_src id = lookup_shared_loan id src_ctx in
    Option.get
      (match_ctxs check_equiv fixed_ids lookup_in_tgt lookup_in_src filt_tgt_ctx
         filt_src_ctx)
  in

  log#ldebug
    (lazy
      ("compute_fixed_point_id_correspondance:\n\n- tgt_to_src_maps:\n"
     ^ show_ids_maps maps ^ "\n\n"));

  let src_to_tgt_borrow_map =
    V.BorrowId.Map.of_list
      (List.map
         (fun (x, y) -> (y, x))
         (V.BorrowId.InjSubst.bindings maps.borrow_id_map))
  in

  (* Sanity check: for every abstraction, the target loans and borrows are mapped
     to the same set of source loans and borrows.

     For instance, if we map the [env_fp] to [env0] (only looking at the bindings,
     ignoring the abstractions) below:
     {[
       env0 = {
         abs@0 { ML l0 }
         ls -> MB l0 (s2 : loops::List<T>)
         i -> s1 : u32
       }

       env_fp = {
         abs@0 { ML l0 }
         ls -> MB l1 (s3 : loops::List<T>)
         i -> s4 : u32
         abs@fp {
           MB l0
           ML l1
         }
       }
     ]}

     We get that l1 is mapped to l0. From there, we see that abs@fp consumes
     the same borrows that it gives: it is indeed an identity function.

     TODO: we should also check the mappings for the shared values (to
     make sure the abstractions are indeed the identity)...
  *)
  List.iter
    (fun abs ->
      let ids, _ = compute_abs_ids abs in
      (* Map the *loan* ids (we just match the corresponding *loans* ) *)
      let loan_ids =
        V.BorrowId.Set.map
          (fun x -> V.BorrowId.InjSubst.find x maps.borrow_id_map)
          ids.loan_ids
      in
      (* Check that the loan and borrows are related *)
      assert (V.BorrowId.Set.equal ids.borrow_ids loan_ids))
    new_absl;

  (* For every target abstraction (going back to the [list_nth_mut] example,
     we have to visit [abs@fp { ML l0, MB l1 }]):
     - go through the tgt borrows ([l1])
     - for every tgt borrow, find the corresponding src borrow ([l0], because
       we have: [borrows_map: { l1 -> l0 }])
     - from there, find the corresponding tgt loan ([l0])

     Note that this borrow does not necessarily appear in the src_to_tgt_borrow_map,
     if it actually corresponds to a borrows introduced when decomposing the
     abstractions to move the shared values out of the source context abstractions.
  *)
  let tgt_borrow_to_loan = ref V.BorrowId.InjSubst.empty in
  let visit_tgt =
    object
      inherit [_] V.iter_abs

      method! visit_borrow_id _ id =
        (* Find the target borrow *)
        let tgt_borrow_id = V.BorrowId.Map.find id src_to_tgt_borrow_map in
        (* Update the map *)
        tgt_borrow_to_loan :=
          V.BorrowId.InjSubst.add id tgt_borrow_id !tgt_borrow_to_loan
    end
  in
  List.iter (visit_tgt#visit_abs ()) new_absl;

  (* Compute the map from loan to borrows *)
  let tgt_loan_to_borrow =
    V.BorrowId.InjSubst.of_list
      (List.map
         (fun (x, y) -> (y, x))
         (V.BorrowId.InjSubst.bindings !tgt_borrow_to_loan))
  in

  (* Return *)
  {
    borrow_to_loan_id_map = !tgt_borrow_to_loan;
    loan_to_borrow_id_map = tgt_loan_to_borrow;
  }

let compute_fp_ctx_symbolic_values (ctx : C.eval_ctx) (fp_ctx : C.eval_ctx) :
    V.SymbolicValueId.Set.t * V.symbolic_value list =
  let old_ids, _ = compute_context_ids ctx in
  let fp_ids, fp_ids_maps = compute_context_ids fp_ctx in
  let fresh_sids = V.SymbolicValueId.Set.diff fp_ids.sids old_ids.sids in

  (* Compute the set of symbolic values which appear in shared values inside
     *fixed* abstractions: because we introduce fresh abstractions and reborrows
     with {!prepare_ashared_loans}, those values are never accessed directly
     inside the loop iterations: we can ignore them (and should, because
     otherwise it leads to a very ugly translation with duplicated, unused
     values) *)
  let shared_sids_in_fixed_abs =
    let fixed_absl =
      List.filter
        (fun (ee : C.env_elem) ->
          match ee with
          | C.EBinding _ | C.EFrame -> false
          | EAbs abs -> V.AbstractionId.Set.mem abs.abs_id old_ids.aids)
        ctx.env
    in

    (* Rem.: as we greedily expand the symbolic values containing borrows, and
       in particular the (mutable/shared) borrows, we could simply list the
       symbolic values appearing in the abstractions: those are necessarily
       shared values. We prefer to be more general, in prevision of later
       changes.
    *)
    let sids = ref V.SymbolicValueId.Set.empty in
    let visitor =
      object (self)
        inherit [_] C.iter_env

        method! visit_ASharedLoan inside_shared _ sv child_av =
          self#visit_typed_value true sv;
          self#visit_typed_avalue inside_shared child_av

        method! visit_symbolic_value_id inside_shared sid =
          if inside_shared then sids := V.SymbolicValueId.Set.add sid !sids
      end
    in
    visitor#visit_env false fixed_absl;
    !sids
  in

  (* Remove the shared symbolic values present in the fixed abstractions -
     see comments for [shared_sids_in_fixed_abs]. *)
  let sids_to_values = fp_ids_maps.sids_to_values in

  log#ldebug
    (lazy
      ("compute_fp_ctx_symbolic_values:" ^ "\n- shared_sids_in_fixed_abs:"
      ^ V.SymbolicValueId.Set.show shared_sids_in_fixed_abs
      ^ "\n- all_sids_to_values: "
      ^ V.SymbolicValueId.Map.show (symbolic_value_to_string ctx) sids_to_values
      ^ "\n"));

  let sids_to_values =
    V.SymbolicValueId.Map.filter
      (fun sid _ ->
        not (V.SymbolicValueId.Set.mem sid shared_sids_in_fixed_abs))
      sids_to_values
  in

  (* List the input symbolic values in proper order.

     We explore the environment, and order the symbolic values in the order
     in which they are found - this way, the symbolic values found in a
     variable [x] which appears before [y] are listed first, for instance.
  *)
  let input_svalues =
    let found_sids = ref V.SymbolicValueId.Set.empty in
    let ordered_sids = ref [] in

    let visitor =
      object (self)
        inherit [_] C.iter_env

        (** We lookup the shared values *)
        method! visit_VSharedBorrow env bid =
          let open InterpreterBorrowsCore in
          let v =
            match snd (lookup_loan ek_all bid fp_ctx) with
            | Concrete (VSharedLoan (_, v)) -> v
            | Abstract (ASharedLoan (_, v, _)) -> v
            | _ -> raise (Failure "Unreachable")
          in
          self#visit_typed_value env v

        method! visit_symbolic_value_id _ id =
          if not (V.SymbolicValueId.Set.mem id !found_sids) then (
            found_sids := V.SymbolicValueId.Set.add id !found_sids;
            ordered_sids := id :: !ordered_sids)
      end
    in

    List.iter (visitor#visit_env_elem ()) (List.rev fp_ctx.env);

    List.filter_map
      (fun id -> V.SymbolicValueId.Map.find_opt id sids_to_values)
      (List.rev !ordered_sids)
  in

  log#ldebug
    (lazy
      ("compute_fp_ctx_symbolic_values:" ^ "\n- src context:\n"
      ^ eval_ctx_to_string_no_filter ctx
      ^ "\n- fixed point:\n"
      ^ eval_ctx_to_string_no_filter fp_ctx
      ^ "\n- fresh_sids: "
      ^ V.SymbolicValueId.Set.show fresh_sids
      ^ "\n- input_svalues: "
      ^ Print.list_to_string (symbolic_value_to_string ctx) input_svalues
      ^ "\n\n"));

  (fresh_sids, input_svalues)
