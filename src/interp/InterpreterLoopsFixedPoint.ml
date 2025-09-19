open Types
open Values
open Contexts
open TypesUtils
open ValuesUtils
module S = SynthesizeSymbolic
open Cps
open InterpreterUtils
open InterpreterBorrows
open InterpreterAbs
open InterpreterLoopsCore
open InterpreterLoopsMatchCtxs
open InterpreterLoopsJoinCtxs

(** The local logger *)
let log = Logging.loops_fixed_point_log

let prepare_ashared_loans (span : Meta.span) (loop_id : LoopId.id option)
    ~(with_abs_conts : bool) : cm_fun =
 fun ctx0 ->
  let ctx = ctx0 in
  [%ldebug "ctx0:\n" ^ eval_ctx_to_string ctx];

  (* Compute the set of borrows which appear in the abstractions, so that
     we can filter the borrows that we reborrow.
  *)
  let absl =
    List.filter_map
      (function
        | EBinding _ | EFrame -> None
        | EAbs abs -> Some abs)
      ctx.env
  in
  let _, absl_id_maps = compute_absl_ids absl in

  (* Map from the fresh sids to the original symbolic values *)
  let sid_subst = ref [] in

  (* Return the same value but where:
     - the shared loans have been removed
     - the symbolic values have been replaced with fresh symbolic values
     - the region ids found in the value and belonging to the set [rids] have
       been substituted with [nrid]
  *)
  let mk_value_with_fresh_sids_no_shared_loans (rids : RegionId.Set.t)
      (nrid : RegionId.id) (v : tvalue) : tvalue =
    (* Remove the shared loans *)
    let v = value_remove_shared_loans v in
    (* Substitute the symbolic values and the region *)
    Substitute.tvalue_subst_ids
      {
        (Substitute.no_abs_id_subst span) with
        r_subst = (fun r -> if RegionId.Set.mem r rids then nrid else r);
        ssubst =
          (fun id ->
            let nid = fresh_symbolic_value_id () in
            let sv = SymbolicValueId.Map.find id absl_id_maps.sids_to_values in
            sid_subst := (nid, sv) :: !sid_subst;
            nid);
      }
      v
  in

  let fresh_absl = ref [] in

  (* Auxiliary function to create a new abstraction for a shared value.

     Example:
     ========
     When exploring:
     {[
       abs'0 { SL l s0 }
       x0 -> SB l
       x1 -> SB l
     ]}

     we find the shared borrow [SB l] in x0 and x1, which maps to a loan in a region
     abstraction. We introduce reborrows the following way:
     {[
       abs'0 { SL l s0 }
       abs'2 { SB l, SL {l1} s1 }
       abs'3 { SB l, SL {l2} s2 }
       x0 -> SB l1
       x1 -> SB l2
     ]}
  *)
  let push_abs_for_shared_value (abs : abs) (sv : tvalue) (lid : BorrowId.id)
      (sid : SharedBorrowId.id) : BorrowId.id * SharedBorrowId.id =
    (* Create fresh borrows (for the reborrow) *)
    let nlid = fresh_borrow_id () in
    let nsid = fresh_shared_borrow_id () in

    (* We need a fresh region for the new abstraction *)
    let nrid = fresh_region_id () in

    (* Prepare the shared value *)
    let nsv =
      mk_value_with_fresh_sids_no_shared_loans abs.regions.owned nrid sv
    in

    (* Rem.: the below sanity checks are not really necessary *)
    [%sanity_check] span (AbstractionId.Set.is_empty abs.parents);
    [%sanity_check] span (abs.original_parents = []);

    (* Introduce the new abstraction for the shared values *)
    [%cassert] span (ty_no_regions sv.ty) "Nested borrows are not supported yet";
    let rty = sv.ty in

    (* Create the shared loan child *)
    let child_rty = rty in
    let child_av = mk_aignored span child_rty None in

    (* Create the shared loan *)
    let loan_rty = TRef (RVar (Free nrid), rty, RShared) in
    let loan_value = ALoan (ASharedLoan (PNone, nlid, nsv, child_av)) in
    let loan_value = mk_tavalue span loan_rty loan_value in

    (* Create the shared borrow *)
    let borrow_rty = loan_rty in
    let borrow_value = ABorrow (ASharedBorrow (PNone, lid, sid)) in
    let borrow_value = mk_tavalue span borrow_rty borrow_value in

    (* Create the abstraction *)
    let avalues = [ borrow_value; loan_value ] in
    let kind : abs_kind =
      match loop_id with
      | Some loop_id -> Loop (loop_id, None, LoopSynthInput)
      | None -> Identity
    in
    let can_end = true in
    let regions : abs_regions = { owned = RegionId.Set.singleton nrid } in
    let cont : abs_cont option =
      if with_abs_conts then
        Some { output = Some (mk_etuple []); input = Some (mk_etuple []) }
      else None
    in
    let fresh_abs =
      {
        abs_id = fresh_abstraction_id ();
        kind;
        can_end;
        parents = AbstractionId.Set.empty;
        original_parents = [];
        regions;
        avalues;
        cont;
      }
    in
    fresh_absl := fresh_abs :: !fresh_absl;
    (nlid, nsid)
  in

  (* Compute the map from borrow id to shared value appearing in a region abstraction -
     we only visit the region abstractions *)
  let loan_to_shared_value = ref BorrowId.Map.empty in
  let visitor =
    object
      inherit [_] iter_abs as super

      method! visit_VSharedLoan abs bid sv =
        loan_to_shared_value :=
          BorrowId.Map.add bid (abs, sv) !loan_to_shared_value;
        super#visit_VSharedLoan abs bid sv

      method! visit_ASharedLoan abs pm bid sv child =
        loan_to_shared_value :=
          BorrowId.Map.add bid (abs, sv) !loan_to_shared_value;
        super#visit_ASharedLoan abs pm bid sv child
    end
  in
  List.iter (fun abs -> visitor#visit_abs abs abs) absl;

  (* Explore the shared borrows in the environment, and introduce
     fresh abstractions with reborrows.

     We simply explore the context and call {!push_abs_for_shared_value}
     when necessary.
  *)
  let visitor =
    object
      inherit [_] map_eval_ctx as super
      method! visit_abs _ abs = (* Do not explore region abstractions *) abs

      method! visit_VSharedBorrow env bid sid =
        (* Check if the corresponding loan is in a region abstraction *)
        match BorrowId.Map.find_opt bid !loan_to_shared_value with
        | None ->
            (* Do nothing *)
            super#visit_VSharedBorrow env bid sid
        | Some (abs, sv) ->
            let bid, sid = push_abs_for_shared_value abs sv bid sid in
            VSharedBorrow (bid, sid)
    end
  in
  let ctx = visitor#visit_eval_ctx () ctx in

  (* Add the abstractions *)
  let fresh_absl = List.map (fun abs -> EAbs abs) !fresh_absl in
  let ctx = { ctx with env = List.append fresh_absl ctx.env } in

  let _, new_ctx_ids_map = compute_ctx_ids ctx in

  (* Synthesize *)
  let cf e =
    (* Add the let-bindings which introduce the fresh symbolic values *)
    List.fold_left
      (fun e (sid, v) ->
        let v = mk_tvalue_from_symbolic_value v in
        let sv = SymbolicValueId.Map.find sid new_ctx_ids_map.sids_to_values in
        SymbolicAst.IntroSymbolic (ctx, None, sv, VaSingleValue v, e))
      e !sid_subst
  in
  Invariants.check_invariants span ctx;
  [%ldebug "resulting ctx:\n" ^ eval_ctx_to_string ctx];
  (ctx, cf)

let prepare_ashared_loans_no_synth (span : Meta.span) (loop_id : LoopId.id)
    ~(with_abs_conts : bool) (ctx : eval_ctx) : eval_ctx =
  fst (prepare_ashared_loans span (Some loop_id) ~with_abs_conts ctx)

let compute_loop_entry_fixed_point (config : config) (span : Meta.span)
    (loop_id : LoopId.id) (eval_loop_body : stl_cm_fun) (ctx0 : eval_ctx) :
    eval_ctx * ids_sets * AbstractionId.id RegionGroupId.Map.t =
  (* Introduce "reborrows" for the shared values in the abstractions, so that
     the shared values in the fixed abstractions never get modified (technically,
     they are immutable, but in practice we can introduce more shared loans, or
     expand symbolic values).

     For more details, see the comments for {!prepare_ashared_loans}
  *)
  let ctx =
    prepare_ashared_loans_no_synth span loop_id ~with_abs_conts:false ctx0
  in

  (* Debug *)
  [%ltrace
    "after prepare_ashared_loans:" ^ "\n\n- ctx0:\n"
    ^ eval_ctx_to_string ~span:(Some span) ~filter:false ctx0
    ^ "\n\n- ctx1:\n"
    ^ eval_ctx_to_string ~span:(Some span) ~filter:false ctx
    ^ "\n"];

  (* The fixed ids. They are the ids of the original ctx, after we ended
     the borrows/loans which end during the first loop iteration (we do
     one loop iteration, then set it to [Some]).
  *)
  let fixed_ids : ids_sets option ref = ref None in

  (* Join the contexts at the loop entry - ctx1 is the current joined
     context (the context at the loop entry, after we called
     {!prepare_ashared_loans}, if this is the first iteration) *)
  let join_ctxs (ctx1 : eval_ctx) (ctxs : eval_ctx list) : eval_ctx =
    [%ltrace "join_ctxs"];
    (* If this is the first iteration, end the borrows/loans/abs which
       appear in ctx1 and not in the other contexts, then compute the
       set of fixed ids. This means those borrows/loans have to end
       in the loop, and we rather end them *before* the loop.

       We also end those borrows in the collected contexts.
    *)
    let ctx1, ctxs =
      match !fixed_ids with
      | Some _ -> (ctx1, ctxs)
      | None ->
          let old_ids, _ = compute_ctx_ids ctx1 in
          let new_ids, _ = compute_ctxs_ids ctxs in
          let lids = BorrowId.Set.diff old_ids.loan_ids new_ids.loan_ids in
          let aids = AbstractionId.Set.diff old_ids.aids new_ids.aids in
          (* End those loans and abstractions *)
          let end_loans_abs (lids : loan_id_set) (aids : abstraction_id_set) ctx
              =
            let ctx = try_end_loans_no_synth config span lids ctx in
            let ctx = end_abstractions_no_synth config span aids ctx in
            ctx
          in
          (* End the loans/abs in [ctx1] *)
          [%ltrace
            "join_ctxs: ending borrows/abstractions before entering the loop:\n\
             - ending loan ids: "
            ^ BorrowId.Set.to_string None lids
            ^ "\n- ending abstraction ids: "
            ^ AbstractionId.Set.to_string None aids];
          let ctx1 = end_loans_abs lids aids ctx1 in
          (* We can also do the same in the contexts [ctxs]: if there are
             several contexts, maybe one of them ended some borrows and some
             others didn't. As we need to end those borrows anyway (the join
             will detect them and ask to end them) we do it preemptively.
          *)
          let ctxs = List.map (end_loans_abs lids aids) ctxs in
          (* Note that the fixed ids are given by the original context, from *before*
             we introduce fresh abstractions/reborrows for the shared values *)
          fixed_ids := Some (fst (compute_ctx_ids ctx0));
          (ctx1, ctxs)
    in

    let fixed_ids = Option.get !fixed_ids in

    (* Join the context with the context at the loop entry *)
    let (_, _), ctx2 =
      loop_join_origin_with_continue_ctxs config span loop_id fixed_ids ctx1
        ctxs
    in
    ctx2
  in
  [%ltrace "after join_ctxs"];

  (* Compute the set of fixed ids - for the symbolic ids, we compute the
     intersection of ids between the original environment and the list
     of new environments *)
  let compute_fixed_ids (ctxl : eval_ctx list) : ids_sets =
    let fixed_ids, _ = compute_ctx_ids ctx0 in
    let {
      aids;
      blids;
      borrow_ids;
      unique_borrow_ids;
      shared_borrow_ids;
      loan_ids;
      dids;
      rids;
      sids;
    } =
      fixed_ids
    in
    let sids = ref sids in
    List.iter
      (fun ctx ->
        let fixed_ids, _ = compute_ctx_ids ctx in
        sids := SymbolicValueId.Set.inter !sids fixed_ids.sids)
      ctxl;
    let sids = !sids in
    let fixed_ids =
      {
        aids;
        blids;
        borrow_ids;
        unique_borrow_ids;
        shared_borrow_ids;
        loan_ids;
        dids;
        rids;
        sids;
      }
    in
    fixed_ids
  in
  (* Check if two contexts are equivalent - modulo alpha conversion on the
     existentially quantified borrows/abstractions/symbolic values.
  *)
  let equiv_ctxs (ctx1 : eval_ctx) (ctx2 : eval_ctx) : bool =
    [%ltrace "equiv_ctx:"];
    let fixed_ids = compute_fixed_ids [ ctx1; ctx2 ] in
    let lookup_shared_value _ = [%craise] span "Unreachable" in
    Option.is_some
      (match_ctxs span ~check_equiv:true fixed_ids lookup_shared_value
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
        | LoopReturn _ | EndEnterLoop _ | EndContinue _ ->
            (* We don't support nested loops for now *)
            [%craise] span "Nested loops are not supported for now"
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

      (* Check if we reached a fixed point: if not, iterate *)
      if equiv_ctxs ctx ctx1 then ctx1 else compute_fixed_point ctx1 i0 (i - 1)
  in
  let fp = compute_fixed_point ctx max_num_iter max_num_iter in

  (* Debug *)
  [%ltrace
    "fixed point computed before matching with input region groups:"
    ^ "\n\n- fp:\n"
    ^ eval_ctx_to_string ~span:(Some span) ~filter:false fp
    ^ "\n"];

  (* Make sure we have exactly one loop abstraction per function region (merge
     abstractions accordingly).

     Rem.: this shouldn't impact the set of symbolic value ids (because we
     already merged abstractions "vertically" and are now merging them
     "horizontally": the symbolic values contained in the abstractions (typically
     the shared values) will be preserved.
  *)
  let fp, rg_to_abs =
    (* List the loop abstractions in the fixed-point *)
    let fp_aids, add_aid, _mem_aid = AbstractionId.Set.mk_stateful_set () in

    let list_loop_abstractions =
      object
        inherit [_] map_eval_ctx

        method! visit_abs _ abs =
          match abs.kind with
          | Loop (loop_id', _, kind) ->
              [%sanity_check] span (loop_id' = loop_id);
              [%sanity_check] span (kind = LoopSynthInput);
              (* The abstractions introduced so far should be endable *)
              [%sanity_check] span (abs.can_end = true);
              add_aid abs.abs_id;
              abs
          | _ -> abs
      end
    in
    let fp = list_loop_abstractions#visit_eval_ctx () fp in

    (* For every input region group:
       - evaluate until we get to a [return]
       - end the input abstraction corresponding to the input region group
       - find which loop abstractions end at that moment

       [fp_ended_aids] links region groups to sets of ended abstractions.
    *)
    let fp_ended_aids = ref RegionGroupId.Map.empty in
    let add_ended_aids (rg_id : RegionGroupId.id) (aids : AbstractionId.Set.t) :
        unit =
      match RegionGroupId.Map.find_opt rg_id !fp_ended_aids with
      | None -> fp_ended_aids := RegionGroupId.Map.add rg_id aids !fp_ended_aids
      | Some aids' ->
          let aids = AbstractionId.Set.union aids aids' in
          fp_ended_aids := RegionGroupId.Map.add rg_id aids !fp_ended_aids
    in
    let end_at_return (ctx, res) =
      [%ltrace "cf_loop"];
      match res with
      | Continue _ | Panic -> ()
      | Break _ ->
          (* We enforce that we can't get there: see {!PrePasses.remove_loop_breaks} *)
          [%craise] span "Unreachable"
      | Unit | LoopReturn _ | EndEnterLoop _ | EndContinue _ ->
          (* For why we can't get [Unit], see the comments inside {!eval_loop_concrete}.
             For [EndEnterLoop] and [EndContinue]: we don't support nested loops for now.
          *)
          [%craise] span "Unreachable"
      | Return ->
          [%ltrace "cf_loop: Return"];
          (* Should we consume the return value and pop the frame?
           * If we check in [Interpreter] that the loop abstraction we end is
           * indeed the correct one, I think it is sound to under-approximate here
           * (and it shouldn't make any difference).
           *)
          List.iter
            (fun rg_id ->
              (* Lookup the input abstraction - we use the fact that the
                 abstractions should have been introduced in a specific
                 order (and we check that it is indeed the case) *)
              let abs_id = AbstractionId.of_int (RegionGroupId.to_int rg_id) in
              (* By default, the [SynthInput] abs can't end *)
              let ctx = ctx_set_abs_can_end span ctx abs_id true in
              [%sanity_check] span
                (let abs = ctx_lookup_abs ctx abs_id in
                 abs.kind = SynthInput rg_id);
              (* End this abstraction *)
              let ctx = end_abstraction_no_synth config span abs_id ctx in
              (* Explore the context, and check which abstractions are not there anymore *)
              let ids, _ = compute_ctx_ids ctx in
              let ended_ids = AbstractionId.Set.diff !fp_aids ids.aids in
              add_ended_aids rg_id ended_ids)
            ctx.region_groups
    in
    List.iter end_at_return (fst (eval_loop_body fp));

    (* Check that the sets of abstractions we need to end per region group are
       pairwise disjoint *)
    let aids_union = ref AbstractionId.Set.empty in
    let _ =
      RegionGroupId.Map.iter
        (fun _ ids ->
          [%cassert] span
            (AbstractionId.Set.disjoint !aids_union ids)
            "The sets of abstractions we need to end per region group are not \
             pairwise disjoint";
          aids_union := AbstractionId.Set.union ids !aids_union)
        !fp_ended_aids
    in
    [%ltrace
      "- aids_union: "
      ^ AbstractionId.Set.to_string None !aids_union
      ^ "\n" ^ "- fp_aids: "
      ^ AbstractionId.Set.to_string None !fp_aids];

    (* If we generate a translation, we check that all the regions need to end
       - this is not necessary per se, but if it doesn't happen it is bizarre and worth investigating...
       We need this check for now for technical reasons to make the translation work.
       If we only borrow-check, we can ignore this.
    *)
    [%sanity_check] span
      (!Config.borrow_check || AbstractionId.Set.equal !aids_union !fp_aids);

    (* Merge the abstractions which need to be merged, and compute the map from
       region id to abstraction id *)
    let fp = ref fp in
    let rg_to_abs = ref RegionGroupId.Map.empty in
    (* List the ids of all the abstractions in the context, in the order in
       which they appear (this is important to preserve some structure:
       we will explore them in this order) *)
    let all_abs_ids =
      List.filter_map
        (function
          | EAbs abs -> Some abs.abs_id
          | _ -> None)
        (* TODO: we may want to use a different order, for instance the order
           in which the regions were ended. *)
        (List.rev !fp.env)
    in
    let _ =
      RegionGroupId.Map.iter
        (fun rg_id ids ->
          (* Make sure we explore the ids in the order in which they appear
             in the context *)
          let ids =
            List.filter (fun id -> AbstractionId.Set.mem id ids) all_abs_ids
          in
          (* Retrieve the first id of the group *)
          match ids with
          | [] ->
              (* We *can* get there, if the loop doesn't touch the borrowed
                 values.
                 For instance:
                 {[
                   pub fn iter_slice(a: &mut [u8]) {
                       let len = a.len();
                       let mut i = 0;
                       while i < len {
                           i += 1;
                       }
                   }
                 ]}
              *)
              [%ltrace
                "No loop region to end for the region group "
                ^ RegionGroupId.to_string rg_id];
              ()
          | id0 :: ids ->
              let id0 = ref id0 in
              (* Add the proper region group into the abstraction *)
              let abs_kind : abs_kind =
                Loop (loop_id, Some rg_id, LoopSynthInput)
              in
              let abs = ctx_lookup_abs !fp !id0 in
              let abs = { abs with kind = abs_kind } in
              let fp', _ = ctx_subst_abs span !fp !id0 abs in
              fp := fp';
              (* Merge all the abstractions into this one *)
              List.iter
                (fun id ->
                  try
                    [%ltrace
                      "merge FP abstraction: " ^ AbstractionId.to_string id
                      ^ " into "
                      ^ AbstractionId.to_string !id0];
                    (* Note that we merge *into* [id0] *)
                    let fp', id0' =
                      merge_into_first_abstraction span loop_id abs_kind
                        ~can_end:false ~with_abs_conts:false !fp !id0 id
                    in
                    fp := fp';
                    id0 := id0';
                    ()
                  with ValueMatchFailure _ -> [%craise] span "Unexpected")
                ids;
              (* Register the mapping *)
              rg_to_abs := RegionGroupId.Map.add_strict rg_id !id0 !rg_to_abs)
        !fp_ended_aids
    in
    let rg_to_abs = !rg_to_abs in

    (* Reorder the fresh abstractions in the fixed-point *)
    let fp = reorder_fresh_abs span false (Option.get !fixed_ids).aids !fp in

    (* Update the abstraction's [can_end] field and their kinds.

       Note that if [remove_rg_id] is [true], we set the region id to [None]
       and set the abstractions as endable: this is so that we can check that
       we have a fixed point (so far in the fixed point the loop abstractions had
       no region group, and we set them as endable just above).

       If [remove_rg_id] is [false], we simply set the abstractions as non-endable
       **when generating a pure translation** to freeze them (we will use the
       fixed point as starting point for the symbolic execution of the loop body,
       and we have to make sure the input abstractions are frozen).
       If we are simply borrow-checking the program, we can set the abstraction
       as endable.
    *)
    let update_loop_abstractions (remove_rg_id : bool) =
      object
        inherit [_] map_eval_ctx

        method! visit_abs _ abs =
          match abs.kind with
          | Loop (loop_id', _, kind) ->
              [%sanity_check] span (loop_id' = loop_id);
              [%sanity_check] span (kind = LoopSynthInput);
              let kind : abs_kind =
                if remove_rg_id then Loop (loop_id, None, LoopSynthInput)
                else abs.kind
              in
              (* If we borrow check we can always set the abstraction as
                 endable. If we generate a pure translation we have a few
                 more constraints. *)
              let can_end =
                if !Config.borrow_check then true else remove_rg_id
              in
              { abs with can_end; kind }
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
      [%ltrace
        "fixed point after matching with the function region groups:\n"
        ^ eval_ctx_to_string ~span:(Some span) ~filter:false fp_test];
      compute_fixed_point fp_test 1 1
    in

    (* Return *)
    (fp, rg_to_abs)
  in
  let fixed_ids = compute_fixed_ids [ fp ] in

  (* Return *)
  (fp, fixed_ids, rg_to_abs)

let compute_fixed_point_id_correspondance (span : Meta.span)
    (fixed_ids : ids_sets) (src_ctx : eval_ctx) (tgt_ctx : eval_ctx) :
    borrow_loan_corresp =
  [%ltrace
    "\n- fixed_ids:\n" ^ show_ids_sets fixed_ids ^ "\n\n- src_ctx:\n"
    ^ eval_ctx_to_string ~span:(Some span) src_ctx
    ^ "\n\n- tgt_ctx:\n"
    ^ eval_ctx_to_string ~span:(Some span) tgt_ctx
    ^ "\n"];

  let filt_src_env, _, _ = ctx_split_fixed_new span fixed_ids src_ctx in
  let filt_src_ctx = { src_ctx with env = filt_src_env } in
  let filt_tgt_env, new_absl, _ = ctx_split_fixed_new span fixed_ids tgt_ctx in
  let filt_tgt_ctx = { tgt_ctx with env = filt_tgt_env } in

  [%ltrace
    "\n- fixed_ids:\n" ^ show_ids_sets fixed_ids ^ "\n\n- filt_src_ctx:\n"
    ^ eval_ctx_to_string ~span:(Some span) filt_src_ctx
    ^ "\n\n- filt_tgt_ctx:\n"
    ^ eval_ctx_to_string ~span:(Some span) filt_tgt_ctx
    ^ "\n"];

  (* Match the source context and the filtered target context *)
  let maps =
    let fixed_ids = ids_sets_empty_borrows_loans fixed_ids in
    let open InterpreterBorrowsCore in
    let lookup_shared_loan lid ctx : tvalue =
      match snd (lookup_loan span ek_all lid ctx) with
      | Concrete (VSharedLoan (_, v)) -> v
      | Abstract (ASharedLoan (pm, _, v, _)) ->
          [%sanity_check] span (pm = PNone);
          v
      | _ -> [%craise] span "Unreachable"
    in
    let lookup_in_tgt id = lookup_shared_loan id tgt_ctx in
    let lookup_in_src id = lookup_shared_loan id src_ctx in
    Option.get
      (match_ctxs span ~check_equiv:false fixed_ids lookup_in_tgt lookup_in_src
         filt_tgt_ctx filt_src_ctx)
  in

  [%ltrace "\n- tgt_to_src_maps:\n" ^ ids_maps_to_string src_ctx maps ^ "\n"];

  let src_to_tgt_borrow_map =
    BorrowId.Map.of_list
      (List.map
         (fun (x, y) -> (y, x))
         (BorrowId.InjSubst.bindings maps.borrow_id_map))
  in
  let src_to_tgt_sid_map =
    SymbolicValueId.Map.of_list
      (List.filter_map
         (fun ((sid, v) : _ * tvalue) ->
           match v.value with
           | VSymbolic v -> Some (v.sv_id, sid)
           | _ -> None)
         (SymbolicValueId.Map.bindings maps.sid_to_value_map))
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
        BorrowId.Set.map
          (fun x -> BorrowId.InjSubst.find x maps.borrow_id_map)
          ids.loan_ids
      in
      (* Check that the loans and borrows are related *)
      [%sanity_check] span (BorrowId.Set.equal ids.borrow_ids loan_ids))
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
  let tgt_borrow_to_loan = ref BorrowId.InjSubst.empty in
  let tgt_borrow_to_loan_proj = ref SymbolicValueId.InjSubst.empty in
  let visit_tgt =
    object
      inherit [_] iter_abs

      method! visit_borrow_id _ id =
        (* Find the target borrow *)
        let tgt_borrow_id = BorrowId.Map.find id src_to_tgt_borrow_map in
        (* Update the map *)
        tgt_borrow_to_loan :=
          BorrowId.InjSubst.add id tgt_borrow_id !tgt_borrow_to_loan

      method! visit_aproj _ proj =
        match proj with
        | AProjLoans { proj = _; consumed; borrows } ->
            [%sanity_check] span (consumed = []);
            [%sanity_check] span (borrows = []);
            ()
        | AProjBorrows { proj; loans } ->
            [%sanity_check] span (loans = []);
            (* Find the target borrow *)
            let tgt_borrow_id =
              SymbolicValueId.Map.find proj.sv_id src_to_tgt_sid_map
            in
            (* Update the map *)
            tgt_borrow_to_loan_proj :=
              SymbolicValueId.InjSubst.add proj.sv_id tgt_borrow_id
                !tgt_borrow_to_loan_proj
        | AEndedProjBorrows _ | AEndedProjLoans _ | AEmpty ->
            (* We shouldn't get there *)
            [%internal_error] span
    end
  in
  List.iter (visit_tgt#visit_abs ()) new_absl;

  (* Compute the map from loan to borrows *)
  let tgt_loan_to_borrow =
    BorrowId.InjSubst.of_list
      (List.map
         (fun (x, y) -> (y, x))
         (BorrowId.InjSubst.bindings !tgt_borrow_to_loan))
  in

  let tgt_loan_to_borrow_proj =
    SymbolicValueId.InjSubst.of_list
      (List.map
         (fun (x, y) -> (y, x))
         (SymbolicValueId.InjSubst.bindings !tgt_borrow_to_loan_proj))
  in

  (* Return *)
  {
    borrow_to_loan_id_map = !tgt_borrow_to_loan;
    loan_to_borrow_id_map = tgt_loan_to_borrow;
    borrow_to_loan_proj_map = !tgt_borrow_to_loan_proj;
    loan_to_borrow_proj_map = tgt_loan_to_borrow_proj;
  }

let compute_fp_ctx_symbolic_values (span : Meta.span) (ctx : eval_ctx)
    (fp_ctx : eval_ctx) : SymbolicValueId.Set.t * symbolic_value list =
  let old_ids, _ = compute_ctx_ids ctx in
  let fp_ids, fp_ids_maps = compute_ctx_ids fp_ctx in
  let fresh_sids = SymbolicValueId.Set.diff fp_ids.sids old_ids.sids in

  (* Compute the set of symbolic values which appear inside *fixed* abstractions.
     There are two kinds of values:
     - shared symbolic values (appearing in shared loans): because we introduce
       fresh abstractions and reborrows with {!prepare_ashared_loans}, those
       values are never accessed directly inside the loop iterations: we can
       ignore them (and should, because otherwise it leads to a very ugly
       translation with duplicated, unused values)
     - projections over symbolic values.
       TODO: actually it may happen that a projector inside a fixed abstraction
       gets expanded. We need to update the way we compute joins and check
       whether two contexts are equivalent to make it more general.
  *)
  let sids_in_fixed_abs =
    let fixed_absl =
      List.filter
        (fun (ee : env_elem) ->
          match ee with
          | EBinding _ | EFrame -> false
          | EAbs abs -> AbstractionId.Set.mem abs.abs_id old_ids.aids)
        ctx.env
    in

    (* Rem.: as we greedily expand the symbolic values containing borrows, and
       in particular the (mutable/shared) borrows, we could simply list the
       symbolic values appearing in the abstractions: those are necessarily
       shared values. We prefer to be more general, in prevision of later
       changes.
    *)
    let sids = ref SymbolicValueId.Set.empty in
    let visitor =
      object (self)
        inherit [_] iter_env

        method! visit_ASharedLoan register _ _ sv child_av =
          self#visit_tvalue true sv;
          self#visit_tavalue register child_av

        method! visit_AProjLoans register proj =
          let { proj = { sv_id; proj_ty }; consumed; borrows } : aproj_loans =
            proj
          in
          self#visit_symbolic_value_id true sv_id;
          self#visit_ty register proj_ty;
          [%sanity_check] span (consumed = []);
          [%sanity_check] span (borrows = [])
        (*self#visit_list
            (fun register ((s, p) : mconsumed_symb * _) ->
              self#visit_msymbolic_value_id register s.sv_id;
              self#visit_aproj register p)
            register consumed;
          self#visit_list
            (fun register ((s, p) : mconsumed_symb * _) ->
              self#visit_msymbolic_value_id register s.sv_id;
              self#visit_aproj register p)
            register borrows*)

        method! visit_symbolic_value_id register sid =
          if register then sids := SymbolicValueId.Set.add sid !sids
      end
    in
    visitor#visit_env false fixed_absl;
    !sids
  in

  (* Remove the shared symbolic values present in the fixed abstractions -
     see comments for [shared_sids_in_fixed_abs]. *)
  let sids_to_values = fp_ids_maps.sids_to_values in

  (* Also remove the symbolic values which appear inside of projectors in
     fixed abstractions - those are "fixed" and not modified between iterations
     of the loop, *)
  [%ltrace
    "- sids_in_fixed_abs:"
    ^ SymbolicValueId.Set.show sids_in_fixed_abs
    ^ "\n- all_sids_to_values: "
    ^ SymbolicValueId.Map.show (symbolic_value_to_string ctx) sids_to_values];

  let sids_to_values =
    SymbolicValueId.Map.filter
      (fun sid _ -> not (SymbolicValueId.Set.mem sid sids_in_fixed_abs))
      sids_to_values
  in

  (* List the input symbolic values in proper order.

     We explore the environment, and order the symbolic values in the order
     in which they are found - this way, the symbolic values found in a
     variable [x] which appears before [y] are listed first, for instance.
  *)
  let input_svalues =
    let found_sids = ref SymbolicValueId.Set.empty in
    let ordered_sids = ref [] in

    let visitor =
      object (self)
        inherit [_] iter_env

        (** We lookup the shared values *)
        method! visit_VSharedBorrow env bid _ =
          let open InterpreterBorrowsCore in
          let v =
            match snd (lookup_loan span ek_all bid fp_ctx) with
            | Concrete (VSharedLoan (_, v)) -> v
            | Abstract (ASharedLoan (pm, _, v, _)) ->
                [%sanity_check] span (pm = PNone);
                v
            | _ -> [%craise] span "Unreachable"
          in
          self#visit_tvalue env v

        method! visit_symbolic_value_id _ id =
          if not (SymbolicValueId.Set.mem id !found_sids) then (
            found_sids := SymbolicValueId.Set.add id !found_sids;
            ordered_sids := id :: !ordered_sids)
      end
    in

    List.iter (visitor#visit_env_elem ()) (List.rev fp_ctx.env);

    List.filter_map
      (fun id -> SymbolicValueId.Map.find_opt id sids_to_values)
      (List.rev !ordered_sids)
  in

  [%ltrace
    "- src context:\n"
    ^ eval_ctx_to_string ~span:(Some span) ~filter:false ctx
    ^ "\n- fixed point:\n"
    ^ eval_ctx_to_string ~span:(Some span) ~filter:false fp_ctx
    ^ "\n- fresh_sids: "
    ^ SymbolicValueId.Set.show fresh_sids
    ^ "\n- input_svalues: "
    ^ Print.list_to_string (symbolic_value_to_string ctx) input_svalues
    ^ "\n"];

  (fresh_sids, input_svalues)
