open Types
open Values
open Cps
open Contexts
open InterpreterUtils
open InterpreterBorrows
open InterpreterAbs
open InterpreterLoopsCore
open InterpreterReduceCollapse
open InterpreterLoopsMatchCtxs

(** The local logger *)
let log = Logging.loops_join_ctxs_log

let join_ctxs (span : Meta.span) (loop_id : LoopId.id) (fixed_ids : ids_sets)
    ~(with_abs_conts : bool) (ctx0 : eval_ctx) (ctx1 : eval_ctx) : ctx_or_update
    =
  (* Debug *)
  [%ltrace
    "\n- fixed_ids:\n" ^ show_ids_sets fixed_ids ^ "\n\n- ctx0:\n"
    ^ eval_ctx_to_string ~span:(Some span) ~filter:true ctx0
    ^ "\n\n- ctx1:\n"
    ^ eval_ctx_to_string ~span:(Some span) ~filter:true ctx1
    ^ "\n"];

  let env0 = List.rev ctx0.env in
  let env1 = List.rev ctx1.env in
  let nabs = ref [] in

  (* Explore the environments. *)
  let join_suffixes (env0 : env) (env1 : env) : env =
    (* Debug *)
    [%ldebug
      "join_suffixes:\n\n- fixed_ids:\n" ^ show_ids_sets fixed_ids
      ^ "\n\n- ctx0:\n"
      ^ eval_ctx_to_string ~span:(Some span) ~filter:false
          { ctx0 with env = List.rev env0 }
      ^ "\n\n- ctx1:\n"
      ^ eval_ctx_to_string ~span:(Some span) ~filter:false
          { ctx1 with env = List.rev env1 }
      ^ "\n"];

    (* Sanity check: there are no values/abstractions which should be in the prefix *)
    let check_valid (ee : env_elem) : unit =
      match ee with
      | EBinding (BVar _, _) ->
          (* Variables are necessarily in the prefix *)
          [%craise] span "Unreachable"
      | EBinding (BDummy did, _) ->
          [%sanity_check] span (not (DummyVarId.Set.mem did fixed_ids.dids))
      | EAbs abs ->
          [%sanity_check] span
            (not (AbstractionId.Set.mem abs.abs_id fixed_ids.aids))
      | EFrame ->
          (* This should have been eliminated *)
          [%craise] span "Unreachable"
    in

    (* Add projection marker to all abstractions in the left and right environments *)
    let add_marker (pm : proj_marker) (ee : env_elem) : env_elem =
      match ee with
      | EAbs abs -> EAbs (abs_add_marker span ctx0 pm abs)
      | x -> x
    in

    let env0 = List.map (add_marker PLeft) env0 in
    let env1 = List.map (add_marker PRight) env1 in

    List.iter check_valid env0;
    List.iter check_valid env1;
    (* Concatenate the suffixes and append the abstractions introduced while
       joining the prefixes *)
    let absl = List.map (fun abs -> EAbs abs) (List.rev !nabs) in
    List.concat [ env0; env1; absl ]
  in

  let symbolic_to_value = ref SymbolicValueId.Map.empty in
  let module S : MatchJoinState = struct
    let span = span
    let loop_id = loop_id
    let nabs = nabs
    let with_abs_conts = with_abs_conts
    let symbolic_to_value = symbolic_to_value
  end in
  let module JM = MakeJoinMatcher (S) in
  let module M = MakeMatcher (JM) in
  (* Rem.: this function raises exceptions *)
  let rec join_prefixes (env0 : env) (env1 : env) : env =
    match (env0, env1) with
    | ( (EBinding (BDummy b0, v0) as var0) :: env0',
        (EBinding (BDummy b1, v1) as var1) :: env1' ) ->
        (* Debug *)
        [%ldebug
          "join_prefixes: BDummys:\n\n- fixed_ids:\n" ^ "\n"
          ^ show_ids_sets fixed_ids ^ "\n\n- value0:\n"
          ^ env_elem_to_string span ctx0 var0
          ^ "\n\n- value1:\n"
          ^ env_elem_to_string span ctx1 var1
          ^ "\n"];

        (* Two cases: the dummy value is an old value, in which case the bindings
           must be the same and we must join their values. Otherwise, it means we
           are not in the prefix anymore *)
        if DummyVarId.Set.mem b0 fixed_ids.dids then (
          (* Still in the prefix: match the values *)
          [%sanity_check] span (b0 = b1);
          let b = b0 in
          let v = M.match_tvalues ctx0 ctx1 v0 v1 in
          let var = EBinding (BDummy b, v) in
          (* Continue *)
          var :: join_prefixes env0' env1')
        else (* Not in the prefix anymore *)
          join_suffixes env0 env1
    | ( (EBinding (BVar b0, v0) as var0) :: env0',
        (EBinding (BVar b1, v1) as var1) :: env1' ) ->
        (* Debug *)
        [%ldebug
          "join_prefixes: BVars:\n\n- fixed_ids:\n" ^ "\n"
          ^ show_ids_sets fixed_ids ^ "\n\n- value0:\n"
          ^ env_elem_to_string span ctx0 var0
          ^ "\n\n- value1:\n"
          ^ env_elem_to_string span ctx1 var1
          ^ "\n"];

        (* Variable bindings *must* be in the prefix and consequently their
           ids must be the same *)
        [%sanity_check] span (b0 = b1);
        (* Match the values *)
        let b = b0 in
        let v = M.match_tvalues ctx0 ctx1 v0 v1 in
        let var = EBinding (BVar b, v) in
        (* Continue *)
        var :: join_prefixes env0' env1'
    | (EAbs abs0 as abs) :: env0', EAbs abs1 :: env1' ->
        (* Debug *)
        [%ldebug
          "join_prefixes: Abs:\n\n- fixed_ids:\n" ^ "\n"
          ^ show_ids_sets fixed_ids ^ "\n\n- abs0:\n"
          ^ abs_to_string span ctx0 abs0
          ^ "\n\n- abs1:\n"
          ^ abs_to_string span ctx1 abs1
          ^ "\n"];

        (* Same as for the dummy values: there are two cases *)
        if AbstractionId.Set.mem abs0.abs_id fixed_ids.aids then (
          (* Still in the prefix: the abstractions must be the same *)
          [%sanity_check] span (abs0 = abs1);
          (* Continue *)
          abs :: join_prefixes env0' env1')
        else (* Not in the prefix anymore *)
          join_suffixes env0 env1
    | _ ->
        (* The elements don't match: we are not in the prefix anymore *)
        join_suffixes env0 env1
  in

  try
    (* Remove the frame delimiter (the first element of an environment is a frame delimiter) *)
    let env0, env1 =
      match (env0, env1) with
      | EFrame :: env0, EFrame :: env1 -> (env0, env1)
      | _ -> [%craise] span "Unreachable"
    in

    [%ldebug
      "- env0:\n"
      ^ env_to_string span ctx0 (List.rev env0) ~filter:false
      ^ "\n\n- env1:\n"
      ^ env_to_string span ctx1 (List.rev env1) ~filter:false
      ^ "\n"];

    let env = List.rev (EFrame :: join_prefixes env0 env1) in

    (* Construct the joined context - of course, the type, fun, etc. contexts
     * should be the same in the two contexts *)
    let {
      type_ctx;
      crate;
      fun_ctx;
      region_groups;
      type_vars;
      const_generic_vars;
      const_generic_vars_map;
      env = _;
      ended_regions = ended_regions0;
    } =
      ctx0
    in
    let {
      type_ctx = _;
      crate = _;
      fun_ctx = _;
      region_groups = _;
      type_vars = _;
      const_generic_vars = _;
      const_generic_vars_map = _;
      env = _;
      ended_regions = ended_regions1;
    } =
      ctx1
    in
    let ended_regions = RegionId.Set.union ended_regions0 ended_regions1 in
    let ctx : eval_ctx =
      {
        crate;
        type_ctx;
        fun_ctx;
        region_groups;
        type_vars;
        const_generic_vars;
        const_generic_vars_map;
        env;
        ended_regions;
      }
    in
    let join_info : ctx_join_info =
      { symbolic_to_value = !symbolic_to_value }
    in
    Ok (ctx, join_info)
  with ValueMatchFailure e -> Error e

(** Destructure all the new abstractions *)
let destructure_new_abs (span : Meta.span) (loop_id : LoopId.id)
    (old_abs_ids : AbstractionId.Set.t) (ctx : eval_ctx) : eval_ctx =
  [%ltrace "ctx:\n\n" ^ eval_ctx_to_string ctx];
  let abs_kind : abs_kind = Loop (loop_id, None) in
  let can_end = true in
  let destructure_shared_values = true in
  let is_fresh_abs_id (id : AbstractionId.id) : bool =
    not (AbstractionId.Set.mem id old_abs_ids)
  in
  let env =
    env_map_abs
      (fun abs ->
        if is_fresh_abs_id abs.abs_id then
          let abs =
            destructure_abs span abs_kind can_end destructure_shared_values ctx
              abs
          in
          abs
        else abs)
      ctx.env
  in
  let ctx = { ctx with env } in
  [%ltrace "resulting ctx:\n\n" ^ eval_ctx_to_string ctx];
  Invariants.check_invariants span ctx;
  ctx

(** Refresh the ids of the fresh abstractions.

    We do this because {!prepare_ashared_loans} introduces some non-fixed
    abstractions in contexts which are later joined: we have to make sure two
    contexts we join don't have non-fixed abstractions with the same ids. *)
let refresh_abs (old_abs : AbstractionId.Set.t) (ctx : eval_ctx) : eval_ctx =
  let ids, _ = compute_ctx_ids ctx in
  let abs_to_refresh = AbstractionId.Set.diff ids.aids old_abs in
  let aids_subst =
    List.map
      (fun id -> (id, fresh_abstraction_id ()))
      (AbstractionId.Set.elements abs_to_refresh)
  in
  let aids_subst = AbstractionId.Map.of_list aids_subst in
  let asubst id =
    match AbstractionId.Map.find_opt id aids_subst with
    | None -> id
    | Some id -> id
  in
  let env =
    Substitute.env_subst_ids { Substitute.empty_id_subst with asubst } ctx.env
  in
  { ctx with env }

let loop_join_origin_with_continue_ctxs (config : config) (span : Meta.span)
    (loop_id : LoopId.id) (fixed_ids : ids_sets) (old_ctx : eval_ctx)
    (ctxl : eval_ctx list) : (eval_ctx * eval_ctx list) * eval_ctx =
  let with_abs_conts = false in
  (* # Join with the new contexts, one by one

     For every context, we repeteadly attempt to join it with the current
     result of the join: if we fail (because we need to end loans for instance),
     we update the context and retry.
  *)
  let joined_ctx = ref old_ctx in
  let rec join_one_aux (ctx : eval_ctx) : eval_ctx =
    match join_ctxs span loop_id fixed_ids ~with_abs_conts !joined_ctx ctx with
    | Ok (nctx, _) ->
        joined_ctx := nctx;
        ctx
    | Error err ->
        let ctx =
          (* TODO: simplify *)
          match err with
          | LoanInRight bid ->
              InterpreterBorrows.end_loan_no_synth config span bid ctx
          | LoansInRight bids ->
              InterpreterBorrows.end_loans_no_synth config span bids ctx
          | LoanInLeft bid ->
              joined_ctx :=
                InterpreterBorrows.end_loan_no_synth config span bid !joined_ctx;
              ctx
          | LoansInLeft bids ->
              joined_ctx :=
                InterpreterBorrows.end_loans_no_synth config span bids
                  !joined_ctx;
              ctx
          | AbsInRight _ | AbsInLeft _ -> [%craise] span "Unexpected"
        in
        join_one_aux ctx
  in
  let join_one (ctx : eval_ctx) : eval_ctx =
    [%ltrace
      "join_one: initial ctx:\n" ^ eval_ctx_to_string ~span:(Some span) ctx];

    (* Simplify the dummy values, by removing as many as we can -
       we ignore the synthesis continuation *)
    let ctx, _ =
      simplify_dummy_values_useless_abs config span fixed_ids.aids ctx
    in
    [%ltrace
      "join_one: after simplify_dummy_values_useless_abs (fixed_ids.abs_ids = "
      ^ AbstractionId.Set.to_string None fixed_ids.aids
      ^ "):\n"
      ^ eval_ctx_to_string ~span:(Some span) ctx];

    (* Destructure the abstractions introduced in the new context *)
    let ctx = destructure_new_abs span loop_id fixed_ids.aids ctx in
    [%ltrace
      "join_one: after destructure:\n"
      ^ eval_ctx_to_string ~span:(Some span) ctx];

    (* Reduce the context we want to add to the join *)
    let ctx =
      reduce_ctx config span ~with_abs_conts:false loop_id fixed_ids ctx
    in
    [%ltrace
      "join_one: after reduce:\n" ^ eval_ctx_to_string ~span:(Some span) ctx];
    (* Sanity check *)
    if !Config.sanity_checks then Invariants.check_invariants span ctx;

    (* Refresh the fresh abstractions *)
    let ctx = refresh_abs fixed_ids.aids ctx in
    (* Sanity check *)
    if !Config.sanity_checks then Invariants.check_invariants span ctx;

    (* Join the two contexts  *)
    let ctx1 = join_one_aux ctx in
    [%ltrace
      "join_one: after join:\n" ^ eval_ctx_to_string ~span:(Some span) ctx1];

    (* Collapse to eliminate the markers *)
    joined_ctx :=
      collapse_ctx_with_merge config span loop_id fixed_ids ~with_abs_conts
        !joined_ctx;
    [%ltrace
      "join_one: after join-collapse:\n"
      ^ eval_ctx_to_string ~span:(Some span) !joined_ctx];
    (* Sanity check *)
    if !Config.sanity_checks then Invariants.check_invariants span !joined_ctx;

    (* Reduce again to reach a fixed point *)
    joined_ctx :=
      reduce_ctx config span ~with_abs_conts:false loop_id fixed_ids !joined_ctx;
    [%ltrace
      "join_one: after last reduce:\n"
      ^ eval_ctx_to_string ~span:(Some span) !joined_ctx];

    (* Sanity check *)
    if !Config.sanity_checks then Invariants.check_invariants span !joined_ctx;
    (* Return *)
    ctx1
  in

  let ctxl = List.map join_one ctxl in

  (* # Return *)
  ((old_ctx, ctxl), !joined_ctx)

let loop_join_break_ctxs (config : config) (span : Meta.span)
    (loop_id : LoopId.id) (fixed_ids : ids_sets) (ctxl : eval_ctx list) :
    eval_ctx =
  (* Simplify the contexts *)
  let with_abs_conts = false in
  let prepare_ctx (ctx : eval_ctx) : eval_ctx =
    [%ltrace
      "join_one: initial ctx:\n" ^ eval_ctx_to_string ~span:(Some span) ctx];

    (* Simplify the dummy values, by removing as many as we can -
       we ignore the synthesis continuation *)
    let ctx, _ =
      simplify_dummy_values_useless_abs config span fixed_ids.aids ctx
    in
    [%ltrace
      "join_one: after simplify_dummy_values_useless_abs (fixed_ids.abs_ids = "
      ^ AbstractionId.Set.to_string None fixed_ids.aids
      ^ "):\n"
      ^ eval_ctx_to_string ~span:(Some span) ctx];

    (* Destructure the abstractions introduced in the new context *)
    let ctx = destructure_new_abs span loop_id fixed_ids.aids ctx in
    [%ltrace
      "join_one: after destructure:\n"
      ^ eval_ctx_to_string ~span:(Some span) ctx];

    (* Reduce the context we want to add to the join *)
    let ctx =
      reduce_ctx config span ~with_abs_conts:false loop_id fixed_ids ctx
    in
    [%ltrace
      "join_one: after reduce:\n" ^ eval_ctx_to_string ~span:(Some span) ctx];
    (* Sanity check *)
    if !Config.sanity_checks then Invariants.check_invariants span ctx;

    (* Refresh the fresh abstractions *)
    let ctx = refresh_abs fixed_ids.aids ctx in
    (* Sanity check *)
    if !Config.sanity_checks then Invariants.check_invariants span ctx;

    ctx
  in
  let ctxl = List.map prepare_ctx ctxl in

  match ctxl with
  | [] -> [%internal_error] span
  | [ ctx ] ->
      (* Special case: simply remove the continuation expressions from the fresh abs *)
      let update (e : env_elem) : env_elem =
        match (e : env_elem) with
        | EAbs abs ->
            if AbstractionId.Set.mem abs.abs_id fixed_ids.aids then e
            else EAbs { abs with cont = None; kind = Loop (loop_id, None) }
        | EBinding _ | EFrame -> e
      in
      { ctx with env = List.map update ctx.env }
  | ctx :: ctxl ->
      let joined_ctx = ref ctx in

      (* # Join the contexts, one by one.

          For every context, we repeteadly attempt to join it with the current
          result of the join: if we fail (because we need to end loans for instance),
          we update the context and retry.
       *)
      let rec join_one_aux (ctx : eval_ctx) =
        match
          join_ctxs span loop_id fixed_ids ~with_abs_conts !joined_ctx ctx
        with
        | Ok (nctx, _) ->
            joined_ctx := nctx;
            ctx
        | Error err ->
            let ctx =
              (* TODO: simplify *)
              match err with
              | LoanInRight bid ->
                  InterpreterBorrows.end_loan_no_synth config span bid ctx
              | LoansInRight bids ->
                  InterpreterBorrows.end_loans_no_synth config span bids ctx
              | LoanInLeft bid ->
                  joined_ctx :=
                    InterpreterBorrows.end_loan_no_synth config span bid
                      !joined_ctx;
                  ctx
              | LoansInLeft bids ->
                  joined_ctx :=
                    InterpreterBorrows.end_loans_no_synth config span bids
                      !joined_ctx;
                  ctx
              | AbsInRight _ | AbsInLeft _ -> [%craise] span "Unexpected"
            in
            join_one_aux ctx
      in
      let join_one (ctx : eval_ctx) =
        (* Join the two contexts  *)
        let ctx1 = join_one_aux ctx in
        [%ltrace
          "join_one: after join:\n" ^ eval_ctx_to_string ~span:(Some span) ctx1];

        (* Collapse to eliminate the markers *)
        joined_ctx :=
          collapse_ctx_with_merge config span loop_id fixed_ids ~with_abs_conts
            !joined_ctx;
        [%ltrace
          "join_one: after join-collapse:\n"
          ^ eval_ctx_to_string ~span:(Some span) !joined_ctx];
        (* Sanity check *)
        if !Config.sanity_checks then
          Invariants.check_invariants span !joined_ctx;

        (* Reduce again to reach a fixed point *)
        joined_ctx :=
          reduce_ctx config span ~with_abs_conts:false loop_id fixed_ids
            !joined_ctx;
        [%ltrace
          "join_one: after last reduce:\n"
          ^ eval_ctx_to_string ~span:(Some span) !joined_ctx];

        (* Sanity check *)
        if !Config.sanity_checks then
          Invariants.check_invariants span !joined_ctx
      in
      List.iter join_one ctxl;

      (* Update the fresh region abstractions *)
      !joined_ctx

let loop_match_ctx_with_target (config : config) (span : Meta.span)
    (loop_id : LoopId.id) (fp_input_svalues : SymbolicValueId.id list)
    (fixed_ids : ids_sets) (src_ctx : eval_ctx) (tgt_ctx : eval_ctx) :
    (eval_ctx
    * eval_ctx
    * tvalue SymbolicValueId.Map.t
    * abs AbstractionId.Map.t)
    * (SymbolicAst.expr -> SymbolicAst.expr) =
  (* Debug *)
  [%ltrace
    "- fixed_ids: " ^ show_ids_sets fixed_ids ^ "\n" ^ "\n- src_ctx: "
    ^ eval_ctx_to_string src_ctx ^ "\n- tgt_ctx: " ^ eval_ctx_to_string tgt_ctx];

  (* Simplify the target context *)
  let tgt_ctx, cc =
    simplify_dummy_values_useless_abs config span fixed_ids.aids tgt_ctx
  in
  [%ltrace
    "- tgt_ctx after simplify_dummy_values_useless_abs:\n"
    ^ eval_ctx_to_string tgt_ctx];

  (* Reduce the context *)
  let tgt_ctx =
    reduce_ctx config span ~with_abs_conts:true loop_id fixed_ids tgt_ctx
  in
  [%ltrace "- tgt_ctx after reduce_ctx:\n" ^ eval_ctx_to_string tgt_ctx];

  (* We first reorganize [tgt_ctx] so that we can match [src_ctx] with it (by
     ending loans for instance - remember that the [src_ctx] is the fixed point
     context, which results from joins during which we ended the loans which
     were introduced during the loop iterations)
  *)
  let tgt_ctx, cc =
    comp cc
      (prepare_loop_match_ctx_with_target config span loop_id fixed_ids src_ctx
         tgt_ctx)
  in
  [%ltrace
    "Finished preparing the match:" ^ "\n- fixed_ids: "
    ^ show_ids_sets fixed_ids ^ "\n" ^ "\n- src_ctx: "
    ^ eval_ctx_to_string src_ctx ^ "\n- tgt_ctx: " ^ eval_ctx_to_string tgt_ctx];

  (* TODO: preparing the match might have moved some borrows to anonymous values,
     so we could call [simplify_dummy_values_useless_abs] again, but if we do so
     it would be better to call [reduce_ctx] and [prepare_loop_match_ctx_with_target]
     again (potentially within a loop). *)

  (* Join the source context with the target context *)
  let joined_ctx, join_info =
    match
      join_ctxs span loop_id fixed_ids ~with_abs_conts:true src_ctx tgt_ctx
    with
    | Ok ctx -> ctx
    | Error _ -> [%craise] span "Could not join the contexts"
  in
  [%ltrace
    "Result of the join:\n- joined_ctx:\n"
    ^ eval_ctx_to_string joined_ctx
    ^ "\n- join_info: "
    ^ SymbolicValueId.Map.to_string (Some "  ")
        (Print.pair_to_string (tvalue_to_string src_ctx)
           (tvalue_to_string src_ctx))
        join_info.symbolic_to_value];

  (* Project the context to only preserve the right part, which corresponds to the
     target *)
  let joined_ctx = project_context span fixed_ids PRight joined_ctx in
  let joined_symbolic_to_tgt_value =
    SymbolicValueId.Map.map (fun (_, x) -> x) join_info.symbolic_to_value
  in
  [%ltrace
    "After projection: joined_ctx:\n"
    ^ eval_ctx_to_string joined_ctx
    ^ "\n- joined_symbolic_to_tgt_value: "
    ^ SymbolicValueId.Map.to_string (Some "  ") (tvalue_to_string src_ctx)
        joined_symbolic_to_tgt_value];

  (* Reduce the context *)
  let joined_ctx =
    reduce_ctx config span ~with_abs_conts:true loop_id fixed_ids joined_ctx
  in
  [%ltrace
    "After reducing the context: joined_ctx:\n" ^ eval_ctx_to_string joined_ctx];

  [%ltrace
    "About to match:" ^ "\n- src_ctx:\n" ^ eval_ctx_to_string src_ctx
    ^ "\n- joined_ctx:\n"
    ^ eval_ctx_to_string joined_ctx];

  (* Check that the source context (i.e., the fixed-point context) matches
     the resulting target context. *)
  let src_to_joined_maps =
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
    let lookup_in_src id = lookup_shared_loan id src_ctx in
    let lookup_in_joined id = lookup_shared_loan id joined_ctx in
    (* Match *)
    match
      match_ctxs span ~check_equiv:false ~check_kind:false ~check_can_end:false
        fixed_ids lookup_in_src lookup_in_joined src_ctx joined_ctx
    with
    | Some ctx -> ctx
    | None -> [%craise] span "Could not match the contexts"
  in
  [%ltrace
    "The match was successful:" ^ "\n\n- src_ctx: "
    ^ eval_ctx_to_string ~span:(Some span) src_ctx
    ^ "\n\n- joined_ctx: "
    ^ eval_ctx_to_string ~span:(Some span) joined_ctx
    ^ "\n\n- fixed_ids:\n" ^ show_ids_sets fixed_ids
    ^ "\n\n- src_to_joined_maps: "
    ^ ids_maps_to_string joined_ctx src_to_joined_maps];

  (* Sanity check *)
  if !Config.sanity_checks then
    Invariants.check_borrowed_values_invariant span joined_ctx;

  (* Compute the loop input values and abstractions *)
  [%ltrace
    "About to compute the input values and abstractions:"
    ^ "\n- fp_input_svalues: "
    ^ String.concat ", " (List.map SymbolicValueId.to_string fp_input_svalues)
    ^ "\n- src_to_joined_maps:\n"
    ^ ids_maps_to_string joined_ctx src_to_joined_maps
    ^ "\n- joined_symbolic_to_tgt_value: "
    ^ SymbolicValueId.Map.to_string (Some "  ") (tvalue_to_string src_ctx)
        joined_symbolic_to_tgt_value
    ^ "\n- src_ctx:\n" ^ eval_ctx_to_string src_ctx ^ "\n- joined_ctx:\n"
    ^ eval_ctx_to_string joined_ctx];
  let input_values =
    SymbolicValueId.Map.of_list
      (List.map
         (fun sid ->
           (* We retrieve the value in two steps:
               - source to joined (which *has* to be a symbolic value)
               - joined to target *)
           let v =
             match
               SymbolicValueId.Map.find_opt sid
                 src_to_joined_maps.sid_to_value_map
             with
             | Some v -> v
             | None ->
                 [%craise] span
                   ("Could not find symbolic value @"
                   ^ SymbolicValueId.to_string sid
                   ^ " in src_to_joined_map")
           in
           let sid' = [%add_loc] symbolic_tvalue_get_id span v in
           let v =
             match
               SymbolicValueId.Map.find_opt sid' joined_symbolic_to_tgt_value
             with
             | Some v -> v
             | None ->
                 [%craise] span
                   ("Could not find symbolic value @"
                   ^ SymbolicValueId.to_string sid
                   ^ " in joined_symbolic_to_tgt_map")
           in
           (sid, v))
         fp_input_svalues)
  in
  let input_abs =
    let aid_map =
      AbstractionId.Map.of_list
        (AbstractionId.InjSubst.bindings src_to_joined_maps.aid_map)
    in
    AbstractionId.Map.filter_map
      (fun src_id joined_id ->
        if AbstractionId.Set.mem src_id fixed_ids.aids then None
        else Some (ctx_lookup_abs joined_ctx joined_id))
      aid_map
  in

  [%ltrace
    "Input values:\n"
    ^ SymbolicValueId.Map.to_string (Some "  ")
        (tvalue_to_string ~span:(Some span) src_ctx)
        input_values
    ^ "\nInput abs:\n"
    ^ AbstractionId.Map.to_string (Some "  ")
        (abs_to_string span src_ctx)
        input_abs];

  (* *)
  Invariants.check_invariants span joined_ctx;

  (* We continue with the *fixed-point* context *)
  ((src_ctx, tgt_ctx, input_values, input_abs), cc)

let loop_match_break_ctx_with_target (config : config) (span : Meta.span)
    (loop_id : LoopId.id) (fp_input_svalues : SymbolicValueId.id list)
    (fixed_ids : ids_sets) (src_ctx : eval_ctx) (tgt_ctx : eval_ctx) :
    (eval_ctx
    * eval_ctx
    * tvalue SymbolicValueId.Map.t
    * abs AbstractionId.Map.t)
    * (SymbolicAst.expr -> SymbolicAst.expr) =
  (* Debug *)
  [%ltrace
    "- fixed_ids: " ^ show_ids_sets fixed_ids ^ "\n" ^ "\n- src_ctx: "
    ^ eval_ctx_to_string src_ctx ^ "\n- tgt_ctx: " ^ eval_ctx_to_string tgt_ctx];

  (* We have to consider the possibility that the break context is not the result
     of a join (because there was a single break in the loop): in this case there
     is no point in joining the break context with the target context, we directly
     check if they are equivalent.

     TODO: is this really useful?
  *)
  let src_to_tgt_maps =
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
    let lookup_in_src id = lookup_shared_loan id src_ctx in
    let lookup_in_tgt id = lookup_shared_loan id tgt_ctx in
    (* Match *)
    match_ctxs span ~check_equiv:false ~check_kind:false ~check_can_end:false
      fixed_ids lookup_in_src lookup_in_tgt src_ctx tgt_ctx
  in

  match src_to_tgt_maps with
  | Some src_to_tgt_maps ->
      [%ltrace
        "The match was successful:" ^ "\n\n- src_ctx: "
        ^ eval_ctx_to_string ~span:(Some span) src_ctx
        ^ "\n\n- tgt_ctx: "
        ^ eval_ctx_to_string ~span:(Some span) tgt_ctx
        ^ "\n\n- fixed_ids:\n" ^ show_ids_sets fixed_ids
        ^ "\n\n- src_to_tgt_maps: "
        ^ ids_maps_to_string tgt_ctx src_to_tgt_maps];

      (* Sanity check *)
      if !Config.sanity_checks then
        Invariants.check_borrowed_values_invariant span tgt_ctx;

      (* Compute the loop input values and abstractions *)
      [%ltrace
        "about to compute the input values and abstractions:"
        ^ "\n- fp_input_svalues: "
        ^ String.concat ", "
            (List.map SymbolicValueId.to_string fp_input_svalues)
        ^ "\n- src_to_tgt_maps:\n"
        ^ ids_maps_to_string tgt_ctx src_to_tgt_maps
        ^ "\n- src_ctx:\n" ^ eval_ctx_to_string src_ctx ^ "\n- tgt_ctx:\n"
        ^ eval_ctx_to_string tgt_ctx];
      let input_values =
        SymbolicValueId.Map.of_list
          (List.map
             (fun sid ->
               let v =
                 SymbolicValueId.Map.find sid src_to_tgt_maps.sid_to_value_map
               in
               (sid, v))
             fp_input_svalues)
      in
      let input_abs =
        let aid_map =
          AbstractionId.Map.of_list
            (AbstractionId.InjSubst.bindings src_to_tgt_maps.aid_map)
        in
        AbstractionId.Map.filter_map
          (fun src_id tgt_id ->
            if AbstractionId.Set.mem src_id fixed_ids.aids then None
            else Some (ctx_lookup_abs tgt_ctx tgt_id))
          aid_map
      in

      [%ltrace
        "Input values:\n"
        ^ SymbolicValueId.Map.to_string (Some "  ")
            (tvalue_to_string ~span:(Some span) src_ctx)
            input_values
        ^ "\nInput abs:\n"
        ^ AbstractionId.Map.to_string (Some "  ")
            (abs_to_string span src_ctx)
            input_abs];

      (* We continue with the *break* context *)
      ((src_ctx, tgt_ctx, input_values, input_abs), fun e -> e)
  | _ ->
      [%ltrace "Match not successful"];

      loop_match_ctx_with_target config span loop_id fp_input_svalues fixed_ids
        src_ctx tgt_ctx
