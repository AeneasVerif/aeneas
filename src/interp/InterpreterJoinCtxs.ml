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

let refresh_non_fixed_abs_ids (_span : Meta.span) (fixed_ids : ids_sets)
    (ctx : eval_ctx) : eval_ctx * abs_id AbsId.Map.t =
  (* Note that abstraction ids appear both inside of region abstractions
     but also inside of evalues (some evalues refer to region abstractions).
     We have to make sure that we keep things consistent: whenever we refresh
     an id, we remember it. *)
  let fresh_map = ref AbsId.Map.empty in

  let visitor =
    object
      inherit [_] map_eval_ctx

      method! visit_abs_id _ id =
        if AbsId.Set.mem id fixed_ids.aids then id
        else
          match AbsId.Map.find_opt id !fresh_map with
          | Some id -> id
          | None ->
              let nid = fresh_abs_id () in
              fresh_map := AbsId.Map.add id nid !fresh_map;
              nid
    end
  in
  let ctx = visitor#visit_eval_ctx () ctx in
  (ctx, !fresh_map)

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

  (* Refresh the non fixed abstraction ids.

     We need to refresh the non-fixed abstraction ids in one of the two contexts,
     because otherwise the join might have twice an abstraction with the same id,
     which is a problem.

     TODO: make the join more general.
  *)
  let ctx1, refreshed_aids = refresh_non_fixed_abs_ids span fixed_ids ctx1 in
  [%ltrace
    "After refreshing the non-fixed abstraction ids of ctx1:\n"
    ^ eval_ctx_to_string ~span:(Some span) ~filter:true ctx1];

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
          [%sanity_check] span (not (AbsId.Set.mem abs.abs_id fixed_ids.aids))
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
        if AbsId.Set.mem abs0.abs_id fixed_ids.aids then (
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
      { symbolic_to_value = !symbolic_to_value; refreshed_aids }
    in

    (* Sanity check *)
    if !Config.sanity_checks then Invariants.check_unique_abs_ids span ctx;

    Ok (ctx, join_info)
  with ValueMatchFailure e -> Error e

(** Destructure all the new abstractions *)
let destructure_new_abs (span : Meta.span) (loop_id : LoopId.id)
    (old_abs_ids : AbsId.Set.t) (ctx : eval_ctx) : eval_ctx =
  [%ltrace "ctx:\n\n" ^ eval_ctx_to_string ctx];
  let abs_kind : abs_kind = Loop loop_id in
  let is_fresh_abs_id (id : AbsId.id) : bool =
    not (AbsId.Set.mem id old_abs_ids)
  in
  let env =
    env_map_abs
      (fun abs ->
        if is_fresh_abs_id abs.abs_id then
          let abs =
            destructure_abs span abs_kind ~can_end:true
              ~destructure_shared_values:true ctx abs
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
let refresh_abs (old_abs : AbsId.Set.t) (ctx : eval_ctx) : eval_ctx =
  let ids, _ = compute_ctx_ids ctx in
  let abs_to_refresh = AbsId.Set.diff ids.aids old_abs in
  let aids_subst =
    List.map
      (fun id -> (id, fresh_abs_id ()))
      (AbsId.Set.elements abs_to_refresh)
  in
  let aids_subst = AbsId.Map.of_list aids_subst in
  let asubst id =
    match AbsId.Map.find_opt id aids_subst with
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
      ^ AbsId.Set.to_string None fixed_ids.aids
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
      collapse_ctx config span loop_id fixed_ids ~with_abs_conts !joined_ctx;
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
      ^ AbsId.Set.to_string None fixed_ids.aids
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
            if AbsId.Set.mem abs.abs_id fixed_ids.aids then e
            else EAbs { abs with cont = None; kind = Loop loop_id }
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
          collapse_ctx config span loop_id fixed_ids ~with_abs_conts !joined_ctx;
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

(** TODO: this is a bit of a hack: remove one the avalues are properly
    destructured. *)
let destructure_shared_loans (span : Meta.span) (fixed_ids : ids_sets) : cm_fun
    =
 fun ctx ->
  let bindings = ref [] in

  let rec copy_value (v : tvalue) : tvalue =
    match v.value with
    | VLiteral _ | VBottom -> v
    | VAdt { variant_id; fields } ->
        let fields = List.map copy_value fields in
        { v with value = VAdt { variant_id; fields } }
    | VBorrow _ | VLoan _ -> [%craise] span "Not implemented"
    | VSymbolic sv ->
        [%cassert] span
          (not (symbolic_value_has_borrows (Some span) ctx sv))
          "Not implemented";
        let sv' = mk_fresh_symbolic_value_opt_span (Some span) sv.sv_ty in
        bindings := (sv', v) :: !bindings;
        { value = VSymbolic sv'; ty = sv.sv_ty }
  in

  let rec destructure_value (abs : abs) (v : tvalue) : tvalue * tavalue list =
    let value, avl =
      match v.value with
      | VLiteral _ | VBottom | VSymbolic _ -> (v.value, [])
      | VAdt { variant_id; fields } ->
          let fields, avl =
            List.split (List.map (destructure_value abs) fields)
          in
          (VAdt { variant_id; fields }, List.flatten avl)
      | VBorrow bc -> (
          match bc with
          | VSharedBorrow _ -> (v.value, [])
          | VMutBorrow (lid, v) ->
              let v, avl = destructure_value abs v in
              (VBorrow (VMutBorrow (lid, v)), avl)
          | VReservedMutBorrow _ -> [%internal_error] span)
      | VLoan lc -> (
          match lc with
          | VSharedLoan (lid, sv) ->
              let sv, avl = destructure_value abs sv in
              let ty = sv.ty in
              [%cassert] span
                (not
                   (TypesUtils.ty_has_borrows (Some span)
                      ctx.type_ctx.type_infos ty))
                "Not implemented";
              let rid = RegionId.Set.choose abs.regions.owned in
              let ref_ty = TRef (RVar (Free rid), ty, RShared) in
              let child = ValuesUtils.mk_aignored span ty None in
              let av = ALoan (ASharedLoan (PNone, lid, copy_value sv, child)) in
              let av : tavalue = { value = av; ty = ref_ty } in
              (sv.value, av :: avl)
          | VMutLoan _ -> (v.value, []))
    in
    ({ v with value }, avl)
  in

  let rec destructure_avalue (abs : abs) (av : tavalue) : tavalue * tavalue list
      =
    let value, avl =
      match av.value with
      | AAdt { variant_id; fields } ->
          let fields, avl =
            List.split (List.map (destructure_avalue abs) fields)
          in
          (AAdt { variant_id; fields }, List.flatten avl)
      | ALoan lc ->
          let lc, avl =
            match lc with
            | AMutLoan (pm, lid, child) ->
                let child, avl = destructure_avalue abs child in
                (AMutLoan (pm, lid, child), avl)
            | ASharedLoan (pm, lid, sv, child) ->
                let sv, avl0 = destructure_value abs sv in
                let child, avl1 = destructure_avalue abs child in
                (ASharedLoan (pm, lid, sv, child), avl0 @ avl1)
            | AEndedMutLoan { child; given_back; given_back_meta } ->
                let child, avl0 = destructure_avalue abs child in
                let given_back, avl1 = destructure_avalue abs given_back in
                ( AEndedMutLoan { child; given_back; given_back_meta },
                  avl0 @ avl1 )
            | AEndedSharedLoan (sv, child) ->
                let sv, avl0 = destructure_value abs sv in
                let child, avl1 = destructure_avalue abs child in
                (AEndedSharedLoan (sv, child), avl0 @ avl1)
            | AIgnoredMutLoan (lid, child) ->
                let child, avl = destructure_avalue abs child in
                (AIgnoredMutLoan (lid, child), avl)
            | AEndedIgnoredMutLoan { child; given_back; given_back_meta } ->
                let child, avl0 = destructure_avalue abs child in
                let given_back, avl1 = destructure_avalue abs given_back in
                ( AEndedIgnoredMutLoan { child; given_back; given_back_meta },
                  avl0 @ avl1 )
            | AIgnoredSharedLoan child ->
                let child, avl = destructure_avalue abs child in
                (AIgnoredSharedLoan child, avl)
          in
          (ALoan lc, avl)
      | ABorrow bc ->
          let bc, avl =
            match bc with
            | AMutBorrow (pm, lid, child) ->
                let child, avl = destructure_avalue abs child in
                (AMutBorrow (pm, lid, child), avl)
            | ASharedBorrow _ -> (bc, [])
            | AIgnoredMutBorrow (lid, child) ->
                let child, avl = destructure_avalue abs child in
                (AIgnoredMutBorrow (lid, child), avl)
            | AEndedMutBorrow _ | AEndedSharedBorrow ->
                (* Shouldn't find ended borrows in live abstractions *)
                [%internal_error] span
            | AEndedIgnoredMutBorrow _ -> (bc, [])
            | AProjSharedBorrow _ -> [%craise] span "Not implemented"
          in
          (ABorrow bc, avl)
      | ASymbolic _ | AIgnored _ -> (av.value, [])
    in
    ({ av with value }, avl)
  in
  let destructure_abs (abs : abs) : abs =
    if not (AbsId.Set.mem abs.abs_id fixed_ids.aids) then
      let avalues = List.map (destructure_avalue abs) abs.avalues in
      let avalues =
        List.flatten (List.map (fun (av, avl) -> av :: avl) avalues)
      in
      { abs with avalues }
    else abs
  in
  let ctx = { ctx with env = env_map_abs destructure_abs ctx.env } in

  let cc e =
    List.fold_right
      (fun (nsv, v) e ->
        SymbolicAst.IntroSymbolic (ctx, None, nsv, VaSingleValue v, e))
      !bindings e
  in

  (ctx, cc)

let loop_match_ctx_with_target (config : config) (span : Meta.span)
    (loop_id : LoopId.id) (fp_input_svalues : SymbolicValueId.id list)
    (fixed_ids : ids_sets) (src_ctx : eval_ctx) (tgt_ctx : eval_ctx) :
    (eval_ctx * eval_ctx * tvalue SymbolicValueId.Map.t * abs AbsId.Map.t)
    * (SymbolicAst.expr -> SymbolicAst.expr) =
  (* Debug *)
  [%ltrace
    "- fixed_ids: " ^ show_ids_sets fixed_ids ^ "\n" ^ "\n- src_ctx: "
    ^ eval_ctx_to_string src_ctx ^ "\n- tgt_ctx: " ^ eval_ctx_to_string tgt_ctx];

  (* We first reorganize [tgt_ctx] so that we can match [src_ctx] with it (by
     ending loans for instance - remember that the [src_ctx] is the fixed point
     context, which results from joins during which we ended the loans which
     were introduced during the loop iterations).

     This operation only ends loans/abstractions and moves some values to anonymous
     values.
  *)
  let tgt_ctx, cc =
    prepare_loop_match_ctx_with_target config span loop_id fixed_ids src_ctx
      tgt_ctx
  in
  [%ltrace
    "Finished preparing the match:" ^ "\n- fixed_ids: "
    ^ show_ids_sets fixed_ids ^ "\n" ^ "\n- src_ctx: "
    ^ eval_ctx_to_string src_ctx ^ "\n- tgt_ctx: " ^ eval_ctx_to_string tgt_ctx];

  (* End all the unnecessary borrows/loans (note that it's better to call
     [prepare_loop_match_ctx_with_target] *before* because it unlocks simplification
     possibilities for [simplify_dummy_values_useless_abs]. *)
  let tgt_ctx, cc =
    comp cc
      (simplify_dummy_values_useless_abs config span fixed_ids.aids tgt_ctx)
  in
  [%ltrace
    "- tgt_ctx after simplify_dummy_values_useless_abs:\n"
    ^ eval_ctx_to_string tgt_ctx];

  (* Removed the ended shared loans and destructure the shared loans *)
  let tgt_ctx, cc = comp cc (destructure_shared_loans span fixed_ids tgt_ctx) in
  [%ltrace
    "- tgt_ctx after simplify_ended_shared_loans:\n"
    ^ eval_ctx_to_string tgt_ctx];

  (* Reduce the context *)
  let tgt_ctx =
    reduce_ctx config span ~with_abs_conts:true loop_id fixed_ids tgt_ctx
  in
  [%ltrace "- tgt_ctx after reduce_ctx:\n" ^ eval_ctx_to_string tgt_ctx];

  (* Join the source context with the target context *)
  let joined_ctx, join_info =
    match
      join_ctxs span loop_id fixed_ids ~with_abs_conts:true src_ctx tgt_ctx
    with
    | Ok x -> x
    | Error _ -> [%craise] span "Could not join the contexts"
  in
  [%ltrace
    "Result of the join:\n- joined_ctx:\n"
    ^ eval_ctx_to_string joined_ctx
    ^ "\n- join_info.symbolic_to_value: "
    ^ SymbolicValueId.Map.to_string (Some "  ")
        (Print.pair_to_string (tvalue_to_string src_ctx)
           (tvalue_to_string src_ctx))
        join_info.symbolic_to_value
    ^ "\n- join_info.refreshed_aids: "
    ^ AbsId.Map.to_string None AbsId.to_string join_info.refreshed_aids];

  (* The id of some region abstractions might have been refreshed in the target
     context: we need to register this because otherwise the translation will
     fail. *)
  let cc =
    if AbsId.Map.is_empty join_info.refreshed_aids then cc
    else cc_comp cc (fun e -> SubstituteAbsIds (join_info.refreshed_aids, e))
  in

  (* We need to collapse the context.

     We have to collapse the context because otherwise some abstractions might not
     get merged, leading to an issue when matching the source context with the
     joined context afterwards. We also do not want to collapse the context then
     project it, because the collapsed context uses elements from both the right
     and left context in its abstraction expressions, which are a bit annoying
     to project. What we do for now is merge the joined context, to register the
     sequence of merges which have to be performed, then project the context
     *before* the collapse, and apply the same sequence to this one.

     TODO: we need to make the match more general so that we do not have to do this.
  *)
  let merge_seq = ref [] in
  let joined_ctx_not_projected =
    collapse_ctx config span ~sequence:(Some merge_seq) ~with_abs_conts:false
      loop_id fixed_ids joined_ctx
  in
  let merge_seq = List.rev !merge_seq in
  [%ltrace
    "After collapsing the (unprojected) context: joined_ctx_not_projected:\n"
    ^ eval_ctx_to_string joined_ctx_not_projected
    ^ "\n\n- merge_seq:\n"
    ^ String.concat "\n"
        (List.map
           (fun (a0, a1, a2) ->
             "(" ^ AbsId.to_string a0 ^ "," ^ AbsId.to_string a1 ^ ") -> "
             ^ AbsId.to_string a2)
           merge_seq)];

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

  (* Apply the sequence of merges to the projected context *)
  let joined_ctx =
    collapse_ctx_no_markers_following_sequence span merge_seq
      ~with_abs_conts:true loop_id fixed_ids joined_ctx
  in
  [%ltrace
    "After collapsing the context: joined_ctx:\n"
    ^ eval_ctx_to_string joined_ctx];

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
      match snd (ctx_lookup_loan span ek_all lid ctx) with
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
              - source to joined
              - joined to target
              Note that joined to target is a partial map: it only maps
              symbolic values appearing in the joined context, and in
              particular appearing in the joined values (not in the region
              abstractions). For all the missing symbolic values, the
              substitution should be the identity.
           *)
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
           (* Update the symbolic values appearing in [v] *)
           let subst =
             object
               inherit [_] map_tvalue

               method! visit_VSymbolic _ sv =
                 match
                   SymbolicValueId.Map.find_opt sv.sv_id
                     joined_symbolic_to_tgt_value
                 with
                 | Some v -> v.value
                 | None -> VSymbolic sv
             end
           in
           let v = subst#visit_tvalue () v in
           (sid, v))
         fp_input_svalues)
  in
  let input_abs =
    let aid_map =
      AbsId.Map.of_list (AbsId.InjSubst.bindings src_to_joined_maps.aid_map)
    in
    AbsId.Map.filter_map
      (fun src_id joined_id ->
        if AbsId.Set.mem src_id fixed_ids.aids then None
        else Some (ctx_lookup_abs joined_ctx joined_id))
      aid_map
  in

  [%ltrace
    "Input values:\n"
    ^ SymbolicValueId.Map.to_string (Some "  ")
        (tvalue_to_string ~span:(Some span) src_ctx)
        input_values
    ^ "\nInput abs:\n"
    ^ AbsId.Map.to_string (Some "  ") (abs_to_string span src_ctx) input_abs];

  (* *)
  Invariants.check_invariants span joined_ctx;

  (* We continue with the *fixed-point* context *)
  ((src_ctx, tgt_ctx, input_values, input_abs), cc)

let loop_match_break_ctx_with_target (config : config) (span : Meta.span)
    (loop_id : LoopId.id) (fp_input_svalues : SymbolicValueId.id list)
    (fixed_ids : ids_sets) (src_ctx : eval_ctx) (tgt_ctx : eval_ctx) :
    (eval_ctx * eval_ctx * tvalue SymbolicValueId.Map.t * abs AbsId.Map.t)
    * (SymbolicAst.expr -> SymbolicAst.expr) =
  (* Debug *)
  [%ltrace
    "- fixed_ids: " ^ show_ids_sets fixed_ids ^ "\n" ^ "\n- src_ctx: "
    ^ eval_ctx_to_string src_ctx ^ "\n- tgt_ctx: " ^ eval_ctx_to_string tgt_ctx];

  (* We have to consider the possibility that the break context is not the result
     of a join (because there was a single break in the loop): in this case there
     is no point in joining the break context with the target context, we directly
     check if they are equivalent.

     TODO: is this really useful? It actually never works.
  *)
  let src_to_tgt_maps =
    let fixed_ids = ids_sets_empty_borrows_loans fixed_ids in
    let open InterpreterBorrowsCore in
    let lookup_shared_loan lid ctx : tvalue =
      match snd (ctx_lookup_loan span ek_all lid ctx) with
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
          AbsId.Map.of_list (AbsId.InjSubst.bindings src_to_tgt_maps.aid_map)
        in
        AbsId.Map.filter_map
          (fun src_id tgt_id ->
            if AbsId.Set.mem src_id fixed_ids.aids then None
            else Some (ctx_lookup_abs tgt_ctx tgt_id))
          aid_map
      in

      [%ltrace
        "Input values:\n"
        ^ SymbolicValueId.Map.to_string (Some "  ")
            (tvalue_to_string ~span:(Some span) src_ctx)
            input_values
        ^ "\nInput abs:\n"
        ^ AbsId.Map.to_string (Some "  ") (abs_to_string span src_ctx) input_abs];

      (* We continue with the *break* context *)
      ((src_ctx, tgt_ctx, input_values, input_abs), fun e -> e)
  | _ ->
      [%ltrace "Match not successful"];

      loop_match_ctx_with_target config span loop_id fp_input_svalues fixed_ids
        src_ctx tgt_ctx
