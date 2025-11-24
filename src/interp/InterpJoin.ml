open Types
open Values
open ValuesUtils
open TypesUtils
open Cps
open Contexts
open InterpUtils
open InterpBorrows
open InterpAbs
open InterpJoinCore
open InterpReduceCollapse
open InterpMatchCtxs

(** The local logger *)
let log = Logging.join_log

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
            let nid = ctx.fresh_symbolic_value_id () in
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
    let nlid = ctx.fresh_borrow_id () in
    let nsid = ctx.fresh_shared_borrow_id () in

    (* We need a fresh region for the new abstraction *)
    let nrid = ctx.fresh_region_id () in

    (* Prepare the shared value *)
    let nsv =
      mk_value_with_fresh_sids_no_shared_loans abs.regions.owned nrid sv
    in

    (* Rem.: the below sanity checks are not really necessary *)
    [%sanity_check] span (AbsId.Set.is_empty abs.parents);
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
      | Some loop_id -> Loop loop_id
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
        abs_id = ctx.fresh_abs_id ();
        kind;
        can_end;
        parents = AbsId.Set.empty;
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
      inherit [_] map_eval_ctx_regular_order as super
      method! visit_abs _ abs = (* Do not explore region abstractions *) abs

      method! visit_VSharedBorrow env bid sid =
        (* Check if the corresponding loan is in a region abstraction *)
        match BorrowId.Map.find_opt bid !loan_to_shared_value with
        | None ->
            (* Do nothing *)
            super#visit_VSharedBorrow env bid sid
        | Some (abs, sv) ->
            (* Check if the region abstraction is frozen *)
            if not abs.can_end then
              let bid, sid = push_abs_for_shared_value abs sv bid sid in
              VSharedBorrow (bid, sid)
            else super#visit_VSharedBorrow env bid sid
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

(* TODO: this could be drastically simplified. *)
let compute_ctx_fresh_ordered_symbolic_values (span : Meta.span)
    ~(only_modified_svalues : bool) (ctx : eval_ctx) (fp_ctx : eval_ctx) :
    symbolic_value list =
  let old_ids, _ = compute_ctx_ids ctx in
  let fp_ids, fp_ids_maps = compute_ctx_ids fp_ctx in
  let fresh_sids = SymbolicValueId.Set.diff fp_ids.sids old_ids.sids in

  (* Compute the set of symbolic values which appear inside *frozen* abstractions.
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
          | EAbs abs -> not abs.can_end)
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
     of the loop *)
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

  (* Remove the symbolic values which are not modified, if the option
     [only_modified_input_svalues] is [true] *)
  let sids_to_values =
    if only_modified_svalues then
      SymbolicValueId.Map.filter
        (fun sid _ -> SymbolicValueId.Set.mem sid fresh_sids)
        sids_to_values
    else sids_to_values
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
          let open InterpBorrowsCore in
          let v =
            match snd (ctx_lookup_loan span ek_all bid fp_ctx) with
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

  input_svalues

let refresh_non_fixed_abs_ids (_span : Meta.span) (fixed_aids : AbsId.Set.t)
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
        if AbsId.Set.mem id fixed_aids then id
        else
          match AbsId.Map.find_opt id !fresh_map with
          | Some id -> id
          | None ->
              let nid = ctx.fresh_abs_id () in
              fresh_map := AbsId.Map.add id nid !fresh_map;
              nid
    end
  in
  let ctx = visitor#visit_eval_ctx () ctx in
  (ctx, !fresh_map)

let join_ctxs (span : Meta.span) (fresh_abs_kind : abs_kind)
    ~(with_abs_conts : bool) (ctx0 : eval_ctx) (ctx1 : eval_ctx) : ctx_or_update
    =
  (* Debug *)
  [%ltrace
    "- ctx0:\n"
    ^ eval_ctx_to_string ~span:(Some span) ~filter:true ctx0
    ^ "\n\n- ctx1:\n"
    ^ eval_ctx_to_string ~span:(Some span) ~filter:true ctx1
    ^ "\n"];

  (* Split the environments in two:
     - we preserve the dummy variables and abstractions which appear in both
       environments: we will match those pairwise. However, for the abstractions:
       we only preserve those which are the same in both abstractions.
     - for the others:
       - we mark the region abstractions with left/right markers
       - we lift the dummy values into region abstractions and mark them as well
  *)
  let dummy_ids0 = ctx_get_dummy_var_ids ctx0 in
  let dummy_ids1 = ctx_get_dummy_var_ids ctx1 in
  let dummy_ids = DummyVarId.Set.inter dummy_ids0 dummy_ids1 in
  let abs_ids = compute_fixed_abs_ids ctx0 ctx1 in

  (* Refresh the non fixed abstraction ids.

     We need to refresh the non-fixed abstraction ids (the ones which do appear,
     while being equal, in both environments) in one of the two contexts,
     because otherwise the join might have twice an abstraction with the same id,
     which is a problem.

     TODO: make the join more general.
  *)
  let ctx1, refreshed_aids = refresh_non_fixed_abs_ids span abs_ids ctx1 in
  [%ltrace
    "After refreshing the non-fixed abstraction ids of ctx1:\n"
    ^ eval_ctx_to_string ~span:(Some span) ~filter:true ctx1];

  let partition (env : env) : env * env =
    List.partition
      (fun (e : env_elem) ->
        match e with
        | EBinding (BVar _, _) ->
            (* All the locals should appear on both sides *) true
        | EBinding (BDummy id, _) -> DummyVarId.Set.mem id dummy_ids
        | EAbs abs -> AbsId.Set.mem abs.abs_id abs_ids
        | EFrame -> true)
      env
  in
  let env0, env0_suffix = partition (List.rev ctx0.env) in
  let env1, env1_suffix = partition (List.rev ctx1.env) in
  [%ldebug
    "\n\n- env0:\n"
    ^ eval_ctx_to_string ~span:(Some span) ~filter:false
        { ctx0 with env = List.rev env0 }
    ^ "\n\n- env0_suffix:\n"
    ^ eval_ctx_to_string ~span:(Some span) ~filter:false
        { ctx0 with env = List.rev env0_suffix }
    ^ "\n\n- env1:\n"
    ^ eval_ctx_to_string ~span:(Some span) ~filter:false
        { ctx1 with env = List.rev env1 }
    ^ "\n\n- env1_suffix:\n"
    ^ eval_ctx_to_string ~span:(Some span) ~filter:false
        { ctx1 with env = List.rev env1_suffix }
    ^ "\n"];

  let nabs = ref [] in

  let symbolic_to_value = ref SymbolicValueId.Map.empty in
  let module S : MatchJoinState = struct
    let fresh_abs_kind = fresh_abs_kind
    let span = span
    let nabs = nabs
    let with_abs_conts = with_abs_conts
    let symbolic_to_value = symbolic_to_value
  end in
  let module JM = MakeJoinMatcher (S) in
  let module M = MakeMatcher (JM) in
  (* Small helper: lookup a binding satisfying some predicate and remove it
     from the enviromnent *)
  let rec pop_binding : 'a. (env_elem -> 'a option) -> env -> 'a * env =
   fun f env ->
    match env with
    | [] -> [%internal_error] span
    | b :: env' -> (
        match f b with
        | None ->
            let out, env' = pop_binding f env' in
            (out, b :: env')
        | Some out -> (out, env'))
  in

  (* Remove a variable from an environment and return the corresponding value *)
  let pop_var (v : real_var_binder) (env : env) : tvalue * env =
    pop_binding
      (fun e ->
        match e with
        | EBinding (BVar v', value) when v' = v -> Some value
        | _ -> None)
      env
  in

  (* Remove a dummy variable from an environment and return the corresponding value *)
  let pop_dummy (v : dummy_var_id) (env : env) : tvalue * env =
    pop_binding
      (fun e ->
        match e with
        | EBinding (BDummy v', value) when v' = v -> Some value
        | _ -> None)
      env
  in

  (* Remove an abs from an environment *)
  let pop_abs (abs_id : abs_id) (env : env) : abs * env =
    pop_binding
      (fun e ->
        match e with
        | EAbs abs when abs.abs_id = abs_id -> Some abs
        | _ -> None)
      env
  in

  (* Rem.: this function raises exceptions.

     We match on the first environment, then pop the corresponding binding
     from the second environment.
  *)
  let rec join_prefixes (env0 : env) (env1 : env) : env =
    match env0 with
    | (EBinding (BDummy b0, v0) as var0) :: env0' ->
        let v1, env1' = pop_dummy b0 env1 in
        let var1 = EBinding (BDummy b0, v1) in

        (* Debug *)
        [%ldebug
          "join_prefixes: BDummys:\n- value0:\n"
          ^ env_elem_to_string span ctx0 var0
          ^ "\n\n- value1:\n"
          ^ env_elem_to_string span ctx1 var1
          ^ "\n"];

        (* Match the values *)
        let b = b0 in
        let v = M.match_tvalues ctx0 ctx1 v0 v1 in
        let var = EBinding (BDummy b, v) in
        (* Continue *)
        var :: join_prefixes env0' env1'
    | (EBinding (BVar b0, v0) as var0) :: env0' ->
        let v1, env1' = pop_var b0 env1 in
        let var1 = EBinding (BVar b0, v1) in

        (* Debug *)
        [%ldebug
          "join_prefixes: BVars:\n- value0:\n"
          ^ env_elem_to_string span ctx0 var0
          ^ "\n\n- value1:\n"
          ^ env_elem_to_string span ctx1 var1
          ^ "\n"];

        (* Variable bindings *must* be in the prefix and consequently their
           ids must be the same *)
        (* Match the values *)
        let b = b0 in
        let v = M.match_tvalues ctx0 ctx1 v0 v1 in
        let var = EBinding (BVar b, v) in
        (* Continue *)
        var :: join_prefixes env0' env1'
    | (EAbs abs0 as abs) :: env0' ->
        let abs1, env1' = pop_abs abs0.abs_id env1 in

        (* Debug *)
        [%ldebug
          "join_prefixes:\n- abs0:\n"
          ^ abs_to_string span ctx0 abs0
          ^ "\n\n- abs1:\n"
          ^ abs_to_string span ctx1 abs1
          ^ "\n"];

        (* The abstractions in the prefix must be the same *)
        [%sanity_check] span (abs0 = abs1);
        (* Continue *)
        abs :: join_prefixes env0' env1'
    | [] ->
        if env1 = [] then []
        else
          [%craise] span
            ("Internal error: please file an issue.\n\
              Could not match:\n\
              - env0:\n"
            ^ eval_ctx_to_string ~span:(Some span) ~filter:false
                { ctx0 with env = List.rev env0 }
            ^ "\n\n- env1:\n"
            ^ eval_ctx_to_string ~span:(Some span) ~filter:false
                { ctx1 with env = List.rev env1 })
    | _ -> [%internal_error] span
  in

  try
    (* Remove the frame delimiter (the first element of an environment is a frame delimiter) *)
    let env0, env1 =
      match (env0, env1) with
      | EFrame :: env0, EFrame :: env1 -> (env0, env1)
      | _ -> [%craise] span "Unreachable"
    in

    (* Match the prefixes *)
    let prefix = join_prefixes env0 env1 in

    (* We do not match the suffixes: we transform the dummy values into
       region abstractions and add projection markers. *)
    let suffix =
      let env0 = env0_suffix in
      let env1 = env1_suffix in
      (* Debug *)
      [%ldebug
        "join_suffixes:" ^ "\n\n- ctx0:\n"
        ^ eval_ctx_to_string ~span:(Some span) ~filter:false
            { ctx0 with env = List.rev env0 }
        ^ "\n\n- ctx1:\n"
        ^ eval_ctx_to_string ~span:(Some span) ~filter:false
            { ctx1 with env = List.rev env1 }
        ^ "\n"];

      (* Add projection marker to all abstractions in the left and right environments.
         Note that we destructure the fresh abstractions - TODO: make the merge more
         general *)
      let destructure_abs ctx =
        destructure_abs span fresh_abs_kind ~can_end:true
          ~destructure_shared_values:true ctx
      in
      let add_marker ctx (pm : proj_marker) (ee : env_elem) : env_elem list =
        match ee with
        | EAbs abs ->
            [
              (let abs = destructure_abs ctx abs in
               EAbs (abs_add_marker span ctx pm abs));
            ]
        | EBinding (BDummy _, v) ->
            (* Transform into a region abstraction and project *)
            let absl =
              convert_value_to_abstractions span fresh_abs_kind ~can_end:true
                ctx v
            in
            let absl = List.map (destructure_abs ctx) absl in
            List.map (fun abs -> EAbs (abs_add_marker span ctx pm abs)) absl
        | EBinding (BVar _, _) | EFrame -> [%internal_error] span
      in

      let env0 = List.flatten (List.map (add_marker ctx0 PLeft) env0) in
      let env1 = List.flatten (List.map (add_marker ctx1 PRight) env1) in

      (* Concatenate the suffixes and append the abstractions introduced while
       joining the prefixes *)
      let absl = List.map (fun abs -> EAbs abs) (List.rev !nabs) in
      List.concat [ env0; env1; absl ]
    in

    let env = List.rev (EFrame :: (prefix @ suffix)) in

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
      _;
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
      _;
    } =
      ctx1
    in
    let ended_regions = RegionId.Set.union ended_regions0 ended_regions1 in
    let ctx : eval_ctx =
      {
        ctx0 with
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

let join_ctxs_list (config : config) (span : Meta.span)
    (fresh_abs_kind : abs_kind) ?(preprocess_first_ctx : bool = true)
    ~(with_abs_conts : bool) (ctxl : eval_ctx list) : eval_ctx list * eval_ctx =
  (* The list of contexts should be non empty *)
  let ctx0, ctxl =
    match ctxl with
    | [] -> [%internal_error] span
    | ctx0 :: ctxl -> (ctx0, ctxl)
  in

  (* Small helper - TODO: probably not necessary anymore as we now preprocess
     the contexts depending on the situation *)
  let preprocess_ctx (ctx : eval_ctx) : eval_ctx =
    (* Simplify the dummy values, by removing as many as we can -
       we ignore the synthesis continuation *)
    let ctx, _ = simplify_dummy_values_useless_abs config span ctx in
    [%ltrace
      "after simplify_dummy_values_useless_abs:\n"
      ^ eval_ctx_to_string ~span:(Some span) ctx];
    ctx
  in

  let ctx0 = if preprocess_first_ctx then preprocess_ctx ctx0 else ctx0 in

  (* # Join with the new contexts, one by one

     For every context, we repeteadly attempt to join it with the current
     result of the join: if we fail (because we need to end loans for instance),
     we update the context and retry.
  *)
  let joined_ctx = ref ctx0 in
  let rec join_one_aux (ctx : eval_ctx) : eval_ctx =
    match join_ctxs span fresh_abs_kind ~with_abs_conts !joined_ctx ctx with
    | Ok (nctx, _) ->
        joined_ctx := nctx;
        ctx
    | Error err ->
        let ctx =
          (* TODO: simplify *)
          match err with
          | LoanInRight bid ->
              InterpBorrows.end_loan_no_synth config span bid ctx
          | LoansInRight bids ->
              InterpBorrows.end_loans_no_synth config span bids ctx
          | LoanInLeft bid ->
              joined_ctx :=
                InterpBorrows.end_loan_no_synth config span bid !joined_ctx;
              ctx
          | LoansInLeft bids ->
              joined_ctx :=
                InterpBorrows.end_loans_no_synth config span bids !joined_ctx;
              ctx
          | AbsInRight _ | AbsInLeft _ -> [%craise] span "Unexpected"
        in
        join_one_aux ctx
  in
  let join_one (ctx : eval_ctx) : eval_ctx =
    [%ltrace
      "join_one: initial ctx:\n" ^ eval_ctx_to_string ~span:(Some span) ctx];

    (* Simplify the dummy values *)
    let ctx = preprocess_ctx ctx in

    (* Join the two contexts  *)
    let ctx1 = join_one_aux ctx in
    [%ltrace
      "join_one: after join:\n"
      ^ eval_ctx_to_string ~span:(Some span) !joined_ctx];

    (* Collapse to eliminate the markers *)
    joined_ctx :=
      collapse_ctx config span fresh_abs_kind ~with_abs_conts !joined_ctx;
    [%ltrace
      "join_one: after join-collapse:\n"
      ^ eval_ctx_to_string ~span:(Some span) !joined_ctx];
    (* Sanity check *)
    if !Config.sanity_checks then Invariants.check_invariants span !joined_ctx;

    (* Return *)
    ctx1
  in

  let ctxl = List.map join_one ctxl in

  (* # Return *)
  (ctx0 :: ctxl, !joined_ctx)

(** Destructure all the new abstractions *)
let destructure_new_abs (span : Meta.span) (old_abs_ids : AbsId.Set.t)
    (ctx : eval_ctx) : eval_ctx =
  [%ltrace "ctx:\n\n" ^ eval_ctx_to_string ctx];
  let is_fresh_abs_id (id : AbsId.id) : bool =
    not (AbsId.Set.mem id old_abs_ids)
  in
  let env =
    env_map_abs
      (fun abs ->
        if is_fresh_abs_id abs.abs_id then
          let abs =
            destructure_abs span abs.kind ~can_end:true
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

let loop_join_origin_with_continue_ctxs (config : config) (span : Meta.span)
    (loop_id : LoopId.id) (ctx0 : eval_ctx) (ctxl : eval_ctx list) :
    (eval_ctx * eval_ctx list) * eval_ctx =
  (* Simplify the contexts we want to join *)
  let simplify (ctx : eval_ctx) : eval_ctx =
    let fixed_aids = compute_fixed_abs_ids ctx0 ctx in
    let fixed_dids = ctx_get_dummy_var_ids ctx0 in
    [%ldebug "- fixed_aids: " ^ AbsId.Set.to_string None fixed_aids];

    (* Simplify the dummy values, by removing as many as we can -
       we ignore the synthesis continuation, as we are only computing a fixed point *)
    let ctx, _ = simplify_dummy_values_useless_abs config span ctx in
    [%ltrace
      "simplify: after simplify_dummy_values_useless_abs:\n"
      ^ eval_ctx_to_string ~span:(Some span) ctx];

    (* Destructure the abstractions introduced in the new context *)
    let ctx = destructure_new_abs span fixed_aids ctx in
    [%ltrace
      "simplify: after destructure:\n"
      ^ eval_ctx_to_string ~span:(Some span) ctx];

    (* Reduce the context we want to add to the join *)
    let ctx =
      reduce_ctx config span ~with_abs_conts:false (Loop loop_id) fixed_aids
        fixed_dids ctx
    in
    [%ltrace
      "simplify: after reduce:\n" ^ eval_ctx_to_string ~span:(Some span) ctx];
    (* Sanity check *)
    if !Config.sanity_checks then Invariants.check_invariants span ctx;

    ctx
  in

  let ctxl = List.map simplify ctxl in

  let ctxl', joined_ctx =
    join_ctxs_list config span (Loop loop_id) ~preprocess_first_ctx:false
      ~with_abs_conts:false (ctx0 :: ctxl)
  in
  [%sanity_check] span (List.length ctxl' = List.length ctxl + 1);
  ((List.hd ctxl', List.tl ctxl'), joined_ctx)

let loop_join_break_ctxs (config : config) (span : Meta.span)
    (loop_id : LoopId.id) (fixed_aids : AbsId.Set.t)
    (fixed_dids : DummyVarId.Set.t) (ctxl : eval_ctx list) : eval_ctx =
  (* Simplify the contexts *)
  let with_abs_conts = false in
  let fresh_abs_kind : abs_kind = Loop loop_id in
  let prepare_ctx (ctx : eval_ctx) : eval_ctx =
    [%ltrace
      "prepate_ctx: initial ctx:\n" ^ eval_ctx_to_string ~span:(Some span) ctx];

    (* Simplify the dummy values, by removing as many as we can -
       we ignore the synthesis continuation *)
    let ctx, _ = simplify_dummy_values_useless_abs config span ctx in
    [%ltrace
      "prepare_ctx: after simplify_dummy_values_useless_abs:\n"
      ^ eval_ctx_to_string ~span:(Some span) ctx];

    (* Destructure the abstractions introduced in the new context *)
    let ctx = destructure_new_abs span fixed_aids ctx in
    [%ltrace
      "prepare_ctx: after destructure:\n"
      ^ eval_ctx_to_string ~span:(Some span) ctx];

    (* Reduce the context we want to add to the join *)
    let ctx =
      reduce_ctx config span ~with_abs_conts:false (Loop loop_id) fixed_aids
        fixed_dids ctx
    in
    [%ltrace
      "prepare_ctx: after reduce:\n" ^ eval_ctx_to_string ~span:(Some span) ctx];
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
            if AbsId.Set.mem abs.abs_id fixed_aids then e
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
        match join_ctxs span fresh_abs_kind ~with_abs_conts !joined_ctx ctx with
        | Ok (nctx, _) ->
            joined_ctx := nctx;
            ctx
        | Error err ->
            let ctx =
              (* TODO: simplify *)
              match err with
              | LoanInRight bid ->
                  InterpBorrows.end_loan_no_synth config span bid ctx
              | LoansInRight bids ->
                  InterpBorrows.end_loans_no_synth config span bids ctx
              | LoanInLeft bid ->
                  joined_ctx :=
                    InterpBorrows.end_loan_no_synth config span bid !joined_ctx;
                  ctx
              | LoansInLeft bids ->
                  joined_ctx :=
                    InterpBorrows.end_loans_no_synth config span bids
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
          collapse_ctx config span fresh_abs_kind ~with_abs_conts !joined_ctx;
        [%ltrace
          "join_one: after join-collapse:\n"
          ^ eval_ctx_to_string ~span:(Some span) !joined_ctx];
        (* Sanity check *)
        if !Config.sanity_checks then
          Invariants.check_invariants span !joined_ctx;

        (* Reduce (it helps matching afterwards) *)
        joined_ctx :=
          reduce_ctx config span ~with_abs_conts fresh_abs_kind fixed_aids
            fixed_dids !joined_ctx;
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

(** TODO: this is a bit of a hack: remove once the avalues are properly
    destructured. *)
let destructure_shared_loans (span : Meta.span) (fixed_aids : AbsId.Set.t) :
    cm_fun =
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
        let sv' =
          mk_fresh_symbolic_value_opt_span (Some span)
            ctx.fresh_symbolic_value_id sv.sv_ty
        in
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
    if not (AbsId.Set.mem abs.abs_id fixed_aids) then
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

let match_ctx_with_target (config : config) (span : Meta.span)
    (fresh_abs_kind : abs_kind) (fixed_aids : AbsId.Set.t)
    (fixed_dids : DummyVarId.Set.t) (input_abs : AbsId.id list)
    (input_svalues : SymbolicValueId.id list) (src_ctx : eval_ctx)
    (tgt_ctx : eval_ctx) :
    (eval_ctx * eval_ctx * tvalue SymbolicValueId.Map.t * abs AbsId.Map.t)
    * (SymbolicAst.expr -> SymbolicAst.expr) =
  (* Debug *)
  [%ltrace
    "- src_ctx: " ^ eval_ctx_to_string src_ctx ^ "\n- tgt_ctx: "
    ^ eval_ctx_to_string tgt_ctx];

  (* We first reorganize [tgt_ctx] so that we can match [src_ctx] with it (by
     ending loans for instance - remember that the [src_ctx] is the fixed point
     context, which results from joins during which we ended the loans which
     were introduced during the loop iterations).

     This operation only ends loans/abstractions and moves some values to anonymous
     values.
  *)
  let tgt_ctx, cc =
    prepare_match_ctx_with_target config span fresh_abs_kind src_ctx tgt_ctx
  in
  [%ltrace
    "Finished preparing the match:" ^ "\n- src_ctx: "
    ^ eval_ctx_to_string src_ctx ^ "\n- tgt_ctx: " ^ eval_ctx_to_string tgt_ctx];

  (* End all the unnecessary borrows/loans (note that it's better to call
     [prepare_loop_match_ctx_with_target] *before* because it unlocks simplification
     possibilities for [simplify_dummy_values_useless_abs]. *)
  let tgt_ctx, cc =
    comp cc (simplify_dummy_values_useless_abs config span tgt_ctx)
  in
  [%ltrace
    "- tgt_ctx after simplify_dummy_values_useless_abs:\n"
    ^ eval_ctx_to_string tgt_ctx];

  (* Removed the ended shared loans and destructure the shared loans.
     We destructure the shared loans in the abstractions which appear in
     [tgt_ctx] but not [src_ctx]. TODO: generalize. *)
  let tgt_ctx, cc =
    comp cc (destructure_shared_loans span fixed_aids tgt_ctx)
  in
  [%ltrace
    "- tgt_ctx after simplify_ended_shared_loans:\n"
    ^ eval_ctx_to_string tgt_ctx];

  (* Reduce the context - TODO: generalize the join so that we don't need to do this *)
  let tgt_ctx =
    reduce_ctx config span ~with_abs_conts:true fresh_abs_kind fixed_aids
      fixed_dids tgt_ctx
  in
  [%ltrace "- tgt_ctx after reduce_ctx:\n" ^ eval_ctx_to_string tgt_ctx];

  (* Join the source context with the target context *)
  let joined_ctx, join_info =
    match
      join_ctxs span fresh_abs_kind ~with_abs_conts:true src_ctx tgt_ctx
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
  let add_borrows_seq = ref [] in
  let joined_ctx_not_projected =
    collapse_ctx config span ~sequence:(Some merge_seq)
      ~shared_borrows_seq:(Some add_borrows_seq) ~with_abs_conts:true
      fresh_abs_kind joined_ctx
  in
  let merge_seq = List.rev !merge_seq in
  (* Update the sequence of shared borrows to introduce: we only want to add
     borrows to the right *)
  let add_borrows_seq =
    List.filter_map
      (fun (abs_id, i, pm, bid, ty) ->
        if pm = PRight then Some (abs_id, i, PNone, bid, ty) else None)
      (List.rev !add_borrows_seq)
  in
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
  let joined_ctx = project_context span fixed_aids PRight joined_ctx in
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
    collapse_ctx_no_markers_following_sequence span merge_seq add_borrows_seq
      ~with_abs_conts:true fresh_abs_kind joined_ctx
  in
  [%ltrace
    "After collapsing the context: joined_ctx:\n"
    ^ eval_ctx_to_string joined_ctx];

  (* There may be empty abstractions in the projected context: end them.

     Remark: we forbid the introduction of (meta) snapshots, because they may
     refer to values which are introduced as, for instance, output of a loop
     and are not bound yet (this may lead to issues). *)
  let joined_ctx, cc =
    comp cc
      (simplify_dummy_values_useless_abs config span ~snapshots:false joined_ctx)
  in
  [%ltrace
    "After applying [simplify_dummy_values_useless_abs] to the joined context: \
     joined_ctx:\n"
    ^ eval_ctx_to_string joined_ctx];

  (* Reorder the region abstractions in the target context -
     TODO: generalize the match so that we don't have to do this *)
  let joined_ctx = reorder_fresh_abs span true fixed_aids joined_ctx in
  [%ltrace
    "After reorder_fresh_abs (fixed_aids: "
    ^ AbsId.Set.to_string None fixed_aids
    ^ "): joined_ctx:\n"
    ^ eval_ctx_to_string ~span:(Some span) joined_ctx];

  [%ltrace
    "About to match:" ^ "\n- src_ctx:\n" ^ eval_ctx_to_string src_ctx
    ^ "\n- joined_ctx:\n"
    ^ eval_ctx_to_string joined_ctx];

  (* Check that the source context (i.e., the fixed-point context) matches
     the resulting target context. *)
  let src_to_joined_maps =
    let open InterpBorrowsCore in
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
    let fixed_ids =
      { empty_ids_sets with aids = ctx_get_frozen_abs_set src_ctx }
    in
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
    ^ "\n\n- src_to_joined_maps: "
    ^ ids_maps_to_string joined_ctx src_to_joined_maps];

  (* Sanity check *)
  if !Config.sanity_checks then
    Invariants.check_borrowed_values_invariant span joined_ctx;

  (* Compute the loop input values and abstractions *)
  [%ltrace
    "About to compute the input values and abstractions:"
    ^ "\n- fp_input_svalues: "
    ^ String.concat ", " (List.map SymbolicValueId.to_string input_svalues)
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
         input_svalues)
  in
  let input_abs =
    let aid_map =
      AbsId.Map.of_list (AbsId.InjSubst.bindings src_to_joined_maps.aid_map)
    in
    AbsId.Map.of_list
      (List.map
         (fun input_aid ->
           match AbsId.Map.find_opt input_aid aid_map with
           | None -> [%internal_error] span
           | Some joined_id -> (input_aid, ctx_lookup_abs joined_ctx joined_id))
         input_abs)
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
    (_loop_id : LoopId.id) (fixed_aids : AbsId.Set.t)
    (fixed_dids : DummyVarId.Set.t) (fp_input_abs : abs_id list)
    (fp_input_svalues : SymbolicValueId.id list) (src_ctx : eval_ctx)
    (tgt_ctx : eval_ctx) :
    (eval_ctx * eval_ctx * tvalue SymbolicValueId.Map.t * abs AbsId.Map.t)
    * (SymbolicAst.expr -> SymbolicAst.expr) =
  (* Debug *)
  [%ltrace
    "- src_ctx:\n" ^ eval_ctx_to_string src_ctx ^ "\n- tgt_ctx:\n"
    ^ eval_ctx_to_string tgt_ctx];

  match_ctx_with_target config span WithCont fixed_aids fixed_dids fp_input_abs
    fp_input_svalues src_ctx tgt_ctx
