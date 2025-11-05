open Types
open Values
open Contexts
open TypesUtils
open ValuesUtils
module S = SynthesizeSymbolic
open Cps
open InterpreterUtils
open InterpreterAbs
open InterpreterMatchCtxs
open InterpreterJoin

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
        abs_id = fresh_abs_id ();
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

(** Update the abstractions introduced by a loop with additional information,
    such as region group ids, continuation expressions, etc. *)
let loop_abs_reorder_and_add_info (span : Meta.span) (fixed_ids : ids_sets)
    (ctx : eval_ctx) : eval_ctx =
  (* Reorder the fresh abstractions in the fixed-point *)
  let fp = reorder_fresh_abs span false fixed_ids.aids ctx in

  (* Introduce continuation expressions. *)
  let add_abs_cont_to_abs (abs : abs) (loop_id : loop_id) : abs =
    (* Retrieve the *mutable* borrows/loans from the abstraction values *)
    let borrows : tevalue list ref = ref [] in
    let loans : tevalue list ref = ref [] in
    let get_borrow_loan (x : tavalue) : unit =
      let ty = x.ty in
      match x.value with
      | ALoan lc -> (
          match lc with
          | AMutLoan (pm, bid, child) ->
              [%sanity_check] span (is_aignored child.value);
              let value : evalue =
                ELoan (EMutLoan (pm, bid, mk_eignored child.ty))
              in
              loans := { value; ty } :: !loans
          | ASharedLoan _ ->
              (* We ignore shared loans *)
              ()
          | AEndedMutLoan _
          | AEndedSharedLoan _
          | AIgnoredMutLoan _
          | AEndedIgnoredMutLoan _
          | AIgnoredSharedLoan _ -> [%internal_error] span)
      | ABorrow bc -> (
          match bc with
          | AMutBorrow (pm, bid, child) ->
              [%sanity_check] span (is_aignored child.value);
              let value : evalue =
                EBorrow (EMutBorrow (pm, bid, mk_eignored child.ty))
              in
              borrows := { value; ty } :: !borrows
          | ASharedBorrow _ -> (* We ignore shared borrows *) ()
          | AIgnoredMutBorrow _
          | AEndedMutBorrow _
          | AEndedSharedBorrow
          | AEndedIgnoredMutBorrow _
          | AProjSharedBorrow _ -> [%internal_error] span)
      | ASymbolic (pm, aproj) -> (
          match aproj with
          | AProjLoans { proj = { sv_id; proj_ty }; consumed; borrows } ->
              [%sanity_check] span (consumed = []);
              [%sanity_check] span (borrows = []);
              let value : evalue =
                ESymbolic
                  ( pm,
                    EProjLoans
                      { proj = { sv_id; proj_ty }; consumed = []; borrows = [] }
                  )
              in
              loans := { value; ty } :: !loans
          | AProjBorrows { proj = { sv_id; proj_ty }; loans } ->
              [%sanity_check] span (loans = []);
              let value : evalue =
                ESymbolic
                  (pm, EProjBorrows { proj = { sv_id; proj_ty }; loans = [] })
              in
              borrows := { value; ty } :: !borrows
          | AEndedProjLoans _ | AEndedProjBorrows _ | AEmpty ->
              [%internal_error] span)
      | AAdt _ | AIgnored _ -> [%internal_error] span
    in
    List.iter get_borrow_loan abs.avalues;

    (* Transform them into input/output expressions *)
    let output = mk_etuple (List.rev !borrows) in
    let input = EApp (ELoop (abs.abs_id, loop_id), List.rev !loans) in
    let input : tevalue = { value = input; ty = output.ty } in

    (* Put everything together *)
    let cont : abs_cont option =
      Some { output = Some output; input = Some input }
    in
    { abs with cont }
  in
  let add_abs_conts ctx =
    let visitor =
      object
        inherit [_] map_eval_ctx

        method! visit_abs _ abs =
          match abs.kind with
          | Loop loop_id ->
              [%sanity_check] span (abs.cont = None);
              add_abs_cont_to_abs abs loop_id
          | _ -> abs
      end
    in
    visitor#visit_eval_ctx () ctx
  in

  let fp = add_abs_conts fp in

  (* Return *)
  fp

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
    prepare_ashared_loans_no_synth span loop_id ~with_abs_conts:false ctx0
  in

  (* Debug *)
  [%ltrace
    "after prepare_ashared_loans:" ^ "\n\n- ctx0:\n"
    ^ eval_ctx_to_string ~span:(Some span) ~filter:false ctx0
    ^ "\n\n- ctx1:\n"
    ^ eval_ctx_to_string ~span:(Some span) ~filter:false ctx
    ^ "\n"];

  (* The fixed ids *)
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
      loop_join_origin_with_continue_ctxs config span loop_id !fixed_ids ctx1
        ctxs
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

      (* Check if we reached a fixed point: if not, iterate *)
      if equiv_ctxs ctx ctx1 then ctx1 else compute_fixed_point ctx1 i0 (i - 1)
  in
  let fp = compute_fixed_point ctx max_num_iter max_num_iter in

  (* Update the region abstractions to introduce continuation expressions, etc. *)
  update_fixed_ids [ fp ];
  let fp = loop_abs_reorder_and_add_info span !fixed_ids fp in

  [%ltrace
    "fixed point:\n- fp:\n"
    ^ eval_ctx_to_string ~span:(Some span) ~filter:false fp];

  (* Return *)
  (fp, !fixed_ids)

let compute_loop_break_context (config : config) (span : Meta.span)
    (loop_id : LoopId.id) (eval_loop_body : stl_cm_fun) (fp_ctx : eval_ctx)
    (fixed_ids : ids_sets) : (eval_ctx * abs list) option =
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
  let keep_break_ctx (ctx, res) =
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
      None
  | ctxs ->
      (* Join the contexts *)
      let break_ctx = loop_join_break_ctxs config span loop_id fixed_ids ctxs in

      (* Debug *)
      [%ltrace
        "after joining break ctxs" ^ "\n\n- ctx0:\n"
        ^ eval_ctx_to_string ~span:(Some span) ~filter:false break_ctx];

      let get_fresh_abs (e : env_elem) : abs option =
        match e with
        | EAbs abs ->
            if not (AbsId.Set.mem abs.abs_id fixed_ids.aids) then Some abs
            else None
        | EBinding _ | EFrame -> None
      in
      (* Pay attention to the fact that the elements are stored in reverse order *)
      let abs = List.rev (List.filter_map get_fresh_abs break_ctx.env) in

      Some (break_ctx, abs)
