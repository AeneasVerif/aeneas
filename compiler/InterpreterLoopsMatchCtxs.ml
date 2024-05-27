(** This module implements support to match contexts for loops.

    The matching functions are used for instance to compute joins, or
    to check if two contexts are equivalent (modulo conversion).
 *)

open Types
open Values
open Contexts
open TypesUtils
open ValuesUtils
open Cps
open InterpreterUtils
open InterpreterBorrowsCore
open InterpreterBorrows
open InterpreterLoopsCore
open Errors
module S = SynthesizeSymbolic

(** The local logger *)
let log = Logging.loops_match_ctxs_log

let compute_abs_borrows_loans_maps (span : Meta.span) (no_duplicates : bool)
    (explore : abs -> bool) (env : env) : abs_borrows_loans_maps =
  let abs_ids = ref [] in
  let abs_to_borrows = ref AbstractionId.Map.empty in
  let abs_to_loans = ref AbstractionId.Map.empty in
  let abs_to_borrows_loans = ref AbstractionId.Map.empty in
  let borrow_to_abs = ref BorrowId.Map.empty in
  let loan_to_abs = ref BorrowId.Map.empty in
  let borrow_loan_to_abs = ref BorrowId.Map.empty in

  let module R (Id0 : Identifiers.Id) (Id1 : Identifiers.Id) = struct
    (*
       [check_singleton_sets]: check that the mapping maps to a singletong.
       [check_not_already_registered]: check if the mapping was not already registered.
    *)
    let register_mapping (check_singleton_sets : bool)
        (check_not_already_registered : bool) (map : Id1.Set.t Id0.Map.t ref)
        (id0 : Id0.id) (id1 : Id1.id) : unit =
      (* Sanity check *)
      (if check_singleton_sets || check_not_already_registered then
         match Id0.Map.find_opt id0 !map with
         | None -> ()
         | Some set ->
             sanity_check __FILE__ __LINE__
               ((not check_not_already_registered) || not (Id1.Set.mem id1 set))
               span);
      (* Update the mapping *)
      map :=
        Id0.Map.update id0
          (fun ids ->
            match ids with
            | None -> Some (Id1.Set.singleton id1)
            | Some ids ->
                (* Sanity check *)
                sanity_check __FILE__ __LINE__ (not check_singleton_sets) span;
                sanity_check __FILE__ __LINE__
                  ((not check_not_already_registered)
                  || not (Id1.Set.mem id1 ids))
                  span;
                (* Update *)
                Some (Id1.Set.add id1 ids))
          !map
  end in
  let module RAbsBorrow = R (AbstractionId) (BorrowId) in
  let module RBorrowAbs = R (BorrowId) (AbstractionId) in
  let register_borrow_id abs_id bid =
    RAbsBorrow.register_mapping false no_duplicates abs_to_borrows abs_id bid;
    RAbsBorrow.register_mapping false false abs_to_borrows_loans abs_id bid;
    RBorrowAbs.register_mapping no_duplicates no_duplicates borrow_to_abs bid
      abs_id;
    RBorrowAbs.register_mapping false false borrow_loan_to_abs bid abs_id
  in

  let register_loan_id abs_id bid =
    RAbsBorrow.register_mapping false no_duplicates abs_to_loans abs_id bid;
    RAbsBorrow.register_mapping false false abs_to_borrows_loans abs_id bid;
    RBorrowAbs.register_mapping no_duplicates no_duplicates loan_to_abs bid
      abs_id;
    RBorrowAbs.register_mapping false false borrow_loan_to_abs bid abs_id
  in

  let explore_abs =
    object (self : 'self)
      inherit [_] iter_typed_avalue as super

      (** Make sure we don't register the ignored ids *)
      method! visit_aloan_content abs_id lc =
        match lc with
        | AMutLoan _ | ASharedLoan _ ->
            (* Process those normally *)
            super#visit_aloan_content abs_id lc
        | AIgnoredMutLoan (_, child)
        | AEndedIgnoredMutLoan { child; given_back = _; given_back_span = _ }
        | AIgnoredSharedLoan child ->
            (* Ignore the id of the loan, if there is *)
            self#visit_typed_avalue abs_id child
        | AEndedMutLoan _ | AEndedSharedLoan _ ->
            craise __FILE__ __LINE__ span "Unreachable"

      (** Make sure we don't register the ignored ids *)
      method! visit_aborrow_content abs_id bc =
        match bc with
        | AMutBorrow _ | ASharedBorrow _ | AProjSharedBorrow _ ->
            (* Process those normally *)
            super#visit_aborrow_content abs_id bc
        | AIgnoredMutBorrow (_, child)
        | AEndedIgnoredMutBorrow { child; given_back = _; given_back_span = _ }
          ->
            (* Ignore the id of the borrow, if there is *)
            self#visit_typed_avalue abs_id child
        | AEndedMutBorrow _ | AEndedSharedBorrow ->
            craise __FILE__ __LINE__ span "Unreachable"

      method! visit_borrow_id abs_id bid = register_borrow_id abs_id bid
      method! visit_loan_id abs_id lid = register_loan_id abs_id lid
    end
  in

  env_iter_abs
    (fun abs ->
      let abs_id = abs.abs_id in
      if explore abs then (
        abs_to_borrows :=
          AbstractionId.Map.add abs_id BorrowId.Set.empty !abs_to_borrows;
        abs_to_loans :=
          AbstractionId.Map.add abs_id BorrowId.Set.empty !abs_to_loans;
        abs_ids := abs.abs_id :: !abs_ids;
        List.iter (explore_abs#visit_typed_avalue abs.abs_id) abs.avalues)
      else ())
    env;

  (* Rem.: there is no need to reverse the abs ids, because we explored the environment
     starting with the freshest values and abstractions *)
  {
    abs_ids = !abs_ids;
    abs_to_borrows = !abs_to_borrows;
    abs_to_loans = !abs_to_loans;
    abs_to_borrows_loans = !abs_to_borrows_loans;
    borrow_to_abs = !borrow_to_abs;
    loan_to_abs = !loan_to_abs;
    borrow_loan_to_abs = !borrow_loan_to_abs;
  }

(** Match two types during a join.

    TODO: probably don't need to take [match_regions] as input anymore.
 *)
let rec match_types (span : Meta.span) (match_distinct_types : ty -> ty -> ty)
    (match_regions : region -> region -> region) (ty0 : ty) (ty1 : ty) : ty =
  let match_rec = match_types span match_distinct_types match_regions in
  match (ty0, ty1) with
  | TAdt (id0, generics0), TAdt (id1, generics1) ->
      sanity_check __FILE__ __LINE__ (id0 = id1) span;
      sanity_check __FILE__ __LINE__
        (generics0.const_generics = generics1.const_generics)
        span;
      sanity_check __FILE__ __LINE__
        (generics0.trait_refs = generics1.trait_refs)
        span;
      let id = id0 in
      let const_generics = generics1.const_generics in
      let trait_refs = generics1.trait_refs in
      let regions =
        List.map
          (fun (id0, id1) -> match_regions id0 id1)
          (List.combine generics0.regions generics1.regions)
      in
      let types =
        List.map
          (fun (ty0, ty1) -> match_rec ty0 ty1)
          (List.combine generics0.types generics1.types)
      in
      let generics = { regions; types; const_generics; trait_refs } in
      TAdt (id, generics)
  | TVar vid0, TVar vid1 ->
      sanity_check __FILE__ __LINE__ (vid0 = vid1) span;
      let vid = vid0 in
      TVar vid
  | TLiteral lty0, TLiteral lty1 ->
      sanity_check __FILE__ __LINE__ (lty0 = lty1) span;
      ty0
  | TNever, TNever -> ty0
  | TRef (r0, ty0, k0), TRef (r1, ty1, k1) ->
      let r = match_regions r0 r1 in
      let ty = match_rec ty0 ty1 in
      sanity_check __FILE__ __LINE__ (k0 = k1) span;
      let k = k0 in
      TRef (r, ty, k)
  | _ -> match_distinct_types ty0 ty1

module MakeMatcher (M : PrimMatcher) : Matcher = struct
  let span = M.span

  let rec match_typed_values (ctx0 : eval_ctx) (ctx1 : eval_ctx)
      (v0 : typed_value) (v1 : typed_value) : typed_value =
    let match_rec = match_typed_values ctx0 ctx1 in
    let ty = M.match_etys ctx0 ctx1 v0.ty v1.ty in
    (* Using ValuesUtils.value_ has_borrows on purpose here: we want
       to make explicit the fact that, though we have to pick
       one of the two contexts (ctx0 here) to call value_has_borrows,
       it doesn't matter here. *)
    let value_has_borrows =
      ValuesUtils.value_has_borrows ctx0.type_ctx.type_infos
    in
    match (v0.value, v1.value) with
    | VLiteral lv0, VLiteral lv1 ->
        if lv0 = lv1 then v1 else M.match_distinct_literals ctx0 ctx1 ty lv0 lv1
    | VAdt av0, VAdt av1 ->
        if av0.variant_id = av1.variant_id then
          let fields = List.combine av0.field_values av1.field_values in
          let field_values =
            List.map (fun (f0, f1) -> match_rec f0 f1) fields
          in
          let value : value =
            VAdt { variant_id = av0.variant_id; field_values }
          in
          { value; ty = v1.ty }
        else (
          (* For now, we don't merge ADTs which contain borrows *)
          sanity_check __FILE__ __LINE__
            (not (value_has_borrows v0.value))
            M.span;
          sanity_check __FILE__ __LINE__
            (not (value_has_borrows v1.value))
            M.span;
          (* Merge *)
          M.match_distinct_adts ctx0 ctx1 ty av0 av1)
    | VBottom, VBottom -> v0
    | VBorrow bc0, VBorrow bc1 ->
        let bc =
          match (bc0, bc1) with
          | VSharedBorrow bid0, VSharedBorrow bid1 ->
              let bid =
                M.match_shared_borrows ctx0 ctx1 match_rec ty bid0 bid1
              in
              VSharedBorrow bid
          | VMutBorrow (bid0, bv0), VMutBorrow (bid1, bv1) ->
              let bv = match_rec bv0 bv1 in

              cassert __FILE__ __LINE__
                (not
                   (ValuesUtils.value_has_borrows ctx0.type_ctx.type_infos
                      bv.value))
                M.span "The join of nested borrows is not supported yet";
              let bid, bv =
                M.match_mut_borrows ctx0 ctx1 ty bid0 bv0 bid1 bv1 bv
              in
              VMutBorrow (bid, bv)
          | VReservedMutBorrow _, _
          | _, VReservedMutBorrow _
          | VSharedBorrow _, VMutBorrow _
          | VMutBorrow _, VSharedBorrow _ ->
              (* If we get here, either there is a typing inconsistency, or we are
                 trying to match a reserved borrow, which shouldn't happen because
                 reserved borrow should be eliminated very quickly - they are introduced
                 just before function calls which activate them *)
              craise __FILE__ __LINE__ M.span "Unexpected"
        in
        { value = VBorrow bc; ty }
    | VLoan lc0, VLoan lc1 ->
        (* TODO: maybe we should enforce that the ids are always exactly the same -
           without matching *)
        let lc =
          match (lc0, lc1) with
          | VSharedLoan (ids0, sv0), VSharedLoan (ids1, sv1) ->
              let sv = match_rec sv0 sv1 in
              cassert __FILE__ __LINE__
                (not (value_has_borrows sv.value))
                M.span "The join of nested borrows is not supported yet";
              let ids, sv = M.match_shared_loans ctx0 ctx1 ty ids0 ids1 sv in
              VSharedLoan (ids, sv)
          | VMutLoan id0, VMutLoan id1 ->
              let id = M.match_mut_loans ctx0 ctx1 ty id0 id1 in
              VMutLoan id
          | VSharedLoan _, VMutLoan _ | VMutLoan _, VSharedLoan _ ->
              craise __FILE__ __LINE__ M.span "Unreachable"
        in
        { value = VLoan lc; ty = v1.ty }
    | VSymbolic sv0, VSymbolic sv1 ->
        (* For now, we force all the symbolic values containing borrows to
           be eagerly expanded, and we don't support nested borrows *)
        cassert __FILE__ __LINE__
          (not (value_has_borrows v0.value))
          M.span
          "Nested borrows are not supported yet and all the symbolic values \
           containing borrows are currently forced to be eagerly expanded";
        cassert __FILE__ __LINE__
          (not (value_has_borrows v1.value))
          M.span
          "Nested borrows are not supported yet and all the symbolic values \
           containing borrows are currently forced to be eagerly expanded";
        (* Match *)
        let sv = M.match_symbolic_values ctx0 ctx1 sv0 sv1 in
        { v1 with value = VSymbolic sv }
    | VLoan lc, _ -> (
        match lc with
        | VSharedLoan (ids, _) -> raise (ValueMatchFailure (LoansInLeft ids))
        | VMutLoan id -> raise (ValueMatchFailure (LoanInLeft id)))
    | _, VLoan lc -> (
        match lc with
        | VSharedLoan (ids, _) -> raise (ValueMatchFailure (LoansInRight ids))
        | VMutLoan id -> raise (ValueMatchFailure (LoanInRight id)))
    | VSymbolic sv, _ -> M.match_symbolic_with_other ctx0 ctx1 true sv v1
    | _, VSymbolic sv -> M.match_symbolic_with_other ctx0 ctx1 false sv v0
    | VBottom, _ -> M.match_bottom_with_other ctx0 ctx1 true v1
    | _, VBottom -> M.match_bottom_with_other ctx0 ctx1 false v0
    | _ ->
        log#ldebug
          (lazy
            ("Unexpected match case:\n- value0: "
            ^ typed_value_to_string ~span:(Some M.span) ctx0 v0
            ^ "\n- value1: "
            ^ typed_value_to_string ~span:(Some M.span) ctx1 v1));
        craise __FILE__ __LINE__ M.span "Unexpected match case"

  and match_typed_avalues (ctx0 : eval_ctx) (ctx1 : eval_ctx)
      (v0 : typed_avalue) (v1 : typed_avalue) : typed_avalue =
    log#ldebug
      (lazy
        ("match_typed_avalues:\n- value0: "
        ^ typed_avalue_to_string ~span:(Some M.span) ctx0 v0
        ^ "\n- value1: "
        ^ typed_avalue_to_string ~span:(Some M.span) ctx1 v1));

    (* Using ValuesUtils.value_has_borrows on purpose here: we want
       to make explicit the fact that, though we have to pick
       one of the two contexts (ctx0 here) to call value_has_borrows,
       it doesn't matter here. *)
    let value_has_borrows =
      ValuesUtils.value_has_borrows ctx0.type_ctx.type_infos
    in

    let match_rec = match_typed_values ctx0 ctx1 in
    let match_arec = match_typed_avalues ctx0 ctx1 in
    let ty = M.match_rtys ctx0 ctx1 v0.ty v1.ty in
    match (v0.value, v1.value) with
    | AAdt av0, AAdt av1 ->
        if av0.variant_id = av1.variant_id then
          let fields = List.combine av0.field_values av1.field_values in
          let field_values =
            List.map (fun (f0, f1) -> match_arec f0 f1) fields
          in
          let value : avalue =
            AAdt { variant_id = av0.variant_id; field_values }
          in
          { value; ty }
        else (* Merge *)
          M.match_distinct_aadts ctx0 ctx1 v0.ty av0 v1.ty av1 ty
    | ABottom, ABottom -> mk_abottom M.span ty
    | AIgnored, AIgnored -> mk_aignored M.span ty
    | ABorrow bc0, ABorrow bc1 -> (
        log#ldebug (lazy "match_typed_avalues: borrows");
        match (bc0, bc1) with
        | ASharedBorrow (pm0, bid0), ASharedBorrow (pm1, bid1) ->
            log#ldebug (lazy "match_typed_avalues: shared borrows");
            M.match_ashared_borrows ctx0 ctx1 v0.ty pm0 bid0 v1.ty pm1 bid1 ty
        | AMutBorrow (pm0, bid0, av0), AMutBorrow (pm1, bid1, av1) ->
            log#ldebug (lazy "match_typed_avalues: mut borrows");
            log#ldebug
              (lazy
                "match_typed_avalues: mut borrows: matching children values");
            let av = match_arec av0 av1 in
            log#ldebug
              (lazy "match_typed_avalues: mut borrows: matched children values");
            M.match_amut_borrows ctx0 ctx1 v0.ty pm0 bid0 av0 v1.ty pm1 bid1 av1
              ty av
        | AIgnoredMutBorrow _, AIgnoredMutBorrow _ ->
            (* The abstractions are destructured: we shouldn't get there *)
            craise __FILE__ __LINE__ M.span "Unexpected"
        | AProjSharedBorrow asb0, AProjSharedBorrow asb1 -> (
            match (asb0, asb1) with
            | [], [] ->
                (* This case actually stands for ignored shared borrows, when
                   there are no nested borrows *)
                v0
            | _ ->
                (* We should get there only if there are nested borrows *)
                craise __FILE__ __LINE__ M.span "Unexpected")
        | _ ->
            (* TODO: getting there is not necessarily inconsistent (it may
               just be because the environments don't match) so we may want
               to call a specific function (which could raise the proper
               exception).
               Rem.: we shouldn't get to the ended borrow cases, because
               an abstraction should never contain ended borrows unless
               we are *currently* ending it, in which case we need
               to completely end it before continuing.
            *)
            craise __FILE__ __LINE__ M.span "Unexpected")
    | ALoan lc0, ALoan lc1 -> (
        log#ldebug (lazy "match_typed_avalues: loans");
        (* TODO: maybe we should enforce that the ids are always exactly the same -
           without matching *)
        match (lc0, lc1) with
        | ASharedLoan (pm0, ids0, sv0, av0), ASharedLoan (pm1, ids1, sv1, av1)
          ->
            log#ldebug (lazy "match_typed_avalues: shared loans");
            let sv = match_rec sv0 sv1 in
            let av = match_arec av0 av1 in
            sanity_check __FILE__ __LINE__
              (not (value_has_borrows sv.value))
              M.span;
            M.match_ashared_loans ctx0 ctx1 v0.ty pm0 ids0 sv0 av0 v1.ty pm1
              ids1 sv1 av1 ty sv av
        | AMutLoan (pm0, id0, av0), AMutLoan (pm1, id1, av1) ->
            log#ldebug (lazy "match_typed_avalues: mut loans");
            log#ldebug
              (lazy "match_typed_avalues: mut loans: matching children values");
            let av = match_arec av0 av1 in
            log#ldebug
              (lazy "match_typed_avalues: mut loans: matched children values");
            M.match_amut_loans ctx0 ctx1 v0.ty pm0 id0 av0 v1.ty pm1 id1 av1 ty
              av
        | AIgnoredMutLoan _, AIgnoredMutLoan _
        | AIgnoredSharedLoan _, AIgnoredSharedLoan _ ->
            (* Those should have been filtered when destructuring the abstractions -
               they are necessary only when there are nested borrows *)
            craise __FILE__ __LINE__ M.span "Unreachable"
        | _ -> craise __FILE__ __LINE__ M.span "Unreachable")
    | ASymbolic _, ASymbolic _ ->
        (* For now, we force all the symbolic values containing borrows to
           be eagerly expanded, and we don't support nested borrows *)
        craise __FILE__ __LINE__ M.span "Unreachable"
    | _ -> M.match_avalues ctx0 ctx1 v0 v1
end

module MakeJoinMatcher (S : MatchJoinState) : PrimMatcher = struct
  (** Small utility *)
  let span = S.span

  let push_abs (abs : abs) : unit = S.nabs := abs :: !S.nabs
  let push_absl (absl : abs list) : unit = List.iter push_abs absl

  let match_etys _ _ ty0 ty1 =
    sanity_check __FILE__ __LINE__ (ty0 = ty1) span;
    ty0

  let match_rtys _ _ ty0 ty1 =
    (* The types must be equal - in effect, this forbids to match symbolic
       values containing borrows *)
    sanity_check __FILE__ __LINE__ (ty0 = ty1) span;
    ty0

  let match_distinct_literals (_ : eval_ctx) (_ : eval_ctx) (ty : ety)
      (_ : literal) (_ : literal) : typed_value =
    mk_fresh_symbolic_typed_value_from_no_regions_ty span ty

  let match_distinct_adts (ctx0 : eval_ctx) (ctx1 : eval_ctx) (ty : ety)
      (adt0 : adt_value) (adt1 : adt_value) : typed_value =
    (* Check that the ADTs don't contain borrows - this is redundant with checks
       performed by the caller, but we prefer to be safe with regards to future
       updates
    *)
    let check_no_borrows ctx (v : typed_value) =
      sanity_check __FILE__ __LINE__ (not (value_has_borrows ctx v.value)) span
    in
    List.iter (check_no_borrows ctx0) adt0.field_values;
    List.iter (check_no_borrows ctx1) adt1.field_values;

    (* Check if there are loans: we request to end them *)
    let check_loans (left : bool) (fields : typed_value list) : unit =
      match InterpreterBorrowsCore.get_first_loan_in_values fields with
      | Some (VSharedLoan (ids, _)) ->
          if left then raise (ValueMatchFailure (LoansInLeft ids))
          else raise (ValueMatchFailure (LoansInRight ids))
      | Some (VMutLoan id) ->
          if left then raise (ValueMatchFailure (LoanInLeft id))
          else raise (ValueMatchFailure (LoanInRight id))
      | None -> ()
    in
    check_loans true adt0.field_values;
    check_loans false adt1.field_values;

    (* If there is a bottom in one of the two values, return bottom: *)
    if
      bottom_in_adt_value ctx0.ended_regions adt0
      || bottom_in_adt_value ctx1.ended_regions adt1
    then mk_bottom span ty
    else
      (* No borrows, no loans, no bottoms: we can introduce a symbolic value *)
      mk_fresh_symbolic_typed_value_from_no_regions_ty span ty

  let match_shared_borrows (ctx0 : eval_ctx) (ctx1 : eval_ctx) match_rec
      (ty : ety) (bid0 : borrow_id) (bid1 : borrow_id) : borrow_id =
    (* Lookup the shared values and match them - we do this mostly
       to make sure we end loans which might appear on one side
       and not on the other. *)
    let sv0 = lookup_shared_value span ctx0 bid0 in
    let sv1 = lookup_shared_value span ctx1 bid1 in
    let sv = match_rec sv0 sv1 in
    if bid0 = bid1 then bid0
    else
      (* We replace bid0 and bid1 with a fresh borrow id, and introduce
         an abstraction which links all of them:
         {[
           { SB bid0, SB bid1, SL {bid2} }
         ]}
      *)
      let rid = fresh_region_id () in
      let bid2 = fresh_borrow_id () in

      (* Update the type of the shared loan to use the fresh region *)
      let _, bv_ty, kind = ty_as_ref ty in
      let borrow_ty = mk_ref_ty (RFVar rid) bv_ty kind in

      (* Generate the avalues for the abstraction *)
      let mk_aborrow (bid : borrow_id) : typed_avalue =
        let value = ABorrow (ASharedBorrow (PNone, bid)) in
        { value; ty = borrow_ty }
      in
      let borrows = [ mk_aborrow bid0; mk_aborrow bid1 ] in

      let loan =
        ASharedLoan
          (PNone, BorrowId.Set.singleton bid2, sv, mk_aignored span bv_ty)
      in
      (* Note that an aloan has a borrow type *)
      let loan : typed_avalue = { value = ALoan loan; ty = borrow_ty } in

      let avalues = List.append borrows [ loan ] in

      (* Generate the abstraction *)
      let abs =
        {
          abs_id = fresh_abstraction_id ();
          kind = Loop (S.loop_id, None, LoopSynthInput);
          can_end = true;
          parents = AbstractionId.Set.empty;
          original_parents = [];
          regions = RegionId.Set.singleton rid;
          ancestors_regions = RegionId.Set.empty;
          avalues;
        }
      in
      push_abs abs;

      (* Return the new borrow *)
      bid2

  let match_mut_borrows (ctx0 : eval_ctx) (_ : eval_ctx) (ty : ety)
      (bid0 : borrow_id) (bv0 : typed_value) (bid1 : borrow_id)
      (bv1 : typed_value) (bv : typed_value) : borrow_id * typed_value =
    if bid0 = bid1 then (
      (* If the merged value is not the same as the original value, we introduce
         an abstraction:

         {[
           { MB bid0, ML nbid }  // where nbid fresh
         ]}

         and we use bid' for the borrow id that we return.

         We do this because we want to make sure that, whenever a mutably
         borrowed value is modified in a loop iteration, then there is
         a fresh abstraction between this borrowed value and the fixed
         abstractions.

         Example:
         ========
         {[
           fn clear(v: &mut Vec<u32>) {
               let mut i = 0;
               while i < v.len() {
                   v[i] = 0;
                   i += 1;
               }
           }
         ]}

         When entering the loop, we have the following environment:
         {[
           abs'0 { ML l0 } // input abstraction
           v -> MB l0 s0
           i -> 0
         ]}

         At every iteration, we update the symbolic value of the vector [v]
         (i.e., [s0]).

         For now, because the translation of the loop is responsible of the
         execution of the end of the function (up to the [return]), we want
         the loop to reborrow the vector [v]: this way, the forward loop
         function returns nothing (it returns what [clear] returns, that is
         to say [unit]) while the backward loop function gives back a new value
         for [v] (i.e., a new symbolic value which will replace [s0]).

         In the future, we will also compute joins at the *loop exits*: when we
         do so, we won't introduce reborrows like above: the forward loop function
         will update [v], while the backward loop function will return nothing.
      *)
      cassert __FILE__ __LINE__
        (not (ValuesUtils.value_has_borrows ctx0.type_ctx.type_infos bv.value))
        span "Nested borrows are not supported yet";

      if bv0 = bv1 then (
        sanity_check __FILE__ __LINE__ (bv0 = bv) span;
        (bid0, bv))
      else
        let rid = fresh_region_id () in
        let nbid = fresh_borrow_id () in

        let kind = RMut in
        let bv_ty = bv.ty in
        sanity_check __FILE__ __LINE__ (ty_no_regions bv_ty) span;
        let borrow_ty = mk_ref_ty (RFVar rid) bv_ty kind in

        let borrow_av =
          let ty = borrow_ty in
          let value =
            ABorrow (AMutBorrow (PNone, bid0, mk_aignored span bv_ty))
          in
          mk_typed_avalue span ty value
        in

        let loan_av =
          let ty = borrow_ty in
          let value = ALoan (AMutLoan (PNone, nbid, mk_aignored span bv_ty)) in
          mk_typed_avalue span ty value
        in

        let avalues = [ borrow_av; loan_av ] in

        (* Generate the abstraction *)
        let abs =
          {
            abs_id = fresh_abstraction_id ();
            kind = Loop (S.loop_id, None, LoopSynthInput);
            can_end = true;
            parents = AbstractionId.Set.empty;
            original_parents = [];
            regions = RegionId.Set.singleton rid;
            ancestors_regions = RegionId.Set.empty;
            avalues;
          }
        in
        push_abs abs;

        (* Return the new borrow *)
        (nbid, bv))
    else
      (* We replace bid0 and bid1 with a fresh borrow id, and introduce
         an abstraction which links all of them:
         {[
           { MB bid0, MB bid1, ML bid2 }
         ]}
      *)
      let rid = fresh_region_id () in
      let bid2 = fresh_borrow_id () in

      (* Generate a fresh symbolic value for the borrowed value *)
      let _, bv_ty, kind = ty_as_ref ty in
      let sv = mk_fresh_symbolic_typed_value_from_no_regions_ty span bv_ty in

      let borrow_ty = mk_ref_ty (RFVar rid) bv_ty kind in

      (* Generate the avalues for the abstraction *)
      let mk_aborrow (bid : borrow_id) (bv : typed_value) : typed_avalue =
        let bv_ty = bv.ty in
        cassert __FILE__ __LINE__ (ty_no_regions bv_ty) span
          "Nested borrows are not supported yet";
        let value = ABorrow (AMutBorrow (PNone, bid, mk_aignored span bv_ty)) in
        { value; ty = borrow_ty }
      in
      let borrows = [ mk_aborrow bid0 bv0; mk_aborrow bid1 bv1 ] in

      let loan = AMutLoan (PNone, bid2, mk_aignored span bv_ty) in
      (* Note that an aloan has a borrow type *)
      let loan : typed_avalue = { value = ALoan loan; ty = borrow_ty } in

      let avalues = List.append borrows [ loan ] in

      (* Generate the abstraction *)
      let abs =
        {
          abs_id = fresh_abstraction_id ();
          kind = Loop (S.loop_id, None, LoopSynthInput);
          can_end = true;
          parents = AbstractionId.Set.empty;
          original_parents = [];
          regions = RegionId.Set.singleton rid;
          ancestors_regions = RegionId.Set.empty;
          avalues;
        }
      in
      push_abs abs;

      (* Return the new borrow *)
      (bid2, sv)

  let match_shared_loans (_ : eval_ctx) (_ : eval_ctx) (_ : ety)
      (ids0 : loan_id_set) (ids1 : loan_id_set) (sv : typed_value) :
      loan_id_set * typed_value =
    (* Check if the ids are the same - Rem.: we forbid the sets of loans
       to be different. However, if we dive inside data-structures (by
       using a shared borrow) the shared values might themselves contain
       shared loans, which need to be matched. For this reason, we destructure
       the shared values (see {!destructure_abs}).
    *)
    let extra_ids_left = BorrowId.Set.diff ids0 ids1 in
    let extra_ids_right = BorrowId.Set.diff ids1 ids0 in
    if not (BorrowId.Set.is_empty extra_ids_left) then
      raise (ValueMatchFailure (LoansInLeft extra_ids_left));
    if not (BorrowId.Set.is_empty extra_ids_right) then
      raise (ValueMatchFailure (LoansInRight extra_ids_right));

    (* This should always be true if we get here *)
    sanity_check __FILE__ __LINE__ (ids0 = ids1) span;
    let ids = ids0 in

    (* Return *)
    (ids, sv)

  let match_mut_loans (_ : eval_ctx) (_ : eval_ctx) (_ : ety) (id0 : loan_id)
      (id1 : loan_id) : loan_id =
    if id0 = id1 then id0
    else
      (* We forbid this case for now: if we get there, we force to end
         both borrows *)
      raise (ValueMatchFailure (LoanInLeft id0))

  let match_symbolic_values (ctx0 : eval_ctx) (ctx1 : eval_ctx)
      (sv0 : symbolic_value) (sv1 : symbolic_value) : symbolic_value =
    let id0 = sv0.sv_id in
    let id1 = sv1.sv_id in
    if id0 = id1 then (
      (* Sanity check *)
      sanity_check __FILE__ __LINE__ (sv0 = sv1) span;
      (* Return *)
      sv0)
    else (
      (* The caller should have checked that the symbolic values don't contain
         borrows *)
      sanity_check __FILE__ __LINE__
        (not (ty_has_borrows ctx0.type_ctx.type_infos sv0.sv_ty))
        span;
      (* TODO: the symbolic values may contain bottoms: we're being conservatice,
         and fail (for now) if part of a symbolic value contains a bottom.
         A more general approach would be to introduce a symbolic value
         with some ended regions. *)
      sanity_check __FILE__ __LINE__
        ((not (symbolic_value_has_ended_regions ctx0.ended_regions sv0))
        && not (symbolic_value_has_ended_regions ctx1.ended_regions sv1))
        span;
      mk_fresh_symbolic_value span sv0.sv_ty)

  let match_symbolic_with_other (ctx0 : eval_ctx) (ctx1 : eval_ctx)
      (left : bool) (sv : symbolic_value) (v : typed_value) : typed_value =
    (* Check that:
       - there are no borrows in the symbolic value
       - there are no borrows in the "regular" value
       If there are loans in the regular value, raise an exception.
    *)
    let type_infos = ctx0.type_ctx.type_infos in
    cassert __FILE__ __LINE__
      (not (ty_has_borrows type_infos sv.sv_ty))
      span
      "Check that:\n\
      \    - there are no borrows in the symbolic value\n\
      \    - there are no borrows in the \"regular\" value\n\
      \    If there are loans in the regular value, raise an exception.";
    cassert __FILE__ __LINE__
      (not (ValuesUtils.value_has_borrows type_infos v.value))
      span
      "Check that:\n\
      \    - there are no borrows in the symbolic value\n\
      \    - there are no borrows in the \"regular\" value\n\
      \    If there are loans in the regular value, raise an exception.";
    let value_is_left = not left in
    (match InterpreterBorrowsCore.get_first_loan_in_value v with
    | None -> ()
    | Some (VSharedLoan (ids, _)) ->
        if value_is_left then raise (ValueMatchFailure (LoansInLeft ids))
        else raise (ValueMatchFailure (LoansInRight ids))
    | Some (VMutLoan id) ->
        if value_is_left then raise (ValueMatchFailure (LoanInLeft id))
        else raise (ValueMatchFailure (LoanInRight id)));

    (* There might be a bottom in the other value. We're being conservative:
       if there is a bottom anywhere (it includes the case where part of the
       value contains bottom) the result of the join is bottom. Otherwise,
       we generate a fresh symbolic value. *)
    if
      symbolic_value_has_ended_regions ctx0.ended_regions sv
      || bottom_in_value ctx1.ended_regions v
    then mk_bottom span sv.sv_ty
    else mk_fresh_symbolic_typed_value span sv.sv_ty

  let match_bottom_with_other (ctx0 : eval_ctx) (ctx1 : eval_ctx) (left : bool)
      (v : typed_value) : typed_value =
    (* If there are outer loans in the non-bottom value, raise an exception.
       Otherwise, convert it to an abstraction and return [Bottom].
    *)
    let with_borrows = false in
    let value_is_left = not left in
    match
      InterpreterBorrowsCore.get_first_outer_loan_or_borrow_in_value
        with_borrows v
    with
    | Some (BorrowContent _) ->
        (* Can't get there: we only ask for outer *loans* *)
        craise __FILE__ __LINE__ span "Unreachable"
    | Some (LoanContent lc) -> (
        match lc with
        | VSharedLoan (ids, _) ->
            if value_is_left then raise (ValueMatchFailure (LoansInLeft ids))
            else raise (ValueMatchFailure (LoansInRight ids))
        | VMutLoan id ->
            if value_is_left then raise (ValueMatchFailure (LoanInLeft id))
            else raise (ValueMatchFailure (LoanInRight id)))
    | None ->
        (*   *)

        (* Convert the value to an abstraction *)
        let abs_kind : abs_kind = Loop (S.loop_id, None, LoopSynthInput) in
        let can_end = true in
        let destructure_shared_values = true in
        let ctx = if value_is_left then ctx0 else ctx1 in
        let absl =
          convert_value_to_abstractions span abs_kind can_end
            destructure_shared_values ctx v
        in
        push_absl absl;
        (* Return [Bottom] *)
        mk_bottom span v.ty

  (* As explained in comments: we don't use the join matcher to join avalues,
     only concrete values *)

  let match_distinct_aadts _ _ _ _ _ _ _ =
    craise __FILE__ __LINE__ span "Unreachable"

  let match_ashared_borrows _ _ _ _ _ _ =
    craise __FILE__ __LINE__ span "Unreachable"

  let match_amut_borrows _ _ _ _ _ _ _ _ _ _ =
    craise __FILE__ __LINE__ span "Unreachable"

  let match_ashared_loans _ _ _ _ _ _ _ _ _ _ _ _ _ =
    craise __FILE__ __LINE__ span "Unreachable"

  let match_amut_loans _ _ _ _ _ _ _ _ _ _ =
    craise __FILE__ __LINE__ span "Unreachable"

  let match_avalues _ _ _ _ = craise __FILE__ __LINE__ span "Unreachable"
end

(* Very annoying: functors only take modules as inputs... *)
module type MatchMoveState = sig
  val span : Meta.span

  (** The current loop *)
  val loop_id : LoopId.id

  (** The moved values *)
  val nvalues : typed_value list ref
end

(* We use this matcher to move values in environment.

   To be more precise, we use this to update the target environment
   (typically, the environment we have when we reach a continue statement)
   by moving values into anonymous variables when the matched value
   coming from the source environment (typically, a loop fixed-point)
   is a bottom.

   Importantly, put aside the case where the source value is bottom
   and the target value is not bottom, we always return the target value.

   Also note that the role of this matcher is simply to perform a reorganization:
   the resulting environment will be matched again with the source.
   This means that it is ok if we are not sure if the source environment
   indeed matches the resulting target environment: it will be re-checked later.
*)
module MakeMoveMatcher (S : MatchMoveState) : PrimMatcher = struct
  let span = S.span

  (** Small utility *)
  let push_moved_value (v : typed_value) : unit = S.nvalues := v :: !S.nvalues

  let match_etys _ _ ty0 ty1 =
    sanity_check __FILE__ __LINE__ (ty0 = ty1) span;
    ty0

  let match_rtys _ _ ty0 ty1 =
    (* The types must be equal - in effect, this forbids to match symbolic
       values containing borrows *)
    sanity_check __FILE__ __LINE__ (ty0 = ty1) span;
    ty0

  let match_distinct_literals (_ : eval_ctx) (_ : eval_ctx) (ty : ety)
      (_ : literal) (l : literal) : typed_value =
    { value = VLiteral l; ty }

  let match_distinct_adts (_ : eval_ctx) (_ : eval_ctx) (ty : ety)
      (_ : adt_value) (adt1 : adt_value) : typed_value =
    (* Note that if there was a bottom inside the ADT on the left,
       the value on the left should have been simplified to bottom. *)
    { ty; value = VAdt adt1 }

  let match_shared_borrows (_ : eval_ctx) (_ : eval_ctx) _ (_ : ety)
      (_ : borrow_id) (bid1 : borrow_id) : borrow_id =
    (* There can't be bottoms in shared values *)
    bid1

  let match_mut_borrows (_ : eval_ctx) (_ : eval_ctx) (_ : ety) (_ : borrow_id)
      (_ : typed_value) (bid1 : borrow_id) (bv1 : typed_value) (_ : typed_value)
      : borrow_id * typed_value =
    (* There can't be bottoms in borrowed values *)
    (bid1, bv1)

  let match_shared_loans (_ : eval_ctx) (_ : eval_ctx) (_ : ety)
      (_ : loan_id_set) (ids1 : loan_id_set) (sv : typed_value) :
      loan_id_set * typed_value =
    (* There can't be bottoms in shared loans *)
    (ids1, sv)

  let match_mut_loans (_ : eval_ctx) (_ : eval_ctx) (_ : ety) (_ : loan_id)
      (id1 : loan_id) : loan_id =
    id1

  let match_symbolic_values (_ : eval_ctx) (_ : eval_ctx) (_ : symbolic_value)
      (sv1 : symbolic_value) : symbolic_value =
    sv1

  let match_symbolic_with_other (ctx0 : eval_ctx) (ctx1 : eval_ctx)
      (left : bool) (sv : symbolic_value) (v : typed_value) : typed_value =
    (* We're being conservative for now: if any of the two values contains
       a bottom, the join is bottom *)
    if
      symbolic_value_has_ended_regions ctx0.ended_regions sv
      || bottom_in_value ctx1.ended_regions v
    then mk_bottom span sv.sv_ty
    else if left then v
    else mk_typed_value_from_symbolic_value sv

  let match_bottom_with_other (_ : eval_ctx) (_ : eval_ctx) (left : bool)
      (v : typed_value) : typed_value =
    let with_borrows = false in
    if left then (
      (* The bottom is on the left *)
      (* Small sanity check *)
      match
        InterpreterBorrowsCore.get_first_outer_loan_or_borrow_in_value
          with_borrows v
      with
      | Some (BorrowContent _) ->
          (* Can't get there: we only ask for outer *loans* *)
          craise __FILE__ __LINE__ span "Unreachable"
      | Some (LoanContent _) ->
          (* We should have ended all the outer loans *)
          craise __FILE__ __LINE__ span "Unexpected outer loan"
      | None ->
          (* Move the value - note that we shouldn't get there if we
             were not allowed to move the value in the first place. *)
          push_moved_value v;
          (* Return [Bottom] *)
          mk_bottom span v.ty)
    else
      (* If we get there it means the source environment (e.g., the
         fixed-point) has a non-bottom value, while the target environment
         (e.g., the environment we have when we reach the continue)
         has bottom: we shouldn't get there. *)
      craise __FILE__ __LINE__ span "Unreachable"

  (* As explained in comments: we don't use the join matcher to join avalues,
     only concrete values *)

  let match_distinct_aadts _ _ _ _ _ _ _ =
    craise __FILE__ __LINE__ span "Unreachable"

  let match_ashared_borrows _ _ _ _ _ _ =
    craise __FILE__ __LINE__ span "Unreachable"

  let match_amut_borrows _ _ _ _ _ _ _ _ _ =
    craise __FILE__ __LINE__ span "Unreachable"

  let match_ashared_loans _ _ _ _ _ _ _ _ _ _ _ _ _ =
    craise __FILE__ __LINE__ span "Unreachable"

  let match_amut_loans _ _ _ _ _ _ _ _ _ _ =
    craise __FILE__ __LINE__ span "Unreachable"

  let match_avalues _ _ _ _ = craise __FILE__ __LINE__ span "Unreachable"
end

module MakeCheckEquivMatcher (S : MatchCheckEquivState) : CheckEquivMatcher =
struct
  let span = S.span

  module MkGetSetM (Id : Identifiers.Id) = struct
    module Inj = Id.InjSubst

    let add (msg : string) (m : Inj.t ref) (k0 : Id.id) (k1 : Id.id) =
      (* Check if k0 is already registered as a key *)
      match Inj.find_opt k0 !m with
      | None ->
          (* Not registered: check if k1 is in the set of values,
             otherwise add the binding *)
          if Inj.Set.mem k1 (Inj.elements !m) then
            raise
              (Distinct
                 (msg ^ "adding [k0=" ^ Id.to_string k0 ^ " -> k1="
                ^ Id.to_string k1 ^ " ]: k1 already in the set of elements"))
          else (
            m := Inj.add k0 k1 !m;
            k1)
      | Some k1' ->
          (* It is: check that the bindings are consistent *)
          if k1 <> k1' then raise (Distinct (msg ^ "already a binding for k0"))
          else k1

    let match_e (msg : string) (m : Inj.t ref) (k0 : Id.id) (k1 : Id.id) : Id.id
        =
      (* TODO: merge the add and merge functions *)
      add msg m k0 k1

    let match_el (msg : string) (m : Inj.t ref) (kl0 : Id.id list)
        (kl1 : Id.id list) : Id.id list =
      List.map (fun (k0, k1) -> match_e msg m k0 k1) (List.combine kl0 kl1)

    (** Figuring out mappings between sets of ids is hard in all generality...
        We use the fact that the fresh ids should have been generated
        the same way (i.e., in the same order) and match the ids two by
        two in increasing order.
     *)
    let match_es (msg : string) (m : Inj.t ref) (ks0 : Id.Set.t)
        (ks1 : Id.Set.t) : Id.Set.t =
      Id.Set.of_list
        (match_el msg m (Id.Set.elements ks0) (Id.Set.elements ks1))
  end

  module GetSetRid = MkGetSetM (RegionId)

  let match_rid = GetSetRid.match_e "match_rid: " S.rid_map
  let match_rids = GetSetRid.match_es "match_rids: " S.rid_map

  module GetSetBid = MkGetSetM (BorrowId)

  let match_blid msg = GetSetBid.match_e msg S.blid_map
  let match_blidl msg = GetSetBid.match_el msg S.blid_map
  let match_blids msg = GetSetBid.match_es msg S.blid_map

  let match_borrow_id =
    if S.check_equiv then match_blid "match_borrow_id: "
    else GetSetBid.match_e "match_borrow_id: " S.borrow_id_map

  let match_borrow_idl =
    if S.check_equiv then match_blidl "match_borrow_idl: "
    else GetSetBid.match_el "match_borrow_idl: " S.borrow_id_map

  let match_borrow_ids =
    if S.check_equiv then match_blids "match_borrow_ids: "
    else GetSetBid.match_es "match_borrow_ids: " S.borrow_id_map

  let match_loan_id =
    if S.check_equiv then match_blid "match_loan_id: "
    else GetSetBid.match_e "match_loan_id: " S.loan_id_map

  let match_loan_idl =
    if S.check_equiv then match_blidl "match_loan_idl: "
    else GetSetBid.match_el "match_loan_idl: " S.loan_id_map

  let match_loan_ids =
    if S.check_equiv then match_blids "match_loan_ids: "
    else GetSetBid.match_es "match_loan_ids: " S.loan_id_map

  module GetSetSid = MkGetSetM (SymbolicValueId)
  module GetSetAid = MkGetSetM (AbstractionId)

  let match_aid = GetSetAid.match_e "match_aid: " S.aid_map
  let match_aidl = GetSetAid.match_el "match_aidl: " S.aid_map
  let match_aids = GetSetAid.match_es "match_aids: " S.aid_map

  (** *)
  let match_etys (_ : eval_ctx) (_ : eval_ctx) ty0 ty1 =
    if ty0 <> ty1 then raise (Distinct "match_etys") else ty0

  let match_rtys (_ : eval_ctx) (_ : eval_ctx) ty0 ty1 =
    let match_distinct_types _ _ = raise (Distinct "match_rtys") in
    let match_regions r0 r1 =
      match (r0, r1) with
      | RStatic, RStatic -> r1
      | RFVar rid0, RFVar rid1 ->
          let rid = match_rid rid0 rid1 in
          RFVar rid
      | _ -> raise (Distinct "match_rtys")
    in
    match_types span match_distinct_types match_regions ty0 ty1

  let match_distinct_literals (_ : eval_ctx) (_ : eval_ctx) (ty : ety)
      (_ : literal) (_ : literal) : typed_value =
    mk_fresh_symbolic_typed_value_from_no_regions_ty span ty

  let match_distinct_adts (_ : eval_ctx) (_ : eval_ctx) (_ty : ety)
      (_adt0 : adt_value) (_adt1 : adt_value) : typed_value =
    raise (Distinct "match_distinct_adts")

  let match_shared_borrows (ctx0 : eval_ctx) (ctx1 : eval_ctx)
      (match_typed_values : typed_value -> typed_value -> typed_value)
      (_ty : ety) (bid0 : borrow_id) (bid1 : borrow_id) : borrow_id =
    log#ldebug
      (lazy
        ("MakeCheckEquivMatcher: match_shared_borrows: " ^ "bid0: "
       ^ BorrowId.to_string bid0 ^ ", bid1: " ^ BorrowId.to_string bid1));

    let bid = match_borrow_id bid0 bid1 in
    (* If we don't check for equivalence (i.e., we apply a fixed-point),
       we lookup the shared values and match them.
    *)
    let _ =
      if S.check_equiv then ()
      else
        let v0 = S.lookup_shared_value_in_ctx0 bid0 in
        let v1 = S.lookup_shared_value_in_ctx1 bid1 in
        log#ldebug
          (lazy
            ("MakeCheckEquivMatcher: match_shared_borrows: looked up values:"
           ^ "sv0: "
            ^ typed_value_to_string ~span:(Some span) ctx0 v0
            ^ ", sv1: "
            ^ typed_value_to_string ~span:(Some span) ctx1 v1));

        let _ = match_typed_values v0 v1 in
        ()
    in
    bid

  let match_mut_borrows (_ : eval_ctx) (_ : eval_ctx) (_ty : ety)
      (bid0 : borrow_id) (_bv0 : typed_value) (bid1 : borrow_id)
      (_bv1 : typed_value) (bv : typed_value) : borrow_id * typed_value =
    let bid = match_borrow_id bid0 bid1 in
    (bid, bv)

  let match_shared_loans (_ : eval_ctx) (_ : eval_ctx) (_ : ety)
      (ids0 : loan_id_set) (ids1 : loan_id_set) (sv : typed_value) :
      loan_id_set * typed_value =
    let ids = match_loan_ids ids0 ids1 in
    (ids, sv)

  let match_mut_loans (_ : eval_ctx) (_ : eval_ctx) (_ : ety) (bid0 : loan_id)
      (bid1 : loan_id) : loan_id =
    match_loan_id bid0 bid1

  let match_symbolic_values (ctx0 : eval_ctx) (ctx1 : eval_ctx)
      (sv0 : symbolic_value) (sv1 : symbolic_value) : symbolic_value =
    let id0 = sv0.sv_id in
    let id1 = sv1.sv_id in

    log#ldebug
      (lazy
        ("MakeCheckEquivMatcher: match_symbolic_values: " ^ "sv0: "
        ^ SymbolicValueId.to_string id0
        ^ ", sv1: "
        ^ SymbolicValueId.to_string id1));

    (* If we don't check for equivalence, we also update the map from sids
       to values *)
    if S.check_equiv then
      (* Create the joined symbolic value *)
      let sv_id =
        GetSetSid.match_e "match_symbolic_values: ids: " S.sid_map id0 id1
      in
      let sv_ty = match_rtys ctx0 ctx1 sv0.sv_ty sv1.sv_ty in
      let sv = { sv_id; sv_ty } in
      sv
    else (
      (* Check: fixed values are fixed *)
      sanity_check __FILE__ __LINE__
        (id0 = id1 || not (SymbolicValueId.InjSubst.mem id0 !S.sid_map))
        span;

      (* Update the symbolic value mapping *)
      let sv1 = mk_typed_value_from_symbolic_value sv1 in

      (* Update the symbolic value mapping *)
      S.sid_to_value_map :=
        SymbolicValueId.Map.add_strict id0 sv1 !S.sid_to_value_map;

      (* Return - the returned value is not used: we can return  whatever
         we want *)
      sv0)

  let match_symbolic_with_other (_ : eval_ctx) (_ : eval_ctx) (left : bool)
      (sv : symbolic_value) (v : typed_value) : typed_value =
    if S.check_equiv then raise (Distinct "match_symbolic_with_other")
    else (
      sanity_check __FILE__ __LINE__ left span;
      let id = sv.sv_id in
      (* Check: fixed values are fixed *)
      sanity_check __FILE__ __LINE__
        (not (SymbolicValueId.InjSubst.mem id !S.sid_map))
        span;
      (* Update the binding for the target symbolic value *)
      S.sid_to_value_map :=
        SymbolicValueId.Map.add_strict id v !S.sid_to_value_map;
      (* Return - the returned value is not used, so we can return whatever we want *)
      v)

  let match_bottom_with_other (ctx0 : eval_ctx) (ctx1 : eval_ctx) (left : bool)
      (v : typed_value) : typed_value =
    (* It can happen that some variables get initialized in some branches
       and not in some others, which causes problems when matching. *)
    (* TODO: the returned value is not used, while it should: in generality it
       should be ok to match a fixed-point with the environment we get at
       a continue, where the fixed point contains some bottom values. *)
    let value_is_left = not left in
    let ctx = if value_is_left then ctx0 else ctx1 in
    if left && not (value_has_loans_or_borrows ctx v.value) then
      mk_bottom span v.ty
    else
      raise
        (Distinct
           ("match_bottom_with_other:\n- bottom value is in left environment: "
          ^ Print.bool_to_string left ^ "\n- value to match with bottom:\n"
          ^ show_typed_value v))

  let match_distinct_aadts _ _ _ _ _ _ _ =
    raise (Distinct "match_distinct_adts")

  let match_ashared_borrows (_ : eval_ctx) (_ : eval_ctx) _ty0 pm0 bid0 _ty1 pm1
      bid1 ty =
    sanity_check __FILE__ __LINE__ (pm0 = PNone && pm1 = PNone) span;
    let bid = match_borrow_id bid0 bid1 in
    let value = ABorrow (ASharedBorrow (PNone, bid)) in
    { value; ty }

  let match_amut_borrows (_ : eval_ctx) (_ : eval_ctx) _ty0 pm0 bid0 _av0 _ty1
      pm1 bid1 _av1 ty av =
    sanity_check __FILE__ __LINE__ (pm0 = PNone && pm1 = PNone) span;
    let bid = match_borrow_id bid0 bid1 in
    let value = ABorrow (AMutBorrow (PNone, bid, av)) in
    { value; ty }

  let match_ashared_loans (_ : eval_ctx) (_ : eval_ctx) _ty0 pm0 ids0 _v0 _av0
      _ty1 pm1 ids1 _v1 _av1 ty v av =
    sanity_check __FILE__ __LINE__ (pm0 = PNone && pm1 = PNone) span;
    let bids = match_loan_ids ids0 ids1 in
    let value = ALoan (ASharedLoan (PNone, bids, v, av)) in
    { value; ty }

  let match_amut_loans (ctx0 : eval_ctx) (ctx1 : eval_ctx) _ty0 pm0 id0 _av0
      _ty1 pm1 id1 _av1 ty av =
    sanity_check __FILE__ __LINE__ (pm0 = PNone && pm1 = PNone) span;
    log#ldebug
      (lazy
        ("MakeCheckEquivMatcher:match_amut_loans:" ^ "\n- id0: "
       ^ BorrowId.to_string id0 ^ "\n- id1: " ^ BorrowId.to_string id1
       ^ "\n- ty: " ^ ty_to_string ctx0 ty ^ "\n- av: "
        ^ typed_avalue_to_string ~span:(Some span) ctx1 av));

    let id = match_loan_id id0 id1 in
    let value = ALoan (AMutLoan (PNone, id, av)) in
    { value; ty }

  let match_avalues (ctx0 : eval_ctx) (ctx1 : eval_ctx) v0 v1 =
    log#ldebug
      (lazy
        ("avalues don't match:\n- v0: "
        ^ typed_avalue_to_string ~span:(Some span) ctx0 v0
        ^ "\n- v1: "
        ^ typed_avalue_to_string ~span:(Some span) ctx1 v1));
    raise (Distinct "match_avalues")
end

let match_ctxs (span : Meta.span) (check_equiv : bool) (fixed_ids : ids_sets)
    (lookup_shared_value_in_ctx0 : BorrowId.id -> typed_value)
    (lookup_shared_value_in_ctx1 : BorrowId.id -> typed_value) (ctx0 : eval_ctx)
    (ctx1 : eval_ctx) : ids_maps option =
  log#ldebug
    (lazy
      ("match_ctxs:\n\n- fixed_ids:\n" ^ show_ids_sets fixed_ids
     ^ "\n\n- ctx0:\n"
      ^ eval_ctx_to_string_no_filter ~span:(Some span) ctx0
      ^ "\n\n- ctx1:\n"
      ^ eval_ctx_to_string_no_filter ~span:(Some span) ctx1
      ^ "\n\n"));

  (* Initialize the maps and instantiate the matcher *)
  let module IdMap (Id : Identifiers.Id) = struct
    let mk_map_ref (ids : Id.Set.t) : Id.InjSubst.t ref =
      ref
        (Id.InjSubst.of_list (List.map (fun x -> (x, x)) (Id.Set.elements ids)))
  end in
  let rid_map =
    let module IdMap = IdMap (RegionId) in
    IdMap.mk_map_ref fixed_ids.rids
  in
  let blid_map =
    let module IdMap = IdMap (BorrowId) in
    IdMap.mk_map_ref fixed_ids.blids
  in
  let borrow_id_map =
    let module IdMap = IdMap (BorrowId) in
    IdMap.mk_map_ref fixed_ids.borrow_ids
  in
  let loan_id_map =
    let module IdMap = IdMap (BorrowId) in
    IdMap.mk_map_ref fixed_ids.loan_ids
  in
  let aid_map =
    let module IdMap = IdMap (AbstractionId) in
    IdMap.mk_map_ref fixed_ids.aids
  in
  let sid_map =
    let module IdMap = IdMap (SymbolicValueId) in
    IdMap.mk_map_ref fixed_ids.sids
  in
  (* In case we don't try to check equivalence but want to compute a mapping
     from a source context to a target context, we use a map from symbolic
     value ids to values (rather than to ids).
  *)
  let sid_to_value_map : typed_value SymbolicValueId.Map.t ref =
    ref SymbolicValueId.Map.empty
  in

  let module S : MatchCheckEquivState = struct
    let span = span
    let check_equiv = check_equiv
    let rid_map = rid_map
    let blid_map = blid_map
    let borrow_id_map = borrow_id_map
    let loan_id_map = loan_id_map
    let sid_map = sid_map
    let sid_to_value_map = sid_to_value_map
    let aid_map = aid_map
    let lookup_shared_value_in_ctx0 = lookup_shared_value_in_ctx0
    let lookup_shared_value_in_ctx1 = lookup_shared_value_in_ctx1
  end in
  let module CEM = MakeCheckEquivMatcher (S) in
  let module M = MakeMatcher (CEM) in
  (* Match the environments - we assume that they have the same structure
     (and fail if they don't) *)

  (* Small utility: check that ids are fixed/mapped to themselves *)
  let ids_are_fixed (ids : ids_sets) : bool =
    let { aids; blids = _; borrow_ids; loan_ids; dids; rids; sids } = ids in
    AbstractionId.Set.subset aids fixed_ids.aids
    && BorrowId.Set.subset borrow_ids fixed_ids.borrow_ids
    && BorrowId.Set.subset loan_ids fixed_ids.loan_ids
    && DummyVarId.Set.subset dids fixed_ids.dids
    && RegionId.Set.subset rids fixed_ids.rids
    && SymbolicValueId.Set.subset sids fixed_ids.sids
  in

  (* Rem.: this function raises exceptions of type [Distinct] *)
  let match_abstractions (abs0 : abs) (abs1 : abs) : unit =
    let {
      abs_id = abs_id0;
      kind = kind0;
      can_end = can_end0;
      parents = parents0;
      original_parents = original_parents0;
      regions = regions0;
      ancestors_regions = ancestors_regions0;
      avalues = avalues0;
    } =
      abs0
    in

    let {
      abs_id = abs_id1;
      kind = kind1;
      can_end = can_end1;
      parents = parents1;
      original_parents = original_parents1;
      regions = regions1;
      ancestors_regions = ancestors_regions1;
      avalues = avalues1;
    } =
      abs1
    in

    let _ = CEM.match_aid abs_id0 abs_id1 in
    if kind0 <> kind1 || can_end0 <> can_end1 then
      raise (Distinct "match_abstractions: kind or can_end");
    let _ = CEM.match_aids parents0 parents1 in
    let _ = CEM.match_aidl original_parents0 original_parents1 in
    let _ = CEM.match_rids regions0 regions1 in
    let _ = CEM.match_rids ancestors_regions0 ancestors_regions1 in

    log#ldebug (lazy "match_abstractions: matching values");
    let _ =
      List.map
        (fun (v0, v1) -> M.match_typed_avalues ctx0 ctx1 v0 v1)
        (List.combine avalues0 avalues1)
    in
    log#ldebug (lazy "match_abstractions: values matched OK");
    ()
  in

  (* Rem.: this function raises exceptions of type [Distinct] *)
  let rec match_envs (env0 : env) (env1 : env) : unit =
    log#ldebug
      (lazy
        ("match_ctxs: match_envs:\n\n- fixed_ids:\n" ^ show_ids_sets fixed_ids
       ^ "\n\n- rid_map: "
        ^ RegionId.InjSubst.show_t !rid_map
        ^ "\n- blid_map: "
        ^ BorrowId.InjSubst.show_t !blid_map
        ^ "\n- sid_map: "
        ^ SymbolicValueId.InjSubst.show_t !sid_map
        ^ "\n- aid_map: "
        ^ AbstractionId.InjSubst.show_t !aid_map
        ^ "\n\n- ctx0:\n"
        ^ eval_ctx_to_string_no_filter ~span:(Some span)
            { ctx0 with env = List.rev env0 }
        ^ "\n\n- ctx1:\n"
        ^ eval_ctx_to_string_no_filter ~span:(Some span)
            { ctx1 with env = List.rev env1 }
        ^ "\n\n"));

    match (env0, env1) with
    | EBinding (BDummy b0, v0) :: env0', EBinding (BDummy b1, v1) :: env1' ->
        (* Sanity check: if the dummy value is an old value, the bindings must
           be the same and their values equal (and the borrows/loans/symbolic *)
        if DummyVarId.Set.mem b0 fixed_ids.dids then (
          (* Fixed values: the values must be equal *)
          sanity_check __FILE__ __LINE__ (b0 = b1) span;
          sanity_check __FILE__ __LINE__ (v0 = v1) span;
          (* The ids present in the left value must be fixed *)
          let ids, _ = compute_typed_value_ids v0 in
          sanity_check __FILE__ __LINE__
            ((not S.check_equiv) || ids_are_fixed ids)
            span);
        (* We still match the values - allows to compute mappings (which
           are the identity actually) *)
        let _ = M.match_typed_values ctx0 ctx1 v0 v1 in
        match_envs env0' env1'
    | EBinding (BVar b0, v0) :: env0', EBinding (BVar b1, v1) :: env1' ->
        sanity_check __FILE__ __LINE__ (b0 = b1) span;
        (* Match the values *)
        let _ = M.match_typed_values ctx0 ctx1 v0 v1 in
        (* Continue *)
        match_envs env0' env1'
    | EAbs abs0 :: env0', EAbs abs1 :: env1' ->
        log#ldebug (lazy "match_ctxs: match_envs: matching abs");
        (* Same as for the dummy values: there are two cases *)
        if AbstractionId.Set.mem abs0.abs_id fixed_ids.aids then (
          log#ldebug (lazy "match_ctxs: match_envs: matching abs: fixed abs");
          (* Still in the prefix: the abstractions must be the same *)
          sanity_check __FILE__ __LINE__ (abs0 = abs1) span;
          (* Their ids must be fixed *)
          let ids, _ = compute_abs_ids abs0 in
          sanity_check __FILE__ __LINE__
            ((not S.check_equiv) || ids_are_fixed ids)
            span;
          (* Continue *)
          match_envs env0' env1')
        else (
          log#ldebug
            (lazy "match_ctxs: match_envs: matching abs: not fixed abs");
          (* Match the values *)
          match_abstractions abs0 abs1;
          (* Continue *)
          match_envs env0' env1')
    | [], [] ->
        (* Done *)
        ()
    | _ ->
        (* The elements don't match *)
        raise (Distinct "match_ctxs: match_envs: env elements don't match")
  in

  (* Match the environments.

     Rem.: we don't match the ended regions (would it make any sense actually?) *)
  try
    (* Remove the frame delimiter (the first element of an environment is a frame delimiter) *)
    let env0 = List.rev ctx0.env in
    let env1 = List.rev ctx1.env in
    let env0, env1 =
      match (env0, env1) with
      | EFrame :: env0, EFrame :: env1 -> (env0, env1)
      | _ -> craise __FILE__ __LINE__ span "Unreachable"
    in

    match_envs env0 env1;
    let maps =
      {
        aid_map = !aid_map;
        blid_map = !blid_map;
        borrow_id_map = !borrow_id_map;
        loan_id_map = !loan_id_map;
        rid_map = !rid_map;
        sid_map = !sid_map;
        sid_to_value_map = !sid_to_value_map;
      }
    in
    Some maps
  with
  | Distinct msg ->
      log#ldebug (lazy ("match_ctxs: distinct: " ^ msg ^ "\n"));
      None
  | ValueMatchFailure k ->
      log#ldebug
        (lazy
          ("match_ctxs: distinct: ValueMatchFailure" ^ show_updt_env_kind k
         ^ "\n"));
      None

let ctxs_are_equivalent (span : Meta.span) (fixed_ids : ids_sets)
    (ctx0 : eval_ctx) (ctx1 : eval_ctx) : bool =
  let check_equivalent = true in
  let lookup_shared_value _ = craise __FILE__ __LINE__ span "Unreachable" in
  Option.is_some
    (match_ctxs span check_equivalent fixed_ids lookup_shared_value
       lookup_shared_value ctx0 ctx1)

let prepare_match_ctx_with_target (config : config) (span : Meta.span)
    (loop_id : LoopId.id) (fixed_ids : ids_sets) (src_ctx : eval_ctx) : cm_fun =
 fun tgt_ctx ->
  (* Debug *)
  log#ldebug
    (lazy
      ("prepare_match_ctx_with_target:\n" ^ "\n- fixed_ids: "
     ^ show_ids_sets fixed_ids ^ "\n" ^ "\n- src_ctx: "
      ^ eval_ctx_to_string ~span:(Some span) src_ctx
      ^ "\n- tgt_ctx: "
      ^ eval_ctx_to_string ~span:(Some span) tgt_ctx));
  (* End the loans which lead to mismatches when joining *)
  let rec reorganize_join_tgt : cm_fun =
   fun tgt_ctx ->
    (* Collect fixed values in the source and target contexts: end the loans in the
       source context which don't appear in the target context *)
    let filt_src_env, _, _ = ctx_split_fixed_new span fixed_ids src_ctx in
    let filt_tgt_env, _, _ = ctx_split_fixed_new span fixed_ids tgt_ctx in

    log#ldebug
      (lazy
        ("prepare_match_ctx_with_target: reorganize_join_tgt:\n"
       ^ "\n- fixed_ids: " ^ show_ids_sets fixed_ids ^ "\n"
       ^ "\n- filt_src_ctx: "
        ^ env_to_string span src_ctx filt_src_env
        ^ "\n- filt_tgt_ctx: "
        ^ env_to_string span tgt_ctx filt_tgt_env));

    (* Remove the abstractions *)
    let filter (ee : env_elem) : bool =
      match ee with EBinding _ -> true | EAbs _ | EFrame -> false
    in
    let filt_src_env = List.filter filter filt_src_env in
    let filt_tgt_env = List.filter filter filt_tgt_env in

    (* Match the values to check if there are loans to eliminate *)
    let nabs = ref [] in

    let module S : MatchJoinState = struct
      let span = span
      let loop_id = loop_id
      let nabs = nabs
    end in
    let module JM = MakeJoinMatcher (S) in
    let module M = MakeMatcher (JM) in
    try
      let _ =
        List.iter
          (fun (var0, var1) ->
            match (var0, var1) with
            | EBinding (BDummy b0, v0), EBinding (BDummy b1, v1) ->
                sanity_check __FILE__ __LINE__ (b0 = b1) span;
                let _ = M.match_typed_values src_ctx tgt_ctx v0 v1 in
                ()
            | EBinding (BVar b0, v0), EBinding (BVar b1, v1) ->
                sanity_check __FILE__ __LINE__ (b0 = b1) span;
                let _ = M.match_typed_values src_ctx tgt_ctx v0 v1 in
                ()
            | _ -> craise __FILE__ __LINE__ span "Unexpected")
          (List.combine filt_src_env filt_tgt_env)
      in
      (* No exception was thrown: continue *)
      log#ldebug
        (lazy
          ("prepare_match_ctx_with_target: reorganize_join_tgt: done with \
            borrows/loans:\n" ^ "\n- fixed_ids: " ^ show_ids_sets fixed_ids
         ^ "\n" ^ "\n- filt_src_ctx: "
          ^ env_to_string span src_ctx filt_src_env
          ^ "\n- filt_tgt_ctx: "
          ^ env_to_string span tgt_ctx filt_tgt_env));

      (* We are done with the borrows/loans: now make sure we move all
         the values which are bottom in the src environment (i.e., the
         fixed-point environment) *)
      (* First compute the map from binder to new value for the target
         environment *)
      let nvalues = ref [] in
      let module S : MatchMoveState = struct
        let span = span
        let loop_id = loop_id
        let nvalues = nvalues
      end in
      let module MM = MakeMoveMatcher (S) in
      let module M = MakeMatcher (MM) in
      let var_to_new_val =
        List.map
          (fun (var0, var1) ->
            match (var0, var1) with
            | EBinding (BDummy b0, v0), EBinding ((BDummy b1 as var1), v1) ->
                sanity_check __FILE__ __LINE__ (b0 = b1) span;
                let v = M.match_typed_values src_ctx tgt_ctx v0 v1 in
                (var1, v)
            | EBinding (BVar b0, v0), EBinding ((BVar b1 as var1), v1) ->
                sanity_check __FILE__ __LINE__ (b0 = b1) span;
                let v = M.match_typed_values src_ctx tgt_ctx v0 v1 in
                (var1, v)
            | _ -> craise __FILE__ __LINE__ span "Unexpected")
          (List.combine filt_src_env filt_tgt_env)
      in
      let var_to_new_val = BinderMap.of_list var_to_new_val in

      (* Update the target environment to take into account the moved values *)
      let tgt_ctx =
        (* Update the bindings *)
        let tgt_env =
          List.map
            (fun b ->
              match b with
              | EBinding (bv, _) -> (
                  match BinderMap.find_opt bv var_to_new_val with
                  | None -> b
                  | Some nv -> EBinding (bv, nv))
              | _ -> b)
            tgt_ctx.env
        in
        (* Insert the moved values *)
        let tgt_ctx = { tgt_ctx with env = tgt_env } in
        ctx_push_fresh_dummy_vars tgt_ctx (List.rev !nvalues)
      in

      log#ldebug
        (lazy
          ("prepare_match_ctx_with_target: reorganize_join_tgt: done with \
            borrows/loans and moves:\n" ^ "\n- fixed_ids: "
         ^ show_ids_sets fixed_ids ^ "\n" ^ "\n- src_ctx: "
          ^ eval_ctx_to_string ~span:(Some span) src_ctx
          ^ "\n- tgt_ctx: "
          ^ eval_ctx_to_string ~span:(Some span) tgt_ctx));

      (tgt_ctx, fun e -> e)
    with ValueMatchFailure e ->
      (* Exception: end the corresponding borrows, and continue *)
      let ctx, cc =
        match e with
        | LoanInRight bid ->
            InterpreterBorrows.end_borrow config span bid tgt_ctx
        | LoansInRight bids ->
            InterpreterBorrows.end_borrows config span bids tgt_ctx
        | AbsInRight _ | AbsInLeft _ | LoanInLeft _ | LoansInLeft _ ->
            craise __FILE__ __LINE__ span "Unexpected"
      in
      comp cc (reorganize_join_tgt ctx)
  in
  (* Apply the reorganization *)
  reorganize_join_tgt tgt_ctx

let match_ctx_with_target (config : config) (span : Meta.span)
    (loop_id : LoopId.id) (is_loop_entry : bool)
    (fp_bl_maps : borrow_loan_corresp)
    (fp_input_svalues : SymbolicValueId.id list) (fixed_ids : ids_sets)
    (src_ctx : eval_ctx) : st_cm_fun =
 fun tgt_ctx ->
  (* Debug *)
  log#ldebug
    (lazy
      ("match_ctx_with_target:\n" ^ "\n- fixed_ids: " ^ show_ids_sets fixed_ids
     ^ "\n" ^ "\n- src_ctx: " ^ eval_ctx_to_string src_ctx ^ "\n- tgt_ctx: "
     ^ eval_ctx_to_string tgt_ctx));

  (* We first reorganize [tgt_ctx] so that we can match [src_ctx] with it (by
     ending loans for instance - remember that the [src_ctx] is the fixed point
     context, which results from joins during which we ended the loans which
     were introduced during the loop iterations)
  *)
  let tgt_ctx, cc =
    prepare_match_ctx_with_target config span loop_id fixed_ids src_ctx tgt_ctx
  in

  (* Introduce the "identity" abstractions for the loop re-entry.

     Match the target context with the source context so as to compute how to
     map the borrows from the target context (i.e., the fixed point context)
     to the borrows in the source context.

     Substitute the *loans* in the abstractions introduced by the target context
     (the abstractions of the fixed point) to properly link those abstraction:
     we introduce *identity* abstractions (the loans are equal to the borrows):
     we substitute the loans and introduce fresh ids for the borrows, symbolic
     values, etc. About the *identity abstractions*, see the comments for
     [compute_fixed_point_id_correspondance].

     TODO: this whole thing is very technical and error-prone.
     We should rely on a more primitive and safer function
     [add_identity_abs] to add the identity abstractions one by one.
  *)
  (* Match the source and target contexts *)
  log#ldebug
    (lazy
      ("cf_introduce_loop_fp_abs:\n" ^ "\n- fixed_ids: "
     ^ show_ids_sets fixed_ids ^ "\n" ^ "\n- src_ctx: "
     ^ eval_ctx_to_string src_ctx ^ "\n- tgt_ctx: " ^ eval_ctx_to_string tgt_ctx
      ));

  let filt_tgt_env, _, _ = ctx_split_fixed_new span fixed_ids tgt_ctx in
  let filt_src_env, new_absl, new_dummyl =
    ctx_split_fixed_new span fixed_ids src_ctx
  in
  sanity_check __FILE__ __LINE__ (new_dummyl = []) span;
  let filt_tgt_ctx = { tgt_ctx with env = filt_tgt_env } in
  let filt_src_ctx = { src_ctx with env = filt_src_env } in

  let src_to_tgt_maps =
    let check_equiv = false in
    let fixed_ids = ids_sets_empty_borrows_loans fixed_ids in
    let open InterpreterBorrowsCore in
    let lookup_shared_loan lid ctx : typed_value =
      match snd (lookup_loan span ek_all lid ctx) with
      | Concrete (VSharedLoan (_, v)) -> v
      | Abstract (ASharedLoan (pm, _, v, _)) ->
          sanity_check __FILE__ __LINE__ (pm = PNone) span;
          v
      | _ -> craise __FILE__ __LINE__ span "Unreachable"
    in
    let lookup_in_src id = lookup_shared_loan id src_ctx in
    let lookup_in_tgt id = lookup_shared_loan id tgt_ctx in
    (* Match *)
    Option.get
      (match_ctxs span check_equiv fixed_ids lookup_in_src lookup_in_tgt
         filt_src_ctx filt_tgt_ctx)
  in
  let tgt_to_src_borrow_map =
    BorrowId.Map.of_list
      (List.map
         (fun (x, y) -> (y, x))
         (BorrowId.InjSubst.bindings src_to_tgt_maps.borrow_id_map))
  in

  (* Debug *)
  log#ldebug
    (lazy
      ("match_ctx_with_target: cf_introduce_loop_fp_abs:" ^ "\n\n- src_ctx: "
      ^ eval_ctx_to_string ~span:(Some span) src_ctx
      ^ "\n\n- tgt_ctx: "
      ^ eval_ctx_to_string ~span:(Some span) tgt_ctx
      ^ "\n\n- filt_tgt_ctx: "
      ^ eval_ctx_to_string_no_filter ~span:(Some span) filt_tgt_ctx
      ^ "\n\n- filt_src_ctx: "
      ^ eval_ctx_to_string_no_filter ~span:(Some span) filt_src_ctx
      ^ "\n\n- new_absl:\n"
      ^ eval_ctx_to_string ~span:(Some span)
          { src_ctx with env = List.map (fun abs -> EAbs abs) new_absl }
      ^ "\n\n- fixed_ids:\n" ^ show_ids_sets fixed_ids ^ "\n\n- fp_bl_maps:\n"
      ^ show_borrow_loan_corresp fp_bl_maps
      ^ "\n\n- src_to_tgt_maps: "
      ^ show_ids_maps src_to_tgt_maps));

  (* Update the borrows and symbolic ids in the source context.

     Going back to the [list_nth_mut_example], the original environment upon
     re-entering the loop is:

     {[
       abs@0 { ML l0 }
       ls -> MB l5 (s@6 : loops::List<T>)
       i -> s@7 : u32
       _@1 -> MB l0 (loops::List::Cons (ML l1, ML l2))
       _@2 -> MB l2 (@Box (ML l4))                      // tail
       _@3 -> MB l1 (s@3 : T)                           // hd
       abs@1 { MB l4, ML l5 }
     ]}

     The fixed-point environment is:
     {[
       env_fp = {
         abs@0 { ML l0 }
         ls -> MB l1 (s3 : loops::List<T>)
         i -> s4 : u32
         abs@fp {
           MB l0 // this borrow appears in [env0]
           ML l1
         }
       }
     ]}

     Through matching, we detect that in [env_fp], [l1] is matched
     to [l5]. We introduce a fresh borrow [l6] for [l1], and remember
     in the map [src_fresh_borrows_map] that: [{ l1 -> l6}].

     We get:
     {[
       abs@0 { ML l0 }
       ls -> MB l6 (s@6 : loops::List<T>) // l6 is fresh and doesn't have a corresponding loan
       i -> s@7 : u32
       _@1 -> MB l0 (loops::List::Cons (ML l1, ML l2))
       _@2 -> MB l2 (@Box (ML l4))                      // tail
       _@3 -> MB l1 (s@3 : T)                           // hd
       abs@1 { MB l4, ML l5 }
     ]}

     Later, we will introduce the identity abstraction:
     {[
       abs@2 { MB l5, ML l6 }
     ]}
  *)
  (* First, compute the set of borrows which appear in the fresh abstractions
     of the fixed-point: we want to introduce fresh ids only for those. *)
  let new_absl_ids, _ = compute_absl_ids new_absl in
  let src_fresh_borrows_map = ref BorrowId.Map.empty in
  let visit_tgt =
    object
      inherit [_] map_eval_ctx

      method! visit_borrow_id _ id =
        (* Map the borrow, if it needs to be mapped *)
        if
          (* We map the borrows for which we computed a mapping *)
          BorrowId.InjSubst.Set.mem id
            (BorrowId.InjSubst.elements src_to_tgt_maps.borrow_id_map)
          (* And which have corresponding loans in the fresh fixed-point abstractions *)
          && BorrowId.Set.mem
               (BorrowId.Map.find id tgt_to_src_borrow_map)
               new_absl_ids.loan_ids
        then (
          let src_id = BorrowId.Map.find id tgt_to_src_borrow_map in
          let nid = fresh_borrow_id () in
          src_fresh_borrows_map :=
            BorrowId.Map.add src_id nid !src_fresh_borrows_map;
          nid)
        else id
    end
  in

  let tgt_ctx = visit_tgt#visit_eval_ctx () tgt_ctx in

  log#ldebug
    (lazy
      ("match_ctx_with_target: cf_introduce_loop_fp_abs: src_fresh_borrows_map:\n"
      ^ BorrowId.Map.show BorrowId.to_string !src_fresh_borrows_map
      ^ "\n"));

  (* Rem.: we don't update the symbolic values. It is not necessary
     because there shouldn't be any symbolic value containing borrows.

     Rem.: we will need to do something about the symbolic values in the
     abstractions and in the *variable bindings* once we allow symbolic
     values containing borrows to not be eagerly expanded.
  *)
  sanity_check __FILE__ __LINE__ Config.greedy_expand_symbolics_with_borrows
    span;

  (* Update the borrows and loans in the abstractions of the target context.

     Going back to the [list_nth_mut] example and by using [src_fresh_borrows_map],
     we instantiate the fixed-point abstractions that we will insert into the
     context.
     The abstraction is [abs { MB l0, ML l1 }].
     Because of [src_fresh_borrows_map], we substitute [l1] with [l6].
     Because of the match between the contexts, we substitute [l0] with [l5].
     We get:
     {[
       abs@2 { MB l5, ML l6 }
     ]}
  *)
  let region_id_map = ref RegionId.Map.empty in
  let get_rid rid =
    match RegionId.Map.find_opt rid !region_id_map with
    | Some rid -> rid
    | None ->
        let nid = fresh_region_id () in
        region_id_map := RegionId.Map.add rid nid !region_id_map;
        nid
  in
  let visit_src =
    object
      inherit [_] map_eval_ctx as super

      method! visit_borrow_id _ bid =
        log#ldebug
          (lazy
            ("match_ctx_with_target: cf_introduce_loop_fp_abs: \
              visit_borrow_id: " ^ BorrowId.to_string bid ^ "\n"));

        (* Lookup the id of the loan corresponding to this borrow *)
        let src_lid =
          BorrowId.InjSubst.find bid fp_bl_maps.borrow_to_loan_id_map
        in

        log#ldebug
          (lazy
            ("match_ctx_with_target: cf_introduce_loop_fp_abs: looked up \
              src_lid: " ^ BorrowId.to_string src_lid ^ "\n"));

        (* Lookup the tgt borrow id to which this borrow was mapped *)
        let tgt_bid =
          BorrowId.InjSubst.find src_lid src_to_tgt_maps.borrow_id_map
        in

        log#ldebug
          (lazy
            ("match_ctx_with_target: cf_introduce_loop_fp_abs: looked up \
              tgt_bid: " ^ BorrowId.to_string tgt_bid ^ "\n"));

        tgt_bid

      method! visit_loan_id _ id =
        log#ldebug
          (lazy
            ("match_ctx_with_target: cf_introduce_loop_fp_abs: visit_loan_id: "
           ^ BorrowId.to_string id ^ "\n"));
        (* Map the borrow - rem.: we mapped the borrows *in the values*,
           meaning we know how to map the *corresponding loans in the
           abstractions* *)
        match BorrowId.Map.find_opt id !src_fresh_borrows_map with
        | None ->
            (* No mapping: this means that the borrow was mapped when
               we matched values (it doesn't come from a fresh abstraction)
               and because of this, it should actually be mapped to itself *)
            sanity_check __FILE__ __LINE__
              (BorrowId.InjSubst.find id src_to_tgt_maps.borrow_id_map = id)
              span;
            id
        | Some id -> id

      method! visit_symbolic_value_id _ _ = fresh_symbolic_value_id ()
      method! visit_abstraction_id _ _ = fresh_abstraction_id ()
      method! visit_region_id _ id = get_rid id

      (** We also need to change the abstraction kind *)
      method! visit_abs env abs =
        match abs.kind with
        | Loop (loop_id', rg_id, kind) ->
            sanity_check __FILE__ __LINE__ (loop_id' = loop_id) span;
            sanity_check __FILE__ __LINE__ (kind = LoopSynthInput) span;
            let can_end = false in
            let kind : abs_kind = Loop (loop_id, rg_id, LoopCall) in
            let abs = { abs with kind; can_end } in
            super#visit_abs env abs
        | _ -> super#visit_abs env abs
    end
  in
  let new_absl = List.map (visit_src#visit_abs ()) new_absl in
  let new_absl = List.map (fun abs -> EAbs abs) new_absl in

  (* Add the abstractions from the target context to the source context *)
  let nenv = List.append new_absl tgt_ctx.env in
  let tgt_ctx = { tgt_ctx with env = nenv } in

  log#ldebug
    (lazy
      ("match_ctx_with_target: cf_introduce_loop_fp_abs: done:\n- result ctx:\n"
      ^ eval_ctx_to_string ~span:(Some span) tgt_ctx));

  (* Sanity check *)
  if !Config.sanity_checks then
    Invariants.check_borrowed_values_invariant span tgt_ctx;
  (* End all the borrows which appear in the *new* abstractions *)
  let new_borrows =
    BorrowId.Set.of_list
      (List.map snd (BorrowId.Map.bindings !src_fresh_borrows_map))
  in
  let tgt_ctx, cc =
    comp cc (InterpreterBorrows.end_borrows config span new_borrows tgt_ctx)
  in

  (* Compute the loop input values *)
  let input_values =
    SymbolicValueId.Map.of_list
      (List.map
         (fun sid ->
           (sid, SymbolicValueId.Map.find sid src_to_tgt_maps.sid_to_value_map))
         fp_input_svalues)
  in

  let res =
    if is_loop_entry then EndEnterLoop (loop_id, input_values)
    else EndContinue (loop_id, input_values)
  in

  ((tgt_ctx, res), cc)
