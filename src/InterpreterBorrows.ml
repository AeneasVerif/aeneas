module T = Types
module V = Values
module C = Contexts
module Subst = Substitute
module L = Logging
module S = SynthesizeSymbolic
open Cps
open ValuesUtils
open TypesUtils
open InterpreterUtils
open InterpreterBorrowsCore
open InterpreterProjectors

(** Auxiliary function to end borrows: lookup a borrow in the environment,
    update it (by returning an updated environment where the borrow has been
    replaced by [Bottom])) if we can end the borrow (for instance, it is not
    an outer borrow...) or return the reason why we couldn't update the borrow.

    [end_borrow] then simply performs a loop: as long as we need to end (outer)
    borrows, we end them, before finally ending the borrow we wanted to end in the
    first place.

    Note that it is possible to end a borrow in an abstraction, without ending
    the whole abstraction, if the corresponding loan is inside the abstraction
    as well. The [allowed_abs] parameter controls whether we allow to end borrows
    in an abstraction or not, and in which abstraction.
*)
let end_borrow_get_borrow (allowed_abs : V.AbstractionId.id option)
    (l : V.BorrowId.id) (ctx : C.eval_ctx) :
    (C.eval_ctx * g_borrow_content option, priority_borrows_or_abs) result =
  (* We use a reference to communicate the kind of borrow we found, if we
   * find one *)
  let replaced_bc : g_borrow_content option ref = ref None in
  let set_replaced_bc (bc : g_borrow_content) =
    assert (Option.is_none !replaced_bc);
    replaced_bc := Some bc
  in
  (* Raise an exception if:
   * - there are outer borrows
   * - if we are inside an abstraction
   * - there are inner loans
   * this exception is caught in a wrapper function *)
  let raise_if_priority (outer : V.AbstractionId.id option * borrow_ids option)
      (borrowed_value : V.typed_value option) =
    (* First, look for outer borrows or abstraction *)
    let outer_abs, outer_borrows = outer in
    (match outer_abs with
    | Some abs -> (
        if
          (* Check if we can end borrows inside this abstraction *)
          Some abs <> allowed_abs
        then raise (FoundPriority (OuterAbs abs))
        else
          match outer_borrows with
          | Some borrows -> raise (FoundPriority (OuterBorrows borrows))
          | None -> ())
    | None -> (
        match outer_borrows with
        | Some borrows -> raise (FoundPriority (OuterBorrows borrows))
        | None -> ()));
    (* Then check if there are inner loans *)
    match borrowed_value with
    | None -> ()
    | Some v -> (
        match get_first_loan_in_value v with
        | None -> ()
        | Some c -> (
            match c with
            | V.SharedLoan (bids, _) ->
                raise (FoundPriority (InnerLoans (Borrows bids)))
            | V.MutLoan bid -> raise (FoundPriority (InnerLoans (Borrow bid)))))
  in

  (* The environment is used to keep track of the outer loans *)
  let obj =
    object
      inherit [_] C.map_eval_ctx as super

      method! visit_Loan (outer : V.AbstractionId.id option * borrow_ids option)
          lc =
        match lc with
        | V.MutLoan bid -> V.Loan (super#visit_MutLoan outer bid)
        | V.SharedLoan (bids, v) ->
            (* Update the outer borrows before diving into the shared value *)
            let outer = update_outer_borrows outer (Borrows bids) in
            V.Loan (super#visit_SharedLoan outer bids v)
      (** We reimplement [visit_Loan] because we may have to update the
          outer borrows *)

      method! visit_Borrow outer bc =
        match bc with
        | SharedBorrow (_, l') | InactivatedMutBorrow l' ->
            (* Check if this is the borrow we are looking for *)
            if l = l' then (
              (* Check if there are outer borrows or if we are inside an abstraction *)
              raise_if_priority outer None;
              (* Register the update *)
              set_replaced_bc (Concrete bc);
              (* Update the value *)
              V.Bottom)
            else super#visit_Borrow outer bc
        | V.MutBorrow (l', bv) ->
            (* Check if this is the borrow we are looking for *)
            if l = l' then (
              (* Check if there are outer borrows or if we are inside an abstraction *)
              raise_if_priority outer (Some bv);
              (* Register the update *)
              set_replaced_bc (Concrete bc);
              (* Update the value *)
              V.Bottom)
            else
              (* Update the outer borrows before diving into the borrowed value *)
              let outer = update_outer_borrows outer (Borrow l') in
              V.Borrow (super#visit_MutBorrow outer l' bv)

      method! visit_ALoan outer lc =
        (* Note that the children avalues are just other, independent loans,
         * so we don't need to update the outer borrows when diving in.
         * We keep track of the parents/children relationship only because we
         * need it to properly instantiate the backward functions when generating
         * the pure translation. *)
        match lc with
        | V.AMutLoan (_, _) ->
            (* Nothing special to do *)
            super#visit_ALoan outer lc
        | V.ASharedLoan (bids, v, av) ->
            (* Explore the shared value - we need to update the outer borrows *)
            let souter = update_outer_borrows outer (Borrows bids) in
            let v = super#visit_typed_value souter v in
            (* Explore the child avalue - we keep the same outer borrows *)
            let av = super#visit_typed_avalue outer av in
            (* Reconstruct *)
            V.ALoan (V.ASharedLoan (bids, v, av))
        | V.AEndedMutLoan { given_back = _; child = _; given_back_meta = _ }
        | V.AEndedSharedLoan _
        (* The loan has ended, so no need to update the outer borrows *)
        | V.AIgnoredMutLoan _ (* Nothing special to do *)
        | V.AEndedIgnoredMutLoan
            { given_back = _; child = _; given_back_meta = _ }
        (* Nothing special to do *)
        | V.AIgnoredSharedLoan _ ->
            (* Nothing special to do *)
            super#visit_ALoan outer lc
      (** We reimplement [visit_ALoan] because we may have to update the
          outer borrows *)

      method! visit_ABorrow outer bc =
        match bc with
        | V.AMutBorrow (_, bid, _) ->
            (* Check if this is the borrow we are looking for *)
            if bid = l then (
              (* When ending a mut borrow, there are two cases:
               * - in the general case, we have to end the whole abstraction
               *   (and thus raise an exception to signal that to the caller)
               * - in some situations, the associated loan is inside the same
               *   abstraction as the borrow. In this situation, we can end
               *   the borrow without ending the whole abstraction, and we
               *   simply move the child avalue around.
               *)
              (* Check there are outer borrows, or if we need to end the whole
               * abstraction *)
              raise_if_priority outer None;
              (* Register the update *)
              set_replaced_bc (Abstract bc);
              (* Update the value - note that we are necessarily in the second
               * of the two cases described above.
               * Also note that, as we are moving the borrowed value inside the
               * abstraction (and not really giving the value back to the context)
               * we do not insert [AEndedMutBorrow] but rather [ABottom] *)
              V.ABottom)
            else
              (* Update the outer borrows before diving into the child avalue *)
              let outer = update_outer_borrows outer (Borrow bid) in
              super#visit_ABorrow outer bc
        | V.ASharedBorrow bid ->
            (* Check if this is the borrow we are looking for *)
            if bid = l then (
              (* Check there are outer borrows, or if we need to end the whole
               * abstraction *)
              raise_if_priority outer None;
              (* Register the update *)
              set_replaced_bc (Abstract bc);
              (* Update the value - note that we are necessarily in the second
               * of the two cases described above *)
              V.ABottom)
            else super#visit_ABorrow outer bc
        | V.AIgnoredMutBorrow (_, _)
        | V.AEndedMutBorrow _
        | V.AEndedIgnoredMutBorrow
            { given_back_loans_proj = _; child = _; given_back_meta = _ } ->
            (* Nothing special to do *)
            super#visit_ABorrow outer bc
        | V.AProjSharedBorrow asb ->
            (* Check if the borrow we are looking for is in the asb *)
            if borrow_in_asb l asb then (
              (* Check there are outer borrows, or if we need to end the whole
               * abstraction *)
              raise_if_priority outer None;
              (* Register the update *)
              set_replaced_bc (Abstract bc);
              (* Update the value - note that we are necessarily in the second
               * of the two cases described above *)
              let asb = remove_borrow_from_asb l asb in
              V.ABorrow (V.AProjSharedBorrow asb))
            else (* Nothing special to do *)
              super#visit_ABorrow outer bc

      method! visit_abs outer abs =
        (* Update the outer abs *)
        let outer_abs, outer_borrows = outer in
        assert (Option.is_none outer_abs);
        assert (Option.is_none outer_borrows);
        let outer = (Some abs.V.abs_id, None) in
        super#visit_abs outer abs
    end
  in
  (* Catch the exceptions - raised if there are outer borrows *)
  try
    let ctx = obj#visit_eval_ctx (None, None) ctx in
    Ok (ctx, !replaced_bc)
  with FoundPriority outers -> Error outers

(** Auxiliary function to end borrows. See [give_back].
    
    When we end a mutable borrow, we need to "give back" the value it contained
    to its original owner by reinserting it at the proper position.

    Note that this function checks that there is exactly one loan to which we
    give the value back.
    TODO: this was not the case before, so some sanity checks are not useful anymore.
 *)
let give_back_value (config : C.config) (bid : V.BorrowId.id)
    (nv : V.typed_value) (ctx : C.eval_ctx) : C.eval_ctx =
  (* Sanity check *)
  assert (not (loans_in_value nv));
  assert (not (bottom_in_value ctx.ended_regions nv));
  (* Debug *)
  log#ldebug
    (lazy
      ("give_back_value:\n- bid: " ^ V.BorrowId.to_string bid ^ "\n- value: "
      ^ typed_value_to_string ctx nv
      ^ "\n- context:\n" ^ eval_ctx_to_string ctx ^ "\n"));
  (* We use a reference to check that we updated exactly one loan *)
  let replaced : bool ref = ref false in
  let set_replaced () =
    assert (not !replaced);
    replaced := true
  in
  (* Whenever giving back symbolic values, they shouldn't contain already ended regions *)
  let check_symbolic_no_ended = true in
  (* We sometimes need to reborrow values while giving a value back due: prepare that *)
  let allow_reborrows = true in
  let fresh_reborrow, apply_registered_reborrows =
    prepare_reborrows config allow_reborrows
  in
  (* The visitor to give back the values *)
  let obj =
    object (self)
      inherit [_] C.map_eval_ctx as super

      method! visit_typed_value opt_abs (v : V.typed_value) : V.typed_value =
        match v.V.value with
        | V.Loan lc ->
            let value = self#visit_typed_Loan opt_abs v.V.ty lc in
            ({ v with V.value } : V.typed_value)
        | _ -> super#visit_typed_value opt_abs v
      (** This is a bit annoying, but as we need the type of the value we
          are exploring, for sanity checks, we need to implement
          [visit_typed_avalue] instead of
          overriding [visit_ALoan] *)

      method visit_typed_Loan opt_abs ty lc =
        match lc with
        | V.SharedLoan (bids, v) ->
            (* We are giving back a value (i.e., the content of a *mutable*
             * borrow): nothing special to do *)
            V.Loan (super#visit_SharedLoan opt_abs bids v)
        | V.MutLoan bid' ->
            (* Check if this is the loan we are looking for *)
            if bid' = bid then (
              (* Sanity check *)
              let expected_ty = ty in
              if nv.V.ty <> expected_ty then (
                log#serror
                  ("give_back_value: improper type:\n- expected: "
                 ^ ety_to_string ctx ty ^ "\n- received: "
                 ^ ety_to_string ctx nv.V.ty);
                failwith "Value given back doesn't have the proper type");
              (* Replace *)
              set_replaced ();
              nv.V.value)
            else V.Loan (super#visit_MutLoan opt_abs bid')

      method! visit_typed_avalue opt_abs (av : V.typed_avalue) : V.typed_avalue
          =
        match av.V.value with
        | V.ALoan lc ->
            let value = self#visit_typed_ALoan opt_abs av.V.ty lc in
            ({ av with V.value } : V.typed_avalue)
        | _ -> super#visit_typed_avalue opt_abs av
      (** This is a bit annoying, but as we need the type of the avalue we
          are exploring, in order to be able to project the value we give
          back, we need to reimplement [visit_typed_avalue] instead of
          [visit_ALoan] *)

      method! visit_ABorrow (opt_abs : V.abs option) (bc : V.aborrow_content)
          : V.avalue =
        match bc with
        | V.AIgnoredMutBorrow (bid', child) ->
            if bid' = Some bid then
              (* Insert a loans projector - note that if this case happens,
               * it is necessarily because we ended a parent abstraction,
               * and the given back value is thus a symbolic value *)
              match nv.V.value with
              | V.Symbolic sv ->
                  let abs = Option.get opt_abs in
                  (* Remember the given back value as a meta-value
                   * TODO: it is a bit annoying to have to deconstruct
                   * the value... Think about a more elegant way. *)
                  let given_back_meta = as_symbolic nv.value in
                  (* The loan projector *)
                  let given_back_loans_proj =
                    mk_aproj_loans_value_from_symbolic_value abs.regions sv
                  in
                  (* Continue giving back in the child value *)
                  let child = super#visit_typed_avalue opt_abs child in
                  (* Return *)
                  V.ABorrow
                    (V.AEndedIgnoredMutBorrow
                       { given_back_loans_proj; child; given_back_meta })
              | _ -> failwith "Unreachable"
            else
              (* Continue exploring *)
              V.ABorrow (super#visit_AIgnoredMutBorrow opt_abs bid' child)
        | _ ->
            (* Continue exploring *)
            super#visit_ABorrow opt_abs bc
      (** We need to inspect ignored mutable borrows, to insert loan projectors
          if necessary.
       *)

      method visit_typed_ALoan (opt_abs : V.abs option) (ty : T.rty)
          (lc : V.aloan_content) : V.avalue =
        (* Preparing a bit *)
        let regions, ancestors_regions =
          match opt_abs with
          | None -> failwith "Unreachable"
          | Some abs -> (abs.V.regions, abs.V.ancestors_regions)
        in
        (* Rk.: there is a small issue with the types of the aloan values.
         * See the comment at the level of definition of [typed_avalue] *)
        let borrowed_value_aty =
          let _, ty, _ = ty_get_ref ty in
          ty
        in
        match lc with
        | V.AMutLoan (bid', child) ->
            if bid' = bid then (
              (* This is the loan we are looking for: apply the projection to
               * the value we give back and replaced this mutable loan with
               * an ended loan *)
              (* Register the insertion *)
              set_replaced ();
              (* Remember the given back value as a meta-value *)
              let given_back_meta = nv in
              (* Apply the projection *)
              let given_back =
                apply_proj_borrows check_symbolic_no_ended ctx fresh_reborrow
                  regions ancestors_regions nv borrowed_value_aty
              in
              (* Continue giving back in the child value *)
              let child = super#visit_typed_avalue opt_abs child in
              (* Return the new value *)
              V.ALoan (V.AEndedMutLoan { child; given_back; given_back_meta }))
            else (* Continue exploring *)
              super#visit_ALoan opt_abs lc
        | V.ASharedLoan (_, _, _) ->
            (* We are giving back a value to a *mutable* loan: nothing special to do *)
            super#visit_ALoan opt_abs lc
        | V.AEndedMutLoan { child = _; given_back = _; given_back_meta = _ }
        | V.AEndedSharedLoan (_, _) ->
            (* Nothing special to do *)
            super#visit_ALoan opt_abs lc
        | V.AIgnoredMutLoan (bid', child) ->
            (* This loan is ignored, but we may have to project on a subvalue
             * of the value which is given back *)
            if bid' = bid then
              (* Remember the given back value as a meta-value *)
              let given_back_meta = nv in
              (* Note that we replace the ignored mut loan by an *ended* ignored
               * mut loan. Also, this is not the loan we are looking for *per se*:
               * we don't register the fact that we inserted the value somewhere
               * (i.e., we don't call [set_replaced]) *)
              let given_back =
                apply_proj_borrows check_symbolic_no_ended ctx fresh_reborrow
                  regions ancestors_regions nv borrowed_value_aty
              in
              (* Continue giving back in the child value *)
              let child = super#visit_typed_avalue opt_abs child in
              V.ALoan
                (V.AEndedIgnoredMutLoan { given_back; child; given_back_meta })
            else super#visit_ALoan opt_abs lc
        | V.AEndedIgnoredMutLoan
            { given_back = _; child = _; given_back_meta = _ }
        | V.AIgnoredSharedLoan _ ->
            (* Nothing special to do *)
            super#visit_ALoan opt_abs lc
      (** We are not specializing an already existing method, but adding a
          new method (for projections, we need type information) *)

      method! visit_Abs opt_abs abs =
        (* We remember in which abstraction we are before diving -
         * this is necessary for projecting values: we need to know
         * over which regions to project *)
        assert (Option.is_none opt_abs);
        super#visit_Abs (Some abs) abs
    end
  in

  (* Explore the environment *)
  let ctx = obj#visit_eval_ctx None ctx in
  (* Check we gave back to exactly one loan *)
  assert !replaced;
  (* Apply the reborrows *)
  apply_registered_reborrows ctx

(** Give back a *modified* symbolic value. *)
let give_back_symbolic_value (_config : C.config)
    (proj_regions : T.RegionId.Set.t) (proj_ty : T.rty) (sv : V.symbolic_value)
    (nsv : V.symbolic_value) (ctx : C.eval_ctx) : C.eval_ctx =
  (* Sanity checks *)
  assert (sv.sv_id <> nsv.sv_id);
  (match nsv.sv_kind with
  | V.SynthInputGivenBack | V.SynthRetGivenBack | V.FunCallGivenBack -> ()
  | V.FunCallRet | V.SynthInput -> failwith "Unrechable");
  (* Store the given-back value as a meta-value for synthesis purposes *)
  let mv = nsv in
  (* Substitution function, to replace the borrow projectors over symbolic values *)
  let subst (_abs : V.abs) local_given_back =
    (* Compute the projection over the given back value *)
    let child_proj =
      match nsv.sv_kind with
      | V.SynthRetGivenBack ->
          (* The given back value comes from the return value of the function
           * we are currently synthesizing (as it is given back, it means
           * we ended one of the regions appearing in the signature: we are
           * currently synthesizing one of the backward functions).
           * 
           * As we don't allow borrow overwrites on returned value, we can
           * (and MUST) forget the borrows *)
          V.AIgnoredProjBorrows
      | V.FunCallGivenBack ->
          (* The value was fed as input to a function, and was given back *)
          V.AProjBorrows (nsv, sv.V.sv_ty)
      | _ -> failwith "Unreachable"
    in
    V.AProjLoans (sv, (mv, child_proj) :: local_given_back)
  in
  update_intersecting_aproj_loans proj_regions proj_ty sv subst ctx

(** Auxiliary function to end borrows. See [give_back].

    This function is similar to [give_back_value] but gives back an [avalue]
    (coming from an abstraction).

    It is used when ending a borrow inside an abstraction, when the corresponding
    loan is inside the same abstraction (in which case we don't need to end the whole
    abstraction).
    
    REMARK: this function can't be used to give back the values borrowed by
    end abstraction when ending this abstraction. When doing this, we need
    to convert the [avalue] to a [value] by introducing the proper symbolic values.
 *)
let give_back_avalue_to_same_abstraction (_config : C.config)
    (bid : V.BorrowId.id) (mv : V.mvalue) (nv : V.typed_avalue)
    (ctx : C.eval_ctx) : C.eval_ctx =
  (* We use a reference to check that we updated exactly one loan *)
  let replaced : bool ref = ref false in
  let set_replaced () =
    assert (not !replaced);
    replaced := true
  in
  let obj =
    object (self)
      inherit [_] C.map_eval_ctx as super

      method! visit_typed_avalue opt_abs (av : V.typed_avalue) : V.typed_avalue
          =
        match av.V.value with
        | V.ALoan lc ->
            let value = self#visit_typed_ALoan opt_abs av.V.ty lc in
            ({ av with V.value } : V.typed_avalue)
        | _ -> super#visit_typed_avalue opt_abs av
      (** This is a bit annoying, but as we need the type of the avalue we
          are exploring, in order to be able to project the value we give
          back, we need to reimplement [visit_typed_avalue] instead of
          [visit_ALoan] *)

      method visit_typed_ALoan (opt_abs : V.abs option) (ty : T.rty)
          (lc : V.aloan_content) : V.avalue =
        match lc with
        | V.AMutLoan (bid', child) ->
            if bid' = bid then (
              (* Sanity check - about why we need to call [ty_get_ref]
               * (and don't do the same thing as in [give_back_value])
               * see the comment at the level of the definition of
               * [typed_avalue] *)
              let _, expected_ty, _ = ty_get_ref ty in
              if nv.V.ty <> expected_ty then (
                log#serror
                  ("give_back_avalue_to_same_abstraction: improper type:\n\
                    - expected: " ^ rty_to_string ctx ty ^ "\n- received: "
                 ^ rty_to_string ctx nv.V.ty);
                failwith "Value given back doesn't have the proper type");
              (* This is the loan we are looking for: apply the projection to
               * the value we give back and replaced this mutable loan with
               * an ended loan *)
              (* Register the insertion *)
              set_replaced ();
              (* Return the new value *)
              V.ALoan
                (V.AEndedMutLoan
                   { given_back = nv; child; given_back_meta = mv }))
            else (* Continue exploring *)
              super#visit_ALoan opt_abs lc
        | V.ASharedLoan (_, _, _)
        (* We are giving back a value to a *mutable* loan: nothing special to do *)
        | V.AEndedMutLoan { given_back = _; child = _; given_back_meta = _ }
        | V.AEndedSharedLoan (_, _) ->
            (* Nothing special to do *)
            super#visit_ALoan opt_abs lc
        | V.AIgnoredMutLoan (bid', child) ->
            (* This loan is ignored, but we may have to project on a subvalue
             * of the value which is given back *)
            if bid' = bid then (
              (* Note that we replace the ignored mut loan by an *ended* ignored
               * mut loan. Also, this is not the loan we are looking for *per se*:
               * we don't register the fact that we inserted the value somewhere
               * (i.e., we don't call [set_replaced]) *)
              (* Sanity check *)
              assert (nv.V.ty = ty);
              V.ALoan
                (V.AEndedIgnoredMutLoan
                   { given_back = nv; child; given_back_meta = mv }))
            else super#visit_ALoan opt_abs lc
        | V.AEndedIgnoredMutLoan
            { given_back = _; child = _; given_back_meta = _ }
        | V.AIgnoredSharedLoan _ ->
            (* Nothing special to do *)
            super#visit_ALoan opt_abs lc
      (** We are not specializing an already existing method, but adding a
          new method (for projections, we need type information) *)
    end
  in

  (* Explore the environment *)
  let ctx = obj#visit_eval_ctx None ctx in
  (* Check we gave back to exactly one loan *)
  assert !replaced;
  (* Return *)
  ctx

(** Auxiliary function to end borrows. See [give_back].
    
    When we end a shared borrow, we need to remove the borrow id from the list
    of borrows to the shared value.

    Note that this function checks that there is exactly one shared loan that
    we update.
    TODO: this was not the case before, so some sanity checks are not useful anymore.
 *)
let give_back_shared _config (bid : V.BorrowId.id) (ctx : C.eval_ctx) :
    C.eval_ctx =
  (* We use a reference to check that we updated exactly one loan *)
  let replaced : bool ref = ref false in
  let set_replaced () =
    assert (not !replaced);
    replaced := true
  in
  let obj =
    object
      inherit [_] C.map_eval_ctx as super

      method! visit_Loan opt_abs lc =
        match lc with
        | V.SharedLoan (bids, shared_value) ->
            if V.BorrowId.Set.mem bid bids then (
              (* This is the loan we are looking for *)
              set_replaced ();
              (* If there remains exactly one borrow identifier, we need
               * to end the loan. Otherwise, we just remove the current
               * loan identifier *)
              if V.BorrowId.Set.cardinal bids = 1 then shared_value.V.value
              else
                V.Loan
                  (V.SharedLoan (V.BorrowId.Set.remove bid bids, shared_value)))
            else
              (* Not the loan we are looking for: continue exploring *)
              V.Loan (super#visit_SharedLoan opt_abs bids shared_value)
        | V.MutLoan bid' ->
            (* We are giving back a *shared* borrow: nothing special to do *)
            V.Loan (super#visit_MutLoan opt_abs bid')

      method! visit_ALoan opt_abs lc =
        match lc with
        | V.AMutLoan (bid, av) ->
            (* Nothing special to do (we are giving back a *shared* borrow) *)
            V.ALoan (super#visit_AMutLoan opt_abs bid av)
        | V.ASharedLoan (bids, shared_value, child) ->
            if V.BorrowId.Set.mem bid bids then (
              (* This is the loan we are looking for *)
              set_replaced ();
              (* If there remains exactly one borrow identifier, we need
               * to end the loan. Otherwise, we just remove the current
               * loan identifier *)
              if V.BorrowId.Set.cardinal bids = 1 then
                V.ALoan (V.AEndedSharedLoan (shared_value, child))
              else
                V.ALoan
                  (V.ASharedLoan
                     (V.BorrowId.Set.remove bid bids, shared_value, child)))
            else
              (* Not the loan we are looking for: continue exploring *)
              super#visit_ALoan opt_abs lc
        | V.AEndedMutLoan { given_back = _; child = _; given_back_meta = _ }
        (* Nothing special to do (the loan has ended) *)
        | V.AEndedSharedLoan (_, _)
        (* Nothing special to do (the loan has ended) *)
        | V.AIgnoredMutLoan (_, _)
        (* Nothing special to do (we are giving back a *shared* borrow) *)
        | V.AEndedIgnoredMutLoan
            { given_back = _; child = _; given_back_meta = _ }
        (* Nothing special to do *)
        | V.AIgnoredSharedLoan _ ->
            (* Nothing special to do *)
            super#visit_ALoan opt_abs lc
    end
  in

  (* Explore the environment *)
  let ctx = obj#visit_eval_ctx None ctx in
  (* Check we gave back to exactly one loan *)
  assert !replaced;
  (* Return *)
  ctx

(** When copying values, we duplicate the shared borrows. This is tantamount
    to reborrowing the shared value. The following function applies this change
    to an environment by inserting a new borrow id in the set of borrows tracked
    by a shared value, referenced by the [original_bid] argument.
 *)
let reborrow_shared (original_bid : V.BorrowId.id) (new_bid : V.BorrowId.id)
    (ctx : C.eval_ctx) : C.eval_ctx =
  (* Keep track of changes *)
  let r = ref false in
  let set_ref () =
    assert (not !r);
    r := true
  in

  let obj =
    object
      inherit [_] C.map_env as super

      method! visit_SharedLoan env bids sv =
        (* Shared loan: check if the borrow id we are looking for is in the
           set of borrow ids. If yes, insert the new borrow id, otherwise
           explore inside the shared value *)
        if V.BorrowId.Set.mem original_bid bids then (
          set_ref ();
          let bids' = V.BorrowId.Set.add new_bid bids in
          V.SharedLoan (bids', sv))
        else super#visit_SharedLoan env bids sv

      method! visit_ASharedLoan env bids v av =
        (* This case is similar to the [SharedLoan] case *)
        if V.BorrowId.Set.mem original_bid bids then (
          set_ref ();
          let bids' = V.BorrowId.Set.add new_bid bids in
          V.ASharedLoan (bids', v, av))
        else super#visit_ASharedLoan env bids v av
    end
  in

  let env = obj#visit_env () ctx.env in
  (* Check that we reborrowed once *)
  assert !r;
  { ctx with env }

(** Auxiliary function: see [end_borrow_in_env] *)
let give_back (config : C.config) (l : V.BorrowId.id) (bc : g_borrow_content)
    (ctx : C.eval_ctx) : C.eval_ctx =
  (* Debug *)
  log#ldebug
    (lazy
      (let bc =
         match bc with
         | Concrete bc -> borrow_content_to_string ctx bc
         | Abstract bc -> aborrow_content_to_string ctx bc
       in
       "give_back:\n- bid: " ^ V.BorrowId.to_string l ^ "\n- content: " ^ bc
       ^ "\n- context:\n" ^ eval_ctx_to_string ctx ^ "\n"));
  (* This is used for sanity checks *)
  let sanity_ek =
    { enter_shared_loans = true; enter_mut_borrows = true; enter_abs = true }
  in
  match bc with
  | Concrete (V.MutBorrow (l', tv)) ->
      (* Sanity check *)
      assert (l' = l);
      assert (not (loans_in_value tv));
      (* Check that the corresponding loan is somewhere - purely a sanity check *)
      assert (Option.is_some (lookup_loan_opt sanity_ek l ctx));
      (* Update the context *)
      give_back_value config l tv ctx
  | Concrete (V.SharedBorrow (_, l') | V.InactivatedMutBorrow l') ->
      (* Sanity check *)
      assert (l' = l);
      (* Check that the borrow is somewhere - purely a sanity check *)
      assert (Option.is_some (lookup_loan_opt sanity_ek l ctx));
      (* Update the context *)
      give_back_shared config l ctx
  | Abstract (V.AMutBorrow (mv, l', av)) ->
      (* Sanity check *)
      assert (l' = l);
      (* Check that the corresponding loan is somewhere - purely a sanity check *)
      assert (Option.is_some (lookup_loan_opt sanity_ek l ctx));
      (* Update the context *)
      give_back_avalue_to_same_abstraction config l mv av ctx
  | Abstract (V.ASharedBorrow l') ->
      (* Sanity check *)
      assert (l' = l);
      (* Check that the borrow is somewhere - purely a sanity check *)
      assert (Option.is_some (lookup_loan_opt sanity_ek l ctx));
      (* Update the context *)
      give_back_shared config l ctx
  | Abstract (V.AProjSharedBorrow asb) ->
      (* Sanity check *)
      assert (borrow_in_asb l asb);
      (* Update the context *)
      give_back_shared config l ctx
  | Abstract
      (V.AEndedMutBorrow _ | V.AIgnoredMutBorrow _ | V.AEndedIgnoredMutBorrow _)
    ->
      failwith "Unreachable"

(** Convert an [avalue] to a [value].

    This function is used when ending abstractions: whenever we end a borrow
    in an abstraction, we converted the borrowed [avalue] to a fresh symbolic
    [value], then give back this [value] to the context.
 
    Note that some regions may have ended in the symbolic value we generate.
    For instance, consider the following function signature:
    ```
    fn f<'a>(x : &'a mut &'a mut u32);
    ```
    When ending the abstraction, the value given back for the outer borrow
    should be ⊥. In practice, we will give back a symbolic value which can't
    be expanded (because expanding this symbolic value would require expanding
    a reference whose region has already ended).
 *)
let convert_avalue_to_given_back_value (abs_kind : V.abs_kind)
    (av : V.typed_avalue) : V.symbolic_value =
  let sv_kind =
    match abs_kind with
    | V.FunCall -> V.FunCallGivenBack
    | V.SynthRet -> V.SynthRetGivenBack
    | V.SynthInput -> V.SynthInputGivenBack
  in
  mk_fresh_symbolic_value sv_kind av.V.ty

(** End a borrow identified by its borrow id in a context.

    Rk.: from now onwards, the functions are written in continuation passing style.
    The reason is that when ending borrows we may end abstractions, which results
    in synthesized code.
    
    First lookup the borrow in the context and replace it with [Bottom].
    Then, check that there is an associated loan in the context. When moving
    values, before putting the value in its destination, we get an
    intermediate state where some values are "outside" the context and thus
    inaccessible. As [give_back_value] just performs a map for instance (TODO:
    not the case anymore), we need to check independently that there is indeed a
    loan ready to receive the value we give back (note that we also have other
    invariants like: there is exacly one mutable loan associated to a mutable
    borrow, etc. but they are more easily maintained).
    Note that in theory, we shouldn't never reach a problematic state as the
    one we describe above, because when we move a value we need to end all the
    loans inside before moving it. Still, it is a very useful sanity check.
    Finally, give the values back.

    Of course, we end outer borrows before updating the target borrow if it
    proves necessary: this is controled by the [io] parameter. If it is [Inner],
    we allow ending inner borrows (without ending the outer borrows first),
    otherwise we only allow ending outer borrows.
    If a borrow is inside an abstraction, we need to end the whole abstraction,
    at the exception of the case where the loan corresponding to the borrow is
    inside the same abstraction. We control this with the [allowed_abs] parameter:
    if it is not `None`, we allow ending a borrow if it is inside the given
    abstraction. In practice, if the value is `Some abs_id`, we should have
    checked that the corresponding loan is inside the abstraction given by
    `abs_id` before. In practice, only [end_borrow] should call itself
    with `allowed_abs = Some ...`, all the other calls should use `allowed_abs = None`:
    if you look ath the implementation details, `end_borrow` performs
    all tne necessary checks in case a borrow is inside an abstraction.
    
    TODO: we should split this function in two: one function which doesn't
    perform anything smart and is trusted, and another function for the
    book-keeping.
 *)
let rec end_borrow (config : C.config) (chain : borrow_or_abs_ids)
    (allowed_abs : V.AbstractionId.id option) (l : V.BorrowId.id) : cm_fun =
 fun cf ctx ->
  (* Check that we don't loop *)
  let chain0 = chain in
  let chain = add_borrow_or_abs_id_to_chain "end_borrow: " (BorrowId l) chain in
  log#ldebug
    (lazy
      ("end borrow: " ^ V.BorrowId.to_string l ^ ":\n- original context:\n"
     ^ eval_ctx_to_string ctx));

  (* Utility function for the sanity checks: check that the borrow disappeared
   * from the context *)
  let ctx0 = ctx in
  let check_disappeared (ctx : C.eval_ctx) : unit =
    let _ =
      match lookup_borrow_opt ek_all l ctx with
      | None -> () (* Ok *)
      | Some _ ->
          log#lerror
            (lazy
              ("end borrow: " ^ V.BorrowId.to_string l
             ^ ": borrow didn't disappear:\n- original context:\n"
             ^ eval_ctx_to_string ctx0 ^ "\n\n- new context:\n"
             ^ eval_ctx_to_string ctx));
          failwith "Borrow not eliminated"
    in
    match lookup_loan_opt ek_all l ctx with
    | None -> () (* Ok *)
    | Some _ ->
        log#lerror
          (lazy
            ("end borrow: " ^ V.BorrowId.to_string l
           ^ ": loan didn't disappear:\n- original context:\n"
           ^ eval_ctx_to_string ctx0 ^ "\n\n- new context:\n"
           ^ eval_ctx_to_string ctx));
        failwith "Loan not eliminated"
  in
  let cf_check_disappeared : cm_fun = unit_to_cm_fun check_disappeared in
  (* The complete sanity check: also check that after we ended a borrow,
   * the invariant is preserved *)
  let cf_check : cm_fun =
    comp cf_check_disappeared (Invariants.cf_check_invariants config)
  in

  (* Start by getting the borrow *)
  match end_borrow_get_borrow allowed_abs l ctx with
  (* Two cases:
   * - error: we found outer borrows or inner loans (end them first)
   * - success: we didn't find outer borrows when updating (but maybe we actually
       didn't find the borrow we were looking for...)
   *)
  | Error priority -> (
      (* Debug *)
      log#ldebug
        (lazy
          ("end borrow: " ^ V.BorrowId.to_string l
         ^ ": found outer borrows/abs or inner loans:"
          ^ show_priority_borrows_or_abs priority));
      (* End the priority borrows, abstraction, then try again to end the target
       * borrow (if necessary) *)
      match priority with
      | OuterBorrows (Borrows bids) | InnerLoans (Borrows bids) ->
          (* Note that we might get there with `allowed_abs <> None`: we might
           * be trying to end a borrow inside an abstraction, but which is actually
           * inside another borrow *)
          let allowed_abs' = None in
          (* End the outer borrows *)
          let cc = end_borrows config chain allowed_abs' bids in
          (* Retry to end the borrow *)
          let cc = comp cc (end_borrow config chain0 allowed_abs l) in
          (* Check and apply *)
          comp cc cf_check cf ctx
      | OuterBorrows (Borrow bid) | InnerLoans (Borrow bid) ->
          let allowed_abs' = None in
          (* End the outer borrow *)
          let cc = end_borrow config chain allowed_abs' bid in
          (* Retry to end the borrow *)
          let cc = comp cc (end_borrow config chain0 allowed_abs l) in
          (* Check and apply *)
          comp cc cf_check cf ctx
      | OuterAbs abs_id ->
          (* The borrow is inside an asbtraction: check if the corresponding
           * loan is inside the same abstraction. If this is the case, we end
           * the borrow without ending the abstraction. If not, we need to
           * end the whole abstraction *)
          (* Note that we can lookup the loan anywhere *)
          let ek =
            {
              enter_shared_loans = true;
              enter_mut_borrows = true;
              enter_abs = true;
            }
          in
          let cf_end_abs : cm_fun =
            match lookup_loan ek l ctx with
            | AbsId loan_abs_id, _ ->
                if loan_abs_id = abs_id then
                  (* Same abstraction! We can end the borrow *)
                  end_borrow config chain0 (Some abs_id) l
                else
                  (* Not the same abstraction: we need to end the whole abstraction.
                   * By doing that we should have ended the target borrow (see the
                   * below sanity check) *)
                  end_abstraction config chain abs_id
            | VarId _, _ ->
                (* The loan is not inside the same abstraction (actually inside
                 * a non-abstraction value): we need to end the whole abstraction *)
                end_abstraction config chain abs_id
          in
          (* Compose with a sanity check *)
          comp cf_end_abs cf_check cf ctx)
  | Ok (ctx, None) ->
      log#ldebug (lazy "End borrow: borrow not found");
      (* It is possible that we can't find a borrow in symbolic mode (ending
       * an abstraction may end several borrows at once *)
      assert (config.mode = SymbolicMode);
      (* Do a sanity check and continue *)
      cf_check cf ctx
  (* We found a borrow: give it back (i.e., update the corresponding loan) *)
  | Ok (ctx, Some bc) ->
      (* Sanity check: the borrowed value shouldn't contain loans *)
      (match bc with
      | Concrete (V.MutBorrow (_, bv)) ->
          assert (Option.is_none (get_first_loan_in_value bv))
      | _ -> ());
      (* Give back the value *)
      let ctx = give_back config l bc ctx in
      (* Do a sanity check and continue *)
      cf_check cf ctx

and end_borrows (config : C.config) (chain : borrow_or_abs_ids)
    (allowed_abs : V.AbstractionId.id option) (lset : V.BorrowId.Set.t) : cm_fun
    =
 fun cf ->
  (* This is not necessary, but we prefer to reorder the borrow ids,
   * so that we actually end from the smallest id to the highest id - just
   * a matter of taste, and may make debugging easier *)
  let ids = V.BorrowId.Set.fold (fun id ids -> id :: ids) lset [] in
  List.fold_left (fun cf id -> end_borrow config chain allowed_abs id cf) cf ids

and end_abstraction (config : C.config) (chain : borrow_or_abs_ids)
    (abs_id : V.AbstractionId.id) : cm_fun =
 fun cf ctx ->
  (* Check that we don't loop *)
  let chain =
    add_borrow_or_abs_id_to_chain "end_abstraction: " (AbsId abs_id) chain
  in
  (* Remember the original context for printing purposes *)
  let ctx0 = ctx in
  log#ldebug
    (lazy
      ("end_abstraction: "
      ^ V.AbstractionId.to_string abs_id
      ^ "\n- original context:\n" ^ eval_ctx_to_string ctx0));

  (* Lookup the abstraction *)
  let abs = C.ctx_lookup_abs ctx abs_id in

  (* End the parent abstractions first *)
  let cc = end_abstractions config chain abs.parents in
  let cc =
    comp_unit cc (fun ctx ->
        log#ldebug
          (lazy
            ("end_abstraction: "
            ^ V.AbstractionId.to_string abs_id
            ^ "\n- context after parent abstractions ended:\n"
            ^ eval_ctx_to_string ctx)))
  in

  (* End the loans inside the abstraction *)
  let cc = comp cc (end_abstraction_loans config chain abs_id) in
  let cc =
    comp_unit cc (fun ctx ->
        log#ldebug
          (lazy
            ("end_abstraction: "
            ^ V.AbstractionId.to_string abs_id
            ^ "\n- context after loans ended:\n" ^ eval_ctx_to_string ctx)))
  in

  (* End the abstraction itself by redistributing the borrows it contains *)
  let cc = comp cc (end_abstraction_borrows config chain abs_id) in

  (* End the regions owned by the abstraction - note that we don't need to
   * relookup the abstraction: the set of regions in an abstraction never
   * changes... *)
  let cc =
    comp_update cc (fun ctx ->
        let ended_regions =
          T.RegionId.Set.union ctx.ended_regions abs.V.regions
        in
        { ctx with ended_regions })
  in

  (* Remove all the references to the id of the current abstraction, and remove
   * the abstraction itself.
   * **Rk.**: this is where we synthesize the updated symbolic AST *)
  let cc = comp cc (end_abstraction_remove_from_context config abs_id) in

  (* Debugging *)
  let cc =
    comp_unit cc (fun ctx ->
        log#ldebug
          (lazy
            ("end_abstraction: "
            ^ V.AbstractionId.to_string abs_id
            ^ "\n- original context:\n" ^ eval_ctx_to_string ctx0
            ^ "\n\n- new context:\n" ^ eval_ctx_to_string ctx)))
  in

  (* Sanity check: ending an abstraction must preserve the invariants *)
  let cc = comp cc (Invariants.cf_check_invariants config) in

  (* Apply the continuation *)
  cc cf ctx

and end_abstractions (config : C.config) (chain : borrow_or_abs_ids)
    (abs_ids : V.AbstractionId.Set.t) : cm_fun =
 fun cf ->
  (* This is not necessary, but we prefer to reorder the abstraction ids,
   * so that we actually end from the smallest id to the highest id - just
   * a matter of taste, and may make debugging easier *)
  let abs_ids = V.AbstractionId.Set.fold (fun id ids -> id :: ids) abs_ids [] in
  List.fold_left (fun cf id -> end_abstraction config chain id cf) cf abs_ids

and end_abstraction_loans (config : C.config) (chain : borrow_or_abs_ids)
    (abs_id : V.AbstractionId.id) : cm_fun =
 fun cf ctx ->
  (* Lookup the abstraction *)
  let abs = C.ctx_lookup_abs ctx abs_id in
  (* End the first loan we find *)
  let obj =
    object
      inherit [_] V.iter_abs as super

      method! visit_aloan_content env lc =
        match lc with
        | V.AMutLoan (bid, _) -> raise (FoundBorrowIds (Borrow bid))
        | V.ASharedLoan (bids, _, _) -> raise (FoundBorrowIds (Borrows bids))
        | V.AEndedMutLoan { given_back = _; child = _; given_back_meta = _ }
        | V.AEndedSharedLoan (_, _) ->
            super#visit_aloan_content env lc
        | V.AIgnoredMutLoan (_, _) ->
            (* Note that this loan can't come from a parent abstraction, because
             * we should have ended them already) *)
            super#visit_aloan_content env lc
        | V.AEndedIgnoredMutLoan
            { given_back = _; child = _; given_back_meta = _ }
        | V.AIgnoredSharedLoan _ ->
            super#visit_aloan_content env lc

      method! visit_aproj env sproj =
        (match sproj with
        | V.AProjBorrows (_, _)
        | V.AEndedProjLoans _ | V.AEndedProjBorrows _ | V.AIgnoredProjBorrows ->
            ()
        | V.AProjLoans (sv, _) -> raise (FoundSymbolicValue sv));
        super#visit_aproj env sproj
    end
  in
  try
    (* Check if there are loans *)
    obj#visit_abs () abs;
    (* No loans: nothing to update *)
    cf ctx
  with
  (* There are loans: end them, then recheck *)
  | FoundBorrowIds bids ->
      (* End the corresponding borrows *)
      let cc : cm_fun =
        match bids with
        | Borrow bid -> end_outer_borrow config bid
        | Borrows bids -> end_outer_borrows config bids
      in
      (* Reexplore, looking for loans *)
      let cc = comp cc (end_abstraction_loans config chain abs_id) in
      (* Continue *)
      cc cf ctx
  | FoundSymbolicValue sv ->
      (* There is a proj_loans over a symbolic value: end the proj_borrows
       * which intersect this proj_loans, then end the proj_loans itself *)
      let cc = end_proj_loans_symbolic config chain abs_id abs.regions sv in
      (* Reexplore, looking for loans *)
      let cc = comp cc (end_abstraction_loans config chain abs_id) in
      (* Continue *)
      cc cf ctx

and end_abstraction_borrows (config : C.config) (chain : borrow_or_abs_ids)
    (abs_id : V.AbstractionId.id) : cm_fun =
 fun cf ctx ->
  (* Note that the abstraction mustn't contain any loans *)
  (* We end the borrows, starting with the *inner* ones. This is important
     when considering nested borrows which have the same lifetime.
     TODO: is that really important? Initially, there was a concern about
     whether we should give back ⊥ or not, but everything is handled by
     the symbolic value expansion... Also, now we use the AEndedMutBorrow
     values to store the children avalues (which was not the case before - we
     initially replaced the ended mut borrows with ⊥).
  *)
  (* We explore in-depth and use exceptions. When exploring a borrow, if
   * the exploration didn't trigger an exception, it means there are no
   * inner borrows to end: we can thus trigger an exception for the current
   * borrow. *)
  let obj =
    object
      inherit [_] V.iter_abs as super

      method! visit_aborrow_content env bc =
        (* In-depth exploration *)
        super#visit_aborrow_content env bc;
        (* No exception was raise: we can raise an exception for the
         * current borrow *)
        match bc with
        | V.AMutBorrow (_, _, _) | V.ASharedBorrow _ ->
            (* Raise an exception *)
            raise (FoundABorrowContent bc)
        | V.AProjSharedBorrow asb ->
            (* Raise an exception only if the asb contains borrows *)
            if
              List.exists
                (fun x -> match x with V.AsbBorrow _ -> true | _ -> false)
                asb
            then raise (FoundABorrowContent bc)
            else ()
        | V.AEndedMutBorrow _ | V.AIgnoredMutBorrow _
        | V.AEndedIgnoredMutBorrow _ ->
            (* Nothing to do for ignored borrows *)
            ()

      method! visit_aproj env sproj =
        (match sproj with
        | V.AProjLoans _ -> failwith "Unexpected"
        | V.AProjBorrows (sv, proj_ty) ->
            raise (FoundAProjBorrows (sv, proj_ty))
        | V.AEndedProjLoans _ | V.AEndedProjBorrows _ | V.AIgnoredProjBorrows ->
            ());
        super#visit_aproj env sproj
    end
  in
  (* Lookup the abstraction *)
  let abs = C.ctx_lookup_abs ctx abs_id in
  try
    (* Explore the abstraction, looking for borrows *)
    obj#visit_abs () abs;
    (* No borrows: nothing to update *)
    cf ctx
  with
  (* There are concrete borrows: end them, then reexplore *)
  | FoundABorrowContent bc ->
      let ctx =
        match bc with
        | V.AMutBorrow (_, bid, av) ->
            (* First, convert the avalue to a (fresh symbolic) value *)
            let v = convert_avalue_to_given_back_value abs.kind av in
            (* Replace the mut borrow to register the fact that we ended
             * it and store with it the freshly generated given back value *)
            let ended_borrow = V.ABorrow (V.AEndedMutBorrow (v, av)) in
            let ctx = update_aborrow ek_all bid ended_borrow ctx in
            (* Give the value back *)
            let v = mk_typed_value_from_symbolic_value v in
            give_back_value config bid v ctx
        | V.ASharedBorrow bid ->
            (* Replace the shared borrow with bottom *)
            let ctx = update_aborrow ek_all bid V.ABottom ctx in
            (* Give back *)
            give_back_shared config bid ctx
        | V.AProjSharedBorrow asb ->
            (* Retrieve the borrow ids *)
            let bids =
              List.filter_map
                (fun asb ->
                  match asb with
                  | V.AsbBorrow bid -> Some bid
                  | V.AsbProjReborrows (_, _) -> None)
                asb
            in
            (* There should be at least one borrow identifier in the set, which we
             * can use to identify the whole set *)
            let repr_bid = List.hd bids in
            (* Replace the shared borrow with Bottom *)
            let ctx = update_aborrow ek_all repr_bid V.ABottom ctx in
            (* Give back the shared borrows *)
            let ctx =
              List.fold_left
                (fun ctx bid -> give_back_shared config bid ctx)
                ctx bids
            in
            (* Continue *)
            ctx
        | V.AEndedMutBorrow _ | V.AIgnoredMutBorrow _
        | V.AEndedIgnoredMutBorrow _ ->
            failwith "Unexpected"
      in
      (* Reexplore *)
      end_abstraction_borrows config chain abs_id cf ctx
  (* There are symbolic borrows: end them, then reexplore *)
  | FoundAProjBorrows (sv, proj_ty) ->
      (* Generate a fresh symbolic value *)
      let nsv = mk_fresh_symbolic_value V.FunCallGivenBack proj_ty in
      (* Replace the proj_borrows - there should be exactly one *)
      let ended_borrow = V.AEndedProjBorrows nsv in
      let ctx = update_aproj_borrows abs.abs_id sv ended_borrow ctx in
      (* Give back the symbolic value *)
      let ctx =
        give_back_symbolic_value config abs.regions proj_ty sv nsv ctx
      in
      (* Reexplore *)
      end_abstraction_borrows config chain abs_id cf ctx

(** Remove an abstraction from the context, as well as all its references *)
and end_abstraction_remove_from_context (_config : C.config)
    (abs_id : V.AbstractionId.id) : cm_fun =
 fun cf ctx ->
  let rec remove_from_env (env : C.env) : C.env * V.abs option =
    match env with
    | [] -> failwith "Unreachable"
    | C.Frame :: _ -> (env, None)
    | Var (bv, v) :: env ->
        let env, abs_opt = remove_from_env env in
        (Var (bv, v) :: env, abs_opt)
    | C.Abs abs :: env ->
        if abs.abs_id = abs_id then (env, Some abs)
        else
          let env, abs_opt = remove_from_env env in
          let parents = V.AbstractionId.Set.remove abs_id abs.parents in
          (C.Abs { abs with V.parents } :: env, abs_opt)
  in
  let env, abs = remove_from_env ctx.C.env in
  let ctx = { ctx with C.env } in
  let abs = Option.get abs in
  (* Apply the continuation *)
  let expr = cf ctx in
  (* Synthesize the symbolic AST *)
  S.synthesize_end_abstraction abs expr

(** End a proj_loan over a symbolic value by ending the proj_borrows which
    intersect this proj_loans.
    
    Rk.:
    - if this symbolic value is primitively copiable, then:
      - either proj_borrows are only present in the concrete context
      - or there is only one intersecting proj_borrow present in an
        abstraction
    - otherwise, this symbolic value is not primitively copiable:
      - there may be proj_borrows_shared over this value
      - if we put aside the proj_borrows_shared, there should be exactly one
        intersecting proj_borrows, either in the concrete context or in an
        abstraction
*)
and end_proj_loans_symbolic (config : C.config) (chain : borrow_or_abs_ids)
    (abs_id : V.AbstractionId.id) (regions : T.RegionId.Set.t)
    (sv : V.symbolic_value) : cm_fun =
 fun cf ctx ->
  (* Small helpers for sanity checks *)
  let check ctx = no_aproj_over_symbolic_in_context sv ctx in
  let cf_check (cf : m_fun) : m_fun =
   fun ctx ->
    check ctx;
    cf ctx
  in
  (* Find the first proj_borrows which intersects the proj_loans *)
  let explore_shared = true in
  match lookup_intersecting_aproj_borrows_opt explore_shared regions sv ctx with
  | None ->
      (* We couldn't find any in the context: it means that the symbolic value
       * is in the concrete environment (or that we dropped it, in which case
       * it is completely absent). We thus simply need to replace the loans
       * projector with an ended projector. *)
      let ctx = update_aproj_loans_to_ended abs_id sv ctx in
      (* Sanity check *)
      check ctx;
      (* Continue *)
      cf ctx
  | Some (SharedProjs projs) ->
      (* We found projectors over shared values - split between the projectors
       * which belong to the current abstraction and the others.
       * The context looks like this:
       * ```
       * abs'0 {
       *   // The loan was initially like this:
       *   // `shared_loan lids (s <: ...) [s]`
       *   // but if we get there it means it was already ended:
       *   ended_shared_loan (s <: ...) [s]
       *   proj_shared_borrows [...; (s <: ...); ...]
       *   proj_shared_borrows [...; (s <: ...); ...]
       *   ...
       * }
       *
       * abs'1 [
       *   proj_shared_borrows [...; (s <: ...); ...]
       *   ...
       * }
       *
       * ...
       *
       * // No `s` outside of abstractions
       * 
       * ```
       *)
      let _owned_projs, external_projs =
        List.partition (fun (abs_id', _) -> abs_id' = abs_id) projs
      in
      (* End the external borrow projectors (end their abstractions) *)
      let cf_end_external : cm_fun =
       fun cf ctx ->
        let abs_ids = List.map fst external_projs in
        let abs_ids =
          List.fold_left
            (fun s id -> V.AbstractionId.Set.add id s)
            V.AbstractionId.Set.empty abs_ids
        in
        (* End the abstractions and continue *)
        end_abstractions config chain abs_ids cf ctx
      in
      (* End the internal borrows projectors and the loans projector *)
      let cf_end_internal : cm_fun =
       fun cf ctx ->
        (* All the proj_borrows are owned: simply erase them *)
        let ctx = remove_intersecting_aproj_borrows_shared regions sv ctx in
        (* End the loan itself *)
        let ctx = update_aproj_loans_to_ended abs_id sv ctx in
        (* Sanity check *)
        check ctx;
        (* Continue *)
        cf ctx
      in
      (* Compose and apply *)
      let cc = comp cf_end_external cf_end_internal in
      cc cf ctx
  | Some (NonSharedProj (abs_id', _proj_ty)) ->
      (* We found one projector of borrows in an abstraction: if it comes
       * from this abstraction, we can end it directly, otherwise we need
       * to end the abstraction where it came from first *)
      if abs_id' = abs_id then (
        (* Note that it happens when a function returns a `&mut ...` which gets
         * expanded to `mut_borrow l s`, and we end the borrow `l` (so `s` gets
         * reinjected in the parent abstraction without having been modified).
         *
         * The context looks like this:
         * ```
         * abs'0 {
         *   [s <: ...]
         *   (s <: ...)
         * }
         *
         * // Note that `s` can't appear in other abstractions or in the
         * // regular environment (because we forbid the duplication of
         * // symbolic values which contain borrows).
         * ```
         *)
        (* End the projector of borrows - TODO: not completely sure what to
         * replace it with... Maybe we should introduce an ABottomProj? *)
        let ctx = update_aproj_borrows abs_id sv V.AIgnoredProjBorrows ctx in
        (* Sanity check: no other occurrence of an intersecting projector of borrows *)
        assert (
          Option.is_none
            (lookup_intersecting_aproj_borrows_opt explore_shared regions sv ctx));
        (* End the projector of loans *)
        let ctx = update_aproj_loans_to_ended abs_id sv ctx in
        (* Sanity check *)
        check ctx;
        (* Continue *)
        cf ctx)
      else
        (* The borrows proj comes from a different abstraction: end it. *)
        let cc = end_abstraction config chain abs_id' in
        (* Retry ending the projector of loans *)
        let cc =
          comp cc (end_proj_loans_symbolic config chain abs_id regions sv)
        in
        (* Sanity check *)
        let cc = comp cc cf_check in
        (* Continue *)
        cc cf ctx

and end_outer_borrow config : V.BorrowId.id -> cm_fun =
  end_borrow config [] None

and end_outer_borrows config : V.BorrowId.Set.t -> cm_fun =
  end_borrows config [] None

(** Helper function: see [activate_inactivated_mut_borrow].

    This function updates the shared loan to a mutable loan (we then update
    the borrow with another helper). Of course, the shared loan must contain
    exactly one borrow id (the one we give as parameter), otherwise we can't
    promote it. Also, the shared value mustn't contain any loan.

    The returned value (previously shared) is checked:
    - it mustn't contain loans
    - it mustn't contain [Bottom]
    - it mustn't contain inactivated borrows
    TODO: this kind of checks should be put in an auxiliary helper, because
    they are redundant
 *)
let promote_shared_loan_to_mut_loan (l : V.BorrowId.id)
    (cf : V.typed_value -> m_fun) : m_fun =
 fun ctx ->
  (* Lookup the shared loan *)
  let ek =
    { enter_shared_loans = false; enter_mut_borrows = true; enter_abs = false }
  in
  match lookup_loan ek l ctx with
  | _, Concrete (V.MutLoan _) ->
      failwith "Expected a shared loan, found a mut loan"
  | _, Concrete (V.SharedLoan (bids, sv)) ->
      (* Check that there is only one borrow id (l) and update the loan *)
      assert (V.BorrowId.Set.mem l bids && V.BorrowId.Set.cardinal bids = 1);
      (* We need to check that there aren't any loans in the value:
         we should have gotten rid of those already, but it is better
         to do a sanity check. *)
      assert (not (loans_in_value sv));
      (* Check there isn't [Bottom] (this is actually an invariant *)
      assert (not (bottom_in_value ctx.ended_regions sv));
      (* Check there aren't inactivated borrows *)
      assert (not (inactivated_in_value sv));
      (* Update the loan content *)
      let ctx = update_loan ek l (V.MutLoan l) ctx in
      (* Continue *)
      cf sv ctx
  | _, Abstract _ ->
      (* I don't think it is possible to have two-phase borrows involving borrows
       * returned by abstractions. I'm not sure how we could handle that anyway. *)
      failwith
        "Can't promote a shared loan to a mutable loan if the loan is inside \
         an abstraction"

(** Helper function: see [activate_inactivated_mut_borrow].

    This function updates a shared borrow to a mutable borrow.
 *)
let promote_inactivated_borrow_to_mut_borrow (l : V.BorrowId.id) (cf : m_fun)
    (borrowed_value : V.typed_value) : m_fun =
 fun ctx ->
  (* Lookup the inactivated borrow - note that we don't go inside borrows/loans:
     there can't be inactivated borrows inside other borrows/loans
  *)
  let ek =
    { enter_shared_loans = false; enter_mut_borrows = false; enter_abs = false }
  in
  let ctx =
    match lookup_borrow ek l ctx with
    | Concrete (V.SharedBorrow _ | V.MutBorrow (_, _)) ->
        failwith "Expected an inactivated mutable borrow"
    | Concrete (V.InactivatedMutBorrow _) ->
        (* Update it *)
        update_borrow ek l (V.MutBorrow (l, borrowed_value)) ctx
    | Abstract _ ->
        (* This can't happen for sure *)
        failwith
          "Can't promote a shared borrow to a mutable borrow if the borrow is \
           inside an abstraction"
  in
  (* Continue *)
  cf ctx

(** Promote an inactivated mut borrow to a mut borrow.

    The borrow must point to a shared value which is borrowed exactly once.
 *)
let rec activate_inactivated_mut_borrow (config : C.config) (l : V.BorrowId.id)
    : cm_fun =
 fun cf ctx ->
  (* Lookup the value *)
  let ek =
    { enter_shared_loans = false; enter_mut_borrows = true; enter_abs = false }
  in
  match lookup_loan ek l ctx with
  | _, Concrete (V.MutLoan _) -> failwith "Unreachable"
  | _, Concrete (V.SharedLoan (bids, sv)) -> (
      (* If there are loans inside the value, end them. Note that there can't be
         inactivated borrows inside the value.
         If we perform an update, do a recursive call to lookup the updated value *)
      match get_first_loan_in_value sv with
      | Some lc ->
          (* End the loans *)
          let cc =
            match lc with
            | V.SharedLoan (bids, _) -> end_outer_borrows config bids
            | V.MutLoan bid -> end_outer_borrow config bid
          in
          (* Recursive call *)
          let cc = comp cc (activate_inactivated_mut_borrow config l) in
          (* Continue *)
          cc cf ctx
      | None ->
          (* No loan to end inside the value *)
          (* Some sanity checks *)
          log#ldebug
            (lazy
              ("activate_inactivated_mut_borrow: resulting value:\n"
              ^ typed_value_to_string ctx sv));
          assert (not (loans_in_value sv));
          assert (not (bottom_in_value ctx.ended_regions sv));
          assert (not (inactivated_in_value sv));
          (* End the borrows which borrow from the value, at the exception of
             the borrow we want to promote *)
          let bids = V.BorrowId.Set.remove l bids in
          let cc = end_outer_borrows config bids in
          (* Promote the loan *)
          let cc = comp cc (promote_shared_loan_to_mut_loan l) in
          (* Promote the borrow - the value should have been checked by
             [promote_shared_loan_to_mut_loan]
          *)
          let cc =
            comp cc (fun cf borrowed_value ->
                promote_inactivated_borrow_to_mut_borrow l cf borrowed_value)
          in
          (* Continue *)
          cc cf ctx)
  | _, Abstract _ ->
      (* I don't think it is possible to have two-phase borrows involving borrows
       * returned by abstractions. I'm not sure how we could handle that anyway. *)
      failwith
        "Can't activate an inactivated mutable borrow referencing a loan inside\n\
        \         an abstraction"
