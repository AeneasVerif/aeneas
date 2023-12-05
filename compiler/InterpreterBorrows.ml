open Types
open Values
open Contexts
open Cps
open ValuesUtils
open TypesUtils
open InterpreterUtils
open InterpreterBorrowsCore
open InterpreterProjectors

(** The local logger *)
let log = Logging.borrows_log

(** Auxiliary function to end borrows: lookup a borrow in the environment,
    update it (by returning an updated environment where the borrow has been
    replaced by {!Bottom})) if we can end the borrow (for instance, it is not
    an outer borrow...) or return the reason why we couldn't update the borrow.

    [end_borrow_aux] then simply performs a loop: as long as we need to end (outer)
    borrows, we end them, before finally ending the borrow we wanted to end in the
    first place.

    - [allowed_abs]: if not [None], allows to get a borrow in the given
      abstraction without ending the whole abstraction first. This parameter
      allows us to use {!end_borrow_aux} as an auxiliary function for
      {!end_abstraction_aux} (we end all the borrows in the abstraction one by one
      before removing the abstraction from the context).
    - [allow_inner_loans]: if [true], allow to end borrows containing inner
      loans. This is used to merge borrows with abstractions, to compute loop
      fixed points for instance.
*)
let end_borrow_get_borrow (allowed_abs : AbstractionId.id option)
    (allow_inner_loans : bool) (l : BorrowId.id) (ctx : eval_ctx) :
    ( eval_ctx * (AbstractionId.id option * g_borrow_content) option,
      priority_borrows_or_abs )
    result =
  (* We use a reference to communicate the kind of borrow we found, if we
   * find one *)
  let replaced_bc : (AbstractionId.id option * g_borrow_content) option ref =
    ref None
  in
  let set_replaced_bc (abs_id : AbstractionId.id option) (bc : g_borrow_content)
      =
    assert (Option.is_none !replaced_bc);
    replaced_bc := Some (abs_id, bc)
  in
  (* Raise an exception if:
   * - there are outer borrows
   * - if we are inside an abstraction
   * - there are inner loans
   * this exception is caught in a wrapper function *)
  let raise_if_priority (outer : AbstractionId.id option * borrow_ids option)
      (borrowed_value : typed_value option) =
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
    if not allow_inner_loans then
      match borrowed_value with
      | None -> ()
      | Some v -> (
          match get_first_loan_in_value v with
          | None -> ()
          | Some c -> (
              match c with
              | VSharedLoan (bids, _) ->
                  raise (FoundPriority (InnerLoans (Borrows bids)))
              | VMutLoan bid -> raise (FoundPriority (InnerLoans (Borrow bid))))
          )
  in

  (* The environment is used to keep track of the outer loans *)
  let obj =
    object
      inherit [_] map_eval_ctx as super

      (** We reimplement {!visit_Loan} because we may have to update the
          outer borrows *)
      method! visit_VLoan (outer : AbstractionId.id option * borrow_ids option)
          lc =
        match lc with
        | VMutLoan bid -> VLoan (super#visit_VMutLoan outer bid)
        | VSharedLoan (bids, v) ->
            (* Update the outer borrows before diving into the shared value *)
            let outer = update_outer_borrows outer (Borrows bids) in
            VLoan (super#visit_VSharedLoan outer bids v)

      method! visit_VBorrow outer bc =
        match bc with
        | VSharedBorrow l' | VReservedMutBorrow l' ->
            (* Check if this is the borrow we are looking for *)
            if l = l' then (
              (* Check if there are outer borrows or if we are inside an abstraction *)
              raise_if_priority outer None;
              (* Register the update *)
              set_replaced_bc (fst outer) (Concrete bc);
              (* Update the value *)
              VBottom)
            else super#visit_VBorrow outer bc
        | VMutBorrow (l', bv) ->
            (* Check if this is the borrow we are looking for *)
            if l = l' then (
              (* Check if there are outer borrows or if we are inside an abstraction *)
              raise_if_priority outer (Some bv);
              (* Register the update *)
              set_replaced_bc (fst outer) (Concrete bc);
              (* Update the value *)
              VBottom)
            else
              (* Update the outer borrows before diving into the borrowed value *)
              let outer = update_outer_borrows outer (Borrow l') in
              VBorrow (super#visit_VMutBorrow outer l' bv)

      (** We reimplement {!visit_ALoan} because we may have to update the
          outer borrows *)
      method! visit_ALoan outer lc =
        (* Note that the children avalues are just other, independent loans,
         * so we don't need to update the outer borrows when diving in.
         * We keep track of the parents/children relationship only because we
         * need it to properly instantiate the backward functions when generating
         * the pure translation. *)
        match lc with
        | AMutLoan (_, _) ->
            (* Nothing special to do *)
            super#visit_ALoan outer lc
        | ASharedLoan (bids, v, av) ->
            (* Explore the shared value - we need to update the outer borrows *)
            let souter = update_outer_borrows outer (Borrows bids) in
            let v = super#visit_typed_value souter v in
            (* Explore the child avalue - we keep the same outer borrows *)
            let av = super#visit_typed_avalue outer av in
            (* Reconstruct *)
            ALoan (ASharedLoan (bids, v, av))
        | AEndedMutLoan { given_back = _; child = _; given_back_meta = _ }
        | AEndedSharedLoan _
        (* The loan has ended, so no need to update the outer borrows *)
        | AIgnoredMutLoan _ (* Nothing special to do *)
        | AEndedIgnoredMutLoan
            { given_back = _; child = _; given_back_meta = _ }
        (* Nothing special to do *)
        | AIgnoredSharedLoan _ ->
            (* Nothing special to do *)
            super#visit_ALoan outer lc

      method! visit_ABorrow outer bc =
        match bc with
        | AMutBorrow (bid, _) ->
            (* Check if this is the borrow we are looking for *)
            if bid = l then (
              (* TODO: treat this case differently. We should not introduce
                 a bottom value. *)
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
              set_replaced_bc (fst outer) (Abstract bc);
              (* Update the value - note that we are necessarily in the second
               * of the two cases described above.
               * Also note that, as we are moving the borrowed value inside the
               * abstraction (and not really giving the value back to the context)
               * we do not insert {!AEndedMutBorrow} but rather {!ABottom} *)
              raise (Failure "Unimplemented")
              (* ABottom *))
            else
              (* Update the outer borrows before diving into the child avalue *)
              let outer = update_outer_borrows outer (Borrow bid) in
              super#visit_ABorrow outer bc
        | ASharedBorrow bid ->
            (* Check if this is the borrow we are looking for *)
            if bid = l then (
              (* Check there are outer borrows, or if we need to end the whole
               * abstraction *)
              raise_if_priority outer None;
              (* Register the update *)
              set_replaced_bc (fst outer) (Abstract bc);
              (* Update the value - note that we are necessarily in the second
               * of the two cases described above *)
              ABottom)
            else super#visit_ABorrow outer bc
        | AIgnoredMutBorrow (_, _)
        | AEndedMutBorrow _
        | AEndedIgnoredMutBorrow
            { given_back = _; child = _; given_back_meta = _ }
        | AEndedSharedBorrow ->
            (* Nothing special to do *)
            super#visit_ABorrow outer bc
        | AProjSharedBorrow asb ->
            (* Check if the borrow we are looking for is in the asb *)
            if borrow_in_asb l asb then (
              (* Check there are outer borrows, or if we need to end the whole
               * abstraction *)
              raise_if_priority outer None;
              (* Register the update *)
              set_replaced_bc (fst outer) (Abstract bc);
              (* Update the value - note that we are necessarily in the second
               * of the two cases described above *)
              let asb = remove_borrow_from_asb l asb in
              ABorrow (AProjSharedBorrow asb))
            else (* Nothing special to do *)
              super#visit_ABorrow outer bc

      method! visit_abs outer abs =
        (* Update the outer abs *)
        let outer_abs, outer_borrows = outer in
        assert (Option.is_none outer_abs);
        assert (Option.is_none outer_borrows);
        let outer = (Some abs.abs_id, None) in
        super#visit_abs outer abs
    end
  in
  (* Catch the exceptions - raised if there are outer borrows *)
  try
    let ctx = obj#visit_eval_ctx (None, None) ctx in
    Ok (ctx, !replaced_bc)
  with FoundPriority outers -> Error outers

(** Auxiliary function to end borrows. See {!give_back}.
    
    When we end a mutable borrow, we need to "give back" the value it contained
    to its original owner by reinserting it at the proper position.

    Note that this function checks that there is exactly one loan to which we
    give the value back.
    TODO: this was not the case before, so some sanity checks are not useful anymore.
 *)
let give_back_value (config : config) (bid : BorrowId.id) (nv : typed_value)
    (ctx : eval_ctx) : eval_ctx =
  (* Sanity check *)
  assert (not (loans_in_value nv));
  assert (not (bottom_in_value ctx.ended_regions nv));
  (* Debug *)
  log#ldebug
    (lazy
      ("give_back_value:\n- bid: " ^ BorrowId.to_string bid ^ "\n- value: "
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
      inherit [_] map_eval_ctx as super

      (** This is a bit annoying, but as we need the type of the value we
          are exploring, for sanity checks, we need to implement
          {!visit_typed_avalue} instead of
          overriding {!visit_ALoan} *)
      method! visit_typed_value opt_abs (v : typed_value) : typed_value =
        match v.value with
        | VLoan lc ->
            let value = self#visit_typed_Loan opt_abs v.ty lc in
            ({ v with value } : typed_value)
        | _ -> super#visit_typed_value opt_abs v

      method visit_typed_Loan opt_abs ty lc =
        match lc with
        | VSharedLoan (bids, v) ->
            (* We are giving back a value (i.e., the content of a *mutable*
             * borrow): nothing special to do *)
            VLoan (super#visit_VSharedLoan opt_abs bids v)
        | VMutLoan bid' ->
            (* Check if this is the loan we are looking for *)
            if bid' = bid then (
              (* Sanity check *)
              let expected_ty = ty in
              if nv.ty <> expected_ty then (
                log#serror
                  ("give_back_value: improper type:\n- expected: "
                 ^ ty_to_string ctx ty ^ "\n- received: "
                 ^ ty_to_string ctx nv.ty);
                raise (Failure "Value given back doesn't have the proper type"));
              (* Replace *)
              set_replaced ();
              nv.value)
            else VLoan (super#visit_VMutLoan opt_abs bid')

      (** This is a bit annoying, but as we need the type of the avalue we
          are exploring, in order to be able to project the value we give
          back, we need to reimplement {!visit_typed_avalue} instead of
          {!visit_ALoan} *)
      method! visit_typed_avalue opt_abs (av : typed_avalue) : typed_avalue =
        match av.value with
        | ALoan lc ->
            let value = self#visit_typed_ALoan opt_abs av.ty lc in
            ({ av with value } : typed_avalue)
        | _ -> super#visit_typed_avalue opt_abs av

      (** We need to inspect ignored mutable borrows, to insert loan projectors
          if necessary.
       *)
      method! visit_ABorrow (opt_abs : abs option) (bc : aborrow_content)
          : avalue =
        match bc with
        | AIgnoredMutBorrow (bid', child) ->
            if bid' = Some bid then
              (* Insert a loans projector - note that if this case happens,
               * it is necessarily because we ended a parent abstraction,
               * and the given back value is thus a symbolic value *)
              match nv.value with
              | VSymbolic sv ->
                  let abs = Option.get opt_abs in
                  (* Remember the given back value as a meta-value
                   * TODO: it is a bit annoying to have to deconstruct
                   * the value... Think about a more elegant way. *)
                  let given_back_meta = as_symbolic nv.value in
                  (* The loan projector *)
                  let given_back =
                    mk_aproj_loans_value_from_symbolic_value abs.regions sv
                  in
                  (* Continue giving back in the child value *)
                  let child = super#visit_typed_avalue opt_abs child in
                  (* Return *)
                  ABorrow
                    (AEndedIgnoredMutBorrow
                       { given_back; child; given_back_meta })
              | _ -> raise (Failure "Unreachable")
            else
              (* Continue exploring *)
              ABorrow (super#visit_AIgnoredMutBorrow opt_abs bid' child)
        | _ ->
            (* Continue exploring *)
            super#visit_ABorrow opt_abs bc

      (** We are not specializing an already existing method, but adding a
          new method (for projections, we need type information) *)
      method visit_typed_ALoan (opt_abs : abs option) (ty : rty)
          (lc : aloan_content) : avalue =
        (* Preparing a bit *)
        let regions, ancestors_regions =
          match opt_abs with
          | None -> raise (Failure "Unreachable")
          | Some abs -> (abs.regions, abs.ancestors_regions)
        in
        (* Rk.: there is a small issue with the types of the aloan values.
         * See the comment at the level of definition of {!typed_avalue} *)
        let borrowed_value_aty =
          let _, ty, _ = ty_get_ref ty in
          ty
        in
        match lc with
        | AMutLoan (bid', child) ->
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
              ALoan (AEndedMutLoan { child; given_back; given_back_meta }))
            else (* Continue exploring *)
              super#visit_ALoan opt_abs lc
        | ASharedLoan (_, _, _) ->
            (* We are giving back a value to a *mutable* loan: nothing special to do *)
            super#visit_ALoan opt_abs lc
        | AEndedMutLoan { child = _; given_back = _; given_back_meta = _ }
        | AEndedSharedLoan (_, _) ->
            (* Nothing special to do *)
            super#visit_ALoan opt_abs lc
        | AIgnoredMutLoan (opt_bid, child) ->
            (* This loan is ignored, but we may have to project on a subvalue
             * of the value which is given back *)
            if opt_bid = Some bid then
              (* Remember the given back value as a meta-value *)
              let given_back_meta = nv in
              (* Note that we replace the ignored mut loan by an *ended* ignored
               * mut loan. Also, this is not the loan we are looking for *per se*:
               * we don't register the fact that we inserted the value somewhere
               * (i.e., we don't call {!set_replaced}) *)
              let given_back =
                apply_proj_borrows check_symbolic_no_ended ctx fresh_reborrow
                  regions ancestors_regions nv borrowed_value_aty
              in
              (* Continue giving back in the child value *)
              let child = super#visit_typed_avalue opt_abs child in
              ALoan
                (AEndedIgnoredMutLoan { given_back; child; given_back_meta })
            else super#visit_ALoan opt_abs lc
        | AEndedIgnoredMutLoan
            { given_back = _; child = _; given_back_meta = _ }
        | AIgnoredSharedLoan _ ->
            (* Nothing special to do *)
            super#visit_ALoan opt_abs lc

      method! visit_EAbs opt_abs abs =
        (* We remember in which abstraction we are before diving -
         * this is necessary for projecting values: we need to know
         * over which regions to project *)
        assert (Option.is_none opt_abs);
        super#visit_EAbs (Some abs) abs
    end
  in

  (* Explore the environment *)
  let ctx = obj#visit_eval_ctx None ctx in
  (* Check we gave back to exactly one loan *)
  assert !replaced;
  (* Apply the reborrows *)
  apply_registered_reborrows ctx

(** Give back a *modified* symbolic value. *)
let give_back_symbolic_value (_config : config) (proj_regions : RegionId.Set.t)
    (proj_ty : rty) (sv : symbolic_value) (nsv : symbolic_value)
    (ctx : eval_ctx) : eval_ctx =
  (* Sanity checks *)
  assert (sv.sv_id <> nsv.sv_id && ty_is_rty proj_ty);
  (* Store the given-back value as a meta-value for synthesis purposes *)
  let mv = nsv in
  (* Substitution function, to replace the borrow projectors over symbolic values *)
  let subst (_abs : abs) local_given_back =
    (* See the below comments: there is something wrong here *)
    let _ = raise Utils.Unimplemented in
    (* Compute the projection over the given back value *)
    let child_proj =
      (* TODO: there is something wrong here.
         Consider this:
         {[
           abs0 {'a} { AProjLoans (s0 : &'a mut T) [] }
           abs1 {'b} { AProjBorrows (s0 : &'a mut T <: &'b mut T) }
         ]}

         Upon ending abs1, we give back some fresh symbolic value [s1],
         that we reinsert where the loan for [s0] is. However, the mutable
         borrow in the type [&'a mut T] was ended: we give back a value of
         type [T]! We thus *mustn't* introduce a projector here.
      *)
      (* AProjBorrows (nsv, sv.sv_ty) *)
      raise (Failure "TODO")
    in
    AProjLoans (sv, (mv, child_proj) :: local_given_back)
  in
  update_intersecting_aproj_loans proj_regions proj_ty sv subst ctx

(** Auxiliary function to end borrows. See {!give_back}.

    This function is similar to {!give_back_value} but gives back an {!avalue}
    (coming from an abstraction).

    It is used when ending a borrow inside an abstraction, when the corresponding
    loan is inside the same abstraction (in which case we don't need to end the whole
    abstraction).
    
    REMARK: this function can't be used to give back the values borrowed by
    end abstraction when ending this abstraction. When doing this, we need
    to convert the {!avalue} to a {!type:value} by introducing the proper symbolic values.
 *)
let give_back_avalue_to_same_abstraction (_config : config) (bid : BorrowId.id)
    (nv : typed_avalue) (nsv : typed_value) (ctx : eval_ctx) : eval_ctx =
  (* We use a reference to check that we updated exactly one loan *)
  let replaced : bool ref = ref false in
  let set_replaced () =
    assert (not !replaced);
    replaced := true
  in
  let obj =
    object (self)
      inherit [_] map_eval_ctx as super

      (** This is a bit annoying, but as we need the type of the avalue we
          are exploring, in order to be able to project the value we give
          back, we need to reimplement {!visit_typed_avalue} instead of
          {!visit_ALoan}.

          TODO: it is possible to do this by remembering the type of the last
          typed avalue we entered.
       *)
      method! visit_typed_avalue opt_abs (av : typed_avalue) : typed_avalue =
        match av.value with
        | ALoan lc ->
            let value = self#visit_typed_ALoan opt_abs av.ty lc in
            ({ av with value } : typed_avalue)
        | _ -> super#visit_typed_avalue opt_abs av

      (** We are not specializing an already existing method, but adding a
          new method (for projections, we need type information).

          TODO: it is possible to do this by remembering the type of the last
          typed avalue we entered.
        *)
      method visit_typed_ALoan (opt_abs : abs option) (ty : rty)
          (lc : aloan_content) : avalue =
        match lc with
        | AMutLoan (bid', child) ->
            if bid' = bid then (
              (* Sanity check - about why we need to call {!ty_get_ref}
               * (and don't do the same thing as in {!give_back_value})
               * see the comment at the level of the definition of
               * {!typed_avalue} *)
              let _, expected_ty, _ = ty_get_ref ty in
              if nv.ty <> expected_ty then (
                log#serror
                  ("give_back_avalue_to_same_abstraction: improper type:\n\
                    - expected: " ^ ty_to_string ctx ty ^ "\n- received: "
                 ^ ty_to_string ctx nv.ty);
                raise (Failure "Value given back doesn't have the proper type"));
              (* This is the loan we are looking for: apply the projection to
               * the value we give back and replaced this mutable loan with
               * an ended loan *)
              (* Register the insertion *)
              set_replaced ();
              (* Return the new value *)
              ALoan
                (AEndedMutLoan { given_back = nv; child; given_back_meta = nsv }))
            else (* Continue exploring *)
              super#visit_ALoan opt_abs lc
        | ASharedLoan (_, _, _)
        (* We are giving back a value to a *mutable* loan: nothing special to do *)
        | AEndedMutLoan { given_back = _; child = _; given_back_meta = _ }
        | AEndedSharedLoan (_, _) ->
            (* Nothing special to do *)
            super#visit_ALoan opt_abs lc
        | AIgnoredMutLoan (bid_opt, child) ->
            (* This loan is ignored, but we may have to project on a subvalue
             * of the value which is given back *)
            if bid_opt = Some bid then (
              (* Note that we replace the ignored mut loan by an *ended* ignored
               * mut loan. Also, this is not the loan we are looking for *per se*:
               * we don't register the fact that we inserted the value somewhere
               * (i.e., we don't call {!set_replaced}) *)
              (* Sanity check *)
              assert (nv.ty = ty);
              ALoan
                (AEndedIgnoredMutLoan
                   { given_back = nv; child; given_back_meta = nsv }))
            else super#visit_ALoan opt_abs lc
        | AEndedIgnoredMutLoan
            { given_back = _; child = _; given_back_meta = _ }
        | AIgnoredSharedLoan _ ->
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

(** Auxiliary function to end borrows. See  {!give_back}.
    
    When we end a shared borrow, we need to remove the borrow id from the list
    of borrows to the shared value.

    Note that this function checks that there is exactly one shared loan that
    we update.
    TODO: this was not the case before, so some sanity checks are not useful anymore.
 *)
let give_back_shared _config (bid : BorrowId.id) (ctx : eval_ctx) : eval_ctx =
  (* We use a reference to check that we updated exactly one loan *)
  let replaced : bool ref = ref false in
  let set_replaced () =
    assert (not !replaced);
    replaced := true
  in
  let obj =
    object
      inherit [_] map_eval_ctx as super

      method! visit_VLoan opt_abs lc =
        match lc with
        | VSharedLoan (bids, shared_value) ->
            if BorrowId.Set.mem bid bids then (
              (* This is the loan we are looking for *)
              set_replaced ();
              (* If there remains exactly one borrow identifier, we need
               * to end the loan. Otherwise, we just remove the current
               * loan identifier *)
              if BorrowId.Set.cardinal bids = 1 then shared_value.value
              else
                VLoan (VSharedLoan (BorrowId.Set.remove bid bids, shared_value)))
            else
              (* Not the loan we are looking for: continue exploring *)
              VLoan (super#visit_VSharedLoan opt_abs bids shared_value)
        | VMutLoan bid' ->
            (* We are giving back a *shared* borrow: nothing special to do *)
            VLoan (super#visit_VMutLoan opt_abs bid')

      method! visit_ALoan opt_abs lc =
        match lc with
        | AMutLoan (bid, av) ->
            (* Nothing special to do (we are giving back a *shared* borrow) *)
            ALoan (super#visit_AMutLoan opt_abs bid av)
        | ASharedLoan (bids, shared_value, child) ->
            if BorrowId.Set.mem bid bids then (
              (* This is the loan we are looking for *)
              set_replaced ();
              (* If there remains exactly one borrow identifier, we need
               * to end the loan. Otherwise, we just remove the current
               * loan identifier *)
              if BorrowId.Set.cardinal bids = 1 then
                ALoan (AEndedSharedLoan (shared_value, child))
              else
                ALoan
                  (ASharedLoan
                     (BorrowId.Set.remove bid bids, shared_value, child)))
            else
              (* Not the loan we are looking for: continue exploring *)
              super#visit_ALoan opt_abs lc
        | AEndedMutLoan { given_back = _; child = _; given_back_meta = _ }
        (* Nothing special to do (the loan has ended) *)
        | AEndedSharedLoan (_, _)
        (* Nothing special to do (the loan has ended) *)
        | AIgnoredMutLoan (_, _)
        (* Nothing special to do (we are giving back a *shared* borrow) *)
        | AEndedIgnoredMutLoan
            { given_back = _; child = _; given_back_meta = _ }
        (* Nothing special to do *)
        | AIgnoredSharedLoan _ ->
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
let reborrow_shared (original_bid : BorrowId.id) (new_bid : BorrowId.id)
    (ctx : eval_ctx) : eval_ctx =
  (* Keep track of changes *)
  let r = ref false in
  let set_ref () =
    assert (not !r);
    r := true
  in

  let obj =
    object
      inherit [_] map_env as super

      method! visit_VSharedLoan env bids sv =
        (* Shared loan: check if the borrow id we are looking for is in the
           set of borrow ids. If yes, insert the new borrow id, otherwise
           explore inside the shared value *)
        if BorrowId.Set.mem original_bid bids then (
          set_ref ();
          let bids' = BorrowId.Set.add new_bid bids in
          VSharedLoan (bids', sv))
        else super#visit_VSharedLoan env bids sv

      method! visit_ASharedLoan env bids v av =
        (* This case is similar to the {!SharedLoan} case *)
        if BorrowId.Set.mem original_bid bids then (
          set_ref ();
          let bids' = BorrowId.Set.add new_bid bids in
          ASharedLoan (bids', v, av))
        else super#visit_ASharedLoan env bids v av
    end
  in

  let env = obj#visit_env () ctx.env in
  (* Check that we reborrowed once *)
  assert !r;
  { ctx with env }

(** Convert an {!type:avalue} to a {!type:value}.

    This function is used when ending abstractions: whenever we end a borrow
    in an abstraction, we converted the borrowed {!avalue} to a fresh symbolic
    {!type:value}, then give back this {!type:value} to the context.

    Note that some regions may have ended in the symbolic value we generate.
    For instance, consider the following function signature:
    {[
      fn f<'a>(x : &'a mut &'a mut u32);
    ]}
    When ending the abstraction, the value given back for the outer borrow
    should be ⊥. In practice, we will give back a symbolic value which can't
    be expanded (because expanding this symbolic value would require expanding
    a reference whose region has already ended).
 *)
let convert_avalue_to_given_back_value (abs_kind : abs_kind) (av : typed_avalue)
    : symbolic_value =
  mk_fresh_symbolic_value av.ty

(** Auxiliary function: see {!end_borrow_aux}.

    When we end a mutable borrow, we need to "give back" the value it contained
    to its original owner by reinserting it at the proper position.

    Rem.: this function is used when we end *one single* borrow (we don't
    end this borrow as member of the group of borrows belonging to an
    abstraction).
    If the borrow is an "abstract" borrow, it means we are ending a borrow
    inside an abstraction (we end a borrow whose corresponding loan is in
    the same abstraction - we are allowed to do so without ending the whole
    abstraction).
    TODO: we should not treat this case here, and should only consider internal
    borrows. This kind of internal reshuffling. should be similar to ending
    abstractions (it is tantamount to ending *sub*-abstractions).
 *)
let give_back (config : config) (abs_id_opt : AbstractionId.id option)
    (l : BorrowId.id) (bc : g_borrow_content) (ctx : eval_ctx) : eval_ctx =
  (* Debug *)
  log#ldebug
    (lazy
      (let bc =
         match bc with
         | Concrete bc -> borrow_content_to_string ctx bc
         | Abstract bc -> aborrow_content_to_string ctx bc
       in
       "give_back:\n- bid: " ^ BorrowId.to_string l ^ "\n- content: " ^ bc
       ^ "\n- context:\n" ^ eval_ctx_to_string ctx ^ "\n"));
  (* This is used for sanity checks *)
  let sanity_ek =
    { enter_shared_loans = true; enter_mut_borrows = true; enter_abs = true }
  in
  match bc with
  | Concrete (VMutBorrow (l', tv)) ->
      (* Sanity check *)
      assert (l' = l);
      assert (not (loans_in_value tv));
      (* Check that the corresponding loan is somewhere - purely a sanity check *)
      assert (Option.is_some (lookup_loan_opt sanity_ek l ctx));
      (* Update the context *)
      give_back_value config l tv ctx
  | Concrete (VSharedBorrow l' | VReservedMutBorrow l') ->
      (* Sanity check *)
      assert (l' = l);
      (* Check that the borrow is somewhere - purely a sanity check *)
      assert (Option.is_some (lookup_loan_opt sanity_ek l ctx));
      (* Update the context *)
      give_back_shared config l ctx
  | Abstract (AMutBorrow (l', av)) ->
      (* Sanity check *)
      assert (l' = l);
      (* Check that the corresponding loan is somewhere - purely a sanity check *)
      assert (Option.is_some (lookup_loan_opt sanity_ek l ctx));
      (* Convert the avalue to a (fresh symbolic) value.

         Rem.: we shouldn't do this here. We should do this in a function
         which takes care of ending *sub*-abstractions.
      *)
      let abs_id = Option.get abs_id_opt in
      let abs = ctx_lookup_abs ctx abs_id in
      let sv = convert_avalue_to_given_back_value abs.kind av in
      (* Update the context *)
      give_back_avalue_to_same_abstraction config l av
        (mk_typed_value_from_symbolic_value sv)
        ctx
  | Abstract (ASharedBorrow l') ->
      (* Sanity check *)
      assert (l' = l);
      (* Check that the borrow is somewhere - purely a sanity check *)
      assert (Option.is_some (lookup_loan_opt sanity_ek l ctx));
      (* Update the context *)
      give_back_shared config l ctx
  | Abstract (AProjSharedBorrow asb) ->
      (* Sanity check *)
      assert (borrow_in_asb l asb);
      (* Update the context *)
      give_back_shared config l ctx
  | Abstract
      ( AEndedMutBorrow _ | AIgnoredMutBorrow _ | AEndedIgnoredMutBorrow _
      | AEndedSharedBorrow ) ->
      raise (Failure "Unreachable")

let check_borrow_disappeared (fun_name : string) (l : BorrowId.id)
    (ctx0 : eval_ctx) : cm_fun =
  let check_disappeared (ctx : eval_ctx) : unit =
    let _ =
      match lookup_borrow_opt ek_all l ctx with
      | None -> () (* Ok *)
      | Some _ ->
          log#lerror
            (lazy
              (fun_name ^ ": " ^ BorrowId.to_string l
             ^ ": borrow didn't disappear:\n- original context:\n"
             ^ eval_ctx_to_string ctx0 ^ "\n\n- new context:\n"
             ^ eval_ctx_to_string ctx));
          raise (Failure "Borrow not eliminated")
    in
    match lookup_loan_opt ek_all l ctx with
    | None -> () (* Ok *)
    | Some _ ->
        log#lerror
          (lazy
            (fun_name ^ ": " ^ BorrowId.to_string l
           ^ ": loan didn't disappear:\n- original context:\n"
           ^ eval_ctx_to_string ctx0 ^ "\n\n- new context:\n"
           ^ eval_ctx_to_string ctx));
        raise (Failure "Loan not eliminated")
  in
  unit_to_cm_fun check_disappeared

(** End a borrow identified by its borrow id in a context.

    This function **preserves invariants** provided [allowed_abs] is [None]: if the
    borrow is inside another borrow/an abstraction, we end the outer borrow/abstraction
    first, etc.

    [allowed_abs]: see the comment for {!end_borrow_get_borrow}.

    [chain]: contains the list of borrows/abstraction ids on which {!end_borrow_aux}
    and {!end_abstraction_aux} were called, to remember the chain of calls. This is
    useful for debugging purposes, and also for sanity checks to detect cycles
    (which shouldn't happen if the environment is well-formed).

    Rk.: from now onwards, the functions are written in continuation passing style.
    The reason is that when ending borrows we may end abstractions, which requires
    generating code for the translation (and we do this in CPS).
    
    TODO: we should split this function in two: one function which doesn't
    perform anything smart and is trusted, and another function for the
    book-keeping.
 *)
let rec end_borrow_aux (config : config) (chain : borrow_or_abs_ids)
    (allowed_abs : AbstractionId.id option) (l : BorrowId.id) : cm_fun =
 fun cf ctx ->
  (* Check that we don't loop *)
  let chain0 = chain in
  let chain =
    add_borrow_or_abs_id_to_chain "end_borrow_aux: " (BorrowId l) chain
  in
  log#ldebug
    (lazy
      ("end borrow: " ^ BorrowId.to_string l ^ ":\n- original context:\n"
     ^ eval_ctx_to_string ctx));

  (* Utility function for the sanity checks: check that the borrow disappeared
   * from the context *)
  let ctx0 = ctx in
  let cf_check : cm_fun = check_borrow_disappeared "end borrow" l ctx0 in
  (* Start by ending the borrow itself (we lookup it up and replace it with [Bottom] *)
  let allow_inner_loans = false in
  match end_borrow_get_borrow allowed_abs allow_inner_loans l ctx with
  (* Two cases:
     - error: we found outer borrows (the borrow is inside a borrowed value) or
       inner loans (the borrow contains loans)
     - success: we didn't find outer borrows when updating (but maybe we actually
       didn't find the borrow we were looking for...). The borrow was successfully
       replaced with [Bottom], and we can proceed to ending the corresponding loan.

     Note that if [allowed_abs] is [Some abs_id] and the borrow is inside the
     abstraction identified by [abs_id], the abstraction is ignored (i.e.:
     {!end_borrow_get_borrow} won't return [Error] because of the abstraction
     itself).
  *)
  | Error priority -> (
      (* Debug *)
      log#ldebug
        (lazy
          ("end borrow: " ^ BorrowId.to_string l
         ^ ": found outer borrows/abs or inner loans:"
          ^ show_priority_borrows_or_abs priority));
      (* End the priority borrows, abstractions, then try again to end the target
       * borrow (if necessary) *)
      match priority with
      | OuterBorrows (Borrows bids) | InnerLoans (Borrows bids) ->
          (* Note that we might get there with [allowed_abs <> None]: we might
           * be trying to end a borrow inside an abstraction, but which is actually
           * inside another borrow *)
          let allowed_abs' = None in
          (* End the outer borrows *)
          let cc = end_borrows_aux config chain allowed_abs' bids in
          (* Retry to end the borrow *)
          let cc = comp cc (end_borrow_aux config chain0 allowed_abs l) in
          (* Check and apply *)
          comp cc cf_check cf ctx
      | OuterBorrows (Borrow bid) | InnerLoans (Borrow bid) ->
          let allowed_abs' = None in
          (* End the outer borrow *)
          let cc = end_borrow_aux config chain allowed_abs' bid in
          (* Retry to end the borrow *)
          let cc = comp cc (end_borrow_aux config chain0 allowed_abs l) in
          (* Check and apply *)
          comp cc cf_check cf ctx
      | OuterAbs abs_id ->
          (* The borrow is inside an abstraction: end the whole abstraction *)
          let cf_end_abs = end_abstraction_aux config chain abs_id in
          (* Compose with a sanity check *)
          comp cf_end_abs cf_check cf ctx)
  | Ok (ctx, None) ->
      log#ldebug (lazy "End borrow: borrow not found");
      (* It is possible that we can't find a borrow in symbolic mode (ending
       * an abstraction may end several borrows at once *)
      assert (config.mode = SymbolicMode);
      (* Do a sanity check and continue *)
      cf_check cf ctx
  (* We found a borrow and replaced it with [Bottom]: give it back (i.e., update
     the corresponding loan) *)
  | Ok (ctx, Some (abs_id_opt, bc)) ->
      (* Sanity check: the borrowed value shouldn't contain loans *)
      (match bc with
      | Concrete (VMutBorrow (_, bv)) ->
          assert (Option.is_none (get_first_loan_in_value bv))
      | _ -> ());
      (* Give back the value *)
      let ctx = give_back config abs_id_opt l bc ctx in
      (* Do a sanity check and continue *)
      cf_check cf ctx

and end_borrows_aux (config : config) (chain : borrow_or_abs_ids)
    (allowed_abs : AbstractionId.id option) (lset : BorrowId.Set.t) : cm_fun =
 fun cf ->
  (* This is not necessary, but we prefer to reorder the borrow ids,
   * so that we actually end from the smallest id to the highest id - just
   * a matter of taste, and may make debugging easier *)
  let ids = BorrowId.Set.fold (fun id ids -> id :: ids) lset [] in
  List.fold_left
    (fun cf id -> end_borrow_aux config chain allowed_abs id cf)
    cf ids

and end_abstraction_aux (config : config) (chain : borrow_or_abs_ids)
    (abs_id : AbstractionId.id) : cm_fun =
 fun cf ctx ->
  (* Check that we don't loop *)
  let chain =
    add_borrow_or_abs_id_to_chain "end_abstraction_aux: " (AbsId abs_id) chain
  in
  (* Remember the original context for printing purposes *)
  let ctx0 = ctx in
  log#ldebug
    (lazy
      ("end_abstraction_aux: "
      ^ AbstractionId.to_string abs_id
      ^ "\n- original context:\n" ^ eval_ctx_to_string ctx0));

  (* Lookup the abstraction *)
  let abs = ctx_lookup_abs ctx abs_id in

  (* Check that we can end the abstraction *)
  if abs.can_end then ()
  else
    raise
      (Failure
         ("Can't end abstraction "
         ^ AbstractionId.to_string abs.abs_id
         ^ " as it is set as non-endable"));

  (* End the parent abstractions first *)
  let cc = end_abstractions_aux config chain abs.parents in
  let cc =
    comp_unit cc (fun ctx ->
        log#ldebug
          (lazy
            ("end_abstraction_aux: "
            ^ AbstractionId.to_string abs_id
            ^ "\n- context after parent abstractions ended:\n"
            ^ eval_ctx_to_string ctx)))
  in

  (* End the loans inside the abstraction *)
  let cc = comp cc (end_abstraction_loans config chain abs_id) in
  let cc =
    comp_unit cc (fun ctx ->
        log#ldebug
          (lazy
            ("end_abstraction_aux: "
            ^ AbstractionId.to_string abs_id
            ^ "\n- context after loans ended:\n" ^ eval_ctx_to_string ctx)))
  in

  (* End the abstraction itself by redistributing the borrows it contains *)
  let cc = comp cc (end_abstraction_borrows config chain abs_id) in

  (* End the regions owned by the abstraction - note that we don't need to
   * relookup the abstraction: the set of regions in an abstraction never
   * changes... *)
  let cc =
    comp_update cc (fun ctx ->
        let ended_regions = RegionId.Set.union ctx.ended_regions abs.regions in
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
            ("end_abstraction_aux: "
            ^ AbstractionId.to_string abs_id
            ^ "\n- original context:\n" ^ eval_ctx_to_string ctx0
            ^ "\n\n- new context:\n" ^ eval_ctx_to_string ctx)))
  in

  (* Sanity check: ending an abstraction must preserve the invariants *)
  let cc = comp cc Invariants.cf_check_invariants in

  (* Apply the continuation *)
  cc cf ctx

and end_abstractions_aux (config : config) (chain : borrow_or_abs_ids)
    (abs_ids : AbstractionId.Set.t) : cm_fun =
 fun cf ->
  (* This is not necessary, but we prefer to reorder the abstraction ids,
   * so that we actually end from the smallest id to the highest id - just
   * a matter of taste, and may make debugging easier *)
  let abs_ids = AbstractionId.Set.fold (fun id ids -> id :: ids) abs_ids [] in
  List.fold_left
    (fun cf id -> end_abstraction_aux config chain id cf)
    cf abs_ids

and end_abstraction_loans (config : config) (chain : borrow_or_abs_ids)
    (abs_id : AbstractionId.id) : cm_fun =
 fun cf ctx ->
  (* Lookup the abstraction *)
  let abs = ctx_lookup_abs ctx abs_id in
  (* End the first loan we find.
   *
   * We ignore the "ignored mut/shared loans": as we should have already ended
   * the parent abstractions, they necessarily come from children. *)
  let opt_loan = get_first_non_ignored_aloan_in_abstraction abs in
  match opt_loan with
  | None ->
      (* No loans: nothing to update *)
      cf ctx
  | Some (BorrowIds bids) ->
      (* There are loans: end the corresponding borrows, then recheck *)
      let cc : cm_fun =
        match bids with
        | Borrow bid -> end_borrow_aux config chain None bid
        | Borrows bids -> end_borrows_aux config chain None bids
      in
      (* Reexplore, looking for loans *)
      let cc = comp cc (end_abstraction_loans config chain abs_id) in
      (* Continue *)
      cc cf ctx
  | Some (SymbolicValue sv) ->
      (* There is a proj_loans over a symbolic value: end the proj_borrows
       * which intersect this proj_loans, then end the proj_loans itself *)
      let cc = end_proj_loans_symbolic config chain abs_id abs.regions sv in
      (* Reexplore, looking for loans *)
      let cc = comp cc (end_abstraction_loans config chain abs_id) in
      (* Continue *)
      cc cf ctx

and end_abstraction_borrows (config : config) (chain : borrow_or_abs_ids)
    (abs_id : AbstractionId.id) : cm_fun =
 fun cf ctx ->
  log#ldebug
    (lazy
      ("end_abstraction_borrows: abs_id: " ^ AbstractionId.to_string abs_id));
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
   * borrow.
   *
   * TODO: there should be a function in InterpreterBorrowsCore which does just
   * that.
   *)
  let obj =
    object
      inherit [_] iter_abs as super

      method! visit_aborrow_content env bc =
        (* In-depth exploration *)
        super#visit_aborrow_content env bc;
        (* No exception was raise: we can raise an exception for the
         * current borrow *)
        match bc with
        | AMutBorrow _ | ASharedBorrow _ ->
            (* Raise an exception *)
            raise (FoundABorrowContent bc)
        | AProjSharedBorrow asb ->
            (* Raise an exception only if the asb contains borrows *)
            if
              List.exists
                (fun x -> match x with AsbBorrow _ -> true | _ -> false)
                asb
            then raise (FoundABorrowContent bc)
            else ()
        | AEndedMutBorrow _ | AIgnoredMutBorrow _ | AEndedIgnoredMutBorrow _
        | AEndedSharedBorrow ->
            (* Nothing to do for ignored borrows *)
            ()

      method! visit_aproj env sproj =
        (match sproj with
        | AProjLoans _ -> raise (Failure "Unexpected")
        | AProjBorrows (sv, proj_ty) -> raise (FoundAProjBorrows (sv, proj_ty))
        | AEndedProjLoans _ | AEndedProjBorrows _ | AIgnoredProjBorrows -> ());
        super#visit_aproj env sproj

      (** We may need to end borrows in "regular" values, because of shared values *)
      method! visit_borrow_content _ bc =
        match bc with
        | VSharedBorrow _ | VMutBorrow (_, _) -> raise (FoundBorrowContent bc)
        | VReservedMutBorrow _ -> raise (Failure "Unreachable")
    end
  in
  (* Lookup the abstraction *)
  let abs = ctx_lookup_abs ctx abs_id in
  try
    (* Explore the abstraction, looking for borrows *)
    obj#visit_abs () abs;
    (* No borrows: nothing to update *)
    cf ctx
  with
  (* There are concrete (i.e., not symbolic) borrows: end them, then reexplore *)
  | FoundABorrowContent bc ->
      log#ldebug
        (lazy
          ("end_abstraction_borrows: found aborrow content: "
          ^ aborrow_content_to_string ctx bc));
      let ctx =
        match bc with
        | AMutBorrow (bid, av) ->
            (* First, convert the avalue to a (fresh symbolic) value *)
            let sv = convert_avalue_to_given_back_value abs.kind av in
            (* Replace the mut borrow to register the fact that we ended
             * it and store with it the freshly generated given back value *)
            let ended_borrow = ABorrow (AEndedMutBorrow (sv, av)) in
            let ctx = update_aborrow ek_all bid ended_borrow ctx in
            (* Give the value back *)
            let sv = mk_typed_value_from_symbolic_value sv in
            give_back_value config bid sv ctx
        | ASharedBorrow bid ->
            (* Replace the shared borrow to account for the fact it ended *)
            let ended_borrow = ABorrow AEndedSharedBorrow in
            let ctx = update_aborrow ek_all bid ended_borrow ctx in
            (* Give back *)
            give_back_shared config bid ctx
        | AProjSharedBorrow asb ->
            (* Retrieve the borrow ids *)
            let bids =
              List.filter_map
                (fun asb ->
                  match asb with
                  | AsbBorrow bid -> Some bid
                  | AsbProjReborrows (_, _) -> None)
                asb
            in
            (* There should be at least one borrow identifier in the set, which we
             * can use to identify the whole set *)
            let repr_bid = List.hd bids in
            (* Replace the shared borrow with Bottom *)
            let ctx = update_aborrow ek_all repr_bid ABottom ctx in
            (* Give back the shared borrows *)
            let ctx =
              List.fold_left
                (fun ctx bid -> give_back_shared config bid ctx)
                ctx bids
            in
            (* Continue *)
            ctx
        | AEndedMutBorrow _ | AIgnoredMutBorrow _ | AEndedIgnoredMutBorrow _
        | AEndedSharedBorrow ->
            raise (Failure "Unexpected")
      in
      (* Reexplore *)
      end_abstraction_borrows config chain abs_id cf ctx
  (* There are symbolic borrows: end them, then reexplore *)
  | FoundAProjBorrows (sv, proj_ty) ->
      log#ldebug
        (lazy
          ("end_abstraction_borrows: found aproj borrows: "
          ^ aproj_to_string ctx (AProjBorrows (sv, proj_ty))));
      (* Generate a fresh symbolic value *)
      let nsv = mk_fresh_symbolic_value proj_ty in
      (* Replace the proj_borrows - there should be exactly one *)
      let ended_borrow = AEndedProjBorrows nsv in
      let ctx = update_aproj_borrows abs.abs_id sv ended_borrow ctx in
      (* Give back the symbolic value *)
      let ctx =
        give_back_symbolic_value config abs.regions proj_ty sv nsv ctx
      in
      (* Reexplore *)
      end_abstraction_borrows config chain abs_id cf ctx
  (* There are concrete (i.e., not symbolic) borrows in shared values: end them, then reexplore *)
  | FoundBorrowContent bc ->
      log#ldebug
        (lazy
          ("end_abstraction_borrows: found borrow content: "
          ^ borrow_content_to_string ctx bc));
      let ctx =
        match bc with
        | VSharedBorrow bid -> (
            (* Replace the shared borrow with bottom *)
            let allow_inner_loans = false in
            match
              end_borrow_get_borrow (Some abs_id) allow_inner_loans bid ctx
            with
            | Error _ -> raise (Failure "Unreachable")
            | Ok (ctx, _) ->
                (* Give back *)
                give_back_shared config bid ctx)
        | VMutBorrow (bid, v) -> (
            (* Replace the mut borrow with bottom *)
            let allow_inner_loans = false in
            match
              end_borrow_get_borrow (Some abs_id) allow_inner_loans bid ctx
            with
            | Error _ -> raise (Failure "Unreachable")
            | Ok (ctx, _) ->
                (* Give the value back - note that the mut borrow was below a
                 * shared borrow: the value is thus unchanged *)
                give_back_value config bid v ctx)
        | VReservedMutBorrow _ -> raise (Failure "Unreachable")
      in
      (* Reexplore *)
      end_abstraction_borrows config chain abs_id cf ctx

(** Remove an abstraction from the context, as well as all its references *)
and end_abstraction_remove_from_context (_config : config)
    (abs_id : AbstractionId.id) : cm_fun =
 fun cf ctx ->
  let ctx, abs = ctx_remove_abs ctx abs_id in
  let abs = Option.get abs in
  (* Apply the continuation *)
  let expr = cf ctx in
  (* Synthesize the symbolic AST *)
  SynthesizeSymbolic.synthesize_end_abstraction ctx abs expr

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
and end_proj_loans_symbolic (config : config) (chain : borrow_or_abs_ids)
    (abs_id : AbstractionId.id) (regions : RegionId.Set.t) (sv : symbolic_value)
    : cm_fun =
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
         which belong to the current abstraction and the others.
         The context looks like this:
         {[
           abs'0 {
             // The loan was initially like this:
             // [shared_loan lids (s <: ...) [s]]
             // but if we get there it means it was already ended:
             ended_shared_loan (s <: ...) [s]
             proj_shared_borrows [...; (s <: ...); ...]
             proj_shared_borrows [...; (s <: ...); ...]
             ...
           }

           abs'1 [
             proj_shared_borrows [...; (s <: ...); ...]
             ...
           }

           ...

           // No [s] outside of abstractions

         ]}
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
            (fun s id -> AbstractionId.Set.add id s)
            AbstractionId.Set.empty abs_ids
        in
        (* End the abstractions and continue *)
        end_abstractions_aux config chain abs_ids cf ctx
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
        (* Note that it happens when a function returns a [&mut ...] which gets
           expanded to [mut_borrow l s], and we end the borrow [l] (so [s] gets
           reinjected in the parent abstraction without having been modified).

           The context looks like this:
           {[
             abs'0 {
               [s <: ...]
               (s <: ...)
             }

             // Note that [s] can't appear in other abstractions or in the
             // regular environment (because we forbid the duplication of
             // symbolic values which contain borrows).
           ]}
        *)
        (* End the projector of borrows - TODO: not completely sure what to
         * replace it with... Maybe we should introduce an ABottomProj? *)
        let ctx = update_aproj_borrows abs_id sv AIgnoredProjBorrows ctx in
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
        let cc = end_abstraction_aux config chain abs_id' in
        (* Retry ending the projector of loans *)
        let cc =
          comp cc (end_proj_loans_symbolic config chain abs_id regions sv)
        in
        (* Sanity check *)
        let cc = comp cc cf_check in
        (* Continue *)
        cc cf ctx

let end_borrow config : BorrowId.id -> cm_fun = end_borrow_aux config [] None

let end_borrows config : BorrowId.Set.t -> cm_fun =
  end_borrows_aux config [] None

let end_abstraction config = end_abstraction_aux config []
let end_abstractions config = end_abstractions_aux config []

let end_borrow_no_synth config id ctx =
  get_cf_ctx_no_synth (end_borrow config id) ctx

let end_borrows_no_synth config ids ctx =
  get_cf_ctx_no_synth (end_borrows config ids) ctx

let end_abstraction_no_synth config id ctx =
  get_cf_ctx_no_synth (end_abstraction config id) ctx

let end_abstractions_no_synth config ids ctx =
  get_cf_ctx_no_synth (end_abstractions config ids) ctx

(** Helper function: see {!activate_reserved_mut_borrow}.

    This function updates the shared loan to a mutable loan (we then update
    the borrow with another helper). Of course, the shared loan must contain
    exactly one borrow id (the one we give as parameter), otherwise we can't
    promote it. Also, the shared value mustn't contain any loan.

    The returned value (previously shared) is checked:
    - it mustn't contain loans
    - it mustn't contain {!Bottom}
    - it mustn't contain reserved borrows
    TODO: this kind of checks should be put in an auxiliary helper, because
    they are redundant.

    The loan to update mustn't be a borrowed value.
 *)
let promote_shared_loan_to_mut_loan (l : BorrowId.id)
    (cf : typed_value -> m_fun) : m_fun =
 fun ctx ->
  (* Debug *)
  log#ldebug
    (lazy
      ("promote_shared_loan_to_mut_loan:\n- loan: " ^ BorrowId.to_string l
     ^ "\n- context:\n" ^ eval_ctx_to_string ctx ^ "\n"));
  (* Lookup the shared loan - note that we can't promote a shared loan
   * in a shared value, but we can do it in a mutably borrowed value.
   * This is important because we can do: [let y = &two-phase ( *x );]
   *)
  let ek =
    { enter_shared_loans = false; enter_mut_borrows = true; enter_abs = false }
  in
  match lookup_loan ek l ctx with
  | _, Concrete (VMutLoan _) ->
      raise (Failure "Expected a shared loan, found a mut loan")
  | _, Concrete (VSharedLoan (bids, sv)) ->
      (* Check that there is only one borrow id (l) and update the loan *)
      assert (BorrowId.Set.mem l bids && BorrowId.Set.cardinal bids = 1);
      (* We need to check that there aren't any loans in the value:
         we should have gotten rid of those already, but it is better
         to do a sanity check. *)
      assert (not (loans_in_value sv));
      (* Check there isn't {!Bottom} (this is actually an invariant *)
      assert (not (bottom_in_value ctx.ended_regions sv));
      (* Check there aren't reserved borrows *)
      assert (not (reserved_in_value sv));
      (* Update the loan content *)
      let ctx = update_loan ek l (VMutLoan l) ctx in
      (* Continue *)
      cf sv ctx
  | _, Abstract _ ->
      (* I don't think it is possible to have two-phase borrows involving borrows
       * returned by abstractions. I'm not sure how we could handle that anyway. *)
      raise
        (Failure
           "Can't promote a shared loan to a mutable loan if the loan is \
            inside an abstraction")

(** Helper function: see {!activate_reserved_mut_borrow}.

    This function updates a shared borrow to a mutable borrow (and that is
    all: it doesn't touch the corresponding loan).
 *)
let replace_reserved_borrow_with_mut_borrow (l : BorrowId.id) (cf : m_fun)
    (borrowed_value : typed_value) : m_fun =
 fun ctx ->
  (* Lookup the reserved borrow - note that we don't go inside borrows/loans:
     there can't be reserved borrows inside other borrows/loans
  *)
  let ek =
    { enter_shared_loans = false; enter_mut_borrows = false; enter_abs = false }
  in
  let ctx =
    match lookup_borrow ek l ctx with
    | Concrete (VSharedBorrow _ | VMutBorrow (_, _)) ->
        raise (Failure "Expected a reserved mutable borrow")
    | Concrete (VReservedMutBorrow _) ->
        (* Update it *)
        update_borrow ek l (VMutBorrow (l, borrowed_value)) ctx
    | Abstract _ ->
        (* This can't happen for sure *)
        raise
          (Failure
             "Can't promote a shared borrow to a mutable borrow if the borrow \
              is inside an abstraction")
  in
  (* Continue *)
  cf ctx

(** Promote a reserved mut borrow to a mut borrow. *)
let rec promote_reserved_mut_borrow (config : config) (l : BorrowId.id) : cm_fun
    =
 fun cf ctx ->
  (* Lookup the value *)
  let ek =
    { enter_shared_loans = false; enter_mut_borrows = true; enter_abs = false }
  in
  match lookup_loan ek l ctx with
  | _, Concrete (VMutLoan _) -> raise (Failure "Unreachable")
  | _, Concrete (VSharedLoan (bids, sv)) -> (
      (* If there are loans inside the value, end them. Note that there can't be
         reserved borrows inside the value.
         If we perform an update, do a recursive call to lookup the updated value *)
      match get_first_loan_in_value sv with
      | Some lc ->
          (* End the loans *)
          let cc =
            match lc with
            | VSharedLoan (bids, _) -> end_borrows config bids
            | VMutLoan bid -> end_borrow config bid
          in
          (* Recursive call *)
          let cc = comp cc (promote_reserved_mut_borrow config l) in
          (* Continue *)
          cc cf ctx
      | None ->
          (* No loan to end inside the value *)
          (* Some sanity checks *)
          log#ldebug
            (lazy
              ("activate_reserved_mut_borrow: resulting value:\n"
              ^ typed_value_to_string ctx sv));
          assert (not (loans_in_value sv));
          assert (not (bottom_in_value ctx.ended_regions sv));
          assert (not (reserved_in_value sv));
          (* End the borrows which borrow from the value, at the exception of
             the borrow we want to promote *)
          let bids = BorrowId.Set.remove l bids in
          let cc = end_borrows config bids in
          (* Promote the loan - TODO: this will fail if the value contains
           * any loans. In practice, it shouldn't, but we could also
           * look for loans inside the value and end them before promoting
           * the borrow. *)
          let cc = comp cc (promote_shared_loan_to_mut_loan l) in
          (* Promote the borrow - the value should have been checked by
             {!promote_shared_loan_to_mut_loan}
          *)
          let cc =
            comp cc (fun cf borrowed_value ->
                replace_reserved_borrow_with_mut_borrow l cf borrowed_value)
          in
          (* Continue *)
          cc cf ctx)
  | _, Abstract _ ->
      (* I don't think it is possible to have two-phase borrows involving borrows
       * returned by abstractions. I'm not sure how we could handle that anyway. *)
      raise
        (Failure
           "Can't activate a reserved mutable borrow referencing a loan inside\n\
           \         an abstraction")

let destructure_abs (abs_kind : abs_kind) (can_end : bool)
    (destructure_shared_values : bool) (ctx : eval_ctx) (abs0 : abs) : abs =
  (* Accumulator to store the destructured values *)
  let avalues = ref [] in
  (* Utility function to store a value in the accumulator *)
  let push_avalue av = avalues := List.append !avalues [ av ] in
  (* We use this function to make sure we never register values (i.e.,
     loans or borrows) when we shouldn't - see it as a sanity check:
     for now, we don't allow nested borrows, which means we should register
     values from children of borrows. In this condition, we could simply
     ignore the children altogether. Instead, we explore them and make sure
     we don't register values while doing so.
  *)
  let push_fail _ = raise (Failure "Unreachable") in
  (* Function to explore an avalue and destructure it *)
  let rec list_avalues (allow_borrows : bool) (push : typed_avalue -> unit)
      (av : typed_avalue) : unit =
    let ty = av.ty in
    match av.value with
    | ABottom | AIgnored -> ()
    | AAdt adt ->
        (* Simply explore the children *)
        List.iter (list_avalues allow_borrows push) adt.field_values
    | ALoan lc -> (
        (* Explore the loan content *)
        match lc with
        | ASharedLoan (bids, sv, child_av) ->
            (* We don't support nested borrows for now *)
            assert (not (value_has_borrows ctx sv.value));
            (* Destructure the shared value *)
            let avl, sv =
              if destructure_shared_values then list_values sv else ([], sv)
            in
            (* Push a value *)
            let ignored = mk_aignored child_av.ty in
            let value = ALoan (ASharedLoan (bids, sv, ignored)) in
            push { value; ty };
            (* Explore the child *)
            list_avalues false push_fail child_av;
            (* Push the avalues introduced because we decomposed the inner loans -
               note that we pay attention to the order in which we introduce
               the avalues: we want to push them *after* the outer loan. If we
               didn't want that, we would have implemented [list_values] in
               exactly the same way as [list_avalues] (i.e., with a similar
               signature) *)
            List.iter push avl
        | AMutLoan (bid, child_av) ->
            (* Explore the child *)
            list_avalues false push_fail child_av;
            (* Explore the whole loan *)
            let ignored = mk_aignored child_av.ty in
            let value = ALoan (AMutLoan (bid, ignored)) in
            push { value; ty }
        | AIgnoredMutLoan (opt_bid, child_av) ->
            (* We don't support nested borrows for now *)
            assert (not (ty_has_borrows ctx.type_context.type_infos child_av.ty));
            assert (opt_bid = None);
            (* Simply explore the child *)
            list_avalues false push_fail child_av
        | AEndedMutLoan
            { child = child_av; given_back = _; given_back_meta = _ }
        | AEndedSharedLoan (_, child_av)
        | AEndedIgnoredMutLoan
            { child = child_av; given_back = _; given_back_meta = _ }
        | AIgnoredSharedLoan child_av ->
            (* We don't support nested borrows for now *)
            assert (not (ty_has_borrows ctx.type_context.type_infos child_av.ty));
            (* Simply explore the child *)
            list_avalues false push_fail child_av)
    | ABorrow bc -> (
        (* Sanity check - rem.: may be redundant with [push_fail] *)
        assert allow_borrows;
        (* Explore the borrow content *)
        match bc with
        | AMutBorrow (bid, child_av) ->
            (* Explore the child *)
            list_avalues false push_fail child_av;
            (* Explore the borrow *)
            let ignored = mk_aignored child_av.ty in
            let value = ABorrow (AMutBorrow (bid, ignored)) in
            push { value; ty }
        | ASharedBorrow _ ->
            (* Nothing specific to do: keep the value as it is *)
            push av
        | AIgnoredMutBorrow (opt_bid, child_av) ->
            (* We don't support nested borrows for now *)
            assert (not (ty_has_borrows ctx.type_context.type_infos child_av.ty));
            assert (opt_bid = None);
            (* Just explore the child *)
            list_avalues false push_fail child_av
        | AEndedIgnoredMutBorrow
            { child = child_av; given_back = _; given_back_meta = _ } ->
            (* We don't support nested borrows for now *)
            assert (not (ty_has_borrows ctx.type_context.type_infos child_av.ty));
            (* Just explore the child *)
            list_avalues false push_fail child_av
        | AProjSharedBorrow asb ->
            (* We don't support nested borrows *)
            assert (asb = []);
            (* Nothing specific to do *)
            ()
        | AEndedMutBorrow _ | AEndedSharedBorrow ->
            (* If we get there it means the abstraction ended: it should not
               be in the context anymore (if we end *one* borrow in an abstraction,
               we have to end them all and remove the abstraction from the context)
            *)
            raise (Failure "Unreachable"))
    | ASymbolic _ ->
        (* For now, we fore all symbolic values containing borrows to be eagerly
           expanded *)
        assert (not (ty_has_borrows ctx.type_context.type_infos ty))
  and list_values (v : typed_value) : typed_avalue list * typed_value =
    let ty = v.ty in
    match v.value with
    | VLiteral _ -> ([], v)
    | VAdt adt ->
        let avll, field_values =
          List.split (List.map list_values adt.field_values)
        in
        let avl = List.concat avll in
        let adt = { adt with field_values } in
        (avl, { v with value = VAdt adt })
    | VBottom -> raise (Failure "Unreachable")
    | VBorrow _ ->
        (* We don't support nested borrows for now *)
        raise (Failure "Unreachable")
    | VLoan lc -> (
        match lc with
        | VSharedLoan (bids, sv) ->
            let avl, sv = list_values sv in
            if destructure_shared_values then (
              (* Rem.: the shared value can't contain loans nor borrows *)
              assert (ty_no_regions ty);
              let av : typed_avalue =
                assert (not (value_has_loans_or_borrows ctx sv.value));
                (* We introduce fresh ids for the symbolic values *)
                let mk_value_with_fresh_sids (v : typed_value) : typed_value =
                  let visitor =
                    object
                      inherit [_] map_typed_avalue

                      method! visit_symbolic_value_id _ _ =
                        fresh_symbolic_value_id ()
                    end
                  in
                  visitor#visit_typed_value () v
                in
                let sv = mk_value_with_fresh_sids sv in
                (* Create the new avalue *)
                let value = ALoan (ASharedLoan (bids, sv, mk_aignored ty)) in
                { value; ty }
              in
              let avl = List.append [ av ] avl in
              (avl, sv))
            else (avl, { v with value = VLoan (VSharedLoan (bids, sv)) })
        | VMutLoan _ -> raise (Failure "Unreachable"))
    | VSymbolic _ ->
        (* For now, we fore all symbolic values containing borrows to be eagerly
           expanded *)
        assert (not (ty_has_borrows ctx.type_context.type_infos ty));
        ([], v)
  in

  (* Destructure the avalues *)
  List.iter (list_avalues true push_avalue) abs0.avalues;
  let avalues = !avalues in
  (* Update *)
  { abs0 with avalues; kind = abs_kind; can_end }

let abs_is_destructured (destructure_shared_values : bool) (ctx : eval_ctx)
    (abs : abs) : bool =
  let abs' =
    destructure_abs abs.kind abs.can_end destructure_shared_values ctx abs
  in
  abs = abs'

let convert_value_to_abstractions (abs_kind : abs_kind) (can_end : bool)
    (destructure_shared_values : bool) (ctx : eval_ctx) (v : typed_value) :
    abs list =
  (* Convert the value to a list of avalues *)
  let absl = ref [] in
  let push_abs (r_id : RegionId.id) (avalues : typed_avalue list) : unit =
    if avalues = [] then ()
    else
      (* Create the abs - note that we keep the order of the avalues as it is
         (unlike the environments) *)
      let abs =
        {
          abs_id = fresh_abstraction_id ();
          kind = abs_kind;
          can_end;
          parents = AbstractionId.Set.empty;
          original_parents = [];
          regions = RegionId.Set.singleton r_id;
          ancestors_regions = RegionId.Set.empty;
          avalues;
        }
      in
      (* Add to the list of abstractions *)
      absl := abs :: !absl
  in

  (* [group]: group in one abstraction (because we dived into a borrow/loan)

     We return one typed-value for the shared values: when we encounter a shared
     loan, we need to compute the value which will be shared. If [destructure_shared_values]
     is [true], this shared value will be stripped of its shared loans.
  *)
  let rec to_avalues (allow_borrows : bool) (inside_borrowed : bool)
      (group : bool) (r_id : RegionId.id) (v : typed_value) :
      typed_avalue list * typed_value =
    (* Debug *)
    log#ldebug
      (lazy
        ("convert_value_to_abstractions: to_avalues:\n- value: "
        ^ typed_value_to_string ctx v));

    let ty = v.ty in
    match v.value with
    | VLiteral _ -> ([], v)
    | VBottom ->
        (* Can happen: we *do* convert dummy values to abstractions, and dummy
           values can contain bottoms *)
        ([], v)
    | VAdt adt ->
        (* Two cases, depending on whether we have to group all the borrows/loans
           inside one abstraction or not *)
        let avl, field_values =
          if group then
            (* Convert to avalues, and transmit to the parent *)
            let avl, field_values =
              List.split
                (List.map
                   (to_avalues allow_borrows inside_borrowed group r_id)
                   adt.field_values)
            in
            (List.concat avl, field_values)
          else
            (* Create one abstraction per field, and transmit nothing to the parent *)
            let field_values =
              List.map
                (fun fv ->
                  let r_id = fresh_region_id () in
                  let avl, fv =
                    to_avalues allow_borrows inside_borrowed group r_id fv
                  in
                  push_abs r_id avl;
                  fv)
                (* Slightly tricky: pay attention to the order in which the
                   abstractions are pushed (i.e.: the [List.rev] is important
                   to get a "good" environment, and a nice translation) *)
                (List.rev adt.field_values)
            in
            ([], field_values)
        in
        let adt = { adt with field_values } in
        (avl, { v with value = VAdt adt })
    | VBorrow bc -> (
        let _, ref_ty, kind = ty_as_ref ty in
        assert (ty_no_regions ref_ty);
        (* Sanity check *)
        assert allow_borrows;
        (* Convert the borrow content *)
        match bc with
        | VSharedBorrow bid ->
            assert (ty_no_regions ref_ty);
            let ty = TRef (RFVar r_id, ref_ty, kind) in
            let value = ABorrow (ASharedBorrow bid) in
            ([ { value; ty } ], v)
        | VMutBorrow (bid, bv) ->
            let r_id = if group then r_id else fresh_region_id () in
            (* We don't support nested borrows for now *)
            assert (not (value_has_borrows ctx bv.value));
            (* Create an avalue to push - note that we use [AIgnore] for the inner avalue *)
            let ty = TRef (RFVar r_id, ref_ty, kind) in
            let ignored = mk_aignored ref_ty in
            let av = ABorrow (AMutBorrow (bid, ignored)) in
            let av = { value = av; ty } in
            (* Continue exploring, looking for loans (and forbidding borrows,
               because we don't support nested borrows for now) *)
            let avl, bv = to_avalues false true true r_id bv in
            let value = { v with value = VBorrow (VMutBorrow (bid, bv)) } in
            (av :: avl, value)
        | VReservedMutBorrow _ ->
            (* This borrow should have been activated *)
            raise (Failure "Unexpected"))
    | VLoan lc -> (
        match lc with
        | VSharedLoan (bids, sv) ->
            let r_id = if group then r_id else fresh_region_id () in
            (* We don't support nested borrows for now *)
            assert (not (value_has_borrows ctx sv.value));
            (* Push the avalue - note that we use [AIgnore] for the inner avalue *)
            (* For avalues, a loan has the borrow type *)
            assert (ty_no_regions ty);
            let ty = mk_ref_ty (RFVar r_id) ty RShared in
            let ignored = mk_aignored ty in
            (* Rem.: the shared value might contain loans *)
            let avl, sv = to_avalues false true true r_id sv in
            let av = ALoan (ASharedLoan (bids, sv, ignored)) in
            let av = { value = av; ty } in
            (* Continue exploring, looking for loans (and forbidding borrows,
               because we don't support nested borrows for now) *)
            let value : value =
              if destructure_shared_values then sv.value
              else VLoan (VSharedLoan (bids, sv))
            in
            let value = { v with value } in
            (av :: avl, value)
        | VMutLoan bid ->
            (* Push the avalue - note that we use [AIgnore] for the inner avalue *)
            (* For avalues, a loan has the borrow type *)
            assert (ty_no_regions ty);
            let ty = mk_ref_ty (RFVar r_id) ty RMut in
            let ignored = mk_aignored ty in
            let av = ALoan (AMutLoan (bid, ignored)) in
            let av = { value = av; ty } in
            ([ av ], v))
    | VSymbolic _ ->
        (* For now, we force all the symbolic values containing borrows to
           be eagerly expanded, and we don't support nested borrows *)
        assert (not (value_has_borrows ctx v.value));
        (* Return nothing *)
        ([], v)
  in
  (* Generate the avalues *)
  let r_id = fresh_region_id () in
  let values, _ = to_avalues true false false r_id v in
  (* Introduce an abstraction for the returned values *)
  push_abs r_id values;
  (* Return *)
  List.rev !absl

type borrow_or_loan_id = BorrowId of borrow_id | LoanId of loan_id

type g_loan_content_with_ty =
  (ety * loan_content, rty * aloan_content) concrete_or_abs

type g_borrow_content_with_ty =
  (ety * borrow_content, rty * aborrow_content) concrete_or_abs

type merge_abstraction_info = {
  loans : loan_id_set;
  borrows : borrow_id_set;
  borrows_loans : borrow_or_loan_id list;
      (** We use a list to preserve the order in which the borrows were found *)
  loan_to_content : g_loan_content_with_ty BorrowId.Map.t;
  borrow_to_content : g_borrow_content_with_ty BorrowId.Map.t;
}

(** Small utility to help merging abstractions.

    We compute the list of loan/borrow contents, maps from borrow/loan ids
    to borrow/loan contents, etc.

    Note that this function is very specific to [merge_into_abstraction]: we
    have strong assumptions about the shape of the abstraction, and in
    particular that:
    - its values don't contain nested borrows
    - all the borrows are destructured (for instance, shared loans can't
      contain shared loans).
 *)
let compute_merge_abstraction_info (ctx : eval_ctx) (abs : abs) :
    merge_abstraction_info =
  let loans : loan_id_set ref = ref BorrowId.Set.empty in
  let borrows : borrow_id_set ref = ref BorrowId.Set.empty in
  let borrows_loans : borrow_or_loan_id list ref = ref [] in
  let loan_to_content : g_loan_content_with_ty BorrowId.Map.t ref =
    ref BorrowId.Map.empty
  in
  let borrow_to_content : g_borrow_content_with_ty BorrowId.Map.t ref =
    ref BorrowId.Map.empty
  in

  let push_loans ids (lc : g_loan_content_with_ty) : unit =
    assert (BorrowId.Set.disjoint !loans ids);
    loans := BorrowId.Set.union !loans ids;
    BorrowId.Set.iter
      (fun id ->
        assert (not (BorrowId.Map.mem id !loan_to_content));
        loan_to_content := BorrowId.Map.add id lc !loan_to_content;
        borrows_loans := LoanId id :: !borrows_loans)
      ids
  in
  let push_loan id (lc : g_loan_content_with_ty) : unit =
    assert (not (BorrowId.Set.mem id !loans));
    loans := BorrowId.Set.add id !loans;
    assert (not (BorrowId.Map.mem id !loan_to_content));
    loan_to_content := BorrowId.Map.add id lc !loan_to_content;
    borrows_loans := LoanId id :: !borrows_loans
  in
  let push_borrow id (bc : g_borrow_content_with_ty) : unit =
    assert (not (BorrowId.Set.mem id !borrows));
    borrows := BorrowId.Set.add id !borrows;
    assert (not (BorrowId.Map.mem id !borrow_to_content));
    borrow_to_content := BorrowId.Map.add id bc !borrow_to_content;
    borrows_loans := BorrowId id :: !borrows_loans
  in

  let iter_avalues =
    object
      inherit [_] iter_typed_avalue as super

      (** We redefine this to track the types *)
      method! visit_typed_avalue _ v =
        super#visit_typed_avalue (Some (Abstract v.ty)) v

      (** We redefine this to track the types *)
      method! visit_typed_value _ (v : typed_value) =
        super#visit_typed_value (Some (Concrete v.ty)) v

      method! visit_loan_content env lc =
        (* Can happen if we explore shared values whose sub-values are
           reborrowed *)
        let ty =
          match Option.get env with
          | Concrete ty -> ty
          | Abstract _ -> raise (Failure "Unreachable")
        in
        (match lc with
        | VSharedLoan (bids, _) -> push_loans bids (Concrete (ty, lc))
        | VMutLoan _ -> raise (Failure "Unreachable"));
        (* Continue *)
        super#visit_loan_content env lc

      method! visit_borrow_content _ _ =
        (* Can happen if we explore shared values which contain borrows -
           i.e., if we have nested borrows (we forbid this for now) *)
        raise (Failure "Unreachable")

      method! visit_aloan_content env lc =
        let ty =
          match Option.get env with
          | Concrete _ -> raise (Failure "Unreachable")
          | Abstract ty -> ty
        in
        (* Register the loans *)
        (match lc with
        | ASharedLoan (bids, _, _) -> push_loans bids (Abstract (ty, lc))
        | AMutLoan (bid, _) -> push_loan bid (Abstract (ty, lc))
        | AEndedMutLoan _ | AEndedSharedLoan _ | AIgnoredMutLoan _
        | AEndedIgnoredMutLoan _ | AIgnoredSharedLoan _ ->
            (* The abstraction has been destructured, so those shouldn't appear *)
            raise (Failure "Unreachable"));
        (* Continue *)
        super#visit_aloan_content env lc

      method! visit_aborrow_content env bc =
        let ty =
          match Option.get env with
          | Concrete _ -> raise (Failure "Unreachable")
          | Abstract ty -> ty
        in
        (* Explore the borrow content *)
        (match bc with
        | AMutBorrow (bid, _) -> push_borrow bid (Abstract (ty, bc))
        | ASharedBorrow bid -> push_borrow bid (Abstract (ty, bc))
        | AProjSharedBorrow asb ->
            let register asb =
              match asb with
              | AsbBorrow bid -> push_borrow bid (Abstract (ty, bc))
              | AsbProjReborrows _ ->
                  (* Can only happen if the symbolic value (potentially) contains
                     borrows - i.e., we have nested borrows *)
                  raise (Failure "Unreachable")
            in
            List.iter register asb
        | AIgnoredMutBorrow _ | AEndedIgnoredMutBorrow _ | AEndedMutBorrow _
        | AEndedSharedBorrow ->
            (* The abstraction has been destructured, so those shouldn't appear *)
            raise (Failure "Unreachable"));
        super#visit_aborrow_content env bc

      method! visit_symbolic_value _ sv =
        (* Sanity check: no borrows *)
        assert (not (symbolic_value_has_borrows ctx sv))
    end
  in

  List.iter (iter_avalues#visit_typed_avalue None) abs.avalues;

  {
    loans = !loans;
    borrows = !borrows;
    borrows_loans = List.rev !borrows_loans;
    loan_to_content = !loan_to_content;
    borrow_to_content = !borrow_to_content;
  }

type merge_duplicates_funcs = {
  merge_amut_borrows :
    borrow_id -> rty -> typed_avalue -> rty -> typed_avalue -> typed_avalue;
      (** Parameters:
          - [id]
          - [ty0]
          - [child0]
          - [ty1]
          - [child1]

          The children should be [AIgnored].
       *)
  merge_ashared_borrows : borrow_id -> rty -> rty -> typed_avalue;
      (** Parameters:
          - [id]
          - [ty0]
          - [ty1]
       *)
  merge_amut_loans :
    loan_id -> rty -> typed_avalue -> rty -> typed_avalue -> typed_avalue;
      (** Parameters:
          - [id]
          - [ty0]
          - [child0]
          - [ty1]
          - [child1]

          The children should be [AIgnored].
       *)
  merge_ashared_loans :
    loan_id_set ->
    rty ->
    typed_value ->
    typed_avalue ->
    rty ->
    typed_value ->
    typed_avalue ->
    typed_avalue;
      (** Parameters:
          - [ids]
          - [ty0]
          - [sv0]
          - [child0]
          - [ty1]
          - [sv1]
          - [child1]
       *)
}

(** Auxiliary function.

    Merge two abstractions into one, without updating the context.
 *)
let merge_into_abstraction_aux (abs_kind : abs_kind) (can_end : bool)
    (merge_funs : merge_duplicates_funcs option) (ctx : eval_ctx) (abs0 : abs)
    (abs1 : abs) : abs =
  log#ldebug
    (lazy
      ("merge_into_abstraction_aux:\n- abs0:\n" ^ abs_to_string ctx abs0
     ^ "\n\n- abs1:\n" ^ abs_to_string ctx abs1));

  (* Check that the abstractions are destructured *)
  if !Config.sanity_checks then (
    let destructure_shared_values = true in
    assert (abs_is_destructured destructure_shared_values ctx abs0);
    assert (abs_is_destructured destructure_shared_values ctx abs1));

  (* Compute the relevant information *)
  let {
    loans = loans0;
    borrows = borrows0;
    borrows_loans = borrows_loans0;
    loan_to_content = loan_to_content0;
    borrow_to_content = borrow_to_content0;
  } =
    compute_merge_abstraction_info ctx abs0
  in

  let {
    loans = loans1;
    borrows = borrows1;
    borrows_loans = borrows_loans1;
    loan_to_content = loan_to_content1;
    borrow_to_content = borrow_to_content1;
  } =
    compute_merge_abstraction_info ctx abs1
  in

  (* Sanity check: there is no loan/borrows which appears in both abstractions,
     unless we allow to merge duplicates *)
  if merge_funs = None then (
    assert (BorrowId.Set.disjoint borrows0 borrows1);
    assert (BorrowId.Set.disjoint loans0 loans1));

  (* Merge.
     There are several cases:
     - if a borrow/loan is only in one abstraction, we simply check if we need
       to filter it (because its associated loan/borrow is in the other
       abstraction).
     - if a borrow/loan is present in both abstractions, we need to merge its
       content.

     Note that it is possible that we may need to merge strictly more than 2 avalues,
     because of shared loans. For instance, if we have:
     {[
       abs'0 { shared_loan { l0, l1 } ... }
       abs'1 { shared_loan { l0 } ..., shared_loan { l1 } ... }
     ]}

     We ignore this case for now: we check that whenever we merge two shared loans,
     then their sets of ids are equal.
  *)
  let merged_borrows = ref BorrowId.Set.empty in
  let merged_loans = ref BorrowId.Set.empty in
  let avalues = ref [] in
  let push_avalue av =
    log#ldebug
      (lazy
        ("merge_into_abstraction_aux: push_avalue: "
        ^ typed_avalue_to_string ctx av));
    avalues := av :: !avalues
  in
  let push_opt_avalue av =
    match av with None -> () | Some av -> push_avalue av
  in

  let intersect =
    BorrowId.Set.union
      (BorrowId.Set.inter loans0 borrows1)
      (BorrowId.Set.inter loans1 borrows0)
  in
  let filter_bids (bids : BorrowId.Set.t) : BorrowId.Set.t =
    let bids = BorrowId.Set.diff bids intersect in
    assert (not (BorrowId.Set.is_empty bids));
    bids
  in
  let filter_bid (bid : BorrowId.id) : BorrowId.id option =
    if BorrowId.Set.mem bid intersect then None else Some bid
  in

  let borrow_is_merged id = BorrowId.Set.mem id !merged_borrows in
  let set_borrow_as_merged id =
    merged_borrows := BorrowId.Set.add id !merged_borrows
  in
  let loan_is_merged id = BorrowId.Set.mem id !merged_loans in
  let set_loan_as_merged id =
    merged_loans := BorrowId.Set.add id !merged_loans
  in
  let set_loans_as_merged ids = BorrowId.Set.iter set_loan_as_merged ids in

  (* Some utility functions *)
  (* Merge two aborrow contents - note that those contents must have the same id *)
  let merge_aborrow_contents (ty0 : rty) (bc0 : aborrow_content) (ty1 : rty)
      (bc1 : aborrow_content) : typed_avalue =
    match (bc0, bc1) with
    | AMutBorrow (id, child0), AMutBorrow (_, child1) ->
        (Option.get merge_funs).merge_amut_borrows id ty0 child0 ty1 child1
    | ASharedBorrow id, ASharedBorrow _ ->
        (Option.get merge_funs).merge_ashared_borrows id ty0 ty1
    | AProjSharedBorrow _, AProjSharedBorrow _ ->
        (* Unreachable because requires nested borrows *)
        raise (Failure "Unreachable")
    | _ ->
        (* Unreachable because those cases are ignored (ended/ignored borrows)
           or inconsistent *)
        raise (Failure "Unreachable")
  in

  let merge_g_borrow_contents (bc0 : g_borrow_content_with_ty)
      (bc1 : g_borrow_content_with_ty) : typed_avalue =
    match (bc0, bc1) with
    | Concrete _, Concrete _ ->
        (* This can happen only in case of nested borrows *)
        raise (Failure "Unreachable")
    | Abstract (ty0, bc0), Abstract (ty1, bc1) ->
        merge_aborrow_contents ty0 bc0 ty1 bc1
    | Concrete _, Abstract _ | Abstract _, Concrete _ ->
        (* TODO: is it really unreachable? *)
        raise (Failure "Unreachable")
  in

  let merge_aloan_contents (ty0 : rty) (lc0 : aloan_content) (ty1 : rty)
      (lc1 : aloan_content) : typed_avalue option =
    match (lc0, lc1) with
    | AMutLoan (id, child0), AMutLoan (_, child1) ->
        (* Register the loan id *)
        set_loan_as_merged id;
        (* Merge *)
        Some ((Option.get merge_funs).merge_amut_loans id ty0 child0 ty1 child1)
    | ASharedLoan (ids0, sv0, child0), ASharedLoan (ids1, sv1, child1) ->
        (* Filter the ids *)
        let ids0 = filter_bids ids0 in
        let ids1 = filter_bids ids1 in
        (* Check that the sets of ids are the same - if it is not the case, it
           means we actually need to merge more than 2 avalues: we ignore this
           case for now *)
        assert (BorrowId.Set.equal ids0 ids1);
        let ids = ids0 in
        if BorrowId.Set.is_empty ids then (
          (* If the set of ids is empty, we can eliminate this shared loan.
             For now, we check that we can eliminate the whole shared value
             altogether.
             A more complete approach would be to explore the value and introduce
             as many shared loans/borrows/etc. as necessary for the sub-values.
             For now, we check that there are no such values that we would need
             to preserve (in practice it works because we destructure the
             shared values in the abstractions, and forbid nested borrows).
          *)
          assert (not (value_has_loans_or_borrows ctx sv0.value));
          assert (not (value_has_loans_or_borrows ctx sv0.value));
          assert (is_aignored child0.value);
          assert (is_aignored child1.value);
          None)
        else (
          (* Register the loan ids *)
          set_loans_as_merged ids;
          (* Merge *)
          Some
            ((Option.get merge_funs).merge_ashared_loans ids ty0 sv0 child0 ty1
               sv1 child1))
    | _ ->
        (* Unreachable because those cases are ignored (ended/ignored borrows)
           or inconsistent *)
        raise (Failure "Unreachable")
  in

  (* Note that because we may filter ids from a set of id, this function has
     to register the merged loan ids: the caller doesn't do it (contrary to
     the borrow case) *)
  let merge_g_loan_contents (lc0 : g_loan_content_with_ty)
      (lc1 : g_loan_content_with_ty) : typed_avalue option =
    match (lc0, lc1) with
    | Concrete _, Concrete _ ->
        (* This can not happen: the values should have been destructured *)
        raise (Failure "Unreachable")
    | Abstract (ty0, lc0), Abstract (ty1, lc1) ->
        merge_aloan_contents ty0 lc0 ty1 lc1
    | Concrete _, Abstract _ | Abstract _, Concrete _ ->
        (* TODO: is it really unreachable? *)
        raise (Failure "Unreachable")
  in

  (* Note that we first explore the borrows/loans of [abs1], because we
     want to merge *into* this abstraction, and as a consequence we want to
     preserve its structure as much as we can *)
  let borrows_loans = List.append borrows_loans1 borrows_loans0 in
  (* Iterate over all the borrows/loans ids found in the abstractions *)
  List.iter
    (fun bl ->
      match bl with
      | BorrowId bid ->
          log#ldebug
            (lazy
              ("merge_into_abstraction_aux: merging borrow "
             ^ BorrowId.to_string bid));

          (* Check if the borrow has already been merged - this can happen
             because we go through all the borrows/loans in [abs0] *then*
             all the borrows/loans in [abs1], and there may be duplicates
             between the two *)
          if borrow_is_merged bid then ()
          else (
            set_borrow_as_merged bid;
            (* Check if we need to filter it *)
            match filter_bid bid with
            | None -> ()
            | Some bid ->
                (* Lookup the contents *)
                let bc0 = BorrowId.Map.find_opt bid borrow_to_content0 in
                let bc1 = BorrowId.Map.find_opt bid borrow_to_content1 in
                (* Merge *)
                let av : typed_avalue =
                  match (bc0, bc1) with
                  | None, Some bc | Some bc, None -> (
                      match bc with
                      | Concrete (_, _) ->
                          (* This can happen only in case of nested borrows -
                             a concrete borrow can only happen inside a shared
                             loan
                          *)
                          raise (Failure "Unreachable")
                      | Abstract (ty, bc) -> { value = ABorrow bc; ty })
                  | Some bc0, Some bc1 ->
                      assert (merge_funs <> None);
                      merge_g_borrow_contents bc0 bc1
                  | None, None -> raise (Failure "Unreachable")
                in
                push_avalue av)
      | LoanId bid ->
          if
            (* Check if the loan has already been treated - it can happen
               for the same reason as for borrows, and also because shared
               loans contain sets of borrows (meaning that when taking care
               of one loan, we can merge several other loans at once).
            *)
            loan_is_merged bid
          then ()
          else (
            log#ldebug
              (lazy
                ("merge_into_abstraction_aux: merging loan "
               ^ BorrowId.to_string bid));

            (* Check if we need to filter it *)
            match filter_bid bid with
            | None -> ()
            | Some bid ->
                (* Lookup the contents *)
                let lc0 = BorrowId.Map.find_opt bid loan_to_content0 in
                let lc1 = BorrowId.Map.find_opt bid loan_to_content1 in
                (* Merge *)
                let av : typed_avalue option =
                  match (lc0, lc1) with
                  | None, Some lc | Some lc, None -> (
                      match lc with
                      | Concrete _ ->
                          (* This shouldn't happen because the avalues should
                             have been destructured. *)
                          raise (Failure "Unreachable")
                      | Abstract (ty, lc) -> (
                          match lc with
                          | ASharedLoan (bids, sv, child) ->
                              let bids = filter_bids bids in
                              assert (not (BorrowId.Set.is_empty bids));
                              assert (is_aignored child.value);
                              assert (
                                not (value_has_loans_or_borrows ctx sv.value));
                              let lc = ASharedLoan (bids, sv, child) in
                              set_loans_as_merged bids;
                              Some { value = ALoan lc; ty }
                          | AMutLoan _ ->
                              set_loan_as_merged bid;
                              Some { value = ALoan lc; ty }
                          | AEndedMutLoan _ | AEndedSharedLoan _
                          | AIgnoredMutLoan _ | AEndedIgnoredMutLoan _
                          | AIgnoredSharedLoan _ ->
                              (* The abstraction has been destructured, so those shouldn't appear *)
                              raise (Failure "Unreachable")))
                  | Some lc0, Some lc1 ->
                      assert (merge_funs <> None);
                      merge_g_loan_contents lc0 lc1
                  | None, None -> raise (Failure "Unreachable")
                in
                push_opt_avalue av))
    borrows_loans;

  (* Reverse the avalues (we visited the loans/borrows in order, but pushed
     new values at the beggining of the stack of avalues) *)
  let avalues = List.rev !avalues in

  (* Reorder the avalues. We want the avalues to have the borrows first, then
     the loans (this structure is more stable when we merge abstractions together,
     meaning it is easier to find fixed points).
  *)
  let avalues =
    let is_borrow (av : typed_avalue) : bool =
      match av.value with
      | ABorrow _ -> true
      | ALoan _ -> false
      | _ -> raise (Failure "Unexpected")
    in
    let aborrows, aloans = List.partition is_borrow avalues in
    List.append aborrows aloans
  in

  (* Filter the regions *)

  (* Create the new abstraction *)
  let abs_id = fresh_abstraction_id () in
  (* Note that one of the two abstractions might a parent of the other *)
  let parents =
    AbstractionId.Set.diff
      (AbstractionId.Set.union abs0.parents abs1.parents)
      (AbstractionId.Set.of_list [ abs0.abs_id; abs1.abs_id ])
  in
  let original_parents = AbstractionId.Set.elements parents in
  let regions = RegionId.Set.union abs0.regions abs1.regions in
  let ancestors_regions =
    RegionId.Set.diff (RegionId.Set.union abs0.regions abs1.regions) regions
  in
  let abs =
    {
      abs_id;
      kind = abs_kind;
      can_end;
      parents;
      original_parents;
      regions;
      ancestors_regions;
      avalues;
    }
  in

  (* Sanity check *)
  if !Config.sanity_checks then assert (abs_is_destructured true ctx abs);
  (* Return *)
  abs

(** Merge the regions in a context to a single region *)
let ctx_merge_regions (ctx : eval_ctx) (rid : RegionId.id)
    (rids : RegionId.Set.t) : eval_ctx =
  let rsubst x = if RegionId.Set.mem x rids then rid else x in
  let env = Substitute.env_subst_rids rsubst ctx.env in
  { ctx with env }

let merge_into_abstraction (abs_kind : abs_kind) (can_end : bool)
    (merge_funs : merge_duplicates_funcs option) (ctx : eval_ctx)
    (abs_id0 : AbstractionId.id) (abs_id1 : AbstractionId.id) :
    eval_ctx * AbstractionId.id =
  (* Lookup the abstractions *)
  let abs0 = ctx_lookup_abs ctx abs_id0 in
  let abs1 = ctx_lookup_abs ctx abs_id1 in

  (* Merge them *)
  let nabs =
    merge_into_abstraction_aux abs_kind can_end merge_funs ctx abs0 abs1
  in

  (* Update the environment: replace the abstraction 1 with the result of the merge,
     remove the abstraction 0 *)
  let ctx = fst (ctx_subst_abs ctx abs_id1 nabs) in
  let ctx = fst (ctx_remove_abs ctx abs_id0) in

  (* Merge all the regions from the abstraction into one (the first - i.e., the
     one with the smallest id). Note that we need to do this in the whole
     environment, as those regions may be referenced as ancestor regions by
     the other abstractions, and may be present in symbolic values, etc. (this
     is not the case if there are no nested borrows, but we anticipate).
  *)
  let ctx =
    let regions = nabs.regions in
    (* Pick the first region id (this is the smallest) *)
    let rid = RegionId.Set.min_elt regions in
    (* If there is only one region, do nothing *)
    if RegionId.Set.cardinal regions = 1 then ctx
    else
      let rids = RegionId.Set.remove rid regions in
      ctx_merge_regions ctx rid rids
  in

  (* Return *)
  (ctx, nabs.abs_id)
