module T = Types
module V = Values
module C = Contexts
module Subst = Substitute
module L = Logging
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
let end_borrow_get_borrow (io : inner_outer)
    (allowed_abs : V.AbstractionId.id option) (l : V.BorrowId.id)
    (ctx : C.eval_ctx) :
    (C.eval_ctx * g_borrow_content option, outer_borrows_or_abs) result =
  (* We use a reference to communicate the kind of borrow we found, if we
   * find one *)
  let replaced_bc : g_borrow_content option ref = ref None in
  let set_replaced_bc (bc : g_borrow_content) =
    assert (Option.is_none !replaced_bc);
    replaced_bc := Some bc
  in
  (* Raise an exception if there are outer borrows or if we are inside an
   * abstraction: this exception is caught in a wrapper function *)
  let raise_if_outer (outer : V.AbstractionId.id option * borrow_ids option) =
    let outer_abs, outer_borrows = outer in
    match outer_abs with
    | Some abs -> (
        if
          (* Check if we can end borrows inside this abstraction *)
          Some abs <> allowed_abs
        then raise (FoundOuter (OuterAbs abs))
        else
          match outer_borrows with
          | Some borrows -> raise (FoundOuter (OuterBorrows borrows))
          | None -> ())
    | None -> (
        match outer_borrows with
        | Some borrows -> raise (FoundOuter (OuterBorrows borrows))
        | None -> ())
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
            let outer = update_outer_borrows io outer (Borrows bids) in
            V.Loan (super#visit_SharedLoan outer bids v)
      (** We reimplement [visit_Loan] because we may have to update the
          outer borrows *)

      method! visit_Borrow outer bc =
        match bc with
        | SharedBorrow l' | InactivatedMutBorrow l' ->
            (* Check if this is the borrow we are looking for *)
            if l = l' then (
              (* Check if there are outer borrows or if we are inside an abstraction *)
              raise_if_outer outer;
              (* Register the update *)
              set_replaced_bc (Concrete bc);
              (* Update the value *)
              V.Bottom)
            else super#visit_Borrow outer bc
        | V.MutBorrow (l', bv) ->
            (* Check if this is the borrow we are looking for *)
            if l = l' then (
              (* Check if there are outer borrows or if we are inside an abstraction *)
              raise_if_outer outer;
              (* Register the update *)
              set_replaced_bc (Concrete bc);
              (* Update the value *)
              V.Bottom)
            else
              (* Update the outer borrows before diving into the borrowed value *)
              let outer = update_outer_borrows io outer (Borrow l') in
              V.Borrow (super#visit_MutBorrow outer l' bv)

      method! visit_ALoan outer lc =
        (* Note that the children avalues are just other, independent loans,
         * so we don't need to update the outer borrows when diving in.
         * We keep track of the parents/children relationship only because we
         * need it to properly instantiate the backward functions when generating
         * the pure translation. *)
        match lc with
        | V.AMutLoan (bid, av) ->
            (* Nothing special to do *)
            V.ALoan (super#visit_AMutLoan outer bid av)
        | V.ASharedLoan (bids, v, av) ->
            (* Explore the shared value - we need to update the outer borrows *)
            let souter = update_outer_borrows io outer (Borrows bids) in
            let v = super#visit_typed_value souter v in
            (* Explore the child avalue - we keep the same outer borrows *)
            let av = super#visit_typed_avalue outer av in
            (* Reconstruct *)
            V.ALoan (V.ASharedLoan (bids, v, av))
        | V.AEndedMutLoan { given_back; child } ->
            (* The loan has ended, so no need to update the outer borrows *)
            V.ALoan (super#visit_AEndedMutLoan outer given_back child)
        | V.AEndedSharedLoan (v, av) ->
            (* The loan has ended, so no need to update the outer borrows *)
            V.ALoan (super#visit_AEndedSharedLoan outer v av)
        | V.AIgnoredMutLoan (bid, av) ->
            (* Nothing special to do *)
            V.ALoan (super#visit_AIgnoredMutLoan outer bid av)
        | V.AEndedIgnoredMutLoan { given_back; child } ->
            (* Nothing special to do *)
            V.ALoan (super#visit_AEndedIgnoredMutLoan outer given_back child)
        | V.AIgnoredSharedLoan av ->
            (* Nothing special to do *)
            V.ALoan (super#visit_AIgnoredSharedLoan outer av)
      (** We reimplement [visit_ALoan] because we may have to update the
          outer borrows *)

      method! visit_ABorrow outer bc =
        match bc with
        | V.AMutBorrow (bid, av) ->
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
              raise_if_outer outer;
              (* Register the update *)
              set_replaced_bc (Abstract bc);
              (* Update the value - note that we are necessarily in the second
               * of the two cases described above *)
              V.ABottom)
            else
              (* Update the outer borrows before diving into the child avalue *)
              let outer = update_outer_borrows io outer (Borrow bid) in
              V.ABorrow (super#visit_AMutBorrow outer bid av)
        | V.ASharedBorrow bid ->
            (* Check if this is the borrow we are looking for *)
            if bid = l then (
              (* Check there are outer borrows, or if we need to end the whole
               * abstraction *)
              raise_if_outer outer;
              (* Register the update *)
              set_replaced_bc (Abstract bc);
              (* Update the value - note that we are necessarily in the second
               * of the two cases described above *)
              V.ABottom)
            else V.ABorrow (super#visit_ASharedBorrow outer bid)
        | V.AIgnoredMutBorrow av ->
            (* Nothing special to do *)
            V.ABorrow (super#visit_AIgnoredMutBorrow outer av)
        | V.AProjSharedBorrow asb ->
            (* Check if the borrow we are looking for is in the asb *)
            if borrow_in_asb l asb then (
              (* Check there are outer borrows, or if we need to end the whole
               * abstraction *)
              raise_if_outer outer;
              (* Register the update *)
              set_replaced_bc (Abstract bc);
              (* Update the value - note that we are necessarily in the second
               * of the two cases described above *)
              let asb = remove_borrow_from_asb l asb in
              V.ABorrow (V.AProjSharedBorrow asb))
            else
              (* Nothing special to do *)
              V.ABorrow (super#visit_AProjSharedBorrow outer asb)

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
  with FoundOuter outers -> Error outers

(** Auxiliary function to end borrows. See [give_back].
    
    When we end a mutable borrow, we need to "give back" the value it contained
    to its original owner by reinserting it at the proper position.

    Note that this function checks that there is exactly one loan to which we
    give the value back.
    TODO: this was not the case before, so some sanity checks are not useful anymore.
 *)
let give_back_value (config : C.config) (bid : V.BorrowId.id)
    (nv : V.typed_value) (ctx : C.eval_ctx) : C.eval_ctx =
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

      method! visit_Loan opt_abs lc =
        match lc with
        | V.SharedLoan (bids, v) ->
            (* We are giving back a value (i.e., the content of a *mutable*
             * borrow): nothing special to do *)
            V.Loan (super#visit_SharedLoan opt_abs bids v)
        | V.MutLoan bid' ->
            (* Check if this is the loan we are looking for *)
            if bid' = bid then (
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

      method visit_typed_ALoan (opt_abs : V.abs option) (ty : T.rty)
          (lc : V.aloan_content) : V.avalue =
        (* Preparing a bit *)
        let regions =
          match opt_abs with
          | None -> failwith "Unreachable"
          | Some abs -> abs.V.regions
        in
        (* Rk.: there is a small issue with the types of the aloan values *)
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
              (* Apply the projection *)
              let given_back =
                apply_proj_borrows check_symbolic_no_ended ctx fresh_reborrow
                  regions nv borrowed_value_aty
              in
              (* Return the new value *)
              V.ALoan (V.AEndedMutLoan { given_back; child }))
            else
              (* Continue exploring *)
              V.ALoan (super#visit_AMutLoan opt_abs bid' child)
        | V.ASharedLoan (bids, v, av) ->
            (* We are giving back a value to a *mutable* loan: nothing special to do *)
            V.ALoan (super#visit_ASharedLoan opt_abs bids v av)
        | V.AEndedMutLoan { given_back; child } ->
            (* Nothing special to do *)
            V.ALoan (super#visit_AEndedMutLoan opt_abs given_back child)
        | V.AEndedSharedLoan (v, av) ->
            (* Nothing special to do *)
            V.ALoan (super#visit_AEndedSharedLoan opt_abs v av)
        | V.AIgnoredMutLoan (bid', child) ->
            (* This loan is ignored, but we may have to project on a subvalue
             * of the value which is given back *)
            if bid' = bid then
              (* Note that we replace the ignored mut loan by an *ended* ignored
               * mut loan. Also, this is not the loan we are looking for *per se*:
               * we don't register the fact that we inserted the value somewhere
               * (i.e., we don't call [set_replaced]) *)
              let given_back =
                apply_proj_borrows check_symbolic_no_ended ctx fresh_reborrow
                  regions nv borrowed_value_aty
              in
              V.ALoan (V.AEndedIgnoredMutLoan { given_back; child })
            else V.ALoan (super#visit_AIgnoredMutLoan opt_abs bid' child)
        | V.AEndedIgnoredMutLoan { given_back; child } ->
            (* Nothing special to do *)
            V.ALoan (super#visit_AEndedIgnoredMutLoan opt_abs given_back child)
        | V.AIgnoredSharedLoan av ->
            (* Nothing special to do *)
            V.ALoan (super#visit_AIgnoredSharedLoan opt_abs av)
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
let give_back_avalue (_config : C.config) (bid : V.BorrowId.id)
    (nv : V.typed_avalue) (ctx : C.eval_ctx) : C.eval_ctx =
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
              (* This is the loan we are looking for: apply the projection to
               * the value we give back and replaced this mutable loan with
               * an ended loan *)
              (* Register the insertion *)
              set_replaced ();
              (* Sanity check *)
              assert (nv.V.ty = ty);
              (* Return the new value *)
              V.ALoan (V.AEndedMutLoan { given_back = nv; child }))
            else
              (* Continue exploring *)
              V.ALoan (super#visit_AMutLoan opt_abs bid' child)
        | V.ASharedLoan (bids, v, av) ->
            (* We are giving back a value to a *mutable* loan: nothing special to do *)
            V.ALoan (super#visit_ASharedLoan opt_abs bids v av)
        | V.AEndedMutLoan { given_back; child } ->
            (* Nothing special to do *)
            V.ALoan (super#visit_AEndedMutLoan opt_abs given_back child)
        | V.AEndedSharedLoan (v, av) ->
            (* Nothing special to do *)
            V.ALoan (super#visit_AEndedSharedLoan opt_abs v av)
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
              V.ALoan (V.AEndedIgnoredMutLoan { given_back = nv; child }))
            else V.ALoan (super#visit_AIgnoredMutLoan opt_abs bid' child)
        | V.AEndedIgnoredMutLoan { given_back; child } ->
            (* Nothing special to do *)
            V.ALoan (super#visit_AEndedIgnoredMutLoan opt_abs given_back child)
        | V.AIgnoredSharedLoan av ->
            (* Nothing special to do *)
            V.ALoan (super#visit_AIgnoredSharedLoan opt_abs av)
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
              V.ALoan (super#visit_ASharedLoan opt_abs bids shared_value child)
        | V.AEndedMutLoan { given_back; child } ->
            (* Nothing special to do (the loan has ended) *)
            V.ALoan (super#visit_AEndedMutLoan opt_abs given_back child)
        | V.AEndedSharedLoan (v, av) ->
            (* Nothing special to do (the loan has ended) *)
            V.ALoan (super#visit_AEndedSharedLoan opt_abs v av)
        | V.AIgnoredMutLoan (bid, av) ->
            (* Nothing special to do (we are giving back a *shared* borrow) *)
            V.ALoan (super#visit_AIgnoredMutLoan opt_abs bid av)
        | V.AEndedIgnoredMutLoan { given_back; child } ->
            (* Nothing special to do *)
            V.ALoan (super#visit_AEndedIgnoredMutLoan opt_abs given_back child)
        | V.AIgnoredSharedLoan av ->
            (* Nothing special to do *)
            V.ALoan (super#visit_AIgnoredSharedLoan opt_abs av)
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
  (* This is used for sanity checks *)
  let sanity_ek =
    { enter_shared_loans = true; enter_mut_borrows = true; enter_abs = true }
  in
  match bc with
  | Concrete (V.MutBorrow (l', tv)) ->
      (* Sanity check *)
      assert (l' = l);
      (* Check that the corresponding loan is somewhere - purely a sanity check *)
      assert (Option.is_some (lookup_loan_opt sanity_ek l ctx));
      (* Update the context *)
      give_back_value config l tv ctx
  | Concrete (V.SharedBorrow l' | V.InactivatedMutBorrow l') ->
      (* Sanity check *)
      assert (l' = l);
      (* Check that the borrow is somewhere - purely a sanity check *)
      assert (Option.is_some (lookup_loan_opt sanity_ek l ctx));
      (* Update the context *)
      give_back_shared config l ctx
  | Abstract (V.AMutBorrow (l', av)) ->
      (* Sanity check *)
      assert (l' = l);
      (* Check that the corresponding loan is somewhere - purely a sanity check *)
      assert (Option.is_some (lookup_loan_opt sanity_ek l ctx));
      (* Update the context *)
      give_back_avalue config l av ctx
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
  | Abstract (V.AIgnoredMutBorrow _) -> failwith "Unreachable"

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
let convert_avalue_to_value (av : V.typed_avalue) : V.typed_value =
  (* Convert the type *)
  let ty = Subst.erase_regions av.V.ty in
  (* Generate the fresh a symbolic value *)
  let sv_id = C.fresh_symbolic_value_id () in
  let svalue : V.symbolic_value = { V.sv_id; sv_ty = av.V.ty } in
  let value = V.Symbolic svalue in
  { V.value; V.ty }

(** End a borrow identified by its borrow id in a context
    
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
 *)
let rec end_borrow (config : C.config) (io : inner_outer)
    (allowed_abs : V.AbstractionId.id option) (l : V.BorrowId.id)
    (ctx : C.eval_ctx) : C.eval_ctx =
  match end_borrow_get_borrow io allowed_abs l ctx with
  (* Two cases:
   * - error: we found outer borrows (end them first)
   * - success: we didn't find outer borrows when updating (but maybe we actually
       didn't find the borrow we were looking for...)
   *)
  | Error outer -> (
      (* End the outer borrows, abstraction, then try again to end the target
       * borrow (if necessary) *)
      match outer with
      | OuterBorrows (Borrows bids) ->
          (* Note that when ending outer borrows, we use io=Outer. However,
           * we shouldn't need to end outer borrows if io=Inner, so we just
           * add the following assertion *)
          assert (io = Outer);
          (* Note that we might get there with `allowed_abs <> None`: we might
           * be trying to end a borrow inside an abstraction, but which is actually
           * inside another borrow *)
          let allowed_abs' = None in
          let ctx = end_borrows config io allowed_abs' bids ctx in
          (* Retry to end the borrow *)
          end_borrow config io allowed_abs l ctx
      | OuterBorrows (Borrow bid) ->
          (* See the comments for the previous case *)
          assert (io = Outer);
          let allowed_abs' = None in
          let ctx = end_borrow config io allowed_abs' bid ctx in
          (* Retry to end the borrow *)
          end_borrow config io allowed_abs l ctx
      | OuterAbs abs_id -> (
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
          match lookup_loan ek l ctx with
          | AbsId loan_abs_id, _ ->
              if loan_abs_id = abs_id then (
                (* Same abstraction! We can end the borrow *)
                let ctx = end_borrow config io (Some abs_id) l ctx in
                (* Sanity check *)
                assert (Option.is_none (lookup_borrow_opt ek l ctx));
                ctx)
              else
                (* Not the same abstraction: we need to end the whole abstraction.
                 * By doing that we should have ended the target borrow (see the
                 * below sanity check) *)
                let ctx = end_abstraction config abs_id ctx in
                (* Sanity check: we ended the target borrow *)
                assert (Option.is_none (lookup_borrow_opt ek l ctx));
                ctx
          | VarId _, _ ->
              (* The loan is not inside the same abstraction (actually inside
               * a non-abstraction value): we need to end the whole abstraction *)
              let ctx = end_abstraction config abs_id ctx in
              (* Sanity check: we ended the target borrow *)
              assert (Option.is_none (lookup_borrow_opt ek l ctx));
              ctx))
  | Ok (ctx, None) ->
      (* It is possible that we can't find a borrow in symbolic mode (ending
       * an abstraction may end several borrows at once *)
      assert (config.mode = SymbolicMode);
      ctx
  (* We found a borrow: give the value back (i.e., update the corresponding loan) *)
  | Ok (ctx, Some bc) -> give_back config l bc ctx

and end_borrows (config : C.config) (io : inner_outer)
    (allowed_abs : V.AbstractionId.id option) (lset : V.BorrowId.Set.t)
    (ctx : C.eval_ctx) : C.eval_ctx =
  V.BorrowId.Set.fold
    (fun id ctx -> end_borrow config io allowed_abs id ctx)
    lset ctx

and end_abstraction (config : C.config) (abs_id : V.AbstractionId.id)
    (ctx : C.eval_ctx) : C.eval_ctx =
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
  let ctx = end_abstractions config abs.parents ctx in
  log#ldebug
    (lazy
      ("end_abstraction: "
      ^ V.AbstractionId.to_string abs_id
      ^ "\n- context after parent abstractions ended:\n"
      ^ eval_ctx_to_string ctx));
  (* End the loans inside the abstraction *)
  let ctx = end_abstraction_loans config abs_id ctx in
  log#ldebug
    (lazy
      ("end_abstraction: "
      ^ V.AbstractionId.to_string abs_id
      ^ "\n- context after loans ended:\n" ^ eval_ctx_to_string ctx));
  (* End the abstraction itself by redistributing the borrows it contains *)
  let ctx = end_abstraction_borrows config abs_id ctx in
  (* End the regions owned by the abstraction - note that we don't need to
   * relookup the abstraction: the set of regions in an abstraction never
   * changes... *)
  let ctx =
    {
      ctx with
      ended_regions = T.RegionId.Set.union ctx.ended_regions abs.V.regions;
    }
  in
  (* Remove all the references to the id of the current abstraction, and remove
   * the abstraction itself *)
  let ctx = end_abstraction_remove_from_context config abs_id ctx in
  (* Debugging *)
  log#ldebug
    (lazy
      ("end_abstraction: "
      ^ V.AbstractionId.to_string abs_id
      ^ "\n- original context:\n" ^ eval_ctx_to_string ctx0
      ^ "\n\n- new context:\n" ^ eval_ctx_to_string ctx));
  (* Return *)
  ctx

and end_abstractions (config : C.config) (abs_ids : V.AbstractionId.set_t)
    (ctx : C.eval_ctx) : C.eval_ctx =
  V.AbstractionId.Set.fold
    (fun id ctx -> end_abstraction config id ctx)
    abs_ids ctx

and end_abstraction_loans (config : C.config) (abs_id : V.AbstractionId.id)
    (ctx : C.eval_ctx) : C.eval_ctx =
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
        | V.AEndedMutLoan { given_back; child } ->
            super#visit_AEndedMutLoan env given_back child
        | V.AEndedSharedLoan (v, av) -> super#visit_AEndedSharedLoan env v av
        | V.AIgnoredMutLoan (bid, av) ->
            (* Note that this loan can't come from a parent abstraction, because
             * we should have ended them already) *)
            super#visit_AIgnoredMutLoan env bid av
        | V.AEndedIgnoredMutLoan { given_back; child } ->
            super#visit_AEndedIgnoredMutLoan env given_back child
        | V.AIgnoredSharedLoan av -> super#visit_AIgnoredSharedLoan env av
    end
  in
  try
    (* Check if there are loans *)
    obj#visit_abs () abs;
    (* No loans: nothing to update *)
    ctx
  with (* There are loans: end them, then recheck *)
  | FoundBorrowIds bids ->
    let ctx =
      match bids with
      | Borrow bid -> end_outer_borrow config bid ctx
      | Borrows bids -> end_outer_borrows config bids ctx
    in
    (* Recheck *)
    end_abstraction_loans config abs_id ctx

and end_abstraction_borrows (config : C.config) (abs_id : V.AbstractionId.id)
    (ctx : C.eval_ctx) : C.eval_ctx =
  (* Note that the abstraction mustn't contain any loans *)
  (* We end the borrows, starting with the *inner* ones. This is important
     when considering nested borrows which have the same lifetime.

     For instance:
     ```
     x -> mut_loan l1
     px -> mut_loan l0
     abs0 { a_mut_borrow l0 (a_mut_borrow l1 (U32 3)) }
     ```

     becomes (`U32 3` doesn't contain ⊥, so we give back a symbolic value):
     ```
     x -> @s0
     px -> mut_loan l0
     abs0 { a_mut_borrow l0 ⊥ }
     ```

     then (the borrowed value contains ⊥, we give back ⊥):
     ```
     x -> @s0
     px -> ⊥
     abs0 { ⊥ }
     ```
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
        | V.AMutBorrow (_, _) | V.ASharedBorrow _ ->
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
        | V.AIgnoredMutBorrow _ ->
            (* Nothing to do for ignored borrows *)
            ()
    end
  in
  (* Lookup the abstraction *)
  let abs = C.ctx_lookup_abs ctx abs_id in
  try
    (* Explore the abstraction, looking for borrows *)
    obj#visit_abs () abs;
    (* No borrows: nothing to update *)
    ctx
  with
  (* There are borrows: end them, then reexplore *)
  | FoundABorrowContent bc ->
    (* First, replace the borrow by ⊥ *)
    let bid =
      match bc with
      | V.AMutBorrow (bid, _) | V.ASharedBorrow bid -> bid
      | V.AProjSharedBorrow asb -> (
          (* There should be at least one borrow identifier in the set, which we
           * can use to identify the whole set *)
          match
            List.find
              (fun x -> match x with V.AsbBorrow _ -> true | _ -> false)
              asb
          with
          | V.AsbBorrow bid -> bid
          | _ -> failwith "Unexpected")
      | V.AIgnoredMutBorrow _ -> failwith "Unexpected"
    in
    let ctx = update_aborrow ek_all bid V.ABottom ctx in
    (* Then give back the value *)
    let ctx =
      match bc with
      | V.AMutBorrow (bid, av) ->
          (* First, convert the avalue to a (fresh symbolic) value *)
          let v = convert_avalue_to_value av in
          give_back_value config bid v ctx
      | V.ASharedBorrow bid -> give_back_shared config bid ctx
      | V.AProjSharedBorrow _ ->
          (* Nothing to do *)
          ctx
      | V.AIgnoredMutBorrow _ -> failwith "Unexpected"
    in
    (* Reexplore *)
    end_abstraction_borrows config abs_id ctx

(** Remove an abstraction from the context, as well as all its references *)
and end_abstraction_remove_from_context (_config : C.config)
    (abs_id : V.AbstractionId.id) (ctx : C.eval_ctx) : C.eval_ctx =
  let map_env_elem (ev : C.env_elem) : C.env_elem option =
    match ev with
    | C.Var (_, _) | C.Frame -> Some ev
    | C.Abs abs ->
        if abs.abs_id = abs_id then None
        else
          let parents = V.AbstractionId.Set.remove abs_id abs.parents in
          Some (C.Abs { abs with V.parents })
  in
  let env = List.filter_map map_env_elem ctx.C.env in
  { ctx with C.env }

and end_outer_borrow config = end_borrow config Outer None

and end_outer_borrows config = end_borrows config Outer None

and end_inner_borrow config = end_borrow config Inner None

and end_inner_borrows config = end_borrows config Inner None

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
let promote_shared_loan_to_mut_loan (l : V.BorrowId.id) (ctx : C.eval_ctx) :
    C.eval_ctx * V.typed_value =
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
      (* Return *)
      (ctx, sv)
  | _, Abstract _ ->
      (* I don't think it is possible to have two-phase borrows involving borrows
       * returned by abstractions. I'm not sure how we could handle that anyway. *)
      failwith
        "Can't promote a shared loan to a mutable loan if the loan is inside \
         an abstraction"

(** Helper function: see [activate_inactivated_mut_borrow].

    This function updates a shared borrow to a mutable borrow.
 *)
let promote_inactivated_borrow_to_mut_borrow (l : V.BorrowId.id)
    (borrowed_value : V.typed_value) (ctx : C.eval_ctx) : C.eval_ctx =
  (* Lookup the inactivated borrow - note that we don't go inside borrows/loans:
     there can't be inactivated borrows inside other borrows/loans
  *)
  let ek =
    { enter_shared_loans = false; enter_mut_borrows = false; enter_abs = false }
  in
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

(** Promote an inactivated mut borrow to a mut borrow.

    The borrow must point to a shared value which is borrowed exactly once.
 *)
let rec activate_inactivated_mut_borrow (config : C.config) (io : inner_outer)
    (l : V.BorrowId.id) (ctx : C.eval_ctx) : C.eval_ctx =
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
          let ctx =
            match lc with
            | V.SharedLoan (bids, _) -> end_outer_borrows config bids ctx
            | V.MutLoan bid -> end_outer_borrow config bid ctx
          in
          (* Recursive call *)
          activate_inactivated_mut_borrow config io l ctx
      | None ->
          (* No loan to end inside the value *)
          (* Some sanity checks *)
          L.log#ldebug
            (lazy
              ("activate_inactivated_mut_borrow: resulting value:\n"
             ^ V.show_typed_value sv));
          assert (not (loans_in_value sv));
          assert (not (bottom_in_value ctx.ended_regions sv));
          assert (not (inactivated_in_value sv));
          (* End the borrows which borrow from the value, at the exception of
             the borrow we want to promote *)
          let bids = V.BorrowId.Set.remove l bids in
          let allowed_abs = None in
          let ctx = end_borrows config io allowed_abs bids ctx in
          (* Promote the loan *)
          let ctx, borrowed_value = promote_shared_loan_to_mut_loan l ctx in
          (* Promote the borrow - the value should have been checked by
             [promote_shared_loan_to_mut_loan]
          *)
          promote_inactivated_borrow_to_mut_borrow l borrowed_value ctx)
  | _, Abstract _ ->
      (* I don't think it is possible to have two-phase borrows involving borrows
       * returned by abstractions. I'm not sure how we could handle that anyway. *)
      failwith
        "Can't activate an inactivated mutable borrow referencing a loan inside\n\
        \         an abstraction"
