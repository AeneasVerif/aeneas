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

(** The local logger *)
let log = L.borrows_log

(** Auxiliary function to end borrows: lookup a borrow in the environment,
    update it (by returning an updated environment where the borrow has been
    replaced by {!V.Bottom})) if we can end the borrow (for instance, it is not
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
let end_borrow_get_borrow (allowed_abs : V.AbstractionId.id option)
    (allow_inner_loans : bool) (l : V.BorrowId.id) (ctx : C.eval_ctx) :
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
    if not allow_inner_loans then
      match borrowed_value with
      | None -> ()
      | Some v -> (
          match get_first_loan_in_value v with
          | None -> ()
          | Some c -> (
              match c with
              | V.SharedLoan (bids, _) ->
                  raise (FoundPriority (InnerLoans (Borrows bids)))
              | V.MutLoan bid -> raise (FoundPriority (InnerLoans (Borrow bid)))
              ))
  in

  (* The environment is used to keep track of the outer loans *)
  let obj =
    object
      inherit [_] C.map_eval_ctx as super

      (** We reimplement {!visit_Loan} because we may have to update the
          outer borrows *)
      method! visit_Loan (outer : V.AbstractionId.id option * borrow_ids option)
          lc =
        match lc with
        | V.MutLoan bid -> V.Loan (super#visit_MutLoan outer bid)
        | V.SharedLoan (bids, v) ->
            (* Update the outer borrows before diving into the shared value *)
            let outer = update_outer_borrows outer (Borrows bids) in
            V.Loan (super#visit_SharedLoan outer bids v)

      method! visit_Borrow outer bc =
        match bc with
        | SharedBorrow (_, l') | ReservedMutBorrow (_, l') ->
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

      (** We reimplement {!visit_ALoan} because we may have to update the
          outer borrows *)
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
               * we do not insert {!AEndedMutBorrow} but rather {!ABottom} *)
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
            { given_back_loans_proj = _; child = _; given_back_meta = _ }
        | V.AEndedSharedBorrow ->
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

(** Auxiliary function to end borrows. See {!give_back}.
    
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

      (** This is a bit annoying, but as we need the type of the value we
          are exploring, for sanity checks, we need to implement
          {!visit_typed_avalue} instead of
          overriding {!visit_ALoan} *)
      method! visit_typed_value opt_abs (v : V.typed_value) : V.typed_value =
        match v.V.value with
        | V.Loan lc ->
            let value = self#visit_typed_Loan opt_abs v.V.ty lc in
            ({ v with V.value } : V.typed_value)
        | _ -> super#visit_typed_value opt_abs v

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
                raise (Failure "Value given back doesn't have the proper type"));
              (* Replace *)
              set_replaced ();
              nv.V.value)
            else V.Loan (super#visit_MutLoan opt_abs bid')

      (** This is a bit annoying, but as we need the type of the avalue we
          are exploring, in order to be able to project the value we give
          back, we need to reimplement {!visit_typed_avalue} instead of
          {!visit_ALoan} *)
      method! visit_typed_avalue opt_abs (av : V.typed_avalue) : V.typed_avalue
          =
        match av.V.value with
        | V.ALoan lc ->
            let value = self#visit_typed_ALoan opt_abs av.V.ty lc in
            ({ av with V.value } : V.typed_avalue)
        | _ -> super#visit_typed_avalue opt_abs av

      (** We need to inspect ignored mutable borrows, to insert loan projectors
          if necessary.
       *)
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
              | _ -> raise (Failure "Unreachable")
            else
              (* Continue exploring *)
              V.ABorrow (super#visit_AIgnoredMutBorrow opt_abs bid' child)
        | _ ->
            (* Continue exploring *)
            super#visit_ABorrow opt_abs bc

      (** We are not specializing an already existing method, but adding a
          new method (for projections, we need type information) *)
      method visit_typed_ALoan (opt_abs : V.abs option) (ty : T.rty)
          (lc : V.aloan_content) : V.avalue =
        (* Preparing a bit *)
        let regions, ancestors_regions =
          match opt_abs with
          | None -> raise (Failure "Unreachable")
          | Some abs -> (abs.V.regions, abs.V.ancestors_regions)
        in
        (* Rk.: there is a small issue with the types of the aloan values.
         * See the comment at the level of definition of {!typed_avalue} *)
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
               * (i.e., we don't call {!set_replaced}) *)
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
  | V.SynthInputGivenBack | SynthRetGivenBack | FunCallGivenBack | LoopGivenBack
    ->
      ()
  | FunCallRet | SynthInput | Global | LoopOutput ->
      raise (Failure "Unrechable"));
  (* Store the given-back value as a meta-value for synthesis purposes *)
  let mv = nsv in
  (* Substitution function, to replace the borrow projectors over symbolic values *)
  let subst (_abs : V.abs) local_given_back =
    (* See the below comments: there is something wrong here *)
    let _ = raise Utils.Unimplemented in
    (* Compute the projection over the given back value *)
    let child_proj =
      match nsv.sv_kind with
      | V.SynthRetGivenBack ->
          (* The given back value comes from the return value of the function
             we are currently synthesizing (as it is given back, it means
             we ended one of the regions appearing in the signature: we are
             currently synthesizing one of the backward functions).

             As we don't allow borrow overwrites on returned value, we can
             (and MUST) forget the borrows *)
          V.AIgnoredProjBorrows
      | V.FunCallGivenBack ->
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
          V.AProjBorrows (nsv, sv.V.sv_ty)
      | _ -> raise (Failure "Unreachable")
    in
    V.AProjLoans (sv, (mv, child_proj) :: local_given_back)
  in
  update_intersecting_aproj_loans proj_regions proj_ty sv subst ctx

(** Auxiliary function to end borrows. See {!give_back}.

    This function is similar to {!give_back_value} but gives back an {!V.avalue}
    (coming from an abstraction).

    It is used when ending a borrow inside an abstraction, when the corresponding
    loan is inside the same abstraction (in which case we don't need to end the whole
    abstraction).
    
    REMARK: this function can't be used to give back the values borrowed by
    end abstraction when ending this abstraction. When doing this, we need
    to convert the {!V.avalue} to a {!type:V.value} by introducing the proper symbolic values.
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

      (** This is a bit annoying, but as we need the type of the avalue we
          are exploring, in order to be able to project the value we give
          back, we need to reimplement {!visit_typed_avalue} instead of
          {!visit_ALoan} *)
      method! visit_typed_avalue opt_abs (av : V.typed_avalue) : V.typed_avalue
          =
        match av.V.value with
        | V.ALoan lc ->
            let value = self#visit_typed_ALoan opt_abs av.V.ty lc in
            ({ av with V.value } : V.typed_avalue)
        | _ -> super#visit_typed_avalue opt_abs av

      (** We are not specializing an already existing method, but adding a
          new method (for projections, we need type information) *)
      method visit_typed_ALoan (opt_abs : V.abs option) (ty : T.rty)
          (lc : V.aloan_content) : V.avalue =
        match lc with
        | V.AMutLoan (bid', child) ->
            if bid' = bid then (
              (* Sanity check - about why we need to call {!ty_get_ref}
               * (and don't do the same thing as in {!give_back_value})
               * see the comment at the level of the definition of
               * {!typed_avalue} *)
              let _, expected_ty, _ = ty_get_ref ty in
              if nv.V.ty <> expected_ty then (
                log#serror
                  ("give_back_avalue_to_same_abstraction: improper type:\n\
                    - expected: " ^ rty_to_string ctx ty ^ "\n- received: "
                 ^ rty_to_string ctx nv.V.ty);
                raise (Failure "Value given back doesn't have the proper type"));
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
               * (i.e., we don't call {!set_replaced}) *)
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
        (* This case is similar to the {!SharedLoan} case *)
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

(** Auxiliary function: see {!end_borrow_aux} *)
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
  | Concrete (V.SharedBorrow (_, l') | V.ReservedMutBorrow (_, l')) ->
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
      ( V.AEndedMutBorrow _ | V.AIgnoredMutBorrow _ | V.AEndedIgnoredMutBorrow _
      | V.AEndedSharedBorrow ) ->
      raise (Failure "Unreachable")

(** Convert an {!type:V.avalue} to a {!type:V.value}.

    This function is used when ending abstractions: whenever we end a borrow
    in an abstraction, we converted the borrowed {!V.avalue} to a fresh symbolic
    {!type:V.value}, then give back this {!type:V.value} to the context.
 
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
let convert_avalue_to_given_back_value (abs_kind : V.abs_kind)
    (av : V.typed_avalue) : V.symbolic_value =
  let sv_kind =
    match abs_kind with
    | V.FunCall _ -> V.FunCallGivenBack
    | V.SynthRet _ -> V.SynthRetGivenBack
    | V.SynthInput _ -> V.SynthInputGivenBack
    | V.Loop _ -> V.LoopGivenBack
  in
  mk_fresh_symbolic_value sv_kind av.V.ty

let check_borrow_disappeared (fun_name : string) (l : V.BorrowId.id)
    (ctx0 : C.eval_ctx) : cm_fun =
  let check_disappeared (ctx : C.eval_ctx) : unit =
    let _ =
      match lookup_borrow_opt ek_all l ctx with
      | None -> () (* Ok *)
      | Some _ ->
          log#lerror
            (lazy
              (fun_name ^ ": " ^ V.BorrowId.to_string l
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
            (fun_name ^ ": " ^ V.BorrowId.to_string l
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
let rec end_borrow_aux (config : C.config) (chain : borrow_or_abs_ids)
    (allowed_abs : V.AbstractionId.id option) (l : V.BorrowId.id) : cm_fun =
 fun cf ctx ->
  (* Check that we don't loop *)
  let chain0 = chain in
  let chain =
    add_borrow_or_abs_id_to_chain "end_borrow_aux: " (BorrowId l) chain
  in
  log#ldebug
    (lazy
      ("end borrow: " ^ V.BorrowId.to_string l ^ ":\n- original context:\n"
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
          ("end borrow: " ^ V.BorrowId.to_string l
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

and end_borrows_aux (config : C.config) (chain : borrow_or_abs_ids)
    (allowed_abs : V.AbstractionId.id option) (lset : V.BorrowId.Set.t) : cm_fun
    =
 fun cf ->
  (* This is not necessary, but we prefer to reorder the borrow ids,
   * so that we actually end from the smallest id to the highest id - just
   * a matter of taste, and may make debugging easier *)
  let ids = V.BorrowId.Set.fold (fun id ids -> id :: ids) lset [] in
  List.fold_left
    (fun cf id -> end_borrow_aux config chain allowed_abs id cf)
    cf ids

and end_abstraction_aux (config : C.config) (chain : borrow_or_abs_ids)
    (abs_id : V.AbstractionId.id) : cm_fun =
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
      ^ V.AbstractionId.to_string abs_id
      ^ "\n- original context:\n" ^ eval_ctx_to_string ctx0));

  (* Lookup the abstraction *)
  let abs = C.ctx_lookup_abs ctx abs_id in

  (* Check that we can end the abstraction *)
  assert abs.can_end;

  (* End the parent abstractions first *)
  let cc = end_abstractions_aux config chain abs.parents in
  let cc =
    comp_unit cc (fun ctx ->
        log#ldebug
          (lazy
            ("end_abstraction_aux: "
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
            ("end_abstraction_aux: "
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
            ("end_abstraction_aux: "
            ^ V.AbstractionId.to_string abs_id
            ^ "\n- original context:\n" ^ eval_ctx_to_string ctx0
            ^ "\n\n- new context:\n" ^ eval_ctx_to_string ctx)))
  in

  (* Sanity check: ending an abstraction must preserve the invariants *)
  let cc = comp cc Invariants.cf_check_invariants in

  (* Apply the continuation *)
  cc cf ctx

and end_abstractions_aux (config : C.config) (chain : borrow_or_abs_ids)
    (abs_ids : V.AbstractionId.Set.t) : cm_fun =
 fun cf ->
  (* This is not necessary, but we prefer to reorder the abstraction ids,
   * so that we actually end from the smallest id to the highest id - just
   * a matter of taste, and may make debugging easier *)
  let abs_ids = V.AbstractionId.Set.fold (fun id ids -> id :: ids) abs_ids [] in
  List.fold_left
    (fun cf id -> end_abstraction_aux config chain id cf)
    cf abs_ids

and end_abstraction_loans (config : C.config) (chain : borrow_or_abs_ids)
    (abs_id : V.AbstractionId.id) : cm_fun =
 fun cf ctx ->
  (* Lookup the abstraction *)
  let abs = C.ctx_lookup_abs ctx abs_id in
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

and end_abstraction_borrows (config : C.config) (chain : borrow_or_abs_ids)
    (abs_id : V.AbstractionId.id) : cm_fun =
 fun cf ctx ->
  log#ldebug
    (lazy
      ("end_abstraction_borrows: abs_id: " ^ V.AbstractionId.to_string abs_id));
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
        | V.AEndedIgnoredMutBorrow _ | V.AEndedSharedBorrow ->
            (* Nothing to do for ignored borrows *)
            ()

      method! visit_aproj env sproj =
        (match sproj with
        | V.AProjLoans _ -> raise (Failure "Unexpected")
        | V.AProjBorrows (sv, proj_ty) ->
            raise (FoundAProjBorrows (sv, proj_ty))
        | V.AEndedProjLoans _ | V.AEndedProjBorrows _ | V.AIgnoredProjBorrows ->
            ());
        super#visit_aproj env sproj

      (** We may need to end borrows in "regular" values, because of shared values *)
      method! visit_borrow_content _ bc =
        match bc with
        | V.SharedBorrow (_, _) | V.MutBorrow (_, _) ->
            raise (FoundBorrowContent bc)
        | V.ReservedMutBorrow _ -> raise (Failure "Unreachable")
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
  (* There are concrete (i.e., not symbolic) borrows: end them, then reexplore *)
  | FoundABorrowContent bc ->
      log#ldebug
        (lazy
          ("end_abstraction_borrows: found aborrow content: "
          ^ aborrow_content_to_string ctx bc));
      let ctx =
        match bc with
        | V.AMutBorrow (_mv, bid, av) ->
            (* First, convert the avalue to a (fresh symbolic) value *)
            let sv = convert_avalue_to_given_back_value abs.kind av in
            (* Replace the mut borrow to register the fact that we ended
             * it and store with it the freshly generated given back value *)
            let ended_borrow = V.ABorrow (V.AEndedMutBorrow (sv, av)) in
            let ctx = update_aborrow ek_all bid ended_borrow ctx in
            (* Give the value back *)
            let sv = mk_typed_value_from_symbolic_value sv in
            give_back_value config bid sv ctx
        | V.ASharedBorrow bid ->
            (* Replace the shared borrow to account for the fact it ended *)
            let ended_borrow = V.ABorrow V.AEndedSharedBorrow in
            let ctx = update_aborrow ek_all bid ended_borrow ctx in
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
        | V.AEndedIgnoredMutBorrow _ | V.AEndedSharedBorrow ->
            raise (Failure "Unexpected")
      in
      (* Reexplore *)
      end_abstraction_borrows config chain abs_id cf ctx
  (* There are symbolic borrows: end them, then reexplore *)
  | FoundAProjBorrows (sv, proj_ty) ->
      log#ldebug
        (lazy
          ("end_abstraction_borrows: found aproj borrows: "
          ^ aproj_to_string ctx (V.AProjBorrows (sv, proj_ty))));
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
  (* There are concrete (i.e., not symbolic) borrows in shared values: end them, then reexplore *)
  | FoundBorrowContent bc ->
      log#ldebug
        (lazy
          ("end_abstraction_borrows: found borrow content: "
          ^ borrow_content_to_string ctx bc));
      let ctx =
        match bc with
        | V.SharedBorrow (_, bid) -> (
            (* Replace the shared borrow with bottom *)
            let allow_inner_loans = false in
            match
              end_borrow_get_borrow (Some abs_id) allow_inner_loans bid ctx
            with
            | Error _ -> raise (Failure "Unreachable")
            | Ok (ctx, _) ->
                (* Give back *)
                give_back_shared config bid ctx)
        | V.MutBorrow (bid, v) -> (
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
        | V.ReservedMutBorrow _ -> raise (Failure "Unreachable")
      in
      (* Reexplore *)
      end_abstraction_borrows config chain abs_id cf ctx

(** Remove an abstraction from the context, as well as all its references *)
and end_abstraction_remove_from_context (_config : C.config)
    (abs_id : V.AbstractionId.id) : cm_fun =
 fun cf ctx ->
  let ctx, abs = C.ctx_remove_abs ctx abs_id in
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
            (fun s id -> V.AbstractionId.Set.add id s)
            V.AbstractionId.Set.empty abs_ids
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
        let cc = end_abstraction_aux config chain abs_id' in
        (* Retry ending the projector of loans *)
        let cc =
          comp cc (end_proj_loans_symbolic config chain abs_id regions sv)
        in
        (* Sanity check *)
        let cc = comp cc cf_check in
        (* Continue *)
        cc cf ctx

let end_borrow config : V.BorrowId.id -> cm_fun = end_borrow_aux config [] None

let end_borrows config : V.BorrowId.Set.t -> cm_fun =
  end_borrows_aux config [] None

let end_abstraction config = end_abstraction_aux config []
let end_abstractions config = end_abstractions_aux config []

(** Auxiliary function - call a function which requires a continuation,
    and return the let context given to the continuation *)
let get_cf_ctx_no_synth (f : cm_fun) (ctx : C.eval_ctx) : C.eval_ctx =
  let nctx = ref None in
  let cf ctx =
    assert (!nctx = None);
    nctx := Some ctx;
    None
  in
  let _ = f cf ctx in
  Option.get !nctx

let end_borrow_no_synth config id ctx =
  get_cf_ctx_no_synth (end_borrow config id) ctx

let end_abstraction_no_synth config id ctx =
  get_cf_ctx_no_synth (end_abstraction config id) ctx

(** Helper function: see {!activate_reserved_mut_borrow}.

    This function updates the shared loan to a mutable loan (we then update
    the borrow with another helper). Of course, the shared loan must contain
    exactly one borrow id (the one we give as parameter), otherwise we can't
    promote it. Also, the shared value mustn't contain any loan.

    The returned value (previously shared) is checked:
    - it mustn't contain loans
    - it mustn't contain {!V.Bottom}
    - it mustn't contain reserved borrows
    TODO: this kind of checks should be put in an auxiliary helper, because
    they are redundant.

    The loan to update mustn't be a borrowed value.
 *)
let promote_shared_loan_to_mut_loan (l : V.BorrowId.id)
    (cf : V.typed_value -> m_fun) : m_fun =
 fun ctx ->
  (* Debug *)
  log#ldebug
    (lazy
      ("promote_shared_loan_to_mut_loan:\n- loan: " ^ V.BorrowId.to_string l
     ^ "\n- context:\n" ^ eval_ctx_to_string ctx ^ "\n"));
  (* Lookup the shared loan - note that we can't promote a shared loan
   * in a shared value, but we can do it in a mutably borrowed value.
   * This is important because we can do: [let y = &two-phase ( *x );]
   *)
  let ek =
    { enter_shared_loans = false; enter_mut_borrows = true; enter_abs = false }
  in
  match lookup_loan ek l ctx with
  | _, Concrete (V.MutLoan _) ->
      raise (Failure "Expected a shared loan, found a mut loan")
  | _, Concrete (V.SharedLoan (bids, sv)) ->
      (* Check that there is only one borrow id (l) and update the loan *)
      assert (V.BorrowId.Set.mem l bids && V.BorrowId.Set.cardinal bids = 1);
      (* We need to check that there aren't any loans in the value:
         we should have gotten rid of those already, but it is better
         to do a sanity check. *)
      assert (not (loans_in_value sv));
      (* Check there isn't {!Bottom} (this is actually an invariant *)
      assert (not (bottom_in_value ctx.ended_regions sv));
      (* Check there aren't reserved borrows *)
      assert (not (reserved_in_value sv));
      (* Update the loan content *)
      let ctx = update_loan ek l (V.MutLoan l) ctx in
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
let replace_reserved_borrow_with_mut_borrow (l : V.BorrowId.id) (cf : m_fun)
    (borrowed_value : V.typed_value) : m_fun =
 fun ctx ->
  (* Lookup the reserved borrow - note that we don't go inside borrows/loans:
     there can't be reserved borrows inside other borrows/loans
  *)
  let ek =
    { enter_shared_loans = false; enter_mut_borrows = false; enter_abs = false }
  in
  let ctx =
    match lookup_borrow ek l ctx with
    | Concrete (V.SharedBorrow _ | V.MutBorrow (_, _)) ->
        raise (Failure "Expected a reserved mutable borrow")
    | Concrete (V.ReservedMutBorrow _) ->
        (* Update it *)
        update_borrow ek l (V.MutBorrow (l, borrowed_value)) ctx
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
let rec promote_reserved_mut_borrow (config : C.config) (l : V.BorrowId.id) :
    cm_fun =
 fun cf ctx ->
  (* Lookup the value *)
  let ek =
    { enter_shared_loans = false; enter_mut_borrows = true; enter_abs = false }
  in
  match lookup_loan ek l ctx with
  | _, Concrete (V.MutLoan _) -> raise (Failure "Unreachable")
  | _, Concrete (V.SharedLoan (bids, sv)) -> (
      (* If there are loans inside the value, end them. Note that there can't be
         reserved borrows inside the value.
         If we perform an update, do a recursive call to lookup the updated value *)
      match get_first_loan_in_value sv with
      | Some lc ->
          (* End the loans *)
          let cc =
            match lc with
            | V.SharedLoan (bids, _) -> end_borrows config bids
            | V.MutLoan bid -> end_borrow config bid
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
          let bids = V.BorrowId.Set.remove l bids in
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

let destructure_abs (abs_kind : V.abs_kind) (can_end : bool) (ctx : C.eval_ctx)
    (abs0 : V.abs) : V.abs =
  (* Accumulator to store the destructured values *)
  let avalues = ref [] in
  (* Utility function to store a value in the accumulator *)
  let push_avalue av = avalues := av :: !avalues in
  (* We use this function to make sure we never register values (i.e.,
     loans or borrows) when we shouldn't - see it as a sanity check:
     for now, we don't allow nested borrows, which means we should register
     values from children of borrows. In this condition, we could simply
     ignore the children altogether. Instead, we explore them and make sure
     we don't register values while doing so.
  *)
  let push_fail _ = raise (Failure "Unreachable") in
  (* Function to explore an avalue and destructure it *)
  let rec list_avalues (allow_borrows : bool) (push : V.typed_avalue -> unit)
      (av : V.typed_avalue) : unit =
    let ty = av.V.ty in
    match av.V.value with
    | V.APrimitive _ | ABottom | AIgnored -> ()
    | AAdt adt ->
        (* Simply explore the children *)
        List.iter (list_avalues allow_borrows push) adt.field_values
    | ALoan lc -> (
        (* Explore the loan content *)
        match lc with
        | V.ASharedLoan (bids, sv, child_av) ->
            (* We don't support nested borrows for now *)
            assert (not (value_has_borrows ctx sv.V.value));
            (* Push a value *)
            let ignored = mk_aignored child_av.V.ty in
            let value = V.ALoan (V.ASharedLoan (bids, sv, ignored)) in
            push { V.value; ty };
            (* Explore the child *)
            list_avalues false push_fail child_av
        | V.AMutLoan (bid, child_av) ->
            let ignored = mk_aignored child_av.V.ty in
            let value = V.ALoan (V.AMutLoan (bid, ignored)) in
            push { V.value; ty };
            (* Explore the child *)
            list_avalues false push_fail child_av
        | V.AEndedMutLoan
            { child = child_av; given_back = _; given_back_meta = _ }
        | V.AEndedSharedLoan (_, child_av)
        | V.AIgnoredMutLoan (_, child_av)
        | V.AEndedIgnoredMutLoan
            { child = child_av; given_back = _; given_back_meta = _ }
        | V.AIgnoredSharedLoan child_av ->
            (* We don't support nested borrows for now *)
            assert (not (ty_has_borrows ctx.type_context.type_infos child_av.ty));
            (* Simply explore the child *)
            list_avalues false push_fail child_av)
    | ABorrow bc -> (
        (* Sanity check - rem.: may be redundant with [push_fail] *)
        assert allow_borrows;
        (* Explore the borrow content *)
        match bc with
        | V.AMutBorrow (mv, bid, child_av) ->
            let ignored = mk_aignored child_av.V.ty in
            let value = V.ABorrow (V.AMutBorrow (mv, bid, ignored)) in
            push { V.value; ty };
            (* Explore the child *)
            list_avalues false push_fail child_av
        | V.ASharedBorrow _ ->
            (* Nothing specific to do: keep the value as it is *)
            push av
        | V.AIgnoredMutBorrow (_, child_av)
        | V.AEndedIgnoredMutBorrow
            { child = child_av; given_back_loans_proj = _; given_back_meta = _ }
          ->
            (* We don't support nested borrows for now *)
            assert (not (ty_has_borrows ctx.type_context.type_infos child_av.ty));
            (* Just explore the child *)
            list_avalues false push_fail child_av
        | V.AProjSharedBorrow _ ->
            (* Nothing specific to do: keep the value as it is *)
            push_avalue av
        | V.AEndedMutBorrow _ | V.AEndedSharedBorrow ->
            (* If we get there it means the abstraction ended: it should not
               be in the context anymore (if we end *one* borrow in an abstraction,
               we have to end them all and remove the abstraction from the context)
            *)
            raise (Failure "Unreachable"))
    | ASymbolic _ ->
        (* For now, we fore all symbolic values containing borrows to be eagerly
           expanded *)
        assert (not (ty_has_borrows ctx.type_context.type_infos ty))
  in
  (* Destructure the avalues *)
  List.iter (list_avalues true push_avalue) abs0.V.avalues;
  let avalues = List.rev !avalues in
  (* Update *)
  { abs0 with V.avalues; kind = abs_kind; can_end }

let abs_is_destructured (ctx : C.eval_ctx) (abs : V.abs) : bool =
  let abs' = destructure_abs abs.kind abs.can_end ctx abs in
  abs = abs'

let convert_value_to_abstractions (abs_kind : V.abs_kind) (can_end : bool)
    (ctx : C.eval_ctx) (v : V.typed_value) : V.abs list =
  (* Convert the value to a list of avalues *)
  let absl = ref [] in
  let push_abs (r_id : T.RegionId.id) (avalues : V.typed_avalue list) : unit =
    if avalues = [] then ()
    else
      (* Reverse the list of avalues *)
      let avalues = List.rev avalues in
      (* Create the abs *)
      let abs =
        {
          V.abs_id = C.fresh_abstraction_id ();
          kind = abs_kind;
          can_end;
          parents = V.AbstractionId.Set.empty;
          original_parents = [];
          regions = T.RegionId.Set.singleton r_id;
          ancestors_regions = T.RegionId.Set.empty;
          avalues;
        }
      in
      (* Add to the list of abstractions *)
      absl := abs :: !absl
  in

  (* [group]: group in one abstraction (because we dived into a borrow/loan) *)
  let rec to_avalues (allow_borrows : bool) (group : bool)
      (r_id : T.RegionId.id) (v : V.typed_value) : V.typed_avalue list =
    let ty = v.V.ty in
    match v.V.value with
    | V.Primitive _ -> []
    | V.Bottom ->
        (* Can happen: we *do* convert dummy values to abstractions, and dummy
           values can contain bottoms *)
        []
    | V.Adt adt ->
        (* Two cases, depending on whether we have to group all the borrows/loans
           inside one abstraction or not *)
        if group then
          (* Convert to avalues, and transmit to the parent *)
          List.concat
            (List.map (to_avalues allow_borrows group r_id) adt.field_values)
        else (
          (* Create one abstraction per field, and transmit nothing to the parent *)
          List.iter
            (fun fv ->
              let r_id = C.fresh_region_id () in
              let values = to_avalues allow_borrows group r_id fv in
              push_abs r_id values)
            adt.field_values;
          [])
    | V.Borrow bc -> (
        let _, ref_ty, kind = ty_as_ref ty in
        (* Sanity check *)
        assert allow_borrows;
        (* Convert the borrow content *)
        match bc with
        | SharedBorrow (_, bid) ->
            let ref_ty = ety_no_regions_to_rty ref_ty in
            let ty = T.Ref (T.Var r_id, ref_ty, kind) in
            let value = V.ABorrow (V.ASharedBorrow bid) in
            [ { V.value; ty } ]
        | MutBorrow (bid, bv) ->
            let r_id = if group then r_id else C.fresh_region_id () in
            (* We don't support nested borrows for now *)
            assert (not (value_has_borrows ctx bv.V.value));
            (* Push the avalue - note that we use [AIgnore] for the inner avalue *)
            let mv = bv in
            let ref_ty = ety_no_regions_to_rty ref_ty in
            let ty = T.Ref (T.Var r_id, ref_ty, kind) in
            let ignored = mk_aignored ref_ty in
            let value = V.ABorrow (V.AMutBorrow (mv, bid, ignored)) in
            let value = { V.value; ty } in
            (* Continue exploring, looking for loans (and forbidding borrows,
               because we don't support nested borrows for now) *)
            value :: to_avalues false true r_id bv
        | ReservedMutBorrow _ ->
            (* This borrow should have been activated *)
            raise (Failure "Unexpected"))
    | V.Loan lc -> (
        match lc with
        | V.SharedLoan (bids, sv) ->
            let r_id = if group then r_id else C.fresh_region_id () in
            (* We don't support nested borrows for now *)
            assert (not (value_has_borrows ctx sv.V.value));
            (* Push the avalue - note that we use [AIgnore] for the inner avalue *)
            let ty = ety_no_regions_to_rty ty in
            let ignored = mk_aignored ty in
            let value = V.ALoan (V.ASharedLoan (bids, sv, ignored)) in
            let value = { V.value; ty } in
            (* Continue exploring, looking for loans (and forbidding borrows,
               because we don't support nested borrows for now) *)
            value :: to_avalues false true r_id sv
        | V.MutLoan bid ->
            (* Push the avalue - note that we use [AIgnore] for the inner avalue *)
            let ty = ety_no_regions_to_rty ty in
            let ignored = mk_aignored ty in
            let value = V.ALoan (V.AMutLoan (bid, ignored)) in
            [ { V.value; ty } ])
    | V.Symbolic _ ->
        (* For now, we force all the symbolic values containing borrows to
           be eagerly expanded *)
        (* We don't support nested borrows for now *)
        assert (not (value_has_borrows ctx v.V.value));
        (* Return nothing *)
        []
  in
  (* Generate the avalues *)
  let r_id = C.fresh_region_id () in
  let values = to_avalues true false r_id v in
  (* Introduce an abstraction for the returned values *)
  push_abs r_id values;
  (* Return *)
  List.rev !absl

let merge_abstractions (abs_kind : V.abs_kind) (can_end : bool)
    (ctx : C.eval_ctx) (abs0 : V.abs) (abs1 : V.abs) : V.abs =
  (* Check that the abstractions are destructured *)
  if !Config.check_invariants then (
    assert (abs_is_destructured ctx abs0);
    assert (abs_is_destructured ctx abs1));

  (* Visit the abstractions, list their borrows and loans *)
  let borrows = ref V.BorrowId.Set.empty in
  let loans = ref V.BorrowId.Set.empty in

  let push_loans ids = loans := V.BorrowId.Set.union !loans ids in
  let push_loan id = loans := V.BorrowId.Set.add id !loans in
  let push_borrow id = borrows := V.BorrowId.Set.add id !borrows in

  let iter_avalues =
    object
      inherit [_] V.iter_typed_avalue as super

      method! visit_loan_content env lc =
        (* Can happen if we explore shared values whose sub-values are
           reborrowed *)
        (match lc with
        | SharedLoan (bids, _) -> push_loans bids
        | MutLoan _ -> raise (Failure "Unreachable"));
        (* Continue *)
        super#visit_loan_content env lc

      method! visit_borrow_content _ _ =
        (* Can happen if we explore shared values which contain borrows -
           i.e., if we have nested borrows (we forbid this for now) *)
        raise (Failure "Unreachable")

      method! visit_aloan_content env lc =
        (* Register the loans *)
        (match lc with
        | V.ASharedLoan (bids, _, _) -> push_loans bids
        | V.AMutLoan (bid, _) -> push_loan bid
        | V.AEndedMutLoan _ | V.AEndedSharedLoan _ | V.AIgnoredMutLoan _
        | V.AEndedIgnoredMutLoan _ | V.AIgnoredSharedLoan _ ->
            (* The abstraction has been destructured, so those shouldn't appear *)
            raise (Failure "Unreachable"));
        (* Continue *)
        super#visit_aloan_content env lc

      method! visit_aborrow_content env bc =
        (* Explore the borrow content *)
        (match bc with
        | V.AMutBorrow (_, bid, _) -> push_borrow bid
        | V.ASharedBorrow bid -> push_borrow bid
        | V.AProjSharedBorrow asb ->
            let register asb =
              match asb with
              | V.AsbBorrow bid -> push_borrow bid
              | V.AsbProjReborrows _ ->
                  (* Can only happen if the symbolic value (potentially) contains
                     borrows - i.e., we have nested borrows *)
                  raise (Failure "Unreachable")
            in
            List.iter register asb
        | V.AIgnoredMutBorrow _ | V.AEndedIgnoredMutBorrow _
        | V.AEndedMutBorrow _ | V.AEndedSharedBorrow ->
            (* The abstraction has been destructured, so those shouldn't appear *)
            raise (Failure "Unreachable"));
        super#visit_aborrow_content env bc

      method! visit_symbolic_value _ _ =
        (* Sanity check *)
        raise (Failure "Unrechable")
    end
  in

  List.iter (iter_avalues#visit_typed_avalue ()) abs0.V.avalues;
  List.iter (iter_avalues#visit_typed_avalue ()) abs1.V.avalues;

  (* List the values, ignoring the loans/borrows which whose associated
     borrows/loans are in the other abstraction already - note that we
     take advantage of the fact that the values are destructured.

     We convert the loans/borrows we want to ignore to [Ignored] values,
     then filter them.
  *)
  let intersect = V.BorrowId.Set.inter !loans !borrows in
  let filter_bids (bids : V.BorrowId.Set.t) : V.BorrowId.Set.t option =
    let bids = V.BorrowId.Set.diff bids intersect in
    if V.BorrowId.Set.is_empty bids then None else Some bids
  in
  let filter_bid (bid : V.BorrowId.id) : V.BorrowId.id option =
    if V.BorrowId.Set.mem bid intersect then None else Some bid
  in

  let map_avalues =
    object (self : 'self)
      inherit [_] V.map_typed_avalue as super

      method! visit_Loan env lc =
        (* Can happen if we explore shared values whose sub-values are
           reborrowed *)
        match lc with
        | SharedLoan (bids, sv) -> (
            match filter_bids bids with
            | None -> (self#visit_typed_value env sv).V.value
            | Some bids -> super#visit_Loan env (SharedLoan (bids, sv)))
        | MutLoan _ -> raise (Failure "Unreachable")

      method! visit_borrow_content _ _ =
        (* Can happen if we explore shared values which contain borrows -
           i.e., if we have nested borrows (we forbid this for now) *)
        raise (Failure "Unreachable")

      method! visit_ALoan env lc =
        (* Register the loans *)
        match lc with
        | V.ASharedLoan (bids, sv, asv) -> (
            match filter_bids bids with
            | None ->
                let sv = super#visit_typed_value env sv in
                assert (is_aignored asv.V.value);
                (* Check if the shared value contains loans or borrows - rem.: there shouldn't
                   be borrows actually, because for now we forbid nested borrows.

                   If it doesn't, we can ignore the value altogether.
                *)
                if
                  loans_in_value sv
                  || ty_has_borrows ctx.type_context.type_infos sv.V.ty
                then
                  (* The value is not shared anymore, but it contains shared sub-values.

                     It would be good to deconstruct the sub-values. For now, let's fail
                     (rem.: it would be sound to have a shared aloan with an empty set
                     of borrow ids).
                  *)
                  raise (Failure "Unimplemented")
                else V.AIgnored
            | Some bids -> super#visit_ALoan env (ASharedLoan (bids, sv, asv)))
        | V.AMutLoan (bid, child) -> (
            assert (is_aignored child.V.value);
            match filter_bid bid with
            | None -> V.AIgnored
            | Some _ -> super#visit_ALoan env lc)
        | V.AEndedMutLoan _ | V.AEndedSharedLoan _ | V.AIgnoredMutLoan _
        | V.AEndedIgnoredMutLoan _ | V.AIgnoredSharedLoan _ ->
            (* The abstraction has been destructured, so those shouldn't appear *)
            raise (Failure "Unreachable")

      method! visit_ABorrow env bc =
        (* Explore the borrow content *)
        match bc with
        | V.AMutBorrow (_, bid, child) -> (
            assert (is_aignored child.V.value);
            match filter_bid bid with
            | None -> V.AIgnored
            | Some _ -> super#visit_ABorrow env bc)
        | V.ASharedBorrow bid -> (
            match filter_bid bid with
            | None -> V.AIgnored
            | Some _ -> super#visit_ABorrow env bc)
        | V.AProjSharedBorrow asb ->
            let filter asb =
              match asb with
              | V.AsbBorrow bid -> (
                  match filter_bid bid with None -> None | Some _ -> Some asb)
              | V.AsbProjReborrows _ ->
                  (* Can only happen if the symbolic value (potentially) contains
                     borrows - i.e., we have nested borrows *)
                  raise (Failure "Unreachable")
            in
            let asb = List.filter_map filter asb in
            V.ABorrow (V.AProjSharedBorrow asb)
        | V.AIgnoredMutBorrow _ | V.AEndedIgnoredMutBorrow _
        | V.AEndedMutBorrow _ | V.AEndedSharedBorrow ->
            (* The abstraction has been destructured, so those shouldn't appear *)
            raise (Failure "Unreachable")

      method! visit_symbolic_value _ _ =
        (* Sanity check *)
        raise (Failure "Unrechable")
    end
  in

  (* Apply the transformation *)
  let avalues =
    List.map
      (map_avalues#visit_typed_avalue ())
      (List.append abs0.avalues abs1.avalues)
  in

  (* Filter the ignored values *)
  let avalues =
    List.filter (fun (v : V.typed_avalue) -> not (is_aignored v.value)) avalues
  in

  (* Create the new abstraction *)
  let abs_id = C.fresh_abstraction_id () in
  (* Note that one of the two abstractions might a parent of the other *)
  let parents =
    V.AbstractionId.Set.diff
      (V.AbstractionId.Set.union abs0.parents abs1.parents)
      (V.AbstractionId.Set.of_list [ abs0.abs_id; abs1.abs_id ])
  in
  let original_parents = V.AbstractionId.Set.elements parents in
  let regions = T.RegionId.Set.union abs0.regions abs1.regions in
  let ancestors_regions =
    T.RegionId.Set.diff (T.RegionId.Set.union abs0.regions abs1.regions) regions
  in
  let abs =
    {
      V.abs_id;
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
  if !Config.check_invariants then assert (abs_is_destructured ctx abs);
  (* Return *)
  abs
