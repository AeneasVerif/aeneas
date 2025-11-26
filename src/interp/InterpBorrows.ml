open Types
open Values
open Contexts
open Cps
open Utils
open ValuesUtils
open TypesUtils
open InterpUtils
open InterpBorrowsCore
open InterpProjectors

(** The local logger *)
let log = Logging.borrows_log

(** Auxiliary function to end borrows: lookup a *concrete* borrow in the
    environment, update it (by returning an updated environment where the borrow
    has been replaced by {!Bottom})) if we can end the borrow (for instance, it
    is not an outer borrow...) or return the reason why we couldn't update the
    borrow.

    We can end a borrow if:
    - it is not inside a borrow
    - it doesn't contain loans
    - it is not inside a region abstraction (it can happen if the borrow is
      inside a shared value)

    [end_borrow_aux] then simply performs a loop: as long as we need to end
    (outer) borrows, we end them, before finally ending the borrow we wanted to
    end in the first place.

    - [allowed_abs]: if not [None], allows to get a borrow in the given
      abstraction without ending the whole abstraction first. This parameter
      allows us to use {!end_borrow_aux} as an auxiliary function for
      {!end_abstraction_aux} (we end all the borrows in the abstraction one by
      one before removing the abstraction from the context). We use this to end
      shared borrows and mutable borrows inside of **shared values**; the other
      borrows are taken care of differently. *)
let end_concrete_borrow_get_borrow_core (span : Meta.span)
    (allowed_abs : AbsId.id option) (l : unique_borrow_id) (ctx : eval_ctx) :
    ( eval_ctx * (AbsId.id option * g_borrow_content) option,
      priority_borrow_or_abs )
    result =
  (* We use a reference to communicate the kind of borrow we found, if we
   * find one *)
  let replaced_bc : (AbsId.id option * g_borrow_content) option ref =
    ref None
  in
  let set_replaced_bc (abs_id : AbsId.id option) (bc : g_borrow_content) =
    [%sanity_check] span (Option.is_none !replaced_bc);
    replaced_bc := Some (abs_id, bc)
  in
  (* Raise an exception if:
     - there are outer borrows
     - if we are inside an abstraction
     - there are inner loans
     (this exception is caught in a wrapper function) *)
  let raise_if_priority (outer : outer) (borrowed_value : tvalue option) =
    (* First, look for outer borrows or abstraction *)
    (match outer.abs_id with
    | Some abs -> (
        if
          (* Check if we can end borrow inside this abstraction *)
          Some abs <> allowed_abs
        then raise (FoundPriority (OuterAbs abs))
        else
          match outer.borrow_loan with
          | Some (MutBorrow bid) -> raise (FoundPriority (OuterMutBorrow bid))
          | Some (SharedLoan lid) -> raise (FoundPriority (OuterSharedLoan lid))
          | None -> ())
    | None -> (
        match outer.borrow_loan with
        | Some (MutBorrow bid) -> raise (FoundPriority (OuterMutBorrow bid))
        | Some (SharedLoan lid) -> raise (FoundPriority (OuterSharedLoan lid))
        | None -> ()));
    (* Then check if there are inner loans *)
    match borrowed_value with
    | None -> ()
    | Some v -> (
        match get_first_loan_in_value v with
        | None -> ()
        | Some c -> (
            match c with
            | VSharedLoan (bid, _) -> raise (FoundPriority (InnerLoan bid))
            | VMutLoan bid -> raise (FoundPriority (InnerLoan bid))))
  in

  (* The environment in the visitor is used to keep track of the first
     outer shared loan or mutable borrow we dived into (because we need to
     end it before ending the target borrow). *)
  let visitor =
    object
      inherit [_] map_eval_ctx as super

      (** We reimplement {!visit_Loan} because we may have to update the outer
          borrows *)
      method! visit_VLoan (outer : outer) lc =
        match lc with
        | VMutLoan bid -> VLoan (super#visit_VMutLoan outer bid)
        | VSharedLoan (bid, v) ->
            (* Remember the outer loan before diving into the shared value,
               in case we haven't dived into a borrow/loan yet. *)
            let outer = update_outer_borrow outer (SharedLoan bid) in
            VLoan (super#visit_VSharedLoan outer bid v)

      method! visit_VBorrow (outer : outer) bc =
        match bc with
        | VSharedBorrow (_, l') | VReservedMutBorrow (_, l') ->
            (* Check if this is the borrow we are looking for *)
            if l = UShared l' then (
              (* Check if there are outer borrows or if we are inside an abstraction *)
              raise_if_priority outer None;
              (* Register the update *)
              set_replaced_bc outer.abs_id (Concrete bc);
              (* Update the value *)
              VBottom)
            else super#visit_VBorrow outer bc
        | VMutBorrow (l', bv) ->
            (* Check if this is the borrow we are looking for *)
            if l = UMut l' then (
              (* Check if there are outer borrows or if we are inside an abstraction *)
              raise_if_priority outer (Some bv);
              (* Register the update *)
              set_replaced_bc outer.abs_id (Concrete bc);
              (* Update the value *)
              VBottom)
            else
              (* Remember the outer borrow before diving into the shared value,
               in case we haven't dived into a borrow/loan yet. *)
              let outer = update_outer_borrow outer (MutBorrow l') in
              VBorrow (super#visit_VMutBorrow outer l' bv)

      (** We reimplement {!visit_ALoan} because we may have to update the outer
          borrows *)
      method! visit_ALoan outer lc =
        (* Note that the children avalues are just other, independent loans,
         * so we don't need to update the outer borrows when diving in.
         * We keep track of the parents/children relationship only because we
         * need it to properly instantiate the backward functions when generating
         * the pure translation. *)
        match lc with
        | AMutLoan (pm, _, _) ->
            [%sanity_check] span (pm = PNone);
            (* Nothing special to do *)
            super#visit_ALoan outer lc
        | ASharedLoan (pm, bid, v, av) ->
            [%sanity_check] span (pm = PNone);
            (* Explore the shared value - we need to update the outer borrows *)
            let souter = update_outer_borrow outer (SharedLoan bid) in
            let v = super#visit_tvalue souter v in
            (* Explore the child avalue - we keep the same outer borrows *)
            let av = super#visit_tavalue outer av in
            (* Reconstruct *)
            ALoan (ASharedLoan (pm, bid, v, av))
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
        | AMutBorrow (pm, bid, _) ->
            [%sanity_check] span (pm = PNone);
            (* Check if this is the borrow we are looking for *)
            if UMut bid = l then (
              (* Signal that we should replace the whole abstraction *)
              raise_if_priority outer None;
              (* We shouldn't get there: this should be taken care of elsewhere *)
              [%craise] span "Unreachable")
            else
              (* Update the outer borrows before diving into the child avalue *)
              let outer = update_outer_borrow outer (MutBorrow bid) in
              super#visit_ABorrow outer bc
        | ASharedBorrow (pm, _, sid) ->
            [%sanity_check] span (pm = PNone);
            (* Check if this is the borrow we are looking for *)
            if UShared sid = l then (
              (* Check there are outer borrows, or if we need to end the whole
               * abstraction *)
              raise_if_priority outer None;
              (* Register the update *)
              set_replaced_bc outer.abs_id (Abstract bc);
              (* Update the value - note that we are necessarily in the second
                 of the two cases described above *)
              ABorrow AEndedSharedBorrow)
            else super#visit_ABorrow outer bc
        | AIgnoredMutBorrow (_, _)
        | AEndedMutBorrow _
        | AEndedIgnoredMutBorrow
            { given_back = _; child = _; given_back_meta = _ }
        | AEndedSharedBorrow ->
            (* Nothing special to do *)
            super#visit_ABorrow outer bc
        | AProjSharedBorrow asb -> (
            (* Check if the borrow we are looking for is in the asb *)
            match l with
            | UShared l ->
                if borrow_in_asb l asb then (
                  (* Check there are outer borrows, or if we need to end the whole
                   * abstraction *)
                  raise_if_priority outer None;
                  (* Register the update *)
                  set_replaced_bc outer.abs_id (Abstract bc);
                  (* Update the value - note that we are necessarily in the second
                   * of the two cases described above *)
                  let asb = remove_borrow_from_asb span l asb in
                  ABorrow (AProjSharedBorrow asb))
                else (* Nothing special to do *)
                  super#visit_ABorrow outer bc
            | UMut _ -> super#visit_ABorrow outer bc)

      method! visit_abs outer abs =
        (* Update the outer abs *)
        [%sanity_check] span (Option.is_none outer.abs_id);
        [%sanity_check] span (Option.is_none outer.borrow_loan);
        let outer = { abs_id = Some abs.abs_id; borrow_loan = None } in
        super#visit_abs outer abs
    end
  in
  (* Catch the exceptions - raised if there are outer borrows *)
  try
    let ctx =
      visitor#visit_eval_ctx { abs_id = None; borrow_loan = None } ctx
    in
    Ok (ctx, !replaced_bc)
  with FoundPriority outers -> Error outers

(** See [end_borrow_get_borrow] *)
let end_concrete_borrow_get_borrow (span : Meta.span) (l : unique_borrow_id)
    (ctx : eval_ctx) :
    ( eval_ctx * (AbsId.id option * g_borrow_content) option,
      priority_borrow_or_abs )
    result =
  end_concrete_borrow_get_borrow_core span None l ctx

let end_concrete_borrow_in_abs_get_borrow (span : Meta.span) (abs_id : abs_id)
    (l : unique_borrow_id) (ctx : eval_ctx) :
    ( eval_ctx * (AbsId.id option * g_borrow_content) option,
      priority_borrow_or_abs )
    result =
  end_concrete_borrow_get_borrow_core span (Some abs_id) l ctx

(** Auxiliary function to end borrows. See {!give_back_concrete}.

    When we end a mutable borrow, we need to "give back" the value it contained
    to its original owner by reinserting it at the proper position.

    Note that this function checks that there is exactly one loan to which we
    give the value back. TODO: this was not the case before, so some sanity
    checks are not useful anymore.

    Also, we take care to also update the **abstraction expressions**. *)
let give_back_value (span : Meta.span) (bid : BorrowId.id) (nv : tvalue)
    (ctx : eval_ctx) : eval_ctx =
  (* Sanity check *)
  [%cassert] span
    (not (concrete_loans_in_value nv))
    "Can not end a borrow because the value to give back contains bottom";
  [%cassert] span
    (not (bottom_in_value ctx.ended_regions nv))
    "Can not end a borrow because the value to give back contains bottom";
  (* Debug *)
  [%ltrace
    "- bid: " ^ BorrowId.to_string bid ^ "\n- value: "
    ^ tvalue_to_string ~span:(Some span) ctx nv
    ^ "\n- context:\n"
    ^ eval_ctx_to_string ~span:(Some span) ctx];
  (* We use a reference to check that we updated exactly one loan *)
  let replaced : bool ref = ref false in
  let set_replaced () =
    [%sanity_check] span (not !replaced);
    replaced := true
  in
  let replaced_evalue : bool ref = ref false in
  let set_replaced_evalue () =
    [%sanity_check] span (not !replaced_evalue);
    replaced_evalue := true
  in
  (* Whenever giving back symbolic values, they shouldn't contain already ended regions *)
  let check_symbolic_no_ended = true in
  (* The visitor to give back the values *)
  let obj =
    object (self)
      inherit [_] map_eval_ctx as super

      (** This is a bit annoying, but as we need the type of the value we are
          exploring, for sanity checks, we need to implement {!visit_tavalue}
          instead of overriding {!visit_ALoan} *)
      method! visit_tvalue opt_abs (v : tvalue) : tvalue =
        match v.value with
        | VLoan lc ->
            let value = self#visit_typed_Loan opt_abs v.ty lc in
            ({ v with value } : tvalue)
        | _ -> super#visit_tvalue opt_abs v

      method visit_typed_Loan opt_abs ty lc =
        match lc with
        | VSharedLoan (bids, v) ->
            (* We are giving back a value (i.e., the content of a *mutable*
               borrow): nothing special to do *)
            VLoan (super#visit_VSharedLoan opt_abs bids v)
        | VMutLoan bid' ->
            (* Check if this is the loan we are looking for *)
            if bid' = bid then (
              (* Sanity check *)
              let expected_ty = ty in
              if nv.ty <> expected_ty then
                [%craise] span
                  ("Value given back doesn't have the proper type:\n\
                    - expected: " ^ ty_to_string ctx ty ^ "\n- received: "
                 ^ ty_to_string ctx nv.ty);
              (* Replace *)
              set_replaced ();
              nv.value)
            else VLoan (super#visit_VMutLoan opt_abs bid')

      (** This is a bit annoying, but as we need the type of the avalue we are
          exploring, in order to be able to project the value we give back, we
          need to reimplement {!visit_tavalue} instead of {!visit_ALoan} *)
      method! visit_tavalue opt_abs (av : tavalue) : tavalue =
        match av.value with
        | ALoan lc ->
            let value = self#visit_typed_ALoan opt_abs av.ty lc in
            ({ av with value } : tavalue)
        | ABorrow bc ->
            let value = self#visit_typed_ABorrow opt_abs av.ty bc in
            ({ av with value } : tavalue)
        | _ -> super#visit_tavalue opt_abs av

      (** Similar to [visit_tevalue] *)
      method! visit_tevalue opt_abs (av : tevalue) : tevalue =
        match av.value with
        | ELoan lc ->
            let value = self#visit_typed_ELoan opt_abs av.ty lc in
            ({ av with value } : tevalue)
        | EBorrow bc ->
            let value = self#visit_typed_EBorrow opt_abs av.ty bc in
            ({ av with value } : tevalue)
        | _ -> super#visit_tevalue opt_abs av

      (** We need to inspect ignored mutable borrows, to insert loan projectors
          if necessary. *)
      method visit_typed_ABorrow (opt_abs : abs option) (ty : rty)
          (bc : aborrow_content) : avalue =
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
                  let given_back_meta = as_symbolic span nv.value in
                  (* The loan projector *)
                  let _, ty, _ = ty_as_ref ty in
                  let given_back =
                    mk_aproj_loans_value_from_symbolic_value abs.regions.owned
                      sv ty
                  in
                  (* Continue giving back in the child value *)
                  let child = super#visit_tavalue opt_abs child in
                  (* Return *)
                  ABorrow
                    (AEndedIgnoredMutBorrow
                       { given_back; child; given_back_meta })
              | _ -> [%craise] span "Unreachable"
            else
              (* Continue exploring *)
              ABorrow (super#visit_AIgnoredMutBorrow opt_abs bid' child)
        | _ ->
            (* Continue exploring *)
            super#visit_ABorrow opt_abs bc

      (** We are not specializing an already existing method, but adding a new
          method (for projections, we need type information) *)
      method visit_typed_ALoan (opt_abs : abs option) (ty : rty)
          (lc : aloan_content) : avalue =
        (* Preparing a bit *)
        let regions =
          match opt_abs with
          | None -> [%craise] span "Unreachable"
          | Some abs -> abs.regions.owned
        in
        (* Rk.: there is a small issue with the types of the aloan values.
         * See the comment at the level of definition of {!tavalue} *)
        let borrowed_value_aty =
          let _, ty, _ = ty_get_ref ty in
          ty
        in
        match lc with
        | AMutLoan (pm, bid', child) ->
            [%sanity_check] span (pm = PNone);
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
                apply_proj_borrows span check_symbolic_no_ended ctx regions nv
                  borrowed_value_aty
              in
              (* Continue giving back in the child value *)
              let child = super#visit_tavalue opt_abs child in
              (* Return the new value *)
              ALoan (AEndedMutLoan { child; given_back; given_back_meta }))
            else (* Continue exploring *)
              super#visit_ALoan opt_abs lc
        | ASharedLoan (pm, _, _, _) ->
            [%sanity_check] span (pm = PNone);
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
                apply_proj_borrows span check_symbolic_no_ended ctx regions nv
                  borrowed_value_aty
              in
              (* Continue giving back in the child value *)
              let child = super#visit_tavalue opt_abs child in
              ALoan
                (AEndedIgnoredMutLoan { given_back; child; given_back_meta })
            else super#visit_ALoan opt_abs lc
        | AEndedIgnoredMutLoan
            { given_back = _; child = _; given_back_meta = _ }
        | AIgnoredSharedLoan _ ->
            (* Nothing special to do *)
            super#visit_ALoan opt_abs lc

      (** We need to inspect ignored mutable borrows, to insert loan projectors
          if necessary. *)
      method visit_typed_EBorrow (opt_abs : abs option) (ty : rty)
          (bc : eborrow_content) : evalue =
        match bc with
        | EIgnoredMutBorrow (bid', child) ->
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
                  let given_back_meta = as_symbolic span nv.value in
                  (* The loan projector *)
                  let _, ty, _ = ty_as_ref ty in
                  let given_back =
                    mk_eproj_loans_value_from_symbolic_value
                      ctx.type_ctx.type_infos abs.regions.owned sv ty
                  in
                  (* Continue giving back in the child value *)
                  let child = super#visit_tevalue opt_abs child in
                  (* Return *)
                  EBorrow
                    (EEndedIgnoredMutBorrow
                       { given_back; child; given_back_meta })
              | _ -> [%craise] span "Unreachable"
            else
              (* Continue exploring *)
              EBorrow (super#visit_EIgnoredMutBorrow opt_abs bid' child)
        | _ ->
            (* Continue exploring *)
            super#visit_EBorrow opt_abs bc

      (** We are not specializing an already existing method, but adding a new
          method (for projections, we need type information) *)
      method visit_typed_ELoan (opt_abs : abs option) (ty : rty)
          (lc : eloan_content) : evalue =
        (* Preparing a bit *)
        let regions =
          match opt_abs with
          | None -> [%craise] span "Unreachable"
          | Some abs -> abs.regions.owned
        in
        (* Rk.: there is a small issue with the types of the aloan values.
         * See the comment at the level of definition of {!tavalue} *)
        let borrowed_value_aty =
          let _, ty, _ = ty_get_ref ty in
          ty
        in
        match lc with
        | EMutLoan (pm, bid', child) ->
            [%sanity_check] span (pm = PNone);
            if bid' = bid then (
              (* This is the loan we are looking for: apply the projection to
               * the value we give back and replaced this mutable loan with
               * an ended loan *)
              (* Register the insertion *)
              set_replaced_evalue ();
              (* Remember the given back value as a meta-value *)
              let given_back_meta = nv in
              (* Apply the projection *)
              let given_back =
                apply_eproj_borrows span check_symbolic_no_ended ctx regions nv
                  borrowed_value_aty
              in
              (* Continue giving back in the child value *)
              let child = super#visit_tevalue opt_abs child in
              (* Return the new value *)
              ELoan (EEndedMutLoan { child; given_back; given_back_meta }))
            else (* Continue exploring *)
              super#visit_ELoan opt_abs lc
        | EEndedMutLoan { child = _; given_back = _; given_back_meta = _ } ->
            (* Nothing special to do *)
            super#visit_ELoan opt_abs lc
        | EIgnoredMutLoan (opt_bid, child) ->
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
                apply_eproj_borrows span check_symbolic_no_ended ctx regions nv
                  borrowed_value_aty
              in
              (* Continue giving back in the child value *)
              let child = super#visit_tevalue opt_abs child in
              ELoan
                (EEndedIgnoredMutLoan { given_back; child; given_back_meta })
            else super#visit_ELoan opt_abs lc
        | EEndedIgnoredMutLoan
            { given_back = _; child = _; given_back_meta = _ } ->
            (* Nothing special to do *)
            super#visit_ELoan opt_abs lc

      method! visit_EAbs opt_abs abs =
        (* We remember in which abstraction we are before diving -
         * this is necessary for projecting values: we need to know
         * over which regions to project *)
        [%sanity_check] span (Option.is_none opt_abs);
        super#visit_EAbs (Some abs) abs
    end
  in

  (* Explore the environment *)
  let ctx = obj#visit_eval_ctx None ctx in
  (* Check we gave back to exactly one loan *)
  [%cassert] span !replaced "No loan updated";
  (* *)
  ctx

(** Update the borrow projectors upon ending some regions in a symbolic value.

    Because doing this introduces a fresh symbolic value which may contain
    borrows, we may need to update the proj_borrows to introduce loan projectors
    over those borrows.

    Note that we also update the abstraction expressions. *)
let end_aproj_borrows (span : Meta.span) (ended_regions : RegionId.Set.t)
    (proj : symbolic_proj) (nsv : symbolic_value) (ctx : eval_ctx) : eval_ctx =
  (* Sanity checks *)
  [%sanity_check] span (proj.sv_id <> nsv.sv_id && ty_is_rty proj.proj_ty);
  [%ltrace
    "- ended regions: "
    ^ RegionId.Set.to_string None ended_regions
    ^ "\n- projection type: "
    ^ ty_to_string ctx proj.proj_ty
    ^ "\n- sv: "
    ^ symbolic_value_id_to_pretty_string proj.sv_id
    ^ "\n- nsv: "
    ^ symbolic_value_to_string ctx nsv
    ^ "\n- ctx: " ^ eval_ctx_to_string ctx];
  (* See the comments about [AProjLoans], we have to update in two situations:
     - if the projection over the symbolic value intersects the borrow projector:
       this is because we are ending exactly this borrow projector, so we need
       to end it.
     - if the *outlive* projection intersects the borrow projector: we need to
       project the inner loans of the given back value.
  *)
  let update_mut ~owned ~outlive (_abs : abs) (aproj : aproj_borrows) : aproj =
    (* We can be in one case, or the other, but not both *)
    [%sanity_check] span ((not owned) || not outlive);

    if owned then
      (* There is nothing to project *)
      let mvalues = { consumed = proj.sv_id; given_back = nsv } in
      AEndedProjBorrows { mvalues; loans = aproj.loans }
    else
      (* Compute the projection over the given back value (we project the loans) *)
      let loan =
        AProjLoans
          {
            proj = { aproj.proj with sv_id = nsv.sv_id };
            consumed = [];
            borrows = [];
          }
      in
      let consumed : mconsumed_symb =
        { sv_id = nsv.sv_id; proj_ty = aproj.proj.proj_ty }
      in
      AProjBorrows { proj; loans = (consumed, loan) :: aproj.loans }
  in
  let update_emut ~owned ~outlive (_abs : abs) (aproj : eproj_borrows) : eproj =
    (* We can be in one case, or the other, but not both *)
    [%sanity_check] span ((not owned) || not outlive);

    if owned then
      (* There is nothing to project *)
      let mvalues = { consumed = proj.sv_id; given_back = nsv } in
      EEndedProjBorrows { mvalues; loans = aproj.loans }
    else
      (* Compute the projection over the given back value (we project the loans) *)
      let loan =
        EProjLoans
          {
            proj = { aproj.proj with sv_id = nsv.sv_id };
            consumed = [];
            borrows = [];
          }
      in
      let consumed : mconsumed_symb =
        { sv_id = nsv.sv_id; proj_ty = aproj.proj.proj_ty }
      in
      let { sv_id; proj_ty } : symbolic_proj = proj in
      EProjBorrows
        { proj = { sv_id; proj_ty }; loans = (consumed, loan) :: aproj.loans }
  in
  update_intersecting_aproj_borrows span ~fail_if_unchanged:true
    ~include_owned:true ~include_outlive:true ~update_shared:None ~update_mut
    ~update_emut ended_regions proj ctx

(** Give back a *modified* symbolic value. *)
let give_back_symbolic_value (_config : config) (span : Meta.span)
    (ended_regions : RegionId.Set.t) (proj : symbolic_proj)
    (nsv : symbolic_value) (ctx : eval_ctx) : eval_ctx =
  (* Sanity checks *)
  [%sanity_check] span (proj.sv_id <> nsv.sv_id && ty_is_rty proj.proj_ty);
  (* Substitution functions, to replace the borrow projectors over symbolic values *)
  (* We need to handle two cases:
     - the regions ended in the symbolic value might intersect with the owned
       regions of the abstraction.

       Ex.: we are ending abs1 below:
       {[
         abs0 {'a} { AProjLoans (s0 : &'a mut T) [] }
         abs1 {'b} { AProjBorrows (s0 : &'a mut T <: &'b mut T) }
       ]}
     - the regions given back in the symbolic value might intersect with the outlive
       regions of the abstraction, in which case we have to introduce a projection
       (because it means we ended ancestor "outer" borrows, and so we need
       to project the given back inner borrows into the abstraction).

       Ex.: we are ending abs2 below, and considering abs1: we have to project
       the inner borrows inside of abs1. However we do not project anything
       into abs0 (see the case above).
       {[
         abs0 {'a} { AProjLoans (s0 : &'a mut &'b mut T) [] }
         abs1 {'b} { AProjLoans (s0 : &'a mut &'b mut T) [] }
         abs2 {'c} { AProjBorrows (s0 : &'a mut &'b mut T <: &'c mut T &'d mut T) }
         abs3 {'d} { AProjBorrows (s0 : &'a mut &'b mut T <: &'c mut T &'d mut T) }
       ]}

     We proceed in two steps:
     - we first update when intersecting with ancestors regions
     - then we update when intersecting with owned regions
  *)
  let subst ~owned ~outlive (_abs : abs) (aproj : aproj_loans) : aproj =
    [%sanity_check] span ((not owned) || not outlive);
    if owned then
      (* There is nothing to project *)
      let child_proj = AEmpty in
      let consumed : mconsumed_symb =
        { sv_id = nsv.sv_id; proj_ty = aproj.proj.proj_ty }
      in
      AProjLoans
        { aproj with consumed = (consumed, child_proj) :: aproj.consumed }
    else
      (* Compute the projection over the given back value *)
      let borrow =
        AProjBorrows
          { proj = { aproj.proj with sv_id = nsv.sv_id }; loans = [] }
      in
      let consumed : mconsumed_symb =
        { sv_id = nsv.sv_id; proj_ty = proj.proj_ty }
      in
      AProjLoans { aproj with borrows = (consumed, borrow) :: aproj.borrows }
  in
  let esubst ~owned ~outlive (_abs : abs) (aproj : eproj_loans) : eproj =
    [%sanity_check] span ((not owned) || not outlive);
    if owned then
      (* There is nothing to project *)
      let child_proj = EEmpty in
      let consumed : mconsumed_symb =
        { sv_id = nsv.sv_id; proj_ty = aproj.proj.proj_ty }
      in
      EProjLoans
        { aproj with consumed = (consumed, child_proj) :: aproj.consumed }
    else
      (* Compute the projection over the given back value *)
      let borrow =
        EProjBorrows
          { proj = { aproj.proj with sv_id = nsv.sv_id }; loans = [] }
      in
      let consumed : mconsumed_symb =
        { sv_id = nsv.sv_id; proj_ty = proj.proj_ty }
      in
      EProjLoans { aproj with borrows = (consumed, borrow) :: aproj.borrows }
  in
  update_intersecting_aproj_loans span ~fail_if_unchanged:true
    ~include_owned:true ~include_outlive:true ended_regions proj subst esubst
    ctx

(** Convert an {!type:avalue} to a {!type:value}.

    This function is used when ending abstractions: whenever we end a borrow in
    an abstraction, we convert the borrowed {!avalue} to a fresh symbolic
    {!type:value}, then give back this {!type:value} to the context.

    Note that some regions may have ended in the symbolic value we generate. For
    instance, consider the following function signature:
    {[
      fn f<'a>(x : &'a mut &'a mut u32);
    ]}
    When ending the abstraction, the value given back for the outer borrow
    should be ⊥. In practice, we will give back a symbolic value which can't be
    expanded (because expanding this symbolic value would require expanding a
    reference whose region has already ended). *)
let convert_avalue_to_given_back_value (span : Meta.span) ctx (av : tavalue) :
    symbolic_value =
  mk_fresh_symbolic_value span ctx av.ty

(** Auxiliary function: see {!end_borrow_aux}.

    When we end a mutable borrow, we need to "give back" the value it contained
    to its original owner by reinserting it at the proper position.

    Rem.: this function is used when we ending *concrete* borrows (we handle
    borrows inside region abstractions elsewhere). *)
let give_back_concrete (span : Meta.span) (l : unique_borrow_id)
    (bc : g_borrow_content) (ctx : eval_ctx) : eval_ctx =
  (* Debug *)
  [%ltrace
    let bc =
      match bc with
      | Concrete bc -> borrow_content_to_string ~span:(Some span) ctx bc
      | Abstract bc -> aborrow_content_to_string ~span:(Some span) ctx bc
    in
    "- bid: "
    ^ unique_borrow_id_to_string l
    ^ "\n- content: " ^ bc ^ "\n- context:\n"
    ^ eval_ctx_to_string ~span:(Some span) ctx];
  (* This is used for sanity checks *)
  let sanity_ek =
    { enter_shared_loans = true; enter_mut_borrows = true; enter_abs = true }
  in
  match bc with
  | Concrete (VMutBorrow (l', tv)) ->
      (* Sanity check *)
      [%sanity_check] span (UMut l' = l);
      [%sanity_check] span (not (concrete_loans_in_value tv));
      (* Check that the corresponding loan is somewhere - purely a sanity check *)
      [%sanity_check] span
        (Option.is_some (ctx_lookup_loan_opt span sanity_ek l' ctx));
      (* Update the context *)
      give_back_value span l' tv ctx
  | Concrete (VSharedBorrow (bid, l') | VReservedMutBorrow (bid, l')) ->
      (* Sanity check *)
      [%sanity_check] span (UShared l' = l);
      (* Check that the borrow is somewhere - purely a sanity check *)
      [%sanity_check] span
        (Option.is_some (ctx_lookup_loan_opt span sanity_ek bid ctx));
      (* We have nothing to update in the context *)
      ctx
  | Abstract _ ->
      (* We shouldn't get here: ending borrows inside abstractions is taken care
       of separately *)
      [%internal_error] span

let check_borrow_disappeared (span : Meta.span) (fun_name : string)
    (l : unique_borrow_id) (ctx0 : eval_ctx) (ctx : eval_ctx) : unit =
  (match lookup_borrow_opt span ek_all l ctx with
  | None -> () (* Ok *)
  | Some _ ->
      log#ltrace
        (lazy
          (fun_name ^ ": "
          ^ unique_borrow_id_to_string l
          ^ ": borrow didn't disappear:\n- original context:\n"
          ^ eval_ctx_to_string ~span:(Some span) ctx0
          ^ "\n\n- new context:\n"
          ^ eval_ctx_to_string ~span:(Some span) ctx));
      [%internal_error] span);
  match l with
  | UShared _ -> ()
  | UMut l -> (
      match ctx_lookup_loan_opt span ek_all l ctx with
      | None -> () (* Ok *)
      | Some _ ->
          log#ltrace
            (lazy
              (fun_name ^ ": " ^ BorrowId.to_string l
             ^ ": loan didn't disappear:\n- original context:\n"
              ^ eval_ctx_to_string ~span:(Some span) ctx0
              ^ "\n\n- new context:\n"
              ^ eval_ctx_to_string ~span:(Some span) ctx));
          [%internal_error] span)

(** End a borrow identified by its borrow id in a context.

    This function **preserves invariants** provided [allowed_abs] is [None]: if
    the borrow is inside another borrow/an abstraction, we end the outer
    borrow/abstraction first, etc.

    [chain]: contains the list of borrows/abstraction ids on which
    {!end_borrow_aux} and {!end_abstraction_aux} were called, to remember the
    chain of calls. This is useful for debugging purposes, and also for sanity
    checks to detect cycles (which shouldn't happen if the environment is
    well-formed).

    Rk.: from now onwards, the functions are written in continuation passing
    style. The reason is that when ending borrows we may end abstractions, which
    requires generating code for the translation (and we do this in CPS).

    TODO: we should split this function in two: one function which doesn't
    perform anything smart and is trusted, and another function for the
    book-keeping. *)
let rec end_borrow_aux (config : config) (span : Meta.span) ~(snapshots : bool)
    (chain : borrow_loan_abs_ids) (l : unique_borrow_id) : cm_fun =
 fun ctx ->
  (* Check that we don't loop *)
  let chain0 = chain in
  let chain =
    add_borrow_loan_abs_id_to_chain span "end_borrow_aux: " (BorrowId l) chain
  in
  [%ltrace
    unique_borrow_id_to_string l
    ^ ":\n- original context:\n"
    ^ eval_ctx_to_string ~span:(Some span) ctx];

  (* Utility function for the sanity checks: check that the borrow disappeared
   * from the context *)
  let ctx0 = ctx in
  let check = check_borrow_disappeared span "end borrow" l ctx0 in
  (* Start by ending the borrow itself (we lookup it up and replace it with [Bottom] *)
  match end_concrete_borrow_get_borrow span l ctx with
  (* Two cases:
     - error: we found outer borrows (the borrow is inside a borrowed value),
       inner loans (the borrow contains loans), or the borrow is inside a
       region abstraction
     - success: either we could not find the borrow or it was successfully
       replaced with [Bottom], and we can proceed to ending the corresponding loan.
  *)
  | Error priority -> (
      (* Debug *)
      [%ltrace
        unique_borrow_id_to_string l
        ^ ": found outer borrows/abs or inner loans:"
        ^ show_priority_borrow_or_abs priority];
      (* End the priority borrows, abstractions, then try again to end the target
       * borrow (if necessary) *)
      match priority with
      | OuterMutBorrow bid | OuterSharedLoan bid | InnerLoan bid ->
          (* End the outer borrows *)
          let ctx, cc = end_loan_aux config span ~snapshots chain bid ctx in
          (* Retry to end the borrow *)
          let ctx, cc =
            comp cc (end_borrow_aux config span ~snapshots chain0 l ctx)
          in
          (* Check and continue *)
          check ctx;
          (ctx, cc)
      | OuterAbs abs_id ->
          (* The borrow is inside an abstraction: end the whole abstraction *)
          let ctx, end_abs =
            end_abstraction_aux config span ~snapshots chain abs_id ctx
          in
          (* Sanity check *)
          check ctx;
          (ctx, end_abs))
  | Ok (ctx, None) ->
      [%ltrace "borrow not found"];
      (* It is possible that we can't find a borrow in symbolic mode (ending
       * an abstraction may end several borrows at once *)
      [%sanity_check] span (config.mode = SymbolicMode);
      (* Do a sanity check and continue *)
      check ctx;
      (ctx, fun e -> e)
  (* We found a borrow and replaced it with [Bottom]: give it back (i.e., update
     the corresponding loan) *)
  | Ok (ctx, Some (_, bc)) ->
      (* Sanity check: the borrowed value shouldn't contain loans *)
      (match bc with
      | Concrete (VMutBorrow (_, bv)) ->
          [%sanity_check] span (Option.is_none (get_first_loan_in_value bv))
      | _ -> ());
      (* Give back the value *)
      let ctx = give_back_concrete span l bc ctx in
      (* Do a sanity check and continue *)
      check ctx;
      (* Save a snapshot of the environment for the name generation *)
      let cc =
        if snapshots then SynthesizeSymbolic.save_snapshot ctx else fun e -> e
      in
      (* Compose *)
      (ctx, cc)

and end_borrows_aux (config : config) (span : Meta.span) ~(snapshots : bool)
    (chain : borrow_loan_abs_ids) (lset : UniqueBorrowIdSet.t) : cm_fun =
 fun ctx ->
  (* This is not necessary, but we prefer to reorder the borrow ids,
     so that we actually end from the smallest id to the highest id - just
     a matter of taste, and may make debugging easier *)
  let ids = UniqueBorrowIdSet.fold (fun id ids -> id :: ids) lset [] in
  fold_left_apply_continuation
    (fun id ctx -> end_borrow_aux config span ~snapshots chain id ctx)
    ids ctx

and try_end_loan_aux (config : config) (span : Meta.span) ~(snapshots : bool)
    (chain : borrow_loan_abs_ids) ~(must_end : bool) (l : loan_id) : cm_fun =
 fun ctx ->
  (* Check that we don't loop *)
  let chain =
    add_borrow_loan_abs_id_to_chain span "end_borrow_aux: " (LoanId l) chain
  in
  (* Lookup the loan to identify whether this is a shared loan or a mutable loan *)
  match ctx_lookup_loan_opt span ek_all l ctx with
  | None ->
      [%sanity_check] span (not must_end);
      (ctx, fun id -> id)
  | Some loan -> (
      match snd loan with
      | Concrete (VSharedLoan _) | Abstract (ASharedLoan _) ->
          end_shared_loan_aux config span ~snapshots chain l ctx
      | Concrete (VMutLoan _) | Abstract (AMutLoan _) ->
          end_borrow_aux config span ~snapshots chain (UMut l) ctx
      | _ -> [%craise] span "Unreachable")

and end_loan_aux (config : config) (span : Meta.span) ~(snapshots : bool)
    (chain : borrow_loan_abs_ids) (l : loan_id) : cm_fun =
  try_end_loan_aux config span ~snapshots chain ~must_end:true l

and try_end_loans_aux (config : config) (span : Meta.span) ~(snapshots : bool)
    (chain : borrow_loan_abs_ids) ~(must_end : bool) (lset : BorrowId.Set.t) :
    cm_fun =
 fun ctx ->
  (* This is not necessary, but we prefer to reorder the borrow ids,
     so that we actually end from the smallest id to the highest id - just
     a matter of taste, and may make debugging easier *)
  let ids = BorrowId.Set.fold (fun id ids -> id :: ids) lset [] in
  fold_left_apply_continuation
    (fun id ctx ->
      try_end_loan_aux config span ~snapshots chain ~must_end id ctx)
    ids ctx

and end_loans_aux (config : config) (span : Meta.span) ~(snapshots : bool)
    (chain : borrow_loan_abs_ids) (lset : BorrowId.Set.t) : cm_fun =
  try_end_loans_aux config span ~snapshots chain ~must_end:true lset

and end_shared_loan_aux (config : config) (span : Meta.span) ~(snapshots : bool)
    (chain : borrow_loan_abs_ids) (l : loan_id) : cm_fun =
 fun ctx ->
  (* Repeateadly lookup and end the borrows corresponding to this loan *)
  let visitor =
    object
      inherit [_] iter_eval_ctx

      method! visit_VSharedBorrow _ bid sid =
        if bid = l then raise (FoundSharedBorrowId (bid, sid)) else ()

      method! visit_ASharedBorrow _ pm bid sid =
        [%sanity_check] span (pm = PNone);
        if bid = l then raise (FoundSharedBorrowId (bid, sid)) else ()
    end
  in
  let rec run : cm_fun =
   fun ctx ->
    try
      visitor#visit_eval_ctx () ctx;
      (ctx, fun x -> x)
    with FoundSharedBorrowId (_, sid) ->
      let ctx, cc =
        end_borrow_aux config span ~snapshots chain (UShared sid) ctx
      in
      comp cc (run ctx)
  in
  let ctx, cc = run ctx in

  (* There are no remaining borrows: end the loan itself *)
  (* We use a reference to check that we updated exactly one loan *)
  let replaced : bool ref = ref false in
  let set_replaced () =
    [%cassert] span (not !replaced) "Exactly one loan should be updated";
    replaced := true
  in
  let obj =
    (* Note that abstraction expressions do not track shared loans/borrows,
       so we only need to look at "regular" abstraction values *)
    object
      inherit [_] map_eval_ctx as super

      method! visit_VLoan env lc =
        match lc with
        | VSharedLoan (l', shared_value) ->
            if l = l' then (
              (* This is the loan we are looking for *)
              set_replaced ();
              (* Remove the loan by replacing it with the shared value *)
              shared_value.value)
            else
              (* Not the loan we are looking for: continue exploring *)
              VLoan (super#visit_VSharedLoan env l' shared_value)
        | VMutLoan bid' ->
            (* We are ending a *shared* loan: nothing special to do *)
            VLoan (super#visit_VMutLoan env bid')

      method! visit_ALoan opt_abs lc =
        match lc with
        | AMutLoan (pm, bid, av) ->
            [%sanity_check] span (pm = PNone);
            (* Nothing special to do (we are ending a *shared* loan) *)
            ALoan (super#visit_AMutLoan opt_abs pm bid av)
        | ASharedLoan (pm, l', shared_value, child) ->
            [%sanity_check] span (pm = PNone);
            if l = l' then (
              (* This is the loan we are looking for *)
              set_replaced ();
              ALoan (AEndedSharedLoan (shared_value, child)))
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
  [%cassert] span !replaced "No loan updated";
  (* Return *)
  (ctx, cc)

and end_abstraction_aux (config : config) (span : Meta.span) ~(snapshots : bool)
    (chain : borrow_loan_abs_ids) (abs_id : AbsId.id) : cm_fun =
 fun ctx ->
  (* Check that we don't loop *)
  let chain =
    add_borrow_loan_abs_id_to_chain span "end_abstraction_aux: " (AbsId abs_id)
      chain
  in
  (* Remember the original context for printing purposes *)
  let ctx0 = ctx in
  [%ltrace
    AbsId.to_string abs_id ^ "\n- original context:\n"
    ^ eval_ctx_to_string ~span:(Some span) ctx0];

  (* Lookup the abstraction - note that if we end a list of abstractions [A1, A0],
     ending the first abstraction A1 may require the last abstraction A0 to
     end first, so when reaching the end of the list, A0 might not be in the
     context anymore, meaning we have to simply ignore it. *)
  match ctx_lookup_abs_opt ctx abs_id with
  | None ->
      [%ltrace
        "abs not found (already ended): " ^ AbsId.to_string abs_id ^ "\n"];
      (ctx, fun e -> e)
  | Some abs ->
      (* Check that we can end the abstraction *)
      if abs.can_end then ()
      else
        [%craise] span
          ("Can't end abstraction " ^ AbsId.to_string abs.abs_id
         ^ " as it is set as non-endable");

      (* End the parent abstractions first *)
      let ctx, cc =
        end_abstractions_aux config span ~snapshots chain abs.parents ctx
      in
      [%ltrace
        AbsId.to_string abs_id
        ^ "\n- context after parent abstractions ended:\n"
        ^ eval_ctx_to_string ~span:(Some span) ctx];

      (* End the loans inside the abstraction *)
      let ctx, cc =
        comp cc (end_abstraction_loans config span ~snapshots chain abs_id ctx)
      in
      [%ltrace
        AbsId.to_string abs_id ^ "\n- context after loans ended:\n"
        ^ eval_ctx_to_string ~span:(Some span) ctx];

      (* End the abstraction itself by redistributing the borrows it contains *)
      let ctx, cc =
        comp cc
          (end_abstraction_borrows config span ~snapshots chain abs_id ctx)
      in

      (* End the regions owned by the abstraction - note that we don't need to
         relookup the abstraction: the set of regions in an abstraction never
         changes... *)
      let ctx =
        let ended_regions =
          RegionId.Set.union ctx.ended_regions abs.regions.owned
        in
        { ctx with ended_regions }
      in

      (* Remove all the references to the id of the current abstraction, and remove
         the abstraction itself.
         **Rk.**: this is where we synthesize the updated symbolic AST *)
      let ctx, cc =
        comp cc (end_abstraction_remove_from_context config span abs_id ctx)
      in

      (* Debugging *)
      [%ltrace
        AbsId.to_string abs_id ^ "\n- original context:\n"
        ^ eval_ctx_to_string ~span:(Some span) ctx0
        ^ "\n\n- new context:\n"
        ^ eval_ctx_to_string ~span:(Some span) ctx];

      (* Sanity check: ending an abstraction must preserve the invariants *)
      Invariants.check_invariants span ctx;

      (* Save a snapshot of the environment for the name generation *)
      let cc =
        if snapshots then cc_comp cc (SynthesizeSymbolic.save_snapshot ctx)
        else cc
      in

      (* Return *)
      (ctx, cc)

and end_abstractions_aux (config : config) (span : Meta.span)
    ~(snapshots : bool) (chain : borrow_loan_abs_ids) (abs_ids : AbsId.Set.t) :
    cm_fun =
 fun ctx ->
  (* This is not necessary, but we prefer to reorder the abstraction ids,
   * so that we actually end from the smallest id to the highest id - just
   * a matter of taste, and may make debugging easier *)
  let abs_ids = AbsId.Set.fold (fun id ids -> id :: ids) abs_ids [] in
  fold_left_apply_continuation
    (fun id ctx -> end_abstraction_aux config span ~snapshots chain id ctx)
    abs_ids ctx

and end_abstraction_loans (config : config) (span : Meta.span)
    ~(snapshots : bool) (chain : borrow_loan_abs_ids) (abs_id : AbsId.id) :
    cm_fun =
 fun ctx ->
  [%ltrace
    "- abs_id: " ^ AbsId.to_string abs_id ^ "\n- ctx:\n"
    ^ eval_ctx_to_string ctx];
  (* Lookup the abstraction *)
  let abs = ctx_lookup_abs ctx abs_id in
  (* End the first loan we find.
   *
   * We ignore the "ignored mut/shared loans": as we should have already ended
   * the parent abstractions, they necessarily come from children. *)
  let opt_loan = get_first_non_ignored_aloan_in_abstraction span abs in
  match opt_loan with
  | None ->
      (* No loans: nothing to update *)
      (ctx, fun e -> e)
  | Some (BorrowId bid) ->
      (* There are loans: end them, then recheck *)
      let ctx, cc = end_loan_aux config span ~snapshots chain bid ctx in
      (* Reexplore, looking for loans *)
      comp cc (end_abstraction_loans config span ~snapshots chain abs_id ctx)
  | Some (SymbolicValue proj) ->
      (* There is a proj_loans over a symbolic value: end the proj_borrows
         which intersect this proj_loans, then end the proj_loans itself *)
      let ctx, cc =
        end_proj_loans_symbolic config span ~snapshots chain abs_id
          abs.regions.owned proj ctx
      in
      (* Reexplore, looking for loans *)
      comp cc (end_abstraction_loans config span ~snapshots chain abs_id ctx)

and end_abstraction_borrows (config : config) (span : Meta.span)
    ~(snapshots : bool) (chain : borrow_loan_abs_ids) (abs_id : AbsId.id) :
    cm_fun =
 fun ctx ->
  [%ltrace "abs_id: " ^ AbsId.to_string abs_id];
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
     the exploration didn't trigger an exception, it means there are no
     inner borrows to end: we can thus trigger an exception for the current
     borrow.

     TODO: we should implement a function in InterpBorrowsCore to do
     exactly that.
  *)
  let visitor =
    object
      inherit [_] iter_abs as super

      method! visit_aborrow_content env bc =
        (* In-depth exploration *)
        super#visit_aborrow_content env bc;
        (* No exception was raised: we can raise an exception for the
         * current borrow *)
        match bc with
        | AMutBorrow _ | ASharedBorrow _ ->
            (* Raise an exception *)
            raise (FoundABorrowContent bc)
        | AProjSharedBorrow asb ->
            (* Raise an exception only if the asb contains borrows *)
            if
              List.exists
                (fun x ->
                  match x with
                  | AsbBorrow _ -> true
                  | _ -> false)
                asb
            then raise (FoundABorrowContent bc)
            else ()
        | AEndedMutBorrow _
        | AIgnoredMutBorrow _
        | AEndedIgnoredMutBorrow _
        | AEndedSharedBorrow ->
            (* Nothing to do for ignored borrows *)
            ()

      method! visit_aproj env sproj =
        (match sproj with
        | AProjLoans _ -> [%craise] span "Unexpected"
        | AProjBorrows aproj -> raise (FoundAProjBorrows aproj)
        | AEndedProjLoans _ | AEndedProjBorrows _ | AEmpty -> ());
        super#visit_aproj env sproj

      (** We may need to end borrows in "regular" values, because of shared
          values *)
      method! visit_borrow_content _ bc =
        match bc with
        | VSharedBorrow _ | VMutBorrow (_, _) -> raise (FoundBorrowContent bc)
        | VReservedMutBorrow _ -> [%craise] span "Unreachable"
    end
  in
  (* Lookup the abstraction *)
  let abs = ctx_lookup_abs ctx abs_id in
  try
    (* Explore the abstraction, looking for borrows *)
    visitor#visit_abs () abs;
    (* No borrows: nothing to update *)
    (* Last sanity check: the region abstraction doesn't contain borrows in its *expression* *)
    [%sanity_check] span (not (abs_has_non_ended_eborrows abs));
    (ctx, fun e -> e)
  with
  (* There are concrete (i.e., not symbolic) borrows: end them, then re-explore *)
  | FoundABorrowContent bc ->
      [%ltrace
        "found aborrow content: "
        ^ aborrow_content_to_string ~span:(Some span) ctx bc];
      let ctx =
        match bc with
        | AMutBorrow (pm, bid, av) ->
            [%sanity_check] span (pm = PNone);
            (* First, convert the avalue to a (fresh symbolic) value *)
            let sv = convert_avalue_to_given_back_value span ctx av in
            (* Replace the mut borrow to register the fact that we ended
               it and store with it the freshly generated given back value *)
            let meta : aended_mut_borrow_meta = { bid; given_back = sv } in
            let ended_borrow = ABorrow (AEndedMutBorrow (meta, av)) in
            let ended_eborrow =
              match lookup_eborrow_opt span ek_all bid ctx with
              | None -> None
              | Some (EMutBorrow (pm, bid, av)) ->
                  [%sanity_check] span (pm = PNone);
                  let meta : eended_mut_borrow_meta =
                    { bid; given_back = sv }
                  in
                  Some (EBorrow (EEndedMutBorrow (meta, av)))
              | Some _ -> [%internal_error] span
            in
            let ctx =
              update_aborrow span ek_all (UMut bid) ended_borrow ended_eborrow
                ctx
            in
            (* Give the value back *)
            let sv = mk_tvalue_from_symbolic_value sv in
            give_back_value span bid sv ctx
        | ASharedBorrow (pm, _, sid) ->
            [%sanity_check] span (pm = PNone);
            (* Replace the shared borrow to account for the fact it ended *)
            let ended_borrow = ABorrow AEndedSharedBorrow in
            update_aborrow span ek_all (UShared sid) ended_borrow None ctx
        | AProjSharedBorrow asb ->
            (* Retrieve the borrow ids *)
            let bids =
              List.filter_map
                (fun asb ->
                  match asb with
                  | AsbBorrow (_, sid) -> Some sid
                  | AsbProjReborrows _ -> None)
                asb
            in
            (* There should be at least one borrow identifier in the set, which we
               can use to identify the whole set *)
            let repr_bid = List.hd bids in
            (* Replace the shared borrow with Bottom *)
            let ctx =
              update_aborrow span ek_all (UShared repr_bid)
                (ABorrow AEndedSharedBorrow) None ctx
            in
            (* Continue *)
            ctx
        | AEndedMutBorrow _
        | AIgnoredMutBorrow _
        | AEndedIgnoredMutBorrow _
        | AEndedSharedBorrow -> [%craise] span "Unexpected"
      in
      (* Reexplore *)
      end_abstraction_borrows config span ~snapshots chain abs_id ctx
  (* There are symbolic borrows: end them, then re-explore *)
  | FoundAProjBorrows aproj ->
      [%ltrace
        "found aproj borrows: " ^ aproj_to_string ctx (AProjBorrows aproj)];
      (* Generate a fresh symbolic value *)
      let nsv = mk_fresh_symbolic_value span ctx aproj.proj.proj_ty in
      (* Replace the proj_borrows - there should be exactly one *)
      let ctx = end_aproj_borrows span abs.regions.owned aproj.proj nsv ctx in
      (* Give back the symbolic value *)
      let ctx =
        give_back_symbolic_value config span abs.regions.owned aproj.proj nsv
          ctx
      in
      (* Reexplore *)
      end_abstraction_borrows config span ~snapshots chain abs_id ctx
  (* There are concrete (i.e., not symbolic) borrows in shared values: end them, then reexplore *)
  | FoundBorrowContent bc ->
      [%ltrace
        "found borrow content: "
        ^ borrow_content_to_string ~span:(Some span) ctx bc];
      let ctx =
        match bc with
        | VSharedBorrow (_, sid) -> (
            (* Replace the shared borrow with bottom *)
            match
              end_concrete_borrow_in_abs_get_borrow span abs_id (UShared sid)
                ctx
            with
            | Error _ -> [%craise] span "Unreachable"
            | Ok (ctx, _) -> ctx)
        | VMutBorrow (bid, v) -> (
            (* Replace the mut borrow with bottom *)
            match
              end_concrete_borrow_in_abs_get_borrow span abs_id (UMut bid) ctx
            with
            | Error _ -> [%craise] span "Unreachable"
            | Ok (ctx, _) ->
                (* Give the value back - note that the mut borrow was below a
                 * shared borrow: the value is thus unchanged *)
                give_back_value span bid v ctx)
        | VReservedMutBorrow _ -> [%craise] span "Unreachable"
      in
      (* Reexplore *)
      end_abstraction_borrows config span ~snapshots chain abs_id ctx

(** Remove an abstraction from the context, as well as all its references *)
and end_abstraction_remove_from_context (_config : config) (span : Meta.span)
    (abs_id : AbsId.id) : cm_fun =
 fun ctx ->
  let ctx, abs = ctx_remove_abs span ctx abs_id in
  let abs = Option.get abs in
  (* Synthesize the symbolic AST *)
  (ctx, SynthesizeSymbolic.synthesize_end_abstraction ctx abs)

(** End a proj_loan over a symbolic value by ending the proj_borrows which
    intersect this proj_loan.

    Remark: if this symbolic value is primitively copiable, then:
    - either proj_borrows are only present in the concrete context
    - or there is only one intersecting proj_borrow present in an abstraction
    - otherwise, this symbolic value is not primitively copiable:
    - there may be proj_borrows_shared over this value
    - if we put aside the proj_borrows_shared, there should be exactly one
      intersecting proj_borrows, either in the concrete context or in an
      abstraction

    Note that we may get recursively get here after a sequence of updates which
    look like this:
    - attempt ending a loan projector
    - end a borrow projector before, and by doing this actually end the loan
      projector
    - retry ending the loan projector

    We thus have to be careful about the fact that maybe the loan projector
    actually doesn't exist anymore when we get here. *)
and end_proj_loans_symbolic (config : config) (span : Meta.span)
    ~(snapshots : bool) (chain : borrow_loan_abs_ids) (abs_id : AbsId.id)
    (regions : RegionId.Set.t) (proj : symbolic_proj) : cm_fun =
 fun ctx ->
  [%ltrace
    "- abs_id: " ^ AbsId.to_string abs_id ^ "\n- regions: "
    ^ RegionId.Set.to_string None regions
    ^ "\n- sv: "
    ^ symbolic_value_id_to_pretty_string proj.sv_id
    ^ "\n- projection type: "
    ^ ty_to_string ctx proj.proj_ty
    ^ "\n- ctx:\n" ^ eval_ctx_to_string ctx];
  (* Small helpers for sanity checks *)
  let check ctx = no_aproj_over_symbolic_in_context span proj.sv_id ctx in
  (* Find the first proj_borrows which intersects the proj_loans *)
  let explore_shared = true in
  match
    lookup_intersecting_aproj_borrows_opt span explore_shared regions proj ctx
  with
  | None ->
      (* We couldn't find any in the context: it means that the symbolic value
         is in the concrete environment (or that we dropped it, in which case
         it is completely absent). We thus simply need to replace the loans
         projector with an ended projector.
      *)
      let ctx = update_aproj_loans_to_ended span abs_id proj.sv_id ctx in
      (* Sanity check *)
      check ctx;
      (* Continue *)
      (ctx, fun e -> e)
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
      let ctx, cc =
        let abs_ids = List.map fst external_projs in
        let abs_ids =
          List.fold_left
            (fun s id -> AbsId.Set.add id s)
            AbsId.Set.empty abs_ids
        in
        (* End the abstractions and continue *)
        end_abstractions_aux config span ~snapshots chain abs_ids ctx
      in
      (* End the internal borrows projectors and the loans projector *)
      let ctx =
        (* All the proj_borrows are owned: simply erase them *)
        let ctx =
          remove_intersecting_aproj_borrows_shared span ~include_owned:true
            ~include_outlive:false regions proj ctx
        in
        (* End the loan itself *)
        update_aproj_loans_to_ended span abs_id proj.sv_id ctx
      in
      (* Sanity check *)
      check ctx;
      (ctx, cc)
  | Some (NonSharedProj (abs_id', _proj_ty)) ->
      (* We found one projector of borrows in an abstraction: if it comes
         from this abstraction, we can end it directly, otherwise we need
         to end the abstraction where it came from first *)
      if abs_id' = abs_id then
        (* TODO: what is below is wrong *)
        raise (Failure "Unimplemented")
        (* (* Note that it happens when a function returns a [&mut ...] which gets
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
           let ctx = update_aproj_borrows span abs_id sv AEmpty ctx in
           (* Sanity check: no other occurrence of an intersecting projector of borrows *)
           [%sanity_check] span
             (Option.is_none
                (lookup_intersecting_aproj_borrows_opt span explore_shared regions
                   sv proj_ty ctx))
             ;
           (* End the projector of loans *)
           let ctx = update_aproj_loans_to_ended span abs_id sv ctx in
           (* Sanity check *)
           check ctx;
           (* Continue *)
                 (ctx, fun e -> e) *)
      else
        (* The borrows proj comes from a different abstraction: end it. *)
        let ctx, cc =
          end_abstraction_aux config span ~snapshots chain abs_id' ctx
        in
        (* Retry ending the projector of loans *)
        let ctx, cc =
          comp cc
            (end_proj_loans_symbolic config span ~snapshots chain abs_id regions
               proj ctx)
        in
        (* Sanity check *)
        check ctx;
        (* Return *)
        (ctx, cc)

let end_borrow config (span : Meta.span) ?(snapshots : bool = true) :
    unique_borrow_id -> cm_fun =
  end_borrow_aux config ~snapshots span []

let end_borrows config (span : Meta.span) ?(snapshots : bool = true) :
    unique_borrow_id_set -> cm_fun =
  end_borrows_aux config ~snapshots span []

let end_loan config (span : Meta.span) ?(snapshots : bool = true) :
    loan_id -> cm_fun =
  end_loan_aux config ~snapshots span []

let end_loans config (span : Meta.span) ?(snapshots : bool = true) :
    loan_id_set -> cm_fun =
  end_loans_aux config ~snapshots span []

let try_end_loans config (span : Meta.span) ?(snapshots : bool = true) :
    loan_id_set -> cm_fun =
  try_end_loans_aux config ~snapshots span [] ~must_end:false

let end_abstraction config span ?(snapshots = true) =
  end_abstraction_aux config ~snapshots span []

let end_abstractions config span ?(snapshots = true) =
  end_abstractions_aux config ~snapshots span []

let end_borrow_no_synth config span ?(snapshots = true) id ctx =
  fst (end_borrow config span ~snapshots id ctx)

let end_borrows_no_synth config span ?(snapshots = true) ids ctx =
  fst (end_borrows config span ~snapshots ids ctx)

let end_loan_no_synth config span ?(snapshots = true) id ctx =
  fst (end_loan config span ~snapshots id ctx)

let end_loans_no_synth config span ?(snapshots = true) ids ctx =
  fst (end_loans config span ~snapshots ids ctx)

let try_end_loans_no_synth config span ?(snapshots = true) ids ctx =
  fst (try_end_loans config span ~snapshots ids ctx)

let end_abstraction_no_synth config span ?(snapshots = true) id ctx =
  fst (end_abstraction config ~snapshots span id ctx)

let end_abstractions_no_synth config span ?(snapshots = true) ids ctx =
  fst (end_abstractions config ~snapshots span ids ctx)

(** Helper function: see {!activate_reserved_mut_borrow}.

    This function updates the shared loan to a mutable loan (we then update the
    borrow with another helper). Of course, the shared loan must contain exactly
    one borrow id (the one we give as parameter), otherwise we can't promote it.
    Also, the shared value mustn't contain any loan.

    The returned value (previously shared) is checked:
    - it mustn't contain loans
    - it mustn't contain {!Bottom}
    - it mustn't contain reserved borrows TODO: this kind of checks should be
      put in an auxiliary helper, because they are redundant.

    The loan to update mustn't be a borrowed value. *)
let promote_shared_loan_to_mut_loan (span : Meta.span) (l : BorrowId.id)
    (bid : SharedBorrowId.id) (ctx : eval_ctx) : tvalue * eval_ctx =
  (* Debug *)
  [%ltrace
    "- loan: " ^ BorrowId.to_string l ^ "\n- context:\n"
    ^ eval_ctx_to_string ~span:(Some span) ctx];
  (* Sanity check: there is exactly one borrow mapping to [bid] in the context,
     and it is the one we want to promote.
   *)
  let borrows = lookup_shared_reserved_borrows l ctx in
  [%sanity_check] span (borrows = [ bid ]);
  (* Lookup the shared loan - note that we can't promote a shared loan
     in a shared value, but we can do it in a mutably borrowed value.
     This is important because we can do: [let y = &two-phase ( *x );]
   *)
  let ek =
    { enter_shared_loans = false; enter_mut_borrows = true; enter_abs = false }
  in
  match ctx_lookup_loan span ek l ctx with
  | _, Concrete (VMutLoan _) ->
      [%craise] span "Expected a shared loan, found a mut loan"
  | _, Concrete (VSharedLoan (_, sv)) ->
      (* We need to check that there aren't any loans in the value:
         we should have gotten rid of those already, but it is better
         to do a sanity check. *)
      [%sanity_check] span (not (concrete_loans_in_value sv));
      (* Check there isn't {!Bottom} (this is actually an invariant *)
      [%cassert] span
        (not (bottom_in_value ctx.ended_regions sv))
        "There shouldn't be a bottom";
      (* Check there aren't reserved borrows *)
      [%cassert] span
        (not (reserved_in_value sv))
        "There shouldn't be reserved borrows";
      (* Update the loan content *)
      let ctx = update_loan span ek l (VMutLoan l) ctx in
      (* Return *)
      (sv, ctx)
  | _, Abstract _ ->
      (* I don't think it is possible to have two-phase borrows involving borrows
         returned by abstractions. I'm not sure how we could handle that anyway. *)
      [%craise] span
        "Can't promote a shared loan to a mutable loan if the loan is inside a \
         region abstraction"

(** Helper function: see {!activate_reserved_mut_borrow}.

    This function updates a shared borrow to a mutable borrow (and that is all:
    it doesn't touch the corresponding loan). *)
let replace_reserved_borrow_with_mut_borrow (span : Meta.span) (l : BorrowId.id)
    (bid : SharedBorrowId.id) (borrowed_value : tvalue) (ctx : eval_ctx) :
    eval_ctx =
  (* Lookup the reserved borrow - note that we don't go inside borrows/loans:
     there can't be reserved borrows inside other borrows/loans
  *)
  let ek =
    { enter_shared_loans = false; enter_mut_borrows = false; enter_abs = false }
  in
  match lookup_borrow span ek (UShared bid) ctx with
  | Concrete (VSharedBorrow _ | VMutBorrow (_, _)) ->
      [%craise] span "Expected a reserved mutable borrow"
  | Concrete (VReservedMutBorrow _) ->
      (* Update it *)
      update_borrow span ek (UShared bid) (VMutBorrow (l, borrowed_value)) ctx
  | Abstract _ ->
      (* This can't happen for sure *)
      [%craise] span
        "Can't promote a shared borrow to a mutable borrow if the borrow is \
         inside a region abstraction"

(** Promote a reserved mut borrow to a mut borrow. *)
let rec promote_reserved_mut_borrow (config : config) (span : Meta.span)
    (l : BorrowId.id) (rid : SharedBorrowId.id) : cm_fun =
 fun ctx ->
  (* Lookup the value *)
  let ek =
    { enter_shared_loans = false; enter_mut_borrows = true; enter_abs = false }
  in
  match ctx_lookup_loan span ek l ctx with
  | _, Concrete (VMutLoan _) -> [%craise] span "Unreachable"
  | _, Concrete (VSharedLoan (_, sv)) -> (
      (* If there are loans inside the value, end them. Note that there can't be
         reserved borrows inside the value.
         If we perform an update, do a recursive call to lookup the updated value *)
      match get_first_loan_in_value sv with
      | Some lc ->
          (* End the loans *)
          let ctx, cc =
            match lc with
            | VSharedLoan (bid', _) | VMutLoan bid' ->
                end_loan config span bid' ctx
          in
          (* Recursive call *)
          comp cc (promote_reserved_mut_borrow config span l rid ctx)
      | None ->
          (* No loan to end inside the value *)
          (* Some sanity checks *)
          [%ltrace
            "resulting value:\n" ^ tvalue_to_string ~span:(Some span) ctx sv];
          [%sanity_check] span (not (concrete_loans_in_value sv));
          [%sanity_check] span (not (bottom_in_value ctx.ended_regions sv));
          [%sanity_check] span (not (reserved_in_value sv));
          (* End the borrows which borrow from the value, at the exception of
             the borrow we want to promote *)
          let bids =
            List.filter
              (fun bid' -> bid' <> rid)
              (lookup_shared_reserved_borrows l ctx)
          in
          let bids = List.map (fun bid -> UShared bid) bids in
          let ctx, cc =
            end_borrows config span (UniqueBorrowIdSet.of_list bids) ctx
          in
          (* Promote the loan - TODO: this will fail if the value contains
           * any loans. In practice, it shouldn't, but we could also
           * look for loans inside the value and end them before promoting
           * the borrow. *)
          let v, ctx = promote_shared_loan_to_mut_loan span l rid ctx in
          (* Promote the borrow - the value should have been checked by
             {!promote_shared_loan_to_mut_loan}
          *)
          let ctx = replace_reserved_borrow_with_mut_borrow span l rid v ctx in
          (* Return *)
          (ctx, cc))
  | _, Abstract _ ->
      (* I don't think it is possible to have two-phase borrows involving borrows
       * returned by abstractions. I'm not sure how we could handle that anyway. *)
      [%craise] span
        "Can't activate a reserved mutable borrow referencing a loan inside\n\
        \         a region abstraction"

let destructure_abs (span : Meta.span) (abs_kind : abs_kind) ~(can_end : bool)
    ~(destructure_shared_values : bool) (ctx : eval_ctx) (abs0 : abs) : abs =
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
  let push_fail _ = [%craise] span "Unreachable" in
  (* Function to explore an avalue and destructure it *)
  let rec list_avalues (allow_borrows : bool) (push : tavalue -> unit)
      (av : tavalue) : unit =
    let ty = av.ty in
    match av.value with
    | AIgnored _ -> ()
    | AAdt adt ->
        (* Simply explore the children *)
        List.iter (list_avalues allow_borrows push) adt.fields
    | ALoan lc -> (
        (* Explore the loan content *)
        match lc with
        | ASharedLoan (pm, bids, sv, child_av) ->
            (* We don't support nested borrows for now *)
            [%cassert] span
              (not (value_has_borrows (Some span) ctx sv.value))
              "Nested borrows are not supported yet";
            (* Destructure the shared value *)
            let avl, sv =
              if destructure_shared_values then list_values sv else ([], sv)
            in
            (* Push a value *)
            let ignored = mk_aignored span child_av.ty None in
            let value = ALoan (ASharedLoan (pm, bids, sv, ignored)) in
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
        | AMutLoan (pm, bid, child_av) ->
            (* Explore the child *)
            list_avalues false push_fail child_av;
            (* Explore the whole loan *)
            let ignored = mk_aignored span child_av.ty None in
            let value = ALoan (AMutLoan (pm, bid, ignored)) in
            push { value; ty }
        | AIgnoredMutLoan (opt_bid, child_av) ->
            (* We don't support nested borrows for now *)
            [%cassert] span
              (not
                 (ty_has_borrows (Some span) ctx.type_ctx.type_infos child_av.ty))
              "Nested borrows are not supported yet";
            [%sanity_check] span (opt_bid = None);
            (* Simply explore the child *)
            list_avalues false push_fail child_av
        | AEndedSharedLoan (sv, child_av) ->
            (* We don't support nested borrows for now *)
            [%cassert] span
              (not
                 (ty_has_borrows (Some span) ctx.type_ctx.type_infos child_av.ty))
              "Nested borrows are not supported yet";
            (* Explore the shared value *)
            (* Destructure the shared value *)
            let avl, _ =
              if destructure_shared_values then list_values sv else ([], sv)
            in
            (* Explore the child *)
            list_avalues false push_fail child_av;
            (* Push the avalues introduced because we decomposed the inner loans
               in the shared value - see the ASharedLoan case *)
            List.iter push avl
        | AEndedMutLoan
            { child = child_av; given_back = _; given_back_meta = _ }
        | AEndedIgnoredMutLoan
            { child = child_av; given_back = _; given_back_meta = _ }
        | AIgnoredSharedLoan child_av ->
            (* We don't support nested borrows for now *)
            [%cassert] span
              (not
                 (ty_has_borrows (Some span) ctx.type_ctx.type_infos child_av.ty))
              "Nested borrows are not supported yet";
            (* Simply explore the child *)
            list_avalues false push_fail child_av)
    | ABorrow bc -> (
        (* Sanity check - rem.: may be redundant with [push_fail] *)
        [%sanity_check] span allow_borrows;
        (* Explore the borrow content *)
        match bc with
        | AMutBorrow (pm, bid, child_av) ->
            (* Explore the child *)
            list_avalues false push_fail child_av;
            (* Explore the borrow *)
            let ignored = mk_aignored span child_av.ty None in
            let value = ABorrow (AMutBorrow (pm, bid, ignored)) in
            push { value; ty }
        | ASharedBorrow _ ->
            (* Nothing specific to do: keep the value as it is *)
            push av
        | AIgnoredMutBorrow (opt_bid, child_av) ->
            (* We don't support nested borrows for now *)
            [%cassert] span
              (not
                 (ty_has_borrows (Some span) ctx.type_ctx.type_infos child_av.ty))
              "Nested borrows are not supported yet";
            [%sanity_check] span (opt_bid = None);
            (* Just explore the child *)
            list_avalues false push_fail child_av
        | AEndedIgnoredMutBorrow
            { child = child_av; given_back = _; given_back_meta = _ } ->
            (* We don't support nested borrows for now *)
            [%cassert] span
              (not
                 (ty_has_borrows (Some span) ctx.type_ctx.type_infos child_av.ty))
              "Nested borrows are not supported yet";
            (* Just explore the child *)
            list_avalues false push_fail child_av
        | AProjSharedBorrow asb ->
            (* We don't support nested borrows *)
            [%cassert] span (asb = []) "Nested borrows are not supported yet";
            (* Nothing specific to do *)
            ()
        | AEndedMutBorrow _ | AEndedSharedBorrow ->
            (* If we get there it means the abstraction ended: it should not
               be in the context anymore (if we end *one* borrow in an abstraction,
               we have to end them all and remove the abstraction from the context)
            *)
            [%craise] span "Unreachable")
    | ASymbolic (_, aproj) -> (
        (* *)
        match aproj with
        | AProjLoans { proj = _; consumed; borrows } ->
            (* There can be children in the presence of nested borrows: we
               don't handle those for now. *)
            [%sanity_check] span (consumed = []);
            [%sanity_check] span (borrows = []);
            push av
        | AProjBorrows { proj = _; loans } ->
            (* For now, we fore all symbolic values containing borrows to be eagerly
               expanded *)
            (* There can be children in the presence of nested borrows: we
               don't handle those for now. *)
            [%sanity_check] span (loans = []);
            push av
        | AEndedProjLoans { proj = _; consumed; borrows } ->
            (* There can be children in the presence of nested borrows: we
               don't handle those for now. *)
            [%sanity_check] span (consumed = []);
            [%sanity_check] span (borrows = []);
            (* Just ignore *)
            ()
        | AEndedProjBorrows { mvalues = _; loans } ->
            (* There can be children in the presence of nested borrows: we
               don't handle those for now. *)
            [%sanity_check] span (loans = []);
            (* Just ignore *)
            ()
        | AEmpty -> ())
  and list_values (v : tvalue) : tavalue list * tvalue =
    let ty = v.ty in
    match v.value with
    | VLiteral _ -> ([], v)
    | VAdt adt ->
        let avll, fields = List.split (List.map list_values adt.fields) in
        let avl = List.concat avll in
        let adt = { adt with fields } in
        (avl, { v with value = VAdt adt })
    | VBottom -> [%craise] span "Unreachable"
    | VBorrow _ ->
        (* We don't support nested borrows for now *)
        [%craise] span "Unreachable"
    | VLoan lc -> (
        match lc with
        | VSharedLoan (bids, sv) ->
            let avl, sv = list_values sv in
            if destructure_shared_values then (
              (* Rem.: the shared value can't contain loans nor borrows *)
              [%cassert] span (ty_no_regions ty)
                "Nested borrows are not supported yet";
              let av : tavalue =
                [%sanity_check] span
                  (not (value_has_loans_or_borrows (Some span) ctx sv.value));
                (* We introduce fresh ids for the symbolic values *)
                let mk_value_with_fresh_sids (v : tvalue) : tvalue =
                  let visitor =
                    object
                      inherit [_] map_tavalue

                      method! visit_symbolic_value_id _ _ =
                        ctx.fresh_symbolic_value_id ()
                    end
                  in
                  visitor#visit_tvalue () v
                in
                let sv = mk_value_with_fresh_sids sv in
                (* Create the new avalue *)
                let value =
                  ALoan
                    (ASharedLoan (PNone, bids, sv, mk_aignored span ty None))
                in
                (* We need to update the type of the value: abstract shared loans
                   have the type `& ...` - TODO: this is annoying and not very clean... *)
                let ty =
                  (* Take the first region of the abstraction - this doesn't really matter *)
                  let r = RegionId.Set.min_elt abs0.regions.owned in
                  TRef (RVar (Free r), ty, RShared)
                in
                { value; ty }
              in
              let avl = List.append [ av ] avl in
              (avl, sv))
            else (avl, { v with value = VLoan (VSharedLoan (bids, sv)) })
        | VMutLoan _ -> [%craise] span "Unreachable")
    | VSymbolic _ ->
        (* For now, we fore all symbolic values containing borrows to be eagerly
           expanded *)
        [%sanity_check] span
          (not (ty_has_borrows (Some span) ctx.type_ctx.type_infos ty));
        ([], v)
  in

  (* Destructure the avalues *)
  List.iter (list_avalues true push_avalue) abs0.avalues;
  let avalues = !avalues in
  (* Update *)
  { abs0 with avalues; kind = abs_kind; can_end }

let abs_is_destructured (span : Meta.span) (destructure_shared_values : bool)
    (ctx : eval_ctx) (abs : abs) : bool =
  let abs' =
    destructure_abs span abs.kind ~can_end:abs.can_end
      ~destructure_shared_values ctx abs
  in
  [%ldebug
    "- abs:\n" ^ abs_to_string span ctx abs ^ "\n- abs':\n"
    ^ abs_to_string span ctx abs'];
  (* TODO: the check is too precise, we need something more general (for instance,
     [destructure_abs] tends to remove the optional meta values in [AIgnored],
     making the check below fail if we directly compare the abstractions).
     For now, we do a few ad-hoc modifications.
  *)
  let visitor =
    object
      inherit [_] map_abs
      method! visit_AIgnored _ _ = AIgnored None
    end
  in
  let abs = visitor#visit_abs () abs in
  abs = abs'

exception FoundBorrowId of unique_borrow_id
exception FoundAbsId of AbsId.id

(** Find the first endable loan projector in an abstraction.

    An endable loan projector is a loan projector over a symbolic value which
    doesn't appear anywhere else in the context.

    This function may raise a [FoundAbsProj] exception. *)
let find_first_endable_loan_proj_in_abs (span : Meta.span) (ctx : eval_ctx)
    (abs : abs) : unit =
  let visitor =
    object
      inherit [_] iter_abs as super

      method! visit_aproj env proj =
        match proj with
        | AProjLoans proj ->
            (* Check if there are borrow projectors in the context
               or symbolic values with the same id *)
            let explore_shared = false in
            (* Look for the symbolic values first *)
            let visitor =
              object
                inherit [_] iter_eval_ctx

                method! visit_VSymbolic _ sv' =
                  if sv'.sv_id = proj.proj.sv_id then raise Found else ()
              end
            in
            begin
              try
                visitor#visit_eval_ctx () ctx;
                (* If we got there it means the symbolic value doesn't appear
                   in a concrete value in the context: check if there are
                   borrow projectors *)
                match
                  lookup_intersecting_aproj_borrows_opt span explore_shared
                    abs.regions.owned proj.proj ctx
                with
                | None ->
                    (* No intersecting projections: we can end this loan projector *)
                    raise (FoundAbsProj (abs.abs_id, proj.proj.sv_id))
                | Some _ ->
                    (* There are intersecting projections: we can't end this loan projector *)
                    super#visit_aproj env (AProjLoans proj)
              with Found -> ()
            end
        | AProjBorrows _ | AEndedProjLoans _ | AEndedProjBorrows _ | AEmpty ->
            super#visit_aproj env proj
    end
  in
  (* Visit *)
  visitor#visit_abs () abs

(** Small helper

    Iterate over all the *concrete* mutable borrows in the abstraction and find
    their corresponding loans: return [true] if one of those loans is inside an
    abstraction identified by the set [fixed_abs_ids]. *)
let abs_mut_borrows_loans_in_fixed span (ctx : eval_ctx)
    (fixed_abs_ids : AbsId.Set.t) (abs : abs) : bool =
  (* Iterate through the loan projectors which intersect a given borrow projector *)
  let visit_proj_loans (proj : symbolic_proj) =
    object
      inherit [_] iter_eval_ctx as super

      method! visit_abs env abs =
        [%sanity_check] span (env = None);
        super#visit_abs (Some abs) abs

      method! visit_AProjLoans env proj' =
        if
          proj.sv_id = proj'.proj.sv_id
          && projections_intersect span abs.regions.owned proj.proj_ty
               (Option.get env).regions.owned proj'.proj.proj_ty
        then raise Found
        else super#visit_AProjLoans env proj'
    end
  in

  let visit_borrows =
    object
      inherit [_] iter_eval_ctx as super

      method! visit_borrow_content _ _ =
        (* We can get there through shared loans: let's just ignore it for now
           (this function should be used to explore abstractions which don't
           have remaining loans - see its use below) *)
        [%internal_error] span

      method! visit_aborrow_content env lc =
        super#visit_aborrow_content env lc;
        match lc with
        | AMutBorrow (_, bid, _) ->
            (* Lookup the loan *)
            let abs_or_var, _ = ctx_lookup_loan span ek_all bid ctx in
            begin
              match abs_or_var with
              | AbsId abs_id ->
                  if AbsId.Set.mem abs_id fixed_abs_ids then raise Found else ()
              | LocalId _ | DummyVarId _ -> ()
            end;
            super#visit_aborrow_content env lc
        | ASharedBorrow _
        | AIgnoredMutBorrow _
        | AEndedMutBorrow _
        | AEndedSharedBorrow
        | AEndedIgnoredMutBorrow _ -> ()
        | AProjSharedBorrow _ ->
            (* Unimplemented for now *)
            [%internal_error] span

      method! visit_aproj env proj =
        super#visit_aproj env proj;
        match proj with
        | AProjBorrows proj ->
            (visit_proj_loans proj.proj)#visit_eval_ctx None ctx
        | AProjLoans _ | AEndedProjLoans _ | AEndedProjBorrows _ | AEmpty -> ()
    end
  in
  try
    visit_borrows#visit_abs () abs;
    false
  with Found -> true

let eliminate_ended_shared_loans (span : Meta.span) (ctx : eval_ctx) : eval_ctx
    =
  (* Filter the avalues *)
  let update_abs (abs : abs) : abs =
    let keep (v : tavalue) : bool =
      match v.value with
      | ALoan (AEndedSharedLoan (sv, child))
        when (not (value_has_loans_or_borrows (Some span) ctx sv.value))
             && is_aignored child.value -> false
      | _ -> true
    in
    let avalues = List.filter keep abs.avalues in
    { abs with avalues }
  in
  let ctx = ctx_map_abs update_abs ctx in

  (* *)
  ctx

(* Repeat until we can't simplify the context anymore:
   - end the borrows which appear in anonymous values and don't contain loans
   - end the region abstractions which can be ended (no loans)
   - replace the values in anonymous values with bottom whenever possible
     (the value is not inside a borrow/loan and doesn't itself contain borrows/loans)
   - end the shared loans which don't have corresponding borrows
   - end the loan projectors inside region abstractions when the corresponding
     symbolic value doesn't appear anywhere else in the context
   However we ignore the "fixed" abstractions.
*)
let rec simplify_dummy_values_useless_abs_aux (config : config)
    ~(snapshots : bool) (span : Meta.span) : cm_fun =
 fun ctx ->
  let simplify_abs = true in
  let simplify_borrows = true in
  (* Small utilities: we do not modify the region abstractions marked as frozen
     (i.e., which should not be ended) - it is usually important that those remain
     the same, for instance when computing fixed points. *)
  let frozen_abs =
    let abs = env_get_abs ctx.env in
    AbsId.Set.of_list
      (List.filter_map
         (fun (abs : abs) -> if abs.can_end then None else Some abs.abs_id)
         (AbsId.Map.values abs))
  in
  let loan_id_not_in_fixed_abs (lid : BorrowId.id) : bool =
    match fst (ctx_lookup_loan span ek_all lid ctx) with
    | AbsId abs_id -> not (AbsId.Set.mem abs_id frozen_abs)
    | _ -> true
  in
  let rec explore_env (ctx : eval_ctx) (env : env) : env =
    match env with
    | [] -> [] (* Done *)
    | EBinding (BDummy vid, v) :: env ->
        [%ldebug
          "Dummy value " ^ DummyVarId.to_string vid ^ ":\n"
          ^ tvalue_to_string ctx v];
        (* If the symbolic value doesn't contain concrete borrows or loans
           we simply ignore it *)
        if not (concrete_borrows_loans_in_value v.value) then (
          [%ldebug "Eliminating the value"];
          explore_env ctx env)
        else (
          [%ldebug "Diving into the value"];
          (* Explore the anonymous value - raises an exception if it finds
             a borrow to end *)
          let visitor =
            object (self)
              inherit [_] map_tvalue as super

              method! visit_VLoan end_borrows lc =
                (* Check if we can end the loan, but don't dive inside *)
                match lc with
                | VSharedLoan (l, value) -> begin
                    [%ldebug
                      "Found shared loan:\n" ^ loan_content_to_string ctx lc];
                    match lookup_shared_reserved_borrows l ctx with
                    | [] ->
                        (* End the loan *)
                        self#visit_value end_borrows value.value
                    | _ -> super#visit_VLoan false lc
                  end
                | _ -> super#visit_VLoan false lc

              method! visit_VBorrow end_borrows bc =
                (* Simplify if the option is on *)
                if end_borrows && simplify_borrows then
                  (* Check if we can end the borrow, do not enter inside if we can't *)
                  match bc with
                  | VSharedBorrow (_, sid) | VReservedMutBorrow (_, sid) ->
                      (* We could directly end the borrow actually
                         (replace it with bottom). But it's also good to
                         raise an exception and call [end_borrow], as it
                         allows to make the implementation more consistent. *)
                      raise (FoundBorrowId (UShared sid))
                  | VMutBorrow (bid, v) ->
                      if
                        (not (concrete_loans_in_value v))
                        && loan_id_not_in_fixed_abs bid
                      then raise (FoundBorrowId (UMut bid))
                      else
                        (* There might be shared loans to end inside the borrow *)
                        let v = self#visit_tvalue false v in
                        VBorrow (VMutBorrow (bid, v))
                else VBorrow bc

              (* If no concrete borrows/loans and we can end borrows (we are not
                 inside a shared loan): replace with bottom *)
              method! visit_value end_borrows v =
                if end_borrows && not (concrete_borrows_loans_in_value v) then
                  VBottom
                else super#visit_value end_borrows v
            end
          in
          let v = visitor#visit_tvalue true v in
          (* No exception was raised: continue *)
          let env = explore_env ctx env in
          (* Check if we eliminated all remaining loans and borrows (we might
             have removed shared loans): we ignore the value if it is the case *)
          if not (concrete_borrows_loans_in_value v.value) then env
          else EBinding (BDummy vid, v) :: env)
    | EBinding (BVar vid, v) :: env ->
        [%ldebug
          "Value (name: "
          ^ Print.option_to_string (fun x -> x) vid.name
          ^ ",id: "
          ^ Expressions.LocalId.to_string vid.index
          ^ "):\n" ^ tvalue_to_string ctx v];
        (* End the shared loans which don't have corresponding borrows.
           We explore the value and raise an exception if it finds a borrow to end *)
        let visitor =
          object (self)
            inherit [_] map_tvalue as super

            method! visit_VLoan end_borrows lc =
              (* Check if we can end the loan, but don't dive inside *)
              match lc with
              | VSharedLoan (l, value) -> begin
                  [%ldebug
                    "Found shared loan:\n" ^ loan_content_to_string ctx lc];
                  match lookup_shared_reserved_borrows l ctx with
                  | [] ->
                      (* End the loan *)
                      self#visit_value end_borrows value.value
                  | _ -> super#visit_VLoan false lc
                end
              | _ -> super#visit_VLoan false lc
          end
        in
        let v = visitor#visit_tvalue true v in
        (* No exception was raised: continue *)
        EBinding (BVar vid, v) :: explore_env ctx env
    | EAbs abs :: env
      when simplify_abs && abs.can_end
           && not (AbsId.Set.mem abs.abs_id frozen_abs) -> (
        [%ldebug "Diving into abs:\n" ^ abs_to_string span ctx abs];
        (* End the shared loans with no corresponding borrows *)
        let visitor =
          object
            inherit [_] map_abs as super

            method! visit_VLoan () lc =
              (* Check if we can end the loan, but don't dive inside *)
              match lc with
              | VSharedLoan (l, value) -> begin
                  match lookup_shared_reserved_borrows l ctx with
                  | [] ->
                      (* End the loan *)
                      super#visit_value () value.value
                  | _ -> super#visit_VLoan () lc
                end
              | _ -> super#visit_VLoan () lc

            method! visit_ASharedLoan () pm l sv child =
              [%sanity_check] span (pm = PNone);
              match lookup_shared_reserved_borrows l ctx with
              | [] ->
                  (* End the loan *)
                  super#visit_AEndedSharedLoan () sv child
              | _ -> super#visit_ASharedLoan () pm l sv child
          end
        in
        let abs = visitor#visit_abs () abs in
        (* Check if it is possible to end the abstraction: if yes, raise an exception *)
        let opt_loan = get_first_non_ignored_aloan_in_abstraction span abs in
        match opt_loan with
        | None ->
            (* No remaining loans: we can end the abstraction.

               However, we need to make sure that ending this abstraction will not
               modify the *fixed* abstractions: we thus explore all the borrows and
               check that there corresponding loans are not inside fixed abstractions
               (because otherwise ending the borrow would end the loan).

               TODO: this limitation is annoying. We need to generalize the join.
            *)
            if not (abs_mut_borrows_loans_in_fixed span ctx frozen_abs abs) then
              raise (FoundAbsId abs.abs_id)
            else EAbs abs :: explore_env ctx env
        | Some _ ->
            (* There are remaining loans: we can't end the abstraction *)
            (* Check if we can end some loan projectors (because there doesn't
               remain corresponding borrow projectors in the context) *)
            find_first_endable_loan_proj_in_abs span ctx abs;
            (* Continue *)
            EAbs abs :: explore_env ctx env)
    | b :: env -> b :: explore_env ctx env
  in
  let rec_call = simplify_dummy_values_useless_abs_aux config span ~snapshots in
  try
    (* Explore the environment.

       Note that we don't need to call [end_loan] whenever we need to end a shared
       loan: we can directly update the value.
    *)
    ({ ctx with env = explore_env ctx ctx.env }, fun e -> e)
  with
  | FoundAbsId abs_id ->
      let ctx, cc = end_abstraction config span ~snapshots abs_id ctx in
      comp cc (rec_call ctx)
  | FoundBorrowId bid ->
      let ctx, cc = end_borrow config span ~snapshots bid ctx in
      comp cc (rec_call ctx)
  | FoundAbsProj (abs_id, sv) ->
      (* We can end this loan projector (there are no corresponding borrows
         projectors in the context): set it as ended and continue *)
      let ctx = update_aproj_loans_to_ended span abs_id sv ctx in
      rec_call ctx

let simplify_dummy_values_useless_abs (config : config)
    ?(snapshots : bool = true) (span : Meta.span) : cm_fun =
 fun ctx0 ->
  [%ldebug eval_ctx_to_string ctx0];
  (* Simplify the context as long as it leads to changes - TODO: make this more efficient *)
  let rec simplify ctx0 =
    let ctx, cc =
      simplify_dummy_values_useless_abs_aux config span ~snapshots ctx0
    in
    Invariants.check_invariants span ctx;
    if ctx.env = ctx0.env then (
      [%ldebug "Done:\n" ^ eval_ctx_to_string ctx];
      (ctx, cc))
    else (
      [%ldebug "Not finished:\n" ^ eval_ctx_to_string ctx];
      comp cc (simplify ctx))
  in
  let ctx, cc = simplify ctx0 in
  let ctx = eliminate_ended_shared_loans span ctx in
  [%ltrace
    "- ctx0:\n" ^ eval_ctx_to_string ctx0 ^ "\n- ctx1:\n"
    ^ if ctx.env = ctx0.env then "UNCHANGED" else eval_ctx_to_string ctx];
  (ctx, cc)
