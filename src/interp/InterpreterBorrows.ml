open Types
open Values
open Contexts
open Cps
open ValuesUtils
open TypesUtils
open InterpreterUtils
open InterpreterBorrowsCore
open InterpreterProjectors
open Errors

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
      We use this to end shared borrows and mutable borrows inside of **shared values**;
      the other borrows are taken care of differently.
*)
let end_borrow_get_borrow (span : Meta.span)
    (allowed_abs : AbstractionId.id option) (l : BorrowId.id) (ctx : eval_ctx) :
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
    sanity_check __FILE__ __LINE__ (Option.is_none !replaced_bc) span;
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
    match borrowed_value with
    | None -> ()
    | Some v -> (
        match get_first_loan_in_value v with
        | None -> ()
        | Some c -> (
            match c with
            | VSharedLoan (bids, _) ->
                raise (FoundPriority (InnerLoans (Borrows bids)))
            | VMutLoan bid -> raise (FoundPriority (InnerLoans (Borrow bid)))))
  in

  (* The environment in the visitor is used to keep track of the outer loans *)
  let visitor =
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
        | AMutLoan (pm, _, _) ->
            sanity_check __FILE__ __LINE__ (pm = PNone) span;
            (* Nothing special to do *)
            super#visit_ALoan outer lc
        | ASharedLoan (pm, bids, v, av) ->
            sanity_check __FILE__ __LINE__ (pm = PNone) span;
            (* Explore the shared value - we need to update the outer borrows *)
            let souter = update_outer_borrows outer (Borrows bids) in
            let v = super#visit_typed_value souter v in
            (* Explore the child avalue - we keep the same outer borrows *)
            let av = super#visit_typed_avalue outer av in
            (* Reconstruct *)
            ALoan (ASharedLoan (pm, bids, v, av))
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
            sanity_check __FILE__ __LINE__ (pm = PNone) span;
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
              craise __FILE__ __LINE__ span "Unimplemented"
              (* ABottom *))
            else
              (* Update the outer borrows before diving into the child avalue *)
              let outer = update_outer_borrows outer (Borrow bid) in
              super#visit_ABorrow outer bc
        | ASharedBorrow (pm, bid) ->
            sanity_check __FILE__ __LINE__ (pm = PNone) span;
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
              let asb = remove_borrow_from_asb span l asb in
              ABorrow (AProjSharedBorrow asb))
            else (* Nothing special to do *)
              super#visit_ABorrow outer bc

      method! visit_abs outer abs =
        (* Update the outer abs *)
        let outer_abs, outer_borrows = outer in
        sanity_check __FILE__ __LINE__ (Option.is_none outer_abs) span;
        sanity_check __FILE__ __LINE__ (Option.is_none outer_borrows) span;
        let outer = (Some abs.abs_id, None) in
        super#visit_abs outer abs
    end
  in
  (* Catch the exceptions - raised if there are outer borrows *)
  try
    let ctx = visitor#visit_eval_ctx (None, None) ctx in
    Ok (ctx, !replaced_bc)
  with FoundPriority outers -> Error outers

(** Auxiliary function to end borrows. See {!give_back}.
    
    When we end a mutable borrow, we need to "give back" the value it contained
    to its original owner by reinserting it at the proper position.

    Note that this function checks that there is exactly one loan to which we
    give the value back.
    TODO: this was not the case before, so some sanity checks are not useful anymore.
 *)
let give_back_value (config : config) (span : Meta.span) (bid : BorrowId.id)
    (nv : typed_value) (ctx : eval_ctx) : eval_ctx =
  (* Sanity check *)
  exec_assert __FILE__ __LINE__
    (not (loans_in_value nv))
    span "Can not end a borrow because the value to give back contains bottom";
  exec_assert __FILE__ __LINE__
    (not (bottom_in_value ctx.ended_regions nv))
    span "Can not end a borrow because the value to give back contains bottom";
  (* Debug *)
  log#ldebug
    (lazy
      ("give_back_value:\n- bid: " ^ BorrowId.to_string bid ^ "\n- value: "
      ^ typed_value_to_string ~span:(Some span) ctx nv
      ^ "\n- context:\n"
      ^ eval_ctx_to_string ~span:(Some span) ctx
      ^ "\n"));
  (* We use a reference to check that we updated exactly one loan *)
  let replaced : bool ref = ref false in
  let set_replaced () =
    sanity_check __FILE__ __LINE__ (not !replaced) span;
    replaced := true
  in
  (* Whenever giving back symbolic values, they shouldn't contain already ended regions *)
  let check_symbolic_no_ended = true in
  (* We sometimes need to reborrow values while giving a value back due: prepare that *)
  let allow_reborrows = true in
  let fresh_reborrow, apply_registered_reborrows =
    prepare_reborrows config span allow_reborrows
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
               borrow): nothing special to do *)
            VLoan (super#visit_VSharedLoan opt_abs bids v)
        | VMutLoan bid' ->
            (* Check if this is the loan we are looking for *)
            if bid' = bid then (
              (* Sanity check *)
              let expected_ty = ty in
              if nv.ty <> expected_ty then
                craise __FILE__ __LINE__ span
                  ("Value given back doesn't have the proper type:\n\
                    - expected: " ^ ty_to_string ctx ty ^ "\n- received: "
                 ^ ty_to_string ctx nv.ty);
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
        | ABorrow bc ->
            let value = self#visit_typed_ABorrow opt_abs av.ty bc in
            ({ av with value } : typed_avalue)
        | _ -> super#visit_typed_avalue opt_abs av

      (** We need to inspect ignored mutable borrows, to insert loan projectors
          if necessary.
       *)
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
                  let child = super#visit_typed_avalue opt_abs child in
                  (* Return *)
                  ABorrow
                    (AEndedIgnoredMutBorrow
                       { given_back; child; given_back_meta })
              | _ -> craise __FILE__ __LINE__ span "Unreachable"
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
          | None -> craise __FILE__ __LINE__ span "Unreachable"
          | Some abs -> (abs.regions.owned, abs.regions.ancestors)
        in
        (* Rk.: there is a small issue with the types of the aloan values.
         * See the comment at the level of definition of {!typed_avalue} *)
        let borrowed_value_aty =
          let _, ty, _ = ty_get_ref ty in
          ty
        in
        match lc with
        | AMutLoan (pm, bid', child) ->
            sanity_check __FILE__ __LINE__ (pm = PNone) span;
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
                apply_proj_borrows span check_symbolic_no_ended ctx
                  fresh_reborrow regions ancestors_regions nv borrowed_value_aty
              in
              (* Continue giving back in the child value *)
              let child = super#visit_typed_avalue opt_abs child in
              (* Return the new value *)
              ALoan (AEndedMutLoan { child; given_back; given_back_meta }))
            else (* Continue exploring *)
              super#visit_ALoan opt_abs lc
        | ASharedLoan (pm, _, _, _) ->
            sanity_check __FILE__ __LINE__ (pm = PNone) span;
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
                apply_proj_borrows span check_symbolic_no_ended ctx
                  fresh_reborrow regions ancestors_regions nv borrowed_value_aty
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
        sanity_check __FILE__ __LINE__ (Option.is_none opt_abs) span;
        super#visit_EAbs (Some abs) abs
    end
  in

  (* Explore the environment *)
  let ctx = obj#visit_eval_ctx None ctx in
  (* Check we gave back to exactly one loan *)
  cassert __FILE__ __LINE__ !replaced span "No loan updated";
  (* Apply the reborrows *)
  apply_registered_reborrows ctx

(** Update the borrow projectors upon ending some regions in a symbolic value.

    Because doing this introduces a fresh symbolic value which may contain
    borrows, we may need to update the proj_borrows to introduce loan projectors
    over those borrows.
 *)
let end_aproj_borrows (span : Meta.span) (ended_regions : RegionId.Set.t)
    (proj_ty : rty) (sv : symbolic_value) (nsv : symbolic_value)
    (ctx : eval_ctx) : eval_ctx =
  (* Sanity checks *)
  sanity_check __FILE__ __LINE__
    (sv.sv_id <> nsv.sv_id && ty_is_rty proj_ty)
    span;
  log#ldebug
    (lazy
      ("end_aproj_borrows:" ^ "\n- ended regions: "
      ^ RegionId.Set.to_string None ended_regions
      ^ "\n- projection type: " ^ ty_to_string ctx proj_ty ^ "\n- sv: "
      ^ symbolic_value_to_string ctx sv
      ^ "\n- nsv: "
      ^ symbolic_value_to_string ctx nsv
      ^ "\n- ctx: " ^ eval_ctx_to_string ctx));
  (* Substitution functions, to replace the borrow projectors over symbolic values *)
  (* We need to handle two cases:
     - If the regions ended in the symbolic value intersect with the owned
       regions of the abstraction (not the ancestor ones): we can simply end the
       borrow projector, there is nothing left to track anymore.

       Ex.: we are ending abs1 below:
       {[
         abs0 {'a} { AProjLoans (s0 : &'a mut T) [] }
         abs1 {'b} { AProjBorrows (s0 : &'a mut T <: &'b mut T) }
       ]}
     - if the regions ended in the symbolic value intersect with the ancestors
       regions of the abstraction, we have to introduce a projection
       (because it means we ended ancestor "outer" borrows, and so we need
       to project the given back inner loans into the abstraction).

       Ex.: we are ending abs2 below, and considering abs1: we have to project
       the inner loans inside of abs3. However we do not project anything
       into abs2 (see the case above).
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
  let update_ancestors (_abs : abs) (abs_sv : symbolic_value)
      (abs_proj_ty : rty) (local_given_back : (msymbolic_value * aproj) list) :
      aproj =
    (* Compute the projection over the given back value *)
    let child_proj = AProjLoans (nsv, abs_proj_ty, []) in
    AProjBorrows (abs_sv, abs_proj_ty, (sv, child_proj) :: local_given_back)
  in
  let ctx =
    update_intersecting_aproj_borrows span ~fail_if_unchanged:false
      ~include_ancestors:true ~include_owned:false ~update_shared:None
      ~update_mut:update_ancestors ended_regions sv proj_ty ctx
  in
  let update_owned (_abs : abs) (_abs_sv : symbolic_value) (_abs_proj_ty : rty)
      (local_given_back : (msymbolic_value * aproj) list) : aproj =
    (* There is nothing to project *)
    let mvalues = { consumed = sv; given_back = nsv } in
    AEndedProjBorrows (mvalues, local_given_back)
  in
  update_intersecting_aproj_borrows span ~fail_if_unchanged:true
    ~include_ancestors:false ~include_owned:true ~update_shared:None
    ~update_mut:update_owned ended_regions sv proj_ty ctx

(** Give back a *modified* symbolic value. *)
let give_back_symbolic_value (_config : config) (span : Meta.span)
    (ended_regions : RegionId.Set.t) (proj_ty : rty) (sv : symbolic_value)
    (nsv : symbolic_value) (ctx : eval_ctx) : eval_ctx =
  (* Sanity checks *)
  sanity_check __FILE__ __LINE__
    (sv.sv_id <> nsv.sv_id && ty_is_rty proj_ty)
    span;
  (* Substitution functions, to replace the borrow projectors over symbolic values *)
  (* We need to handle two cases:
     - If the regions ended in the symbolic value intersect with the owned
       regions of the abstraction (not the ancestor ones): we can simply end the
       loan, there is nothing left to track anymore.

       Ex.: we are ending abs1 below:
       {[
         abs0 {'a} { AProjLoans (s0 : &'a mut T) [] }
         abs1 {'b} { AProjBorrows (s0 : &'a mut T <: &'b mut T) }
       ]}
     - if the regions ended in the symbolic value intersect with the ancestors
       regions of the abstraction, we have to introduce a projection
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
  let subst_ancestors (_abs : abs) abs_sv abs_proj_ty local_given_back =
    (* Compute the projection over the given back value *)
    let child_proj = AProjBorrows (nsv, sv.sv_ty, []) in
    AProjLoans (abs_sv, abs_proj_ty, (sv, child_proj) :: local_given_back)
  in
  let ctx =
    update_intersecting_aproj_loans span ~fail_if_unchanged:false
      ~include_ancestors:true ~include_owned:false ended_regions proj_ty sv
      subst_ancestors ctx
  in
  let subst_owned (_abs : abs) abs_sv _abs_proj_ty local_given_back =
    (* There is nothing to project *)
    let child_proj = AEmpty in
    AEndedProjLoans (abs_sv, (nsv, child_proj) :: local_given_back)
  in
  update_intersecting_aproj_loans span ~fail_if_unchanged:true
    ~include_ancestors:false ~include_owned:true ended_regions proj_ty sv
    subst_owned ctx

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
let give_back_avalue_to_same_abstraction (_config : config) (span : Meta.span)
    (bid : BorrowId.id) (nv : typed_avalue) (nsv : typed_value) (ctx : eval_ctx)
    : eval_ctx =
  (* We use a reference to check that we updated exactly one loan *)
  let replaced : bool ref = ref false in
  let set_replaced () =
    cassert __FILE__ __LINE__ (not !replaced) span
      "Exacly one loan should be updated";
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
        | AMutLoan (pm, bid', child) ->
            sanity_check __FILE__ __LINE__ (pm = PNone) span;
            if bid' = bid then (
              (* Sanity check - about why we need to call {!ty_get_ref}
               * (and don't do the same thing as in {!give_back_value})
               * see the comment at the level of the definition of
               * {!typed_avalue} *)
              let _, expected_ty, _ = ty_get_ref ty in
              if nv.ty <> expected_ty then
                craise __FILE__ __LINE__ span
                  ("Value given back doesn't have the proper type:\n\
                    - expected: " ^ ty_to_string ctx ty ^ "\n- received: "
                 ^ ty_to_string ctx nv.ty);
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
        | ASharedLoan (PNone, _, _, _)
        (* We are giving back a value to a *mutable* loan: nothing special to do *)
        | AEndedMutLoan { given_back = _; child = _; given_back_meta = _ }
        | AEndedSharedLoan (_, _) ->
            (* Nothing special to do *)
            super#visit_ALoan opt_abs lc
        | ASharedLoan (_, _, _, _) ->
            (* We get there if the projection marker is not [PNone] *)
            internal_error __FILE__ __LINE__ span
        | AIgnoredMutLoan (bid_opt, child) ->
            (* This loan is ignored, but we may have to project on a subvalue
             * of the value which is given back *)
            if bid_opt = Some bid then (
              (* Note that we replace the ignored mut loan by an *ended* ignored
               * mut loan. Also, this is not the loan we are looking for *per se*:
               * we don't register the fact that we inserted the value somewhere
               * (i.e., we don't call {!set_replaced}) *)
              (* Sanity check *)
              sanity_check __FILE__ __LINE__ (nv.ty = ty) span;
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
  cassert __FILE__ __LINE__ !replaced span "No loan updated";
  (* Return *)
  ctx

(** Auxiliary function to end borrows. See  {!give_back}.
    
    When we end a shared borrow, we need to remove the borrow id from the list
    of borrows to the shared value.

    Note that this function checks that there is exactly one shared loan that
    we update.
    TODO: this was not the case before, so some sanity checks are not useful anymore.
 *)
let give_back_shared _config (span : Meta.span) (bid : BorrowId.id)
    (ctx : eval_ctx) : eval_ctx =
  (* We use a reference to check that we updated exactly one loan *)
  let replaced : bool ref = ref false in
  let set_replaced () =
    cassert __FILE__ __LINE__ (not !replaced) span
      "Exactly one loan should be updated";
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
        | AMutLoan (pm, bid, av) ->
            sanity_check __FILE__ __LINE__ (pm = PNone) span;
            (* Nothing special to do (we are giving back a *shared* borrow) *)
            ALoan (super#visit_AMutLoan opt_abs pm bid av)
        | ASharedLoan (pm, bids, shared_value, child) ->
            sanity_check __FILE__ __LINE__ (pm = PNone) span;
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
                     (pm, BorrowId.Set.remove bid bids, shared_value, child)))
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
  cassert __FILE__ __LINE__ !replaced span "No loan updated";
  (* Return *)
  ctx

(** When copying values, we duplicate the shared borrows. This is tantamount
    to reborrowing the shared value. The following function applies this change
    to an environment by inserting a new borrow id in the set of borrows tracked
    by a shared value, referenced by the [original_bid] argument.
 *)
let reborrow_shared (span : Meta.span) (original_bid : BorrowId.id)
    (new_bid : BorrowId.id) (ctx : eval_ctx) : eval_ctx =
  (* Keep track of changes *)
  let r = ref false in
  let set_ref () =
    sanity_check __FILE__ __LINE__ (not !r) span;
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

      method! visit_ASharedLoan env pm bids v av =
        sanity_check __FILE__ __LINE__ (pm = PNone) span;
        (* This case is similar to the {!SharedLoan} case *)
        if BorrowId.Set.mem original_bid bids then (
          set_ref ();
          let bids' = BorrowId.Set.add new_bid bids in
          ASharedLoan (pm, bids', v, av))
        else super#visit_ASharedLoan env pm bids v av
    end
  in

  let env = obj#visit_env () ctx.env in
  (* Check that we reborrowed once *)
  sanity_check __FILE__ __LINE__ !r span;
  { ctx with env }

(** Convert an {!type:avalue} to a {!type:value}.

    This function is used when ending abstractions: whenever we end a borrow
    in an abstraction, we convert the borrowed {!avalue} to a fresh symbolic
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
let convert_avalue_to_given_back_value (span : Meta.span) (av : typed_avalue) :
    symbolic_value =
  mk_fresh_symbolic_value span av.ty

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
let give_back (config : config) (span : Meta.span) (l : BorrowId.id)
    (bc : g_borrow_content) (ctx : eval_ctx) : eval_ctx =
  (* Debug *)
  log#ldebug
    (lazy
      (let bc =
         match bc with
         | Concrete bc -> borrow_content_to_string ~span:(Some span) ctx bc
         | Abstract bc -> aborrow_content_to_string ~span:(Some span) ctx bc
       in
       "give_back:\n- bid: " ^ BorrowId.to_string l ^ "\n- content: " ^ bc
       ^ "\n- context:\n"
       ^ eval_ctx_to_string ~span:(Some span) ctx
       ^ "\n"));
  (* This is used for sanity checks *)
  let sanity_ek =
    { enter_shared_loans = true; enter_mut_borrows = true; enter_abs = true }
  in
  match bc with
  | Concrete (VMutBorrow (l', tv)) ->
      (* Sanity check *)
      sanity_check __FILE__ __LINE__ (l' = l) span;
      sanity_check __FILE__ __LINE__ (not (loans_in_value tv)) span;
      (* Check that the corresponding loan is somewhere - purely a sanity check *)
      sanity_check __FILE__ __LINE__
        (Option.is_some (lookup_loan_opt span sanity_ek l ctx))
        span;
      (* Update the context *)
      give_back_value config span l tv ctx
  | Concrete (VSharedBorrow l' | VReservedMutBorrow l') ->
      (* Sanity check *)
      sanity_check __FILE__ __LINE__ (l' = l) span;
      (* Check that the borrow is somewhere - purely a sanity check *)
      sanity_check __FILE__ __LINE__
        (Option.is_some (lookup_loan_opt span sanity_ek l ctx))
        span;
      (* Update the context *)
      give_back_shared config span l ctx
  | Abstract (AMutBorrow (pm, l', av)) ->
      (* Sanity check *)
      sanity_check __FILE__ __LINE__ (pm = PNone) span;
      sanity_check __FILE__ __LINE__ (l' = l) span;
      (* Check that the corresponding loan is somewhere - purely a sanity check *)
      sanity_check __FILE__ __LINE__
        (Option.is_some (lookup_loan_opt span sanity_ek l ctx))
        span;
      (* Convert the avalue to a (fresh symbolic) value.

         Rem.: we shouldn't do this here. We should do this in a function
         which takes care of ending *sub*-abstractions.
      *)
      let sv = convert_avalue_to_given_back_value span av in
      (* Update the context *)
      give_back_avalue_to_same_abstraction config span l av
        (mk_typed_value_from_symbolic_value sv)
        ctx
  | Abstract (ASharedBorrow (pm, l')) ->
      (* Sanity check *)
      sanity_check __FILE__ __LINE__ (pm = PNone) span;
      sanity_check __FILE__ __LINE__ (l' = l) span;
      (* Check that the borrow is somewhere - purely a sanity check *)
      sanity_check __FILE__ __LINE__
        (Option.is_some (lookup_loan_opt span sanity_ek l ctx))
        span;
      (* Update the context *)
      give_back_shared config span l ctx
  | Abstract (AProjSharedBorrow asb) ->
      (* Sanity check *)
      sanity_check __FILE__ __LINE__ (borrow_in_asb l asb) span;
      (* Update the context *)
      give_back_shared config span l ctx
  | Abstract
      ( AEndedMutBorrow _
      | AIgnoredMutBorrow _
      | AEndedIgnoredMutBorrow _
      | AEndedSharedBorrow ) -> craise __FILE__ __LINE__ span "Unreachable"

let check_borrow_disappeared (span : Meta.span) (fun_name : string)
    (l : BorrowId.id) (ctx0 : eval_ctx) (ctx : eval_ctx) : unit =
  (match lookup_borrow_opt span ek_all l ctx with
  | None -> () (* Ok *)
  | Some _ ->
      log#ltrace
        (lazy
          (fun_name ^ ": " ^ BorrowId.to_string l
         ^ ": borrow didn't disappear:\n- original context:\n"
          ^ eval_ctx_to_string ~span:(Some span) ctx0
          ^ "\n\n- new context:\n"
          ^ eval_ctx_to_string ~span:(Some span) ctx));
      internal_error __FILE__ __LINE__ span);
  match lookup_loan_opt span ek_all l ctx with
  | None -> () (* Ok *)
  | Some _ ->
      log#ltrace
        (lazy
          (fun_name ^ ": " ^ BorrowId.to_string l
         ^ ": loan didn't disappear:\n- original context:\n"
          ^ eval_ctx_to_string ~span:(Some span) ctx0
          ^ "\n\n- new context:\n"
          ^ eval_ctx_to_string ~span:(Some span) ctx));
      internal_error __FILE__ __LINE__ span

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
let rec end_borrow_aux (config : config) (span : Meta.span)
    (chain : borrow_or_abs_ids) (allowed_abs : AbstractionId.id option)
    (l : BorrowId.id) : cm_fun =
 fun ctx ->
  (* Check that we don't loop *)
  let chain0 = chain in
  let chain =
    add_borrow_or_abs_id_to_chain span "end_borrow_aux: " (BorrowId l) chain
  in
  log#ldebug
    (lazy
      ("end borrow: " ^ BorrowId.to_string l ^ ":\n- original context:\n"
      ^ eval_ctx_to_string ~span:(Some span) ctx));

  (* Utility function for the sanity checks: check that the borrow disappeared
   * from the context *)
  let ctx0 = ctx in
  let check = check_borrow_disappeared span "end borrow" l ctx0 in
  (* Start by ending the borrow itself (we lookup it up and replace it with [Bottom] *)
  match end_borrow_get_borrow span allowed_abs l ctx with
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
          let ctx, cc =
            end_borrows_aux config span chain allowed_abs' bids ctx
          in
          (* Retry to end the borrow *)
          let ctx, cc =
            comp cc (end_borrow_aux config span chain0 allowed_abs l ctx)
          in
          (* Check and continue *)
          check ctx;
          (ctx, cc)
      | OuterBorrows (Borrow bid) | InnerLoans (Borrow bid) ->
          let allowed_abs' = None in
          (* End the outer borrow *)
          let ctx, cc = end_borrow_aux config span chain allowed_abs' bid ctx in
          (* Retry to end the borrow *)
          let ctx, cc =
            comp cc (end_borrow_aux config span chain0 allowed_abs l ctx)
          in
          (* Check and continue *)
          check ctx;
          (ctx, cc)
      | OuterAbs abs_id ->
          (* The borrow is inside an abstraction: end the whole abstraction *)
          let ctx, end_abs = end_abstraction_aux config span chain abs_id ctx in
          (* Sanity check *)
          check ctx;
          (ctx, end_abs))
  | Ok (ctx, None) ->
      log#ldebug (lazy "End borrow: borrow not found");
      (* It is possible that we can't find a borrow in symbolic mode (ending
       * an abstraction may end several borrows at once *)
      sanity_check __FILE__ __LINE__ (config.mode = SymbolicMode) span;
      (* Do a sanity check and continue *)
      check ctx;
      (ctx, fun e -> e)
  (* We found a borrow and replaced it with [Bottom]: give it back (i.e., update
     the corresponding loan) *)
  | Ok (ctx, Some (_, bc)) ->
      (* Sanity check: the borrowed value shouldn't contain loans *)
      (match bc with
      | Concrete (VMutBorrow (_, bv)) ->
          sanity_check __FILE__ __LINE__
            (Option.is_none (get_first_loan_in_value bv))
            span
      | _ -> ());
      (* Give back the value *)
      let ctx = give_back config span l bc ctx in
      (* Do a sanity check and continue *)
      check ctx;
      (* Save a snapshot of the environment for the name generation *)
      let cc = SynthesizeSymbolic.save_snapshot ctx in
      (* Compose *)
      (ctx, cc)

and end_borrows_aux (config : config) (span : Meta.span)
    (chain : borrow_or_abs_ids) (allowed_abs : AbstractionId.id option)
    (lset : BorrowId.Set.t) : cm_fun =
 fun ctx ->
  (* This is not necessary, but we prefer to reorder the borrow ids,
     so that we actually end from the smallest id to the highest id - just
     a matter of taste, and may make debugging easier *)
  let ids = BorrowId.Set.fold (fun id ids -> id :: ids) lset [] in
  fold_left_apply_continuation
    (fun id ctx -> end_borrow_aux config span chain allowed_abs id ctx)
    ids ctx

and end_abstraction_aux (config : config) (span : Meta.span)
    (chain : borrow_or_abs_ids) (abs_id : AbstractionId.id) : cm_fun =
 fun ctx ->
  (* Check that we don't loop *)
  let chain =
    add_borrow_or_abs_id_to_chain span "end_abstraction_aux: " (AbsId abs_id)
      chain
  in
  (* Remember the original context for printing purposes *)
  let ctx0 = ctx in
  log#ldebug
    (lazy
      ("end_abstraction_aux: "
      ^ AbstractionId.to_string abs_id
      ^ "\n- original context:\n"
      ^ eval_ctx_to_string ~span:(Some span) ctx0));

  (* Lookup the abstraction - note that if we end a list of abstractions [A1, A0],
     ending the first abstraction A1 may require the last abstraction A0 to
     end first, so when reaching the end of the list, A0 might not be in the
     context anymore, meaning we have to simply ignore it. *)
  match ctx_lookup_abs_opt ctx abs_id with
  | None ->
      log#ldebug
        (lazy
          ("abs not found (already ended): "
          ^ AbstractionId.to_string abs_id
          ^ "\n"));
      (ctx, fun e -> e)
  | Some abs ->
      (* Check that we can end the abstraction *)
      if abs.can_end then ()
      else
        craise __FILE__ __LINE__ span
          ("Can't end abstraction "
          ^ AbstractionId.to_string abs.abs_id
          ^ " as it is set as non-endable");

      (* End the parent abstractions first *)
      let ctx, cc = end_abstractions_aux config span chain abs.parents ctx in
      log#ldebug
        (lazy
          ("end_abstraction_aux: "
          ^ AbstractionId.to_string abs_id
          ^ "\n- context after parent abstractions ended:\n"
          ^ eval_ctx_to_string ~span:(Some span) ctx));

      (* End the loans inside the abstraction *)
      let ctx, cc =
        comp cc (end_abstraction_loans config span chain abs_id ctx)
      in
      log#ldebug
        (lazy
          ("end_abstraction_aux: "
          ^ AbstractionId.to_string abs_id
          ^ "\n- context after loans ended:\n"
          ^ eval_ctx_to_string ~span:(Some span) ctx));

      (* End the abstraction itself by redistributing the borrows it contains *)
      let ctx, cc =
        comp cc (end_abstraction_borrows config span chain abs_id ctx)
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
      log#ldebug
        (lazy
          ("end_abstraction_aux: "
          ^ AbstractionId.to_string abs_id
          ^ "\n- original context:\n"
          ^ eval_ctx_to_string ~span:(Some span) ctx0
          ^ "\n\n- new context:\n"
          ^ eval_ctx_to_string ~span:(Some span) ctx));

      (* Sanity check: ending an abstraction must preserve the invariants *)
      Invariants.check_invariants span ctx;

      (* Save a snapshot of the environment for the name generation *)
      let cc = cc_comp cc (SynthesizeSymbolic.save_snapshot ctx) in

      (* Return *)
      (ctx, cc)

and end_abstractions_aux (config : config) (span : Meta.span)
    (chain : borrow_or_abs_ids) (abs_ids : AbstractionId.Set.t) : cm_fun =
 fun ctx ->
  (* This is not necessary, but we prefer to reorder the abstraction ids,
   * so that we actually end from the smallest id to the highest id - just
   * a matter of taste, and may make debugging easier *)
  let abs_ids = AbstractionId.Set.fold (fun id ids -> id :: ids) abs_ids [] in
  fold_left_apply_continuation
    (fun id ctx -> end_abstraction_aux config span chain id ctx)
    abs_ids ctx

and end_abstraction_loans (config : config) (span : Meta.span)
    (chain : borrow_or_abs_ids) (abs_id : AbstractionId.id) : cm_fun =
 fun ctx ->
  log#ldebug
    (lazy
      ("end_abstraction_loans:" ^ "\n- abs_id: "
      ^ AbstractionId.to_string abs_id
      ^ "\n- ctx:\n" ^ eval_ctx_to_string ctx));
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
  | Some (BorrowIds bids) ->
      (* There are loans: end the corresponding borrows, then recheck *)
      let ctx, cc =
        match bids with
        | Borrow bid -> end_borrow_aux config span chain None bid ctx
        | Borrows bids -> end_borrows_aux config span chain None bids ctx
      in
      (* Reexplore, looking for loans *)
      comp cc (end_abstraction_loans config span chain abs_id ctx)
  | Some (SymbolicValue (sv, proj_ty)) ->
      (* There is a proj_loans over a symbolic value: end the proj_borrows
         which intersect this proj_loans, then end the proj_loans itself *)
      let ctx, cc =
        end_proj_loans_symbolic config span chain abs_id abs.regions.owned sv
          proj_ty ctx
      in
      (* Reexplore, looking for loans *)
      comp cc (end_abstraction_loans config span chain abs_id ctx)

and end_abstraction_borrows (config : config) (span : Meta.span)
    (chain : borrow_or_abs_ids) (abs_id : AbstractionId.id) : cm_fun =
 fun ctx ->
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
     the exploration didn't trigger an exception, it means there are no
     inner borrows to end: we can thus trigger an exception for the current
     borrow.

     TODO: we should implement a function in InterpreterBorrowsCore to do
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
        | AProjLoans _ -> craise __FILE__ __LINE__ span "Unexpected"
        | AProjBorrows (sv, proj_ty, given_back) ->
            raise (FoundAProjBorrows (sv, proj_ty, given_back))
        | AEndedProjLoans _ | AEndedProjBorrows _ | AEmpty -> ());
        super#visit_aproj env sproj

      (** We may need to end borrows in "regular" values, because of shared values *)
      method! visit_borrow_content _ bc =
        match bc with
        | VSharedBorrow _ | VMutBorrow (_, _) -> raise (FoundBorrowContent bc)
        | VReservedMutBorrow _ -> craise __FILE__ __LINE__ span "Unreachable"
    end
  in
  (* Lookup the abstraction *)
  let abs = ctx_lookup_abs ctx abs_id in
  try
    (* Explore the abstraction, looking for borrows *)
    visitor#visit_abs () abs;
    (* No borrows: nothing to update *)
    (ctx, fun e -> e)
  with
  (* There are concrete (i.e., not symbolic) borrows: end them, then re-explore *)
  | FoundABorrowContent bc ->
      log#ldebug
        (lazy
          ("end_abstraction_borrows: found aborrow content: "
          ^ aborrow_content_to_string ~span:(Some span) ctx bc));
      let ctx =
        match bc with
        | AMutBorrow (pm, bid, av) ->
            sanity_check __FILE__ __LINE__ (pm = PNone) span;
            (* First, convert the avalue to a (fresh symbolic) value *)
            let sv = convert_avalue_to_given_back_value span av in
            (* Replace the mut borrow to register the fact that we ended
               it and store with it the freshly generated given back value *)
            let meta = { bid; given_back = sv } in
            let ended_borrow = ABorrow (AEndedMutBorrow (meta, av)) in
            let ctx = update_aborrow span ek_all bid ended_borrow ctx in
            (* Give the value back *)
            let sv = mk_typed_value_from_symbolic_value sv in
            give_back_value config span bid sv ctx
        | ASharedBorrow (pm, bid) ->
            sanity_check __FILE__ __LINE__ (pm = PNone) span;
            (* Replace the shared borrow to account for the fact it ended *)
            let ended_borrow = ABorrow AEndedSharedBorrow in
            let ctx = update_aborrow span ek_all bid ended_borrow ctx in
            (* Give back *)
            give_back_shared config span bid ctx
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
               can use to identify the whole set *)
            let repr_bid = List.hd bids in
            (* Replace the shared borrow with Bottom *)
            let ctx = update_aborrow span ek_all repr_bid ABottom ctx in
            (* Give back the shared borrows *)
            let ctx =
              List.fold_left
                (fun ctx bid -> give_back_shared config span bid ctx)
                ctx bids
            in
            (* Continue *)
            ctx
        | AEndedMutBorrow _
        | AIgnoredMutBorrow _
        | AEndedIgnoredMutBorrow _
        | AEndedSharedBorrow -> craise __FILE__ __LINE__ span "Unexpected"
      in
      (* Reexplore *)
      end_abstraction_borrows config span chain abs_id ctx
  (* There are symbolic borrows: end them, then reexplore *)
  | FoundAProjBorrows (sv, proj_ty, given_back) ->
      log#ldebug
        (lazy
          ("end_abstraction_borrows: found aproj borrows: "
          ^ aproj_to_string ctx (AProjBorrows (sv, proj_ty, given_back))));
      (* Generate a fresh symbolic value *)
      let nsv = mk_fresh_symbolic_value span proj_ty in
      (* Replace the proj_borrows - there should be exactly one *)
      let ctx = end_aproj_borrows span abs.regions.owned proj_ty sv nsv ctx in
      (* Give back the symbolic value *)
      let ctx =
        give_back_symbolic_value config span abs.regions.owned proj_ty sv nsv
          ctx
      in
      (* Reexplore *)
      end_abstraction_borrows config span chain abs_id ctx
  (* There are concrete (i.e., not symbolic) borrows in shared values: end them, then reexplore *)
  | FoundBorrowContent bc ->
      log#ldebug
        (lazy
          ("end_abstraction_borrows: found borrow content: "
          ^ borrow_content_to_string ~span:(Some span) ctx bc));
      let ctx =
        match bc with
        | VSharedBorrow bid -> (
            (* Replace the shared borrow with bottom *)
            match end_borrow_get_borrow span (Some abs_id) bid ctx with
            | Error _ -> craise __FILE__ __LINE__ span "Unreachable"
            | Ok (ctx, _) ->
                (* Give back *)
                give_back_shared config span bid ctx)
        | VMutBorrow (bid, v) -> (
            (* Replace the mut borrow with bottom *)
            match end_borrow_get_borrow span (Some abs_id) bid ctx with
            | Error _ -> craise __FILE__ __LINE__ span "Unreachable"
            | Ok (ctx, _) ->
                (* Give the value back - note that the mut borrow was below a
                 * shared borrow: the value is thus unchanged *)
                give_back_value config span bid v ctx)
        | VReservedMutBorrow _ -> craise __FILE__ __LINE__ span "Unreachable"
      in
      (* Reexplore *)
      end_abstraction_borrows config span chain abs_id ctx

(** Remove an abstraction from the context, as well as all its references *)
and end_abstraction_remove_from_context (_config : config) (span : Meta.span)
    (abs_id : AbstractionId.id) : cm_fun =
 fun ctx ->
  let ctx, abs = ctx_remove_abs span ctx abs_id in
  let abs = Option.get abs in
  (* Synthesize the symbolic AST *)
  (ctx, SynthesizeSymbolic.synthesize_end_abstraction ctx abs)

(** End a proj_loan over a symbolic value by ending the proj_borrows which
    intersect this proj_loan.
    
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

    Note that we may get recursively get here after a sequence of updates which
    look like this:
    - attempt ending a loan projector
    - end a borrow projector before, and by doing this actually end the loan projector
    - retry ending the loan projector
    We thus have to be careful about the fact that maybe the loan projector actually
    doesn't exist anymore when we get here.
*)
and end_proj_loans_symbolic (config : config) (span : Meta.span)
    (chain : borrow_or_abs_ids) (abs_id : AbstractionId.id)
    (regions : RegionId.Set.t) (sv : symbolic_value) (proj_ty : rty) : cm_fun =
 fun ctx ->
  log#ldebug
    (lazy
      ("end_proj_loans_symbolic:" ^ "\n- abs_id: "
      ^ AbstractionId.to_string abs_id
      ^ "\n- regions: "
      ^ RegionId.Set.to_string None regions
      ^ "\n- sv: "
      ^ symbolic_value_to_string ctx sv
      ^ "\n- projection type: " ^ ty_to_string ctx proj_ty ^ "\n- ctx:\n"
      ^ eval_ctx_to_string ctx));
  (* Small helpers for sanity checks *)
  let check ctx = no_aproj_over_symbolic_in_context span sv ctx in
  (* Find the first proj_borrows which intersects the proj_loans *)
  let explore_shared = true in
  match
    lookup_intersecting_aproj_borrows_opt span explore_shared regions sv proj_ty
      ctx
  with
  | None ->
      (* We couldn't find any in the context: it means that the symbolic value
         is in the concrete environment (or that we dropped it, in which case
         it is completely absent). We thus simply need to replace the loans
         projector with an ended projector.
      *)
      let ctx = update_aproj_loans_to_ended span abs_id sv ctx in
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
            (fun s id -> AbstractionId.Set.add id s)
            AbstractionId.Set.empty abs_ids
        in
        (* End the abstractions and continue *)
        end_abstractions_aux config span chain abs_ids ctx
      in
      (* End the internal borrows projectors and the loans projector *)
      let ctx =
        (* All the proj_borrows are owned: simply erase them *)
        let ctx =
          remove_intersecting_aproj_borrows_shared span ~include_ancestors:false
            ~include_owned:true regions sv proj_ty ctx
        in
        (* End the loan itself *)
        update_aproj_loans_to_ended span abs_id sv ctx
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
           sanity_check __FILE__ __LINE__
             (Option.is_none
                (lookup_intersecting_aproj_borrows_opt span explore_shared regions
                   sv proj_ty ctx))
             span;
           (* End the projector of loans *)
           let ctx = update_aproj_loans_to_ended span abs_id sv ctx in
           (* Sanity check *)
           check ctx;
           (* Continue *)
                 (ctx, fun e -> e) *)
      else
        (* The borrows proj comes from a different abstraction: end it. *)
        let ctx, cc = end_abstraction_aux config span chain abs_id' ctx in
        (* Retry ending the projector of loans *)
        let ctx, cc =
          comp cc
            (end_proj_loans_symbolic config span chain abs_id regions sv proj_ty
               ctx)
        in
        (* Sanity check *)
        check ctx;
        (* Return *)
        (ctx, cc)

let end_borrow config (span : Meta.span) : BorrowId.id -> cm_fun =
  end_borrow_aux config span [] None

let end_borrows config (span : Meta.span) : BorrowId.Set.t -> cm_fun =
  end_borrows_aux config span [] None

let end_abstraction config span = end_abstraction_aux config span []
let end_abstractions config span = end_abstractions_aux config span []
let end_borrow_no_synth config span id ctx = fst (end_borrow config span id ctx)

let end_borrows_no_synth config span ids ctx =
  fst (end_borrows config span ids ctx)

let end_abstraction_no_synth config span id ctx =
  fst (end_abstraction config span id ctx)

let end_abstractions_no_synth config span ids ctx =
  fst (end_abstractions config span ids ctx)

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
let promote_shared_loan_to_mut_loan (span : Meta.span) (l : BorrowId.id)
    (ctx : eval_ctx) : typed_value * eval_ctx =
  (* Debug *)
  log#ldebug
    (lazy
      ("promote_shared_loan_to_mut_loan:\n- loan: " ^ BorrowId.to_string l
     ^ "\n- context:\n"
      ^ eval_ctx_to_string ~span:(Some span) ctx
      ^ "\n"));
  (* Lookup the shared loan - note that we can't promote a shared loan
   * in a shared value, but we can do it in a mutably borrowed value.
   * This is important because we can do: [let y = &two-phase ( *x );]
   *)
  let ek =
    { enter_shared_loans = false; enter_mut_borrows = true; enter_abs = false }
  in
  match lookup_loan span ek l ctx with
  | _, Concrete (VMutLoan _) ->
      craise __FILE__ __LINE__ span "Expected a shared loan, found a mut loan"
  | _, Concrete (VSharedLoan (bids, sv)) ->
      (* Check that there is only one borrow id (l) and update the loan *)
      cassert __FILE__ __LINE__
        (BorrowId.Set.mem l bids && BorrowId.Set.cardinal bids = 1)
        span "There should only be one borrow id";
      (* We need to check that there aren't any loans in the value:
         we should have gotten rid of those already, but it is better
         to do a sanity check. *)
      sanity_check __FILE__ __LINE__ (not (loans_in_value sv)) span;
      (* Check there isn't {!Bottom} (this is actually an invariant *)
      cassert __FILE__ __LINE__
        (not (bottom_in_value ctx.ended_regions sv))
        span "There shouldn't be a bottom";
      (* Check there aren't reserved borrows *)
      cassert __FILE__ __LINE__
        (not (reserved_in_value sv))
        span "There shouldn't be reserved borrows";
      (* Update the loan content *)
      let ctx = update_loan span ek l (VMutLoan l) ctx in
      (* Return *)
      (sv, ctx)
  | _, Abstract _ ->
      (* I don't think it is possible to have two-phase borrows involving borrows
         returned by abstractions. I'm not sure how we could handle that anyway. *)
      craise __FILE__ __LINE__ span
        "Can't promote a shared loan to a mutable loan if the loan is inside a \
         region abstraction"

(** Helper function: see {!activate_reserved_mut_borrow}.

    This function updates a shared borrow to a mutable borrow (and that is
    all: it doesn't touch the corresponding loan).
 *)
let replace_reserved_borrow_with_mut_borrow (span : Meta.span) (l : BorrowId.id)
    (borrowed_value : typed_value) (ctx : eval_ctx) : eval_ctx =
  (* Lookup the reserved borrow - note that we don't go inside borrows/loans:
     there can't be reserved borrows inside other borrows/loans
  *)
  let ek =
    { enter_shared_loans = false; enter_mut_borrows = false; enter_abs = false }
  in
  match lookup_borrow span ek l ctx with
  | Concrete (VSharedBorrow _ | VMutBorrow (_, _)) ->
      craise __FILE__ __LINE__ span "Expected a reserved mutable borrow"
  | Concrete (VReservedMutBorrow _) ->
      (* Update it *)
      update_borrow span ek l (VMutBorrow (l, borrowed_value)) ctx
  | Abstract _ ->
      (* This can't happen for sure *)
      craise __FILE__ __LINE__ span
        "Can't promote a shared borrow to a mutable borrow if the borrow is \
         inside a region abstraction"

(** Promote a reserved mut borrow to a mut borrow. *)
let rec promote_reserved_mut_borrow (config : config) (span : Meta.span)
    (l : BorrowId.id) : cm_fun =
 fun ctx ->
  (* Lookup the value *)
  let ek =
    { enter_shared_loans = false; enter_mut_borrows = true; enter_abs = false }
  in
  match lookup_loan span ek l ctx with
  | _, Concrete (VMutLoan _) -> craise __FILE__ __LINE__ span "Unreachable"
  | _, Concrete (VSharedLoan (bids, sv)) -> (
      (* If there are loans inside the value, end them. Note that there can't be
         reserved borrows inside the value.
         If we perform an update, do a recursive call to lookup the updated value *)
      match get_first_loan_in_value sv with
      | Some lc ->
          (* End the loans *)
          let ctx, cc =
            match lc with
            | VSharedLoan (bids, _) -> end_borrows config span bids ctx
            | VMutLoan bid -> end_borrow config span bid ctx
          in
          (* Recursive call *)
          comp cc (promote_reserved_mut_borrow config span l ctx)
      | None ->
          (* No loan to end inside the value *)
          (* Some sanity checks *)
          log#ldebug
            (lazy
              ("activate_reserved_mut_borrow: resulting value:\n"
              ^ typed_value_to_string ~span:(Some span) ctx sv));
          sanity_check __FILE__ __LINE__ (not (loans_in_value sv)) span;
          sanity_check __FILE__ __LINE__
            (not (bottom_in_value ctx.ended_regions sv))
            span;
          sanity_check __FILE__ __LINE__ (not (reserved_in_value sv)) span;
          (* End the borrows which borrow from the value, at the exception of
             the borrow we want to promote *)
          let bids = BorrowId.Set.remove l bids in
          let ctx, cc = end_borrows config span bids ctx in
          (* Promote the loan - TODO: this will fail if the value contains
           * any loans. In practice, it shouldn't, but we could also
           * look for loans inside the value and end them before promoting
           * the borrow. *)
          let v, ctx = promote_shared_loan_to_mut_loan span l ctx in
          (* Promote the borrow - the value should have been checked by
             {!promote_shared_loan_to_mut_loan}
          *)
          let ctx = replace_reserved_borrow_with_mut_borrow span l v ctx in
          (* Return *)
          (ctx, cc))
  | _, Abstract _ ->
      (* I don't think it is possible to have two-phase borrows involving borrows
       * returned by abstractions. I'm not sure how we could handle that anyway. *)
      craise __FILE__ __LINE__ span
        "Can't activate a reserved mutable borrow referencing a loan inside\n\
        \         a region abstraction"

let destructure_abs (span : Meta.span) (abs_kind : abs_kind) (can_end : bool)
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
  let push_fail _ = craise __FILE__ __LINE__ span "Unreachable" in
  (* Function to explore an avalue and destructure it *)
  let rec list_avalues (allow_borrows : bool) (push : typed_avalue -> unit)
      (av : typed_avalue) : unit =
    let ty = av.ty in
    match av.value with
    | ABottom | AIgnored _ -> ()
    | AAdt adt ->
        (* Simply explore the children *)
        List.iter (list_avalues allow_borrows push) adt.field_values
    | ALoan lc -> (
        (* Explore the loan content *)
        match lc with
        | ASharedLoan (pm, bids, sv, child_av) ->
            (* We don't support nested borrows for now *)
            cassert __FILE__ __LINE__
              (not (value_has_borrows (Some span) ctx sv.value))
              span "Nested borrows are not supported yet";
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
            cassert __FILE__ __LINE__
              (not
                 (ty_has_borrows (Some span) ctx.type_ctx.type_infos child_av.ty))
              span "Nested borrows are not supported yet";
            sanity_check __FILE__ __LINE__ (opt_bid = None) span;
            (* Simply explore the child *)
            list_avalues false push_fail child_av
        | AEndedMutLoan
            { child = child_av; given_back = _; given_back_meta = _ }
        | AEndedSharedLoan (_, child_av)
        | AEndedIgnoredMutLoan
            { child = child_av; given_back = _; given_back_meta = _ }
        | AIgnoredSharedLoan child_av ->
            (* We don't support nested borrows for now *)
            cassert __FILE__ __LINE__
              (not
                 (ty_has_borrows (Some span) ctx.type_ctx.type_infos child_av.ty))
              span "Nested borrows are not supported yet";
            (* Simply explore the child *)
            list_avalues false push_fail child_av)
    | ABorrow bc -> (
        (* Sanity check - rem.: may be redundant with [push_fail] *)
        sanity_check __FILE__ __LINE__ allow_borrows span;
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
            cassert __FILE__ __LINE__
              (not
                 (ty_has_borrows (Some span) ctx.type_ctx.type_infos child_av.ty))
              span "Nested borrows are not supported yet";
            sanity_check __FILE__ __LINE__ (opt_bid = None) span;
            (* Just explore the child *)
            list_avalues false push_fail child_av
        | AEndedIgnoredMutBorrow
            { child = child_av; given_back = _; given_back_meta = _ } ->
            (* We don't support nested borrows for now *)
            cassert __FILE__ __LINE__
              (not
                 (ty_has_borrows (Some span) ctx.type_ctx.type_infos child_av.ty))
              span "Nested borrows are not supported yet";
            (* Just explore the child *)
            list_avalues false push_fail child_av
        | AProjSharedBorrow asb ->
            (* We don't support nested borrows *)
            cassert __FILE__ __LINE__ (asb = []) span
              "Nested borrows are not supported yet";
            (* Nothing specific to do *)
            ()
        | AEndedMutBorrow _ | AEndedSharedBorrow ->
            (* If we get there it means the abstraction ended: it should not
               be in the context anymore (if we end *one* borrow in an abstraction,
               we have to end them all and remove the abstraction from the context)
            *)
            craise __FILE__ __LINE__ span "Unreachable")
    | ASymbolic (_, aproj) -> (
        (* *)
        match aproj with
        | AProjLoans (_, _, children) ->
            (* There can be children in the presence of nested borrows: we
               don't handle those for now. *)
            sanity_check __FILE__ __LINE__ (children = []) span;
            push av
        | AProjBorrows (_, _, children) ->
            (* For now, we fore all symbolic values containing borrows to be eagerly
               expanded *)
            (* There can be children in the presence of nested borrows: we
               don't handle those for now. *)
            sanity_check __FILE__ __LINE__ (children = []) span;
            push av
        | AEndedProjLoans (_, children) | AEndedProjBorrows (_, children) ->
            (* There can be children in the presence of nested borrows: we
               don't handle those for now. *)
            sanity_check __FILE__ __LINE__ (children = []) span;
            (* Just ignore *)
            ()
        | AEmpty -> ())
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
    | VBottom -> craise __FILE__ __LINE__ span "Unreachable"
    | VBorrow _ ->
        (* We don't support nested borrows for now *)
        craise __FILE__ __LINE__ span "Unreachable"
    | VLoan lc -> (
        match lc with
        | VSharedLoan (bids, sv) ->
            let avl, sv = list_values sv in
            if destructure_shared_values then (
              (* Rem.: the shared value can't contain loans nor borrows *)
              cassert __FILE__ __LINE__ (ty_no_regions ty) span
                "Nested borrows are not supported yet";
              let av : typed_avalue =
                sanity_check __FILE__ __LINE__
                  (not (value_has_loans_or_borrows (Some span) ctx sv.value))
                  span;
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
        | VMutLoan _ -> craise __FILE__ __LINE__ span "Unreachable")
    | VSymbolic _ ->
        (* For now, we fore all symbolic values containing borrows to be eagerly
           expanded *)
        sanity_check __FILE__ __LINE__
          (not (ty_has_borrows (Some span) ctx.type_ctx.type_infos ty))
          span;
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
    destructure_abs span abs.kind abs.can_end destructure_shared_values ctx abs
  in
  abs = abs'

let convert_value_to_abstractions (span : Meta.span) (abs_kind : abs_kind)
    (can_end : bool) (destructure_shared_values : bool) (ctx : eval_ctx)
    (v : typed_value) : abs list =
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
          regions =
            {
              owned = RegionId.Set.singleton r_id;
              ancestors = RegionId.Set.empty;
            };
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
        ^ typed_value_to_string ~span:(Some span) ctx v));

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
        cassert __FILE__ __LINE__ (ty_no_regions ref_ty) span
          "Nested borrows are not supported yet";
        (* Sanity check *)
        sanity_check __FILE__ __LINE__ allow_borrows span;
        (* Convert the borrow content *)
        match bc with
        | VSharedBorrow bid ->
            cassert __FILE__ __LINE__ (ty_no_regions ref_ty) span
              "Nested borrows are not supported yet";
            let ty = TRef (RVar (Free r_id), ref_ty, kind) in
            let value = ABorrow (ASharedBorrow (PNone, bid)) in
            ([ { value; ty } ], v)
        | VMutBorrow (bid, bv) ->
            let r_id = if group then r_id else fresh_region_id () in
            (* We don't support nested borrows for now *)
            cassert __FILE__ __LINE__
              (not (value_has_borrows (Some span) ctx bv.value))
              span "Nested borrows are not supported yet";
            (* Create an avalue to push - note that we use [AIgnore] for the inner avalue *)
            let ty = TRef (RVar (Free r_id), ref_ty, kind) in
            let ignored = mk_aignored span ref_ty None in
            let av = ABorrow (AMutBorrow (PNone, bid, ignored)) in
            let av = { value = av; ty } in
            (* Continue exploring, looking for loans (and forbidding borrows,
               because we don't support nested borrows for now) *)
            let avl, bv = to_avalues false true true r_id bv in
            let value = { v with value = VBorrow (VMutBorrow (bid, bv)) } in
            (av :: avl, value)
        | VReservedMutBorrow _ ->
            (* This borrow should have been activated *)
            craise __FILE__ __LINE__ span "Unexpected")
    | VLoan lc -> (
        match lc with
        | VSharedLoan (bids, sv) ->
            let r_id = if group then r_id else fresh_region_id () in
            (* We don't support nested borrows for now *)
            cassert __FILE__ __LINE__
              (not (value_has_borrows (Some span) ctx sv.value))
              span "Nested borrows are not supported yet";
            (* Push the avalue *)
            cassert __FILE__ __LINE__ (ty_no_regions ty) span
              "Nested borrows are not supported yet";
            (* We use [AIgnore] for the inner value *)
            let ignored = mk_aignored span ty None in
            (* For avalues, a loan has the type borrow (see the comments in [avalue]) *)
            let ty = mk_ref_ty (RVar (Free r_id)) ty RShared in
            (* Rem.: the shared value might contain loans *)
            let avl, sv = to_avalues false true true r_id sv in
            let av = ALoan (ASharedLoan (PNone, bids, sv, ignored)) in
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
            (* Push the avalue *)
            cassert __FILE__ __LINE__ (ty_no_regions ty) span
              "Nested borrows are not supported yet";
            (* We use [AIgnore] for the inner value *)
            let ignored = mk_aignored span ty in
            (* For avalues, a loan has the type borrow (see the comments in [avalue]) *)
            let ty = mk_ref_ty (RVar (Free r_id)) ty RMut in
            let av = ALoan (AMutLoan (PNone, bid, ignored None)) in
            let av = { value = av; ty } in
            ([ av ], v))
    | VSymbolic _ ->
        (* For now, we force all the symbolic values containing borrows to
           be eagerly expanded, and we don't support nested borrows *)
        cassert __FILE__ __LINE__
          (not (value_has_borrows (Some span) ctx v.value))
          span "Nested borrows are not supported yet";
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

type 'a borrow_or_loan = Borrow of 'a | Loan of 'a

type g_loan_content_with_ty =
  (ety * loan_content, rty * aloan_content) concrete_or_abs

type g_borrow_content_with_ty =
  (ety * borrow_content, rty * aborrow_content) concrete_or_abs

type merge_abstraction_info = {
  loans : MarkedBorrowId.Set.t;
  borrows : MarkedBorrowId.Set.t;
  loan_projs : MarkedNormSymbProj.Set.t;
  borrow_projs : MarkedNormSymbProj.Set.t;
  borrows_loans : marked_borrow_id borrow_or_loan list;
  borrow_loan_projs : marked_norm_symb_proj borrow_or_loan list;
      (** We use a list to preserve the order in which the borrows were found *)
  loan_to_content : g_loan_content_with_ty MarkedBorrowId.Map.t;
  borrow_to_content : g_borrow_content_with_ty MarkedBorrowId.Map.t;
  loan_proj_to_content : (ty * proj_marker * aproj) MarkedNormSymbProj.Map.t;
  borrow_proj_to_content : (ty * proj_marker * aproj) MarkedNormSymbProj.Map.t;
}

(** Small utility to help merging abstractions.

    We compute the list of loan/borrow contents, maps from borrow/loan ids
    to borrow/loan contents, etc.

    Note that this function is very specific to [merge_into_first_abstraction]: we
    have strong assumptions about the shape of the abstraction, and in
    particular that:
    - its values don't contain nested borrows
    - all the borrows are destructured (for instance, shared loans can't
      contain shared loans).
 *)
let compute_merge_abstraction_info (span : Meta.span) (ctx : eval_ctx)
    (owned_regions : RegionId.Set.t) (avalues : typed_avalue list) :
    merge_abstraction_info =
  let loans : MarkedBorrowId.Set.t ref = ref MarkedBorrowId.Set.empty in
  let borrows : MarkedBorrowId.Set.t ref = ref MarkedBorrowId.Set.empty in
  let loan_projs = ref MarkedNormSymbProj.Set.empty in
  let borrow_projs = ref MarkedNormSymbProj.Set.empty in
  let borrows_loans : marked_borrow_id borrow_or_loan list ref = ref [] in
  let borrow_loan_projs = ref [] in
  let loan_to_content : g_loan_content_with_ty MarkedBorrowId.Map.t ref =
    ref MarkedBorrowId.Map.empty
  in
  let borrow_to_content : g_borrow_content_with_ty MarkedBorrowId.Map.t ref =
    ref MarkedBorrowId.Map.empty
  in
  let loan_proj_to_content = ref MarkedNormSymbProj.Map.empty in
  let borrow_proj_to_content = ref MarkedNormSymbProj.Map.empty in

  let module Push
      (Set : Collections.Set)
      (Map : Collections.Map with type key = Set.elt) =
  struct
    let push (set : Set.t ref) (content : 'a) (to_content : 'a Map.t ref)
        (is_borrow : bool) (borrows_loans : Set.elt borrow_or_loan list ref)
        (marked : Set.elt) : unit =
      sanity_check __FILE__ __LINE__ (not (Set.mem marked !set)) span;
      set := Set.add marked !set;
      sanity_check __FILE__ __LINE__ (not (Map.mem marked !to_content)) span;
      to_content := Map.add marked content !to_content;
      borrows_loans :=
        (if is_borrow then Borrow marked else Loan marked) :: !borrows_loans
  end in
  let module PushConcrete = Push (MarkedBorrowId.Set) (MarkedBorrowId.Map) in
  let push_loan pm id (lc : g_loan_content_with_ty) =
    PushConcrete.push loans lc loan_to_content false borrows_loans (pm, id)
  in
  let push_loans pm ids lc : unit =
    BorrowId.Set.iter (fun id -> push_loan pm id lc) ids
  in
  let push_borrow pm id (bc : g_borrow_content_with_ty) =
    PushConcrete.push borrows bc borrow_to_content true borrows_loans (pm, id)
  in

  let module PushSymbolic =
    Push (MarkedNormSymbProj.Set) (MarkedNormSymbProj.Map)
  in
  let push_loan_proj pm sv_id proj_ty lc =
    let norm_proj_ty = normalize_proj_ty owned_regions proj_ty in
    let proj = { pm; sv_id; norm_proj_ty } in
    PushSymbolic.push loan_projs lc loan_proj_to_content false borrow_loan_projs
      proj
  in
  let push_borrow_proj pm sv_id proj_ty bc =
    let norm_proj_ty = normalize_proj_ty owned_regions proj_ty in
    let proj = { pm; sv_id; norm_proj_ty } in
    PushSymbolic.push borrow_projs bc borrow_proj_to_content true
      borrow_loan_projs proj
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

      method! visit_loan_content _ _ =
        (* Could happen if we explore shared values whose sub-values are
           reborrowed. We use the fact that we destructure the nested shared
           loans before reducing a context or computing a join. *)
        craise __FILE__ __LINE__ span "Unreachable"

      method! visit_borrow_content _ _ =
        (* Can happen if we explore shared values which contain borrows -
           i.e., if we have nested borrows (we forbid this for now) *)
        craise __FILE__ __LINE__ span "Unreachable"

      method! visit_aloan_content env lc =
        let ty =
          match Option.get env with
          | Concrete _ -> craise __FILE__ __LINE__ span "Unreachable"
          | Abstract ty -> ty
        in
        (* Register the loans *)
        (match lc with
        | ASharedLoan (pm, bids, _, _) -> push_loans pm bids (Abstract (ty, lc))
        | AMutLoan (pm, bid, _) -> push_loan pm bid (Abstract (ty, lc))
        | AEndedMutLoan _
        | AEndedSharedLoan _
        | AIgnoredMutLoan _
        | AEndedIgnoredMutLoan _
        | AIgnoredSharedLoan _ ->
            (* The abstraction has been destructured, so those shouldn't appear *)
            craise __FILE__ __LINE__ span "Unreachable");
        (* Continue *)
        super#visit_aloan_content env lc

      method! visit_aborrow_content env bc =
        let ty =
          match Option.get env with
          | Concrete _ -> craise __FILE__ __LINE__ span "Unreachable"
          | Abstract ty -> ty
        in
        (* Explore the borrow content *)
        (match bc with
        | AMutBorrow (pm, bid, _) | ASharedBorrow (pm, bid) ->
            push_borrow pm bid (Abstract (ty, bc))
        | AProjSharedBorrow asb ->
            let register asb =
              match asb with
              | AsbBorrow bid -> push_borrow PNone bid (Abstract (ty, bc))
              | AsbProjReborrows _ ->
                  (* Can only happen if the symbolic value (potentially) contains
                     borrows - i.e., we have nested borrows *)
                  craise __FILE__ __LINE__ span "Unreachable"
            in
            List.iter register asb
        | AIgnoredMutBorrow _
        | AEndedIgnoredMutBorrow _
        | AEndedMutBorrow _
        | AEndedSharedBorrow ->
            (* The abstraction has been destructured, so those shouldn't appear *)
            craise __FILE__ __LINE__ span "Unreachable");
        super#visit_aborrow_content env bc

      method! visit_symbolic_value _ sv =
        (* Sanity check: no borrows *)
        sanity_check __FILE__ __LINE__
          (not (symbolic_value_has_borrows (Some span) ctx sv))
          span

      method! visit_ASymbolic env pm proj =
        let ty =
          match Option.get env with
          | Concrete _ -> craise __FILE__ __LINE__ span "Unreachable"
          | Abstract ty -> ty
        in
        match proj with
        | AProjLoans (sv, proj_ty, children) ->
            sanity_check __FILE__ __LINE__ (children = []) span;
            push_loan_proj pm sv.sv_id proj_ty (ty, pm, proj)
        | AProjBorrows (sv, proj_ty, children) ->
            sanity_check __FILE__ __LINE__ (children = []) span;
            push_borrow_proj pm sv.sv_id proj_ty (ty, pm, proj)
        | AEndedProjLoans _ | AEndedProjBorrows _ ->
            craise __FILE__ __LINE__ span "Unreachable"
        | AEmpty -> ()
    end
  in

  List.iter (iter_avalues#visit_typed_avalue None) avalues;

  {
    loans = !loans;
    borrows = !borrows;
    borrows_loans = List.rev !borrows_loans;
    loan_to_content = !loan_to_content;
    borrow_to_content = !borrow_to_content;
    loan_projs = !loan_projs;
    borrow_projs = !borrow_projs;
    borrow_loan_projs = List.rev !borrow_loan_projs;
    loan_proj_to_content = !loan_proj_to_content;
    borrow_proj_to_content = !borrow_proj_to_content;
  }

type merge_duplicates_funcs = {
  merge_amut_borrows :
    borrow_id ->
    rty ->
    proj_marker ->
    typed_avalue ->
    rty ->
    proj_marker ->
    typed_avalue ->
    typed_avalue;
      (** Parameters:
          - [id]
          - [ty0]
          - [pm0]
          - [child0]
          - [ty1]
          - [pm1]
          - [child1]

          The children should be [AIgnored].
       *)
  merge_ashared_borrows :
    borrow_id -> rty -> proj_marker -> rty -> proj_marker -> typed_avalue;
      (** Parameters:
          - [id]
          - [ty0]
          - [pm0]
          - [ty1]
          - [pm1]
       *)
  merge_amut_loans :
    loan_id ->
    rty ->
    proj_marker ->
    typed_avalue ->
    rty ->
    proj_marker ->
    typed_avalue ->
    typed_avalue;
      (** Parameters:
          - [id]
          - [ty0]
          - [pm0]
          - [child0]
          - [ty1]
          - [pm1]
          - [child1]

          The children should be [AIgnored].
       *)
  merge_ashared_loans :
    loan_id_set ->
    rty ->
    proj_marker ->
    typed_value ->
    typed_avalue ->
    rty ->
    proj_marker ->
    typed_value ->
    typed_avalue ->
    typed_avalue;
      (** Parameters:
          - [ids]
          - [ty0]
          - [pm0]
          - [sv0]
          - [child0]
          - [ty1]
          - [pm1]
          - [sv1]
          - [child1]
       *)
  merge_aborrow_projs :
    ty ->
    proj_marker ->
    symbolic_value ->
    ty ->
    (msymbolic_value * aproj) list ->
    ty ->
    proj_marker ->
    symbolic_value ->
    ty ->
    (msymbolic_value * aproj) list ->
    typed_avalue;
      (** Parameters:
      - [ty0]
      - [pm0]
      - [sv0]
      - [proj_ty0]
      - [children0]
      - [ty1]
      - [pm1]
      - [sv1]
      - [proj_ty1]
      - [children1]
    *)
  merge_aloan_projs :
    ty ->
    proj_marker ->
    symbolic_value ->
    ty ->
    (msymbolic_value * aproj) list ->
    ty ->
    proj_marker ->
    symbolic_value ->
    ty ->
    (msymbolic_value * aproj) list ->
    typed_avalue;
      (** Parameters:
      - [ty0]
      - [pm0]
      - [sv0]
      - [proj_ty0]
      - [children0]
      - [ty1]
      - [pm1]
      - [sv1]
      - [proj_ty1]
      - [children1]
    *)
}

(** Small utility: if a value doesn't have any marker, split it into two values
    with complementary markers. We use this for {!merge_abstractions}.

    We assume the value has been destructured (there are no nested loans,
    adts, the children are ignored, etc.).
 *)
let typed_avalue_split_marker (span : Meta.span) (ctx : eval_ctx)
    (av : typed_avalue) : typed_avalue list =
  let mk_split mk_value = [ mk_value PLeft; mk_value PRight ] in
  let mk_opt_split pm mk_value =
    if pm = PNone then mk_split mk_value else [ av ]
  in
  match av.value with
  | AAdt _ | ABottom | AIgnored _ -> internal_error __FILE__ __LINE__ span
  | ABorrow bc -> (
      match bc with
      | AMutBorrow (pm, bid, child) ->
          sanity_check __FILE__ __LINE__ (is_aignored child.value) span;
          let mk_value pm =
            { av with value = ABorrow (AMutBorrow (pm, bid, child)) }
          in
          mk_opt_split pm mk_value
      | ASharedBorrow (pm, bid) ->
          let mk_value pm =
            { av with value = ABorrow (ASharedBorrow (pm, bid)) }
          in
          mk_opt_split pm mk_value
      | _ -> internal_error __FILE__ __LINE__ span)
  | ALoan lc -> (
      match lc with
      | AMutLoan (pm, bid, child) ->
          sanity_check __FILE__ __LINE__ (is_aignored child.value) span;
          let mk_value pm =
            { av with value = ALoan (AMutLoan (pm, bid, child)) }
          in
          mk_opt_split pm mk_value
      | ASharedLoan (pm, bids, sv, child) ->
          sanity_check __FILE__ __LINE__ (is_aignored child.value) span;
          sanity_check __FILE__ __LINE__
            (not (value_has_borrows (Some span) ctx sv.value))
            span;
          let mk_value pm =
            { av with value = ALoan (ASharedLoan (pm, bids, sv, child)) }
          in
          mk_opt_split pm mk_value
      | _ -> internal_error __FILE__ __LINE__ span)
  | ASymbolic (pm, proj) -> (
      if pm <> PNone then [ av ]
      else
        match proj with
        | AProjLoans (_, _, children) | AProjBorrows (_, _, children) ->
            sanity_check __FILE__ __LINE__ (children = []) span;
            let mk_value pm = { av with value = ASymbolic (pm, proj) } in
            mk_split mk_value
        | AEndedProjLoans _ | AEndedProjBorrows _ | AEmpty ->
            internal_error __FILE__ __LINE__ span)

let abs_split_markers (span : Meta.span) (ctx : eval_ctx) (abs : abs) : abs =
  {
    abs with
    avalues =
      List.concat (List.map (typed_avalue_split_marker span ctx) abs.avalues);
  }

(** Auxiliary function for {!merge_abstractions}.

    Phase 1 of the merge: we simplify all loan/borrow pairs, if a loan is
    in the left abstraction and its corresponding borrow is in the right
    abstraction.

    Important: this is asymmetric (the loan must be in the left abstraction).

    Example:
    {[
      abs0 { ML l0, MB l1 } |><| abs1 { MB l0 }
          ~~> abs1 { MB l1 }
    ]}

    But:
    {[
      abs1 { MB l0 } |><| abs0 { ML l0, MB l1 }
          ~~> abs1 { MB l0, ML l0, MB l1 }
    ]}

    We return the list of merged values.
 *)
let merge_abstractions_merge_loan_borrow_pairs (span : Meta.span)
    (merge_funs : merge_duplicates_funcs option) (ctx : eval_ctx) (abs0 : abs)
    (abs1 : abs) : typed_avalue list =
  log#ldebug (lazy "merge_abstractions_merge_loan_borrow_pairs");

  (* Split the markers inside the abstractions (if we allow using markers).

     We do so because it enables simplification later when we are in the following case:
     {[
       abs0 { ML l0 } |><| abs1 { |MB l0|, MB l1 }
     ]}

     If we split before merging we get:
     {[
       abs0 { |ML l0|, ︙ML l0︙ } |><| abs1 { |MB l0|, |MB l1|, ︙MB l1︙ }
           ~~> merge
       abs2 { ︙ML l0︙, |MB l1|, ︙MB l1︙ }
           ~~> simplify the complementary markers
       abs2 { ︙ML l0︙, MB l1 }
     ]}
  *)
  let abs0, abs1 =
    if merge_funs = None then (abs0, abs1)
    else (abs_split_markers span ctx abs0, abs_split_markers span ctx abs1)
  in

  (* Compute the relevant information *)
  let {
    loans = loans0;
    borrows = borrows0;
    loan_projs = loan_projs0;
    borrow_projs = borrow_projs0;
    borrows_loans = borrows_loans0;
    borrow_loan_projs = borrow_loan_projs0;
    loan_to_content = loan_to_content0;
    loan_proj_to_content = loan_proj_to_content0;
    borrow_to_content = borrow_to_content0;
    borrow_proj_to_content = borrow_proj_to_content0;
  } =
    compute_merge_abstraction_info span ctx abs0.regions.owned abs0.avalues
  in

  let {
    loans = loans1;
    borrows = borrows1;
    loan_projs = loan_projs1;
    borrow_projs = borrow_projs1;
    borrows_loans = borrows_loans1;
    borrow_loan_projs = borrow_loan_projs1;
    loan_to_content = loan_to_content1;
    loan_proj_to_content = loan_proj_to_content1;
    borrow_to_content = borrow_to_content1;
    borrow_proj_to_content = borrow_proj_to_content1;
  } =
    compute_merge_abstraction_info span ctx abs1.regions.owned abs1.avalues
  in

  (* Sanity check: no markers appear unless we allow merging duplicates.
     Also, the borrows must be disjoint, and the loans must be disjoint.
  *)
  if merge_funs = None then (
    sanity_check __FILE__ __LINE__
      (List.for_all
         (function
           | Loan (pm, _) | Borrow (pm, _) -> pm = PNone)
         (borrows_loans0 @ borrows_loans1))
      span;
    sanity_check __FILE__ __LINE__
      (List.for_all
         (function
           | Loan proj | Borrow proj -> proj.pm = PNone)
         (borrow_loan_projs0 @ borrow_loan_projs1))
      span;
    sanity_check __FILE__ __LINE__
      (MarkedBorrowId.Set.disjoint borrows0 borrows1)
      span;
    sanity_check __FILE__ __LINE__
      (MarkedBorrowId.Set.disjoint loans0 loans1)
      span;
    sanity_check __FILE__ __LINE__
      (MarkedNormSymbProj.Set.disjoint borrow_projs0 borrow_projs1)
      span;
    sanity_check __FILE__ __LINE__
      (MarkedNormSymbProj.Set.disjoint loan_projs0 loan_projs1)
      span);

  (* Merge.
     There are several cases:
     - if a borrow/loan is only in one abstraction, we simply check if we need
       to filter it (because its associated loan/borrow is in the other
       abstraction).
     - if a borrow/loan is present in both abstractions, we need to merge its
       content.

     Note that we may need to merge strictly more than two avalues, because of
     shared loans. For instance, if we have:
     {[
       abs'0 { shared_loan { l0, l1 } ... }
       abs'1 { shared_loan { l0 } ..., shared_loan { l1 } ... }
     ]}

     We ignore this case for now: we check that whenever we merge two shared loans,
     then their sets of ids are equal, and fail if it is not the case.
     Remark: a way of solving this problem would be to destructure shared loans
     so that they always have exactly one id.
  *)
  let merged_borrows = ref MarkedBorrowId.Set.empty in
  let merged_borrow_projs = ref MarkedNormSymbProj.Set.empty in
  let merged_loans = ref MarkedBorrowId.Set.empty in
  let merged_loan_projs = ref MarkedNormSymbProj.Set.empty in
  let borrow_avalues = ref [] in
  let loan_avalues = ref [] in
  let push_borrow_avalue av =
    log#ldebug
      (lazy
        ("merge_abstractions_merge_loan_borrow_pairs: push_borrow_avalue: "
        ^ typed_avalue_to_string ~span:(Some span) ctx av));
    borrow_avalues := av :: !borrow_avalues
  in
  let push_loan_avalue av =
    log#ldebug
      (lazy
        ("merge_abstractions_merge_loan_borrow_pairs: push_loan_avalue: "
        ^ typed_avalue_to_string ~span:(Some span) ctx av));
    loan_avalues := av :: !loan_avalues
  in

  (* Compute the intersection of:
     - the loans coming from the left abstraction
     - the borrows coming from the right abstraction
     We will need to filter those (because the loan from the left will cancel
     out with the borrow from the right)
  *)
  let intersect_concrete = MarkedBorrowId.Set.inter loans0 borrows1 in
  let intersect_symbolic =
    MarkedNormSymbProj.Set.inter loan_projs0 borrow_projs1
  in

  (* This function is called when handling shared loans: we have to apply a projection
     marker to a set of borrow ids. *)
  let filter_bids (pm : proj_marker) (bids : BorrowId.Set.t) : BorrowId.Set.t =
    let bids =
      BorrowId.Set.to_seq bids
      |> Seq.map (fun x -> (pm, x))
      |> MarkedBorrowId.Set.of_seq
    in
    let bids = MarkedBorrowId.Set.diff bids intersect_concrete in
    sanity_check __FILE__ __LINE__ (not (MarkedBorrowId.Set.is_empty bids)) span;
    MarkedBorrowId.Set.to_seq bids |> Seq.map snd |> BorrowId.Set.of_seq
  in
  let filter_concrete (bid : marked_borrow_id) : bool =
    MarkedBorrowId.Set.mem bid intersect_concrete
  in
  let filter_symbolic (marked : marked_norm_symb_proj) : bool =
    MarkedNormSymbProj.Set.mem marked intersect_symbolic
  in

  let borrow_is_merged id = MarkedBorrowId.Set.mem id !merged_borrows in
  let borrow_proj_is_merged id =
    MarkedNormSymbProj.Set.mem id !merged_borrow_projs
  in
  let set_borrow_as_merged id =
    merged_borrows := MarkedBorrowId.Set.add id !merged_borrows
  in
  let set_borrow_proj_as_merged id =
    merged_borrow_projs := MarkedNormSymbProj.Set.add id !merged_borrow_projs
  in
  let loan_is_merged id = MarkedBorrowId.Set.mem id !merged_loans in
  let loan_proj_is_merged id =
    MarkedNormSymbProj.Set.mem id !merged_loan_projs
  in
  let set_loan_as_merged id =
    merged_loans := MarkedBorrowId.Set.add id !merged_loans
  in
  let set_loan_proj_as_merged id =
    merged_loan_projs := MarkedNormSymbProj.Set.add id !merged_loan_projs
  in

  let module Merge
      (Set : Collections.Set)
      (Map : Collections.Map with type key = Set.elt)
      (Marked : sig
        type borrow_content
        type loan_content

        val to_string : Set.elt -> string
        val borrow_is_merged : Set.elt -> bool
        val loan_is_merged : Set.elt -> bool
        val filter_marked : Set.elt -> bool
        val set_borrow_as_merged : Set.elt -> unit
        val set_loan_as_merged : Set.elt -> unit
        val make_borrow_value : Set.elt -> borrow_content -> typed_avalue

        (** Return the list of marked values to mark as merged - this is important
            for shared loans: the loan itself is identified by a single loan id,
            but we need to mark *all* the loan ids contained in the set as merged. *)
        val make_loan_value :
          Set.elt -> loan_content -> Set.elt list * typed_avalue
      end) =
  struct
    (* Iterate over all the borrows/loans found in the abstractions and merge them *)
    let merge (borrow_to_content0 : Marked.borrow_content Map.t)
        (borrow_to_content1 : Marked.borrow_content Map.t)
        (loan_to_content0 : Marked.loan_content Map.t)
        (loan_to_content1 : Marked.loan_content Map.t)
        (borrows_loans : Set.elt borrow_or_loan list) : unit =
      List.iter
        (function
          | Borrow marked ->
              log#ldebug
                (lazy
                  ("merge_abstractions: merging borrow "
                 ^ Marked.to_string marked));

              (* Check if the borrow has already been merged - this can happen
                 because we go through all the borrows/loans in [abs0] *then*
                 all the borrows/loans in [abs1], and there may be duplicates
                 between the two *)
              if Marked.borrow_is_merged marked then ()
              else (
                Marked.set_borrow_as_merged marked;
                (* Check if we need to filter it *)
                if Marked.filter_marked marked then ()
                else
                  (* Lookup the contents *)
                  let bc0 = Map.find_opt marked borrow_to_content0 in
                  let bc1 = Map.find_opt marked borrow_to_content1 in
                  (* Merge *)
                  let av : typed_avalue =
                    match (bc0, bc1) with
                    | None, Some bc | Some bc, None ->
                        Marked.make_borrow_value marked bc
                    | Some _, Some _ ->
                        (* Because of markers, the case where the same borrow is duplicated should
                           be unreachable. Note, this is due to all shared borrows currently
                           taking different ids, this will not be the case anymore when shared loans
                           will take a unique id instead of a set *)
                        craise __FILE__ __LINE__ span "Unreachable"
                    | None, None -> craise __FILE__ __LINE__ span "Unreachable"
                  in
                  push_borrow_avalue av)
          | Loan marked ->
              if
                (* Check if the loan has already been treated - it can happen
                   for the same reason as for borrows, and also because shared
                   loans contain sets of borrows (meaning that when taking care
                   of one loan, we can merge several other loans at once).
                *)
                Marked.loan_is_merged marked
              then ()
              else (
                (* Do not set the loans as merged yet *)
                log#ldebug
                  (lazy
                    ("merge_abstractions: merging loan "
                   ^ Marked.to_string marked));
                (* Check if we need to filter it *)
                if Marked.filter_marked marked then ()
                else
                  (* Lookup the contents *)
                  let lc0 = Map.find_opt marked loan_to_content0 in
                  let lc1 = Map.find_opt marked loan_to_content1 in
                  (* Merge *)
                  let ml, av =
                    match (lc0, lc1) with
                    | None, Some lc | Some lc, None ->
                        Marked.make_loan_value marked lc
                    | Some _, Some _ ->
                        (* With projection markers, shared loans should not be duplicated *)
                        craise __FILE__ __LINE__ span "Unreachable"
                    | None, None -> craise __FILE__ __LINE__ span "Unreachable"
                  in
                  List.iter Marked.set_loan_as_merged ml;
                  push_loan_avalue av))
        borrows_loans
  end in
  (* First merge the concrete borrows/loans *)
  let module MergeConcrete =
    Merge (MarkedBorrowId.Set) (MarkedBorrowId.Map)
      (struct
        type borrow_content =
          ( ty * Values.borrow_content,
            ty * Values.aborrow_content )
          concrete_or_abs

        type loan_content =
          (ty * Values.loan_content, ty * Values.aloan_content) concrete_or_abs

        let to_string = MarkedBorrowId.to_string
        let borrow_is_merged = borrow_is_merged
        let loan_is_merged = loan_is_merged
        let filter_marked = filter_concrete
        let set_borrow_as_merged = set_borrow_as_merged
        let set_loan_as_merged = set_loan_as_merged

        let make_borrow_value _ bc : typed_avalue =
          match bc with
          | Concrete _ ->
              (* This can happen only in case of nested borrows - a concrete
                 borrow can only happen inside a shared loan *)
              craise __FILE__ __LINE__ span "Unreachable"
          | Abstract (ty, bc) -> { value = ABorrow bc; ty }

        let make_loan_value _ lc : marked_borrow_id list * typed_avalue =
          match lc with
          | Concrete _ ->
              (* This shouldn't happen because the avalues should
                 have been destructured. *)
              craise __FILE__ __LINE__ span "Unreachable"
          | Abstract (ty, lc) -> (
              match lc with
              | ASharedLoan (pm, bids, sv, child) ->
                  let bids = filter_bids pm bids in
                  sanity_check __FILE__ __LINE__
                    (not (BorrowId.Set.is_empty bids))
                    span;
                  sanity_check __FILE__ __LINE__ (is_aignored child.value) span;
                  sanity_check __FILE__ __LINE__
                    (not (value_has_loans_or_borrows (Some span) ctx sv.value))
                    span;
                  let marked_bids =
                    List.map (fun bid -> (pm, bid)) (BorrowId.Set.elements bids)
                  in
                  let lc = ASharedLoan (pm, bids, sv, child) in
                  (marked_bids, { value = ALoan lc; ty })
              | AMutLoan (pm, bid, _) ->
                  ([ (pm, bid) ], { value = ALoan lc; ty })
              | AEndedMutLoan _
              | AEndedSharedLoan _
              | AIgnoredMutLoan _
              | AEndedIgnoredMutLoan _
              | AIgnoredSharedLoan _ ->
                  (* The abstraction has been destructured, so those shouldn't appear *)
                  craise __FILE__ __LINE__ span "Unreachable")
      end)
  in
  (* Note that we first explore the borrows/loans of [abs0], because we
     want to merge *into* this abstraction, and as a consequence we want to
     preserve its structure as much as we can *)
  let borrows_loans = List.append borrows_loans0 borrows_loans1 in
  MergeConcrete.merge borrow_to_content0 borrow_to_content1 loan_to_content0
    loan_to_content1 borrows_loans;

  (* Do the same for the symbolic projections *)
  let borrows_loans = List.append borrow_loan_projs0 borrow_loan_projs1 in
  (* First merge the concrete borrows/loans *)
  let module MergeSymbolic =
    Merge (MarkedNormSymbProj.Set) (MarkedNormSymbProj.Map)
      (struct
        type borrow_content = ty * proj_marker * aproj
        type loan_content = ty * proj_marker * aproj

        let to_string = MarkedNormSymbProj.to_string
        let borrow_is_merged = borrow_proj_is_merged
        let loan_is_merged = loan_proj_is_merged
        let filter_marked = filter_symbolic
        let set_borrow_as_merged = set_borrow_proj_as_merged
        let set_loan_as_merged = set_loan_proj_as_merged

        let make_borrow_value _ (ty, pm, proj) =
          { value = ASymbolic (pm, proj); ty }

        let make_loan_value marked (ty, pm, proj) =
          ([ marked ], { value = ASymbolic (pm, proj); ty })
      end)
  in
  MergeSymbolic.merge borrow_proj_to_content0 borrow_proj_to_content1
    loan_proj_to_content0 loan_proj_to_content1 borrows_loans;

  (* Reverse the avalues (we visited the loans/borrows in order, but pushed
     new values at the beggining of the stack of avalues). Also note that we
     put the borrows, then the loans. *)
  List.rev !borrow_avalues @ List.rev !loan_avalues

(** Auxiliary function for {!merge_abstractions}.

    Phase 2 of the merge: we remove markers, by merging pairs of the same
    element with different markers into one element without markers.

    Example:
    {[
      |MB l0|, MB l1, ︙MB l0︙
           ~~>
      MB l0, MB l1
    ]}
 *)
let merge_abstractions_merge_markers (span : Meta.span)
    (merge_funs : merge_duplicates_funcs option) (ctx : eval_ctx)
    (owned_regions : RegionId.Set.t) (avalues : typed_avalue list) :
    typed_avalue list =
  log#ldebug
    (lazy
      ("merge_abstractions_merge_markers:\n- avalues:\n"
      ^ String.concat ", " (List.map (typed_avalue_to_string ctx) avalues)));

  (* We linearly traverse the list of avalues created through the first phase. *)

  (* Compute some relevant information *)
  let {
    loans = _;
    borrows = _;
    borrows_loans;
    loan_to_content;
    borrow_to_content;
    loan_projs = _;
    borrow_projs = _;
    borrow_loan_projs;
    loan_proj_to_content;
    borrow_proj_to_content;
  } =
    compute_merge_abstraction_info span ctx owned_regions avalues
  in

  (* Utilities to accumulate the list of values resulting from the merge *)
  let avalues = ref [] in
  let push_avalue av =
    log#ldebug
      (lazy
        ("merge_abstractions_merge_markers: push_avalue: "
        ^ typed_avalue_to_string ~span:(Some span) ctx av));
    avalues := av :: !avalues
  in

  (* We will merge elements with the same borrow/loan id, but with different markers.
     Hence, we only keep track of the id here: if [Borrow PLeft bid] has been merged
     and we see [Borrow PRight bid], we should ignore [Borrow PRight bid] (because
     when seeing [Borrow PLeft bid] we stored [Borrow PNone bid] into the list
     of values to insert in the resulting abstraction). *)
  let merged_borrows = ref BorrowId.Set.empty in
  let merged_loans = ref BorrowId.Set.empty in
  let merged_borrow_projs = ref NormSymbProj.Set.empty in
  let merged_loan_projs = ref NormSymbProj.Set.empty in

  let borrow_is_merged id = BorrowId.Set.mem id !merged_borrows in
  let set_borrow_as_merged id =
    merged_borrows := BorrowId.Set.add id !merged_borrows
  in

  let borrow_proj_is_merged m =
    NormSymbProj.Set.mem
      (marked_norm_symb_proj_to_unmarked m)
      !merged_borrow_projs
  in
  let set_borrow_proj_as_merged m =
    merged_borrow_projs :=
      NormSymbProj.Set.add
        (marked_norm_symb_proj_to_unmarked m)
        !merged_borrow_projs
  in

  let loan_is_merged id = BorrowId.Set.mem id !merged_loans in
  let set_loan_as_merged id =
    merged_loans := BorrowId.Set.add id !merged_loans
  in
  let set_loans_as_merged ids = BorrowId.Set.iter set_loan_as_merged ids in

  let loan_proj_is_merged m =
    NormSymbProj.Set.mem
      (marked_norm_symb_proj_to_unmarked m)
      !merged_loan_projs
  in
  let set_loan_proj_as_merged m =
    merged_loan_projs :=
      NormSymbProj.Set.add
        (marked_norm_symb_proj_to_unmarked m)
        !merged_loan_projs
  in

  (* Recreates an avalue from a borrow_content. *)
  let avalue_from_bc = function
    | Concrete (_, _) ->
        (* This can happen only in case of nested borrows, and should have been filtered during phase 1 *)
        craise __FILE__ __LINE__ span "Unreachable"
    | Abstract (ty, bc) -> { value = ABorrow bc; ty }
  in

  (* Recreates an avalue from a loan_content, and adds the set of loan ids as merged.
     See the comment in the loop below for a detailed explanation *)
  let avalue_from_lc = function
    | Concrete (_, _) ->
        (* This can happen only in case of nested borrows, and should have been filtered
           during phase 1 *)
        craise __FILE__ __LINE__ span "Unreachable"
    | Abstract (ty, bc) ->
        (match bc with
        | AMutLoan (_, id, _) -> set_loan_as_merged id
        | ASharedLoan (_, ids, _, _) -> set_loans_as_merged ids
        | _ -> craise __FILE__ __LINE__ span "Unreachable");
        { value = ALoan bc; ty }
  in

  (* Recreates an avalue from a borrow projector. *)
  let avalue_from_borrow_proj ((ty, pm, proj) : ty * proj_marker * aproj) :
      typed_avalue =
    { value = ASymbolic (pm, proj); ty }
  in

  (* Recreates an avalue from a loan_content, and adds the set of loan ids as merged.
     See the comment in the loop below for a detailed explanation *)
  let avalue_from_loan_proj ((ty, pm, proj) : ty * proj_marker * aproj) :
      typed_avalue =
    { value = ASymbolic (pm, proj); ty }
  in

  let complementary_markers pm0 pm1 =
    (pm0 = PLeft && pm1 = PRight) || (pm0 = PRight && pm1 = PLeft)
  in

  (* Some utility functions *)
  (* Merge two aborrow contents - note that those contents must have the same id *)
  let merge_aborrow_contents (ty0 : rty) (bc0 : aborrow_content) (ty1 : rty)
      (bc1 : aborrow_content) : typed_avalue =
    match (bc0, bc1) with
    | AMutBorrow (pm0, id0, child0), AMutBorrow (pm1, id1, child1) ->
        (* Sanity-check of the precondition *)
        sanity_check __FILE__ __LINE__ (complementary_markers pm0 pm1) span;
        sanity_check __FILE__ __LINE__ (id0 = id1) span;
        (Option.get merge_funs).merge_amut_borrows id0 ty0 pm0 child0 ty1 pm1
          child1
    | ASharedBorrow (pm0, id0), ASharedBorrow (pm1, id1) ->
        (* Sanity-check of the precondition *)
        sanity_check __FILE__ __LINE__ (complementary_markers pm0 pm1) span;
        sanity_check __FILE__ __LINE__ (id0 = id1) span;
        (Option.get merge_funs).merge_ashared_borrows id0 ty0 pm0 ty1 pm1
    | AProjSharedBorrow _, AProjSharedBorrow _ ->
        (* Unreachable because requires nested borrows *)
        craise __FILE__ __LINE__ span "Unreachable"
    | _ ->
        (* Unreachable because those cases are ignored (ended/ignored borrows)
           or inconsistent *)
        craise __FILE__ __LINE__ span "Unreachable"
  in

  let merge_g_borrow_contents (bc0 : g_borrow_content_with_ty)
      (bc1 : g_borrow_content_with_ty) : typed_avalue =
    match (bc0, bc1) with
    | Concrete _, Concrete _ ->
        (* This can happen only in case of nested borrows - the borrow has
           to appear inside a shared loan. *)
        craise __FILE__ __LINE__ span "Unreachable"
    | Abstract (ty0, bc0), Abstract (ty1, bc1) ->
        merge_aborrow_contents ty0 bc0 ty1 bc1
    | Concrete _, Abstract _ | Abstract _, Concrete _ ->
        (* TODO: is it really unreachable? *)
        craise __FILE__ __LINE__ span "Unreachable"
  in

  let loan_content_to_ids (lc : g_loan_content_with_ty) : BorrowId.Set.t =
    match lc with
    | Abstract (_, lc) -> (
        match lc with
        | AMutLoan (_, id, _) -> BorrowId.Set.singleton id
        | ASharedLoan (_, ids, _, _) -> ids
        | _ ->
            (* Unreachable because those cases are ignored (ended/ignored borrows)
               or inconsistent *)
            craise __FILE__ __LINE__ span "Unreachable")
    | Concrete _ ->
        (* Can only happen with nested borrows *)
        craise __FILE__ __LINE__ span "Unreachable"
  in

  let merge_aloan_contents (ty0 : rty) (lc0 : aloan_content) (ty1 : rty)
      (lc1 : aloan_content) : typed_avalue =
    match (lc0, lc1) with
    | AMutLoan (pm0, id0, child0), AMutLoan (pm1, id1, child1) ->
        (* Sanity-check of the precondition *)
        sanity_check __FILE__ __LINE__ (complementary_markers pm0 pm1) span;
        sanity_check __FILE__ __LINE__ (id0 = id1) span;
        (* Merge *)
        (Option.get merge_funs).merge_amut_loans id0 ty0 pm0 child0 ty1 pm1
          child1
    | ASharedLoan (pm0, ids0, sv0, child0), ASharedLoan (pm1, ids1, sv1, child1)
      ->
        (* Check that the sets of ids are the same - if it is not the case, it
           means we actually need to merge more than 2 avalues: we ignore this
           case for now *)
        sanity_check __FILE__ __LINE__ (complementary_markers pm0 pm1) span;
        sanity_check __FILE__ __LINE__ (BorrowId.Set.equal ids0 ids1) span;
        let ids = ids0 in
        (* Merge *)
        (Option.get merge_funs).merge_ashared_loans ids ty0 pm0 sv0 child0 ty1
          pm1 sv1 child1
    | _ ->
        (* Unreachable because those cases are ignored (ended/ignored borrows)
           or inconsistent *)
        craise __FILE__ __LINE__ span "Unreachable"
  in

  (* Note that because we may filter ids from a set of id, this function has
     to register the merged loan ids: the caller doesn't do it (contrary to
     the borrow case) *)
  let merge_g_loan_contents (lc0 : g_loan_content_with_ty)
      (lc1 : g_loan_content_with_ty) : typed_avalue =
    match (lc0, lc1) with
    | Concrete _, Concrete _ ->
        (* This can not happen: the values should have been destructured *)
        craise __FILE__ __LINE__ span "Unreachable"
    | Abstract (ty0, lc0), Abstract (ty1, lc1) ->
        merge_aloan_contents ty0 lc0 ty1 lc1
    | Concrete _, Abstract _ | Abstract _, Concrete _ ->
        (* TODO: is it really unreachable? *)
        craise __FILE__ __LINE__ span "Unreachable"
  in

  let merge_borrow_projs ((ty0, pm0, proj0) : ty * proj_marker * aproj)
      ((ty1, pm1, proj1) : ty * proj_marker * aproj) : typed_avalue =
    sanity_check __FILE__ __LINE__ (complementary_markers pm0 pm1) span;
    match (proj0, proj1) with
    | AProjBorrows (sv0, proj_ty0, child0), AProjBorrows (sv1, proj_ty1, child1)
      ->
        (* Sanity-check of the precondition *)
        sanity_check __FILE__ __LINE__ (sv0 = sv1) span;
        (* Merge *)
        (Option.get merge_funs).merge_aborrow_projs ty0 pm0 sv0 proj_ty0 child0
          ty1 pm1 sv1 proj_ty1 child1
    | _ ->
        (* Unreachable because those cases are ignored (ended/ignored borrows)
           or inconsistent *)
        craise __FILE__ __LINE__ span "Unreachable"
  in

  let merge_loan_projs ((ty0, pm0, proj0) : ty * proj_marker * aproj)
      ((ty1, pm1, proj1) : ty * proj_marker * aproj) : typed_avalue =
    sanity_check __FILE__ __LINE__ (complementary_markers pm0 pm1) span;
    match (proj0, proj1) with
    | AProjLoans (sv0, proj_ty0, child0), AProjLoans (sv1, proj_ty1, child1) ->
        (* Sanity-check of the precondition *)
        sanity_check __FILE__ __LINE__ (sv0 = sv1) span;
        (* Merge *)
        (Option.get merge_funs).merge_aloan_projs ty0 pm0 sv0 proj_ty0 child0
          ty1 pm1 sv1 proj_ty1 child1
    | _ ->
        (* Unreachable because those cases are ignored (ended/ignored borrows)
           or inconsistent *)
        craise __FILE__ __LINE__ span "Unreachable"
  in

  let invert_proj_marker = function
    | PNone -> craise __FILE__ __LINE__ span "Unreachable"
    | PLeft -> PRight
    | PRight -> PLeft
  in

  (* We now iter over all the accumulated elements. For each element with a marker
     (i.e., not [PNone]), we attempt to find the dual element in the rest of the list. If so,
     we remove both elements, and insert the same element but with no marker.

     Importantly, attempting the merge when first seeing a marked element allows us to preserve
     the structure of the abstraction we are merging into (i.e., abs0). Note that during phase 1,
     we traversed the borrow/loans of the abs 0 first, and hence these elements are at the top of
     the list. *)
  let module Merge
      (Set : Collections.Set)
      (Map : Collections.Map with type key = Set.elt)
      (Marked : sig
        type borrow_content
        type loan_content
        type loan_id_set

        val get_marker : Set.elt -> proj_marker
        val invert_marker : Set.elt -> Set.elt
        val borrow_is_merged : Set.elt -> bool
        val loan_is_merged : Set.elt -> bool
        val set_borrow_as_merged : Set.elt -> unit
        val set_loans_as_merged : loan_id_set -> unit
        val loan_content_to_ids : loan_content -> loan_id_set
        val avalue_from_bc : borrow_content -> typed_avalue
        val avalue_from_lc : loan_content -> typed_avalue

        val merge_borrow_contents :
          borrow_content -> borrow_content -> typed_avalue

        val merge_loan_contents : loan_content -> loan_content -> typed_avalue
      end) =
  struct
    let merge (borrow_to_content : Marked.borrow_content Map.t)
        (loan_to_content : Marked.loan_content Map.t) borrows_loans =
      List.iter
        (function
          | Borrow marked ->
              (* Case disjunction: no marker/marker *)
              if Marked.get_marker marked = PNone then begin
                sanity_check __FILE__ __LINE__
                  (not (Marked.borrow_is_merged marked))
                  span;
                (* This element has no marker. We do not filter it, hence we retrieve the
                   contents and inject it into the avalues list *)
                let bc = Map.find marked borrow_to_content in
                push_avalue (Marked.avalue_from_bc bc);
                (* Setting the borrow as merged is not really necessary but we do it
                   for consistency, and this allows us to do some sanity checks. *)
                Marked.set_borrow_as_merged marked
              end
              else if
                (* Check if the borrow has already been merged. If so, it means we already
                   added the merged value to the avalues list, and we can thus skip it *)
                Marked.borrow_is_merged marked
              then ()
              else (
                (* Not merged: set it as merged *)
                Marked.set_borrow_as_merged marked;
                (* Lookup the content of the borrow *)
                let bc0 = Map.find marked borrow_to_content in
                (* Check if there exists the same borrow but with the complementary marker *)
                let obc1 =
                  Map.find_opt (Marked.invert_marker marked) borrow_to_content
                in
                match obc1 with
                | None ->
                    (* No dual element found, we keep the current one in the list of avalues,
                       with the same marker *)
                    push_avalue (Marked.avalue_from_bc bc0)
                | Some bc1 ->
                    (* We have borrows with left and right markers in the environment.
                       We merge their values, and push the result to the list of avalues.
                       The merge will also remove the projection marker *)
                    push_avalue (Marked.merge_borrow_contents bc0 bc1))
          | Loan marked -> (
              if
                (* Case disjunction: no marker/marker *)
                Marked.get_marker marked = PNone
              then (
                if
                  (* Since we currently have a set of loan ids associated to a shared_borrow, we can
                     have several loan ids associated to the same element. Hence, we need to ensure
                     that we did not previously add the corresponding element.

                     To do so, we use the loan id merged set for both marked and unmarked values.
                     The assumption is that we should not have the same loan id for both an unmarked
                     element and a marked element. It might be better to sanity-check this.

                     Adding the loan id to the merged set will be done inside avalue_from_lc.

                     Remark: Once we move to a single loan id per shared_loan, this should not
                     be needed anymore.
                  *)
                  Marked.loan_is_merged marked
                then ()
                else
                  let lc = Map.find marked loan_to_content in
                  push_avalue (Marked.avalue_from_lc lc);
                  (* Mark as merged *)
                  let ids = Marked.loan_content_to_ids lc in
                  Marked.set_loans_as_merged ids)
              else if
                (* Check if the loan has already been merged. If so, we skip it. *)
                Marked.loan_is_merged marked
              then ()
              else
                let lc0 = Map.find marked loan_to_content in
                let olc1 =
                  Map.find_opt (Marked.invert_marker marked) loan_to_content
                in
                (* Mark as merged *)
                let ids0 = Marked.loan_content_to_ids lc0 in
                Marked.set_loans_as_merged ids0;
                match olc1 with
                | None ->
                    (* No dual element found, we keep the current one with the same marker *)
                    push_avalue (Marked.avalue_from_lc lc0)
                | Some lc1 ->
                    push_avalue (Marked.merge_loan_contents lc0 lc1);
                    (* Mark as merged *)
                    let ids1 = Marked.loan_content_to_ids lc1 in
                    Marked.set_loans_as_merged ids1))
        borrows_loans
  end in
  (* Merge the concrete borrows/loans *)
  let module MergeConcrete =
    Merge (MarkedBorrowId.Set) (MarkedBorrowId.Map)
      (struct
        type borrow_content = g_borrow_content_with_ty
        type loan_content = g_loan_content_with_ty
        type loan_id_set = Values.loan_id_set

        let get_marker (pm, _) = pm
        let invert_marker (pm, bid) = (invert_proj_marker pm, bid)
        let borrow_is_merged (_, bid) = borrow_is_merged bid
        let loan_is_merged (_, bid) = loan_is_merged bid
        let set_borrow_as_merged (_, bid) = set_borrow_as_merged bid
        let set_loans_as_merged bids = set_loans_as_merged bids
        let loan_content_to_ids = loan_content_to_ids
        let avalue_from_bc = avalue_from_bc
        let avalue_from_lc = avalue_from_lc
        let merge_borrow_contents = merge_g_borrow_contents
        let merge_loan_contents = merge_g_loan_contents
      end)
  in
  MergeConcrete.merge borrow_to_content loan_to_content borrows_loans;

  (* Merge the symbolic borrows/loans *)
  let module MergeSymbolic =
    Merge (MarkedNormSymbProj.Set) (MarkedNormSymbProj.Map)
      (struct
        type borrow_content = ty * proj_marker * aproj
        type loan_content = ty * proj_marker * aproj
        type loan_id_set = marked_norm_symb_proj

        let get_marker marked = marked.pm

        let invert_marker marked =
          { marked with pm = invert_proj_marker marked.pm }

        let borrow_is_merged marked = borrow_proj_is_merged marked
        let loan_is_merged marked = loan_proj_is_merged marked
        let set_borrow_as_merged marked = set_borrow_proj_as_merged marked
        let set_loans_as_merged bids = set_loan_proj_as_merged bids

        let loan_content_to_ids ((_, pm, proj) : ty * proj_marker * aproj) :
            marked_norm_symb_proj =
          match proj with
          | AProjLoans (sv, proj_ty, _) ->
              let norm_proj_ty = normalize_proj_ty owned_regions proj_ty in
              { pm; sv_id = sv.sv_id; norm_proj_ty }
          | _ -> internal_error __FILE__ __LINE__ span

        let avalue_from_bc = avalue_from_borrow_proj
        let avalue_from_lc = avalue_from_loan_proj
        let merge_borrow_contents = merge_borrow_projs
        let merge_loan_contents = merge_loan_projs
      end)
  in
  MergeSymbolic.merge borrow_proj_to_content loan_proj_to_content
    borrow_loan_projs;

  (* Reorder the avalues. We want the avalues to have the borrows first, then
     the loans (this structure is more stable when we merge abstractions together,
     meaning it is easier to find fixed points).
  *)
  let avalues = List.rev !avalues in
  let is_borrow (av : typed_avalue) : bool =
    match av.value with
    | ABorrow _ | ASymbolic (_, AProjBorrows _) -> true
    | ALoan _ | ASymbolic (_, AProjLoans _) -> false
    | _ -> craise __FILE__ __LINE__ span "Unexpected"
  in
  let aborrows, aloans = List.partition is_borrow avalues in
  List.append aborrows aloans

(** Auxiliary function.

    Merge two abstractions into one, without updating the context.
 *)
let merge_abstractions (span : Meta.span) (abs_kind : abs_kind) (can_end : bool)
    (merge_funs : merge_duplicates_funcs option) (ctx : eval_ctx) (abs0 : abs)
    (abs1 : abs) : abs =
  log#ldebug
    (lazy
      ("merge_abstractions:\n- abs0:\n"
      ^ abs_to_string span ctx abs0
      ^ "\n\n- abs1:\n"
      ^ abs_to_string span ctx abs1));
  (* Sanity check: we can't merge an abstraction with itself *)
  sanity_check __FILE__ __LINE__ (abs0.abs_id <> abs1.abs_id) span;

  (* Check that the abstractions are destructured (i.e., there are no nested
     values, etc.) *)
  if !Config.sanity_checks then (
    let destructure_shared_values = true in
    sanity_check __FILE__ __LINE__
      (abs_is_destructured span destructure_shared_values ctx abs0)
      span;
    sanity_check __FILE__ __LINE__
      (abs_is_destructured span destructure_shared_values ctx abs1)
      span);

  (* Compute the ancestor regions, owned regions, etc.
     Note that one of the two abstractions might a parent of the other *)
  let parents =
    AbstractionId.Set.diff
      (AbstractionId.Set.union abs0.parents abs1.parents)
      (AbstractionId.Set.of_list [ abs0.abs_id; abs1.abs_id ])
  in
  let original_parents = AbstractionId.Set.elements parents in
  let regions =
    let owned = RegionId.Set.union abs0.regions.owned abs1.regions.owned in
    let ancestors =
      RegionId.Set.diff
        (RegionId.Set.union abs0.regions.ancestors abs1.regions.ancestors)
        owned
    in
    { owned; ancestors }
  in

  (* Phase 1: simplify the loans coming from the left abstraction with
     the borrows coming from the right abstraction. *)
  let avalues =
    merge_abstractions_merge_loan_borrow_pairs span merge_funs ctx abs0 abs1
  in

  (* Phase 2: we now remove markers, by merging pairs of the same element with
     different markers into one element. To do so, we linearly traverse the list
     of avalues created through the first phase. *)
  let avalues =
    merge_abstractions_merge_markers span merge_funs ctx regions.owned avalues
  in

  (* Create the new abstraction *)
  let abs_id = fresh_abstraction_id () in
  let abs =
    {
      abs_id;
      kind = abs_kind;
      can_end;
      parents;
      original_parents;
      regions;
      avalues;
    }
  in

  (* Sanity check *)
  sanity_check __FILE__ __LINE__ (abs_is_destructured span true ctx abs) span;
  (* Return *)
  abs

(** Merge the regions in a context to a single region *)
let ctx_merge_regions (ctx : eval_ctx) (rid : RegionId.id)
    (rids : RegionId.Set.t) : eval_ctx =
  let rsubst x = if RegionId.Set.mem x rids then rid else x in
  let env = Substitute.env_subst_rids rsubst ctx.env in
  { ctx with env }

let merge_into_first_abstraction (span : Meta.span) (abs_kind : abs_kind)
    (can_end : bool) (merge_funs : merge_duplicates_funcs option)
    (ctx : eval_ctx) (abs_id0 : AbstractionId.id) (abs_id1 : AbstractionId.id) :
    eval_ctx * AbstractionId.id =
  (* Small sanity check *)
  sanity_check __FILE__ __LINE__ (abs_id0 <> abs_id1) span;

  (* Lookup the abstractions *)
  let abs0 = ctx_lookup_abs ctx abs_id0 in
  let abs1 = ctx_lookup_abs ctx abs_id1 in

  (* Merge them *)
  let nabs =
    merge_abstractions span abs_kind can_end merge_funs ctx abs0 abs1
  in

  (* Update the environment: replace the abstraction 0 with the result of the merge,
     remove the abstraction 1 *)
  let ctx = fst (ctx_subst_abs span ctx abs_id0 nabs) in
  let ctx = fst (ctx_remove_abs span ctx abs_id1) in

  (* Merge all the regions from the abstraction into one (the first - i.e., the
     one with the smallest id). Note that we need to do this in the whole
     environment, as those regions may be referenced as ancestor regions by
     the other abstractions, and may be present in symbolic values, etc. (this
     is not the case if there are no nested borrows, but we anticipate).
  *)
  let ctx =
    let regions = nabs.regions.owned in
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

(** Reorder the loans and borrows inside the fresh abstractions.

    See {!reorder_fresh_abs}.
 *)
let reorder_loans_borrows_in_fresh_abs (span : Meta.span) (allow_markers : bool)
    (old_abs_ids : AbstractionId.Set.t) (ctx : eval_ctx) : eval_ctx =
  let reorder_in_fresh_abs (abs : abs) : abs =
    (* Split between the loans and borrows, and between the concrete
       and symbolic values. *)
    let is_borrow (av : typed_avalue) : bool =
      match av.value with
      | ABorrow _ | ASymbolic (_, AProjBorrows _) -> true
      | ALoan _ | ASymbolic (_, AProjLoans _) -> false
      | _ -> craise __FILE__ __LINE__ span "Unexpected"
    in
    let is_concrete (av : typed_avalue) : bool =
      match av.value with
      | ABorrow _ | ALoan _ -> true
      | ASymbolic (_, (AProjBorrows _ | AProjLoans _)) -> false
      | _ -> craise __FILE__ __LINE__ span "Unexpected"
    in
    let aborrows, aloans = List.partition is_borrow abs.avalues in
    let aborrows, borrow_projs = List.partition is_concrete aborrows in
    let aloans, loan_projs = List.partition is_concrete aloans in

    (* Reoder the borrows, and the loans.

       After experimenting, it seems that a good way of reordering the loans
       and the borrows to find fixed points is simply to sort them by increasing
       order of id (taking the smallest id of a set of ids, in case of sets).

       This is actually not as arbitrary as it might seem, because the ids give
       us the order in which we introduced those borrows/loans.

       We do the same thing for the symbolic values: we use the symbolic ids.
       The final order is:
         borrows, borrow projectors, loans, loan projectors
       (all sorted by increasing id)
    *)
    let get_borrow_id (av : typed_avalue) : BorrowId.id =
      match av.value with
      | ABorrow (AMutBorrow (pm, bid, _) | ASharedBorrow (pm, bid)) ->
          sanity_check __FILE__ __LINE__ (allow_markers || pm = PNone) span;
          bid
      | _ -> craise __FILE__ __LINE__ span "Unexpected"
    in
    let get_loan_id (av : typed_avalue) : BorrowId.id =
      match av.value with
      | ALoan (AMutLoan (pm, lid, _)) ->
          sanity_check __FILE__ __LINE__ (allow_markers || pm = PNone) span;
          lid
      | ALoan (ASharedLoan (pm, lids, _, _)) ->
          sanity_check __FILE__ __LINE__ (allow_markers || pm = PNone) span;
          BorrowId.Set.min_elt lids
      | _ -> craise __FILE__ __LINE__ span "Unexpected"
    in
    let get_symbolic_id (av : typed_avalue) : SymbolicValueId.id =
      match av.value with
      | ASymbolic (pm, aproj) -> begin
          sanity_check __FILE__ __LINE__ (allow_markers || pm = PNone) span;
          match aproj with
          | AProjLoans (sv, _, _) | AProjBorrows (sv, _, _) -> sv.sv_id
          | _ -> craise __FILE__ __LINE__ span "Unexpected"
        end
      | _ -> craise __FILE__ __LINE__ span "Unexpected"
    in
    let compare_pair :
          'a. ('a -> 'a -> int) -> 'a * typed_avalue -> 'a * typed_avalue -> int
        =
     fun compare_id x y ->
      let fst = compare_id (fst x) (fst y) in
      cassert __FILE__ __LINE__ (fst <> 0) span
        ("Unexpected: can't compare: '"
        ^ typed_avalue_to_string ctx (snd x)
        ^ "' with '"
        ^ typed_avalue_to_string ctx (snd y)
        ^ "'");
      fst
    in
    (* We use ordered maps to reorder the borrows and loans *)
    let reorder :
          'a.
          (typed_avalue -> 'a) ->
          ('a -> 'a -> int) ->
          typed_avalue list ->
          typed_avalue list =
     fun get_id compare_id values ->
      let values = List.map (fun v -> (get_id v, v)) values in
      List.map snd (List.stable_sort (compare_pair compare_id) values)
    in
    let aborrows = reorder get_borrow_id compare_borrow_id aborrows in
    let borrow_projs =
      reorder get_symbolic_id compare_symbolic_value_id borrow_projs
    in
    let aloans = reorder get_loan_id compare_borrow_id aloans in
    let loan_projs =
      reorder get_symbolic_id compare_symbolic_value_id loan_projs
    in
    let avalues = List.concat [ aborrows; borrow_projs; aloans; loan_projs ] in
    { abs with avalues }
  in

  let reorder_in_abs (abs : abs) =
    if AbstractionId.Set.mem abs.abs_id old_abs_ids then abs
    else reorder_in_fresh_abs abs
  in

  let env = env_map_abs reorder_in_abs ctx.env in

  { ctx with env }

type typed_avalue_list = typed_avalue list [@@deriving ord, show]

module OrderedTypedAvalueList :
  Collections.OrderedType with type t = typed_avalue list = struct
  type t = typed_avalue_list

  let compare x y = compare_typed_avalue_list x y
  let to_string x = show_typed_avalue_list x
  let pp_t fmt x = Format.pp_print_string fmt (show_typed_avalue_list x)
  let show_t x = show_typed_avalue_list x
end

let reorder_fresh_abs_aux (span : Meta.span) (old_abs_ids : AbstractionId.Set.t)
    (ctx : eval_ctx) : eval_ctx =
  (* Split between the fresh abstractions and the rest of the context *)
  let env, fresh_abs =
    List.partition
      (function
        | EAbs abs -> AbstractionId.Set.mem abs.abs_id old_abs_ids
        | _ -> true)
      ctx.env
  in

  (* Reorder the fresh abstractions.

     We use the content of the abstractions to reorder them.
     In practice, this allows us to reorder the abstractions by using the ids
     of the loans, borrows and symbolic values. This is far from perfect, but
     allows us to have a quite simple matching algorithm for now, to compute
     the joins as well as to check whether two environments are equivalent.
     We may want to make this algorithm more general in the future.
  *)
  let cmp abs0 abs1 =
    match (abs0, abs1) with
    | EAbs abs0, EAbs abs1 ->
        compare_typed_avalue_list abs0.avalues abs1.avalues
    | _ -> internal_error __FILE__ __LINE__ span
  in
  let fresh_abs = List.sort cmp fresh_abs |> List.rev in

  (* Reconstruct the environment *)
  let env = fresh_abs @ env in

  { ctx with env }

let reorder_fresh_abs (span : Meta.span) (allow_markers : bool)
    (old_abs_ids : AbstractionId.Set.t) (ctx : eval_ctx) : eval_ctx =
  reorder_loans_borrows_in_fresh_abs span allow_markers old_abs_ids ctx
  |> reorder_fresh_abs_aux span old_abs_ids
