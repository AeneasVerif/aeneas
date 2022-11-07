module T = Types
module V = Values
module E = Expressions
module C = Contexts
module Subst = Substitute
module L = Logging
open TypesUtils
open InterpreterUtils
open InterpreterBorrowsCore

(** The local logger *)
let log = L.projectors_log

let rec apply_proj_borrows_on_shared_borrow (ctx : C.eval_ctx)
    (fresh_reborrow : V.BorrowId.id -> V.BorrowId.id)
    (regions : T.RegionId.Set.t) (v : V.typed_value) (ty : T.rty) :
    V.abstract_shared_borrows =
  (* Sanity check - TODO: move this elsewhere (here we perform the check at every
   * recursive call which is a bit overkill...) *)
  let ety = Subst.erase_regions ty in
  assert (ety = v.V.ty);
  (* Project - if there are no regions from the abstraction in the type, return [_] *)
  if not (ty_has_regions_in_set regions ty) then []
  else
    match (v.V.value, ty) with
    | V.Primitive _, (T.Bool | T.Char | T.Integer _ | T.Str) -> []
    | V.Adt adt, T.Adt (id, region_params, tys) ->
        (* Retrieve the types of the fields *)
        let field_types =
          Subst.ctx_adt_value_get_instantiated_field_rtypes ctx adt id
            region_params tys
        in
        (* Project over the field values *)
        let fields_types = List.combine adt.V.field_values field_types in
        let proj_fields =
          List.map
            (fun (fv, fty) ->
              apply_proj_borrows_on_shared_borrow ctx fresh_reborrow regions fv
                fty)
            fields_types
        in
        List.concat proj_fields
    | V.Bottom, _ -> raise (Failure "Unreachable")
    | V.Borrow bc, T.Ref (r, ref_ty, kind) ->
        (* Retrieve the bid of the borrow and the asb of the projected borrowed value *)
        let bid, asb =
          (* Not in the set: dive *)
          match (bc, kind) with
          | V.MutBorrow (bid, bv), T.Mut ->
              (* Apply the projection on the borrowed value *)
              let asb =
                apply_proj_borrows_on_shared_borrow ctx fresh_reborrow regions
                  bv ref_ty
              in
              (bid, asb)
          | V.SharedBorrow (_, bid), T.Shared ->
              (* Lookup the shared value *)
              let ek = ek_all in
              let sv = lookup_loan ek bid ctx in
              let asb =
                match sv with
                | _, Concrete (V.SharedLoan (_, sv))
                | _, Abstract (V.ASharedLoan (_, sv, _)) ->
                    apply_proj_borrows_on_shared_borrow ctx fresh_reborrow
                      regions sv ref_ty
                | _ -> raise (Failure "Unexpected")
              in
              (bid, asb)
          | V.ReservedMutBorrow _, _ ->
              raise
                (Failure
                   "Can't apply a proj_borrow over a reserved mutable \
                    borrow")
          | _ -> raise (Failure "Unreachable")
        in
        let asb =
          (* Check if the region is in the set of projected regions (note that
           * we never project over static regions) *)
          if region_in_set r regions then
            let bid' = fresh_reborrow bid in
            V.AsbBorrow bid' :: asb
          else asb
        in
        asb
    | V.Loan _, _ -> raise (Failure "Unreachable")
    | V.Symbolic s, _ ->
        (* Check that the projection doesn't contain ended regions *)
        assert (
          not (projections_intersect s.V.sv_ty ctx.ended_regions ty regions));
        [ V.AsbProjReborrows (s, ty) ]
    | _ -> raise (Failure "Unreachable")

let rec apply_proj_borrows (check_symbolic_no_ended : bool) (ctx : C.eval_ctx)
    (fresh_reborrow : V.BorrowId.id -> V.BorrowId.id)
    (regions : T.RegionId.Set.t) (ancestors_regions : T.RegionId.Set.t)
    (v : V.typed_value) (ty : T.rty) : V.typed_avalue =
  (* Sanity check - TODO: move this elsewhere (here we perform the check at every
   * recursive call which is a bit overkill...) *)
  let ety = Substitute.erase_regions ty in
  assert (ety = v.V.ty);
  (* Project - if there are no regions from the abstraction in the type, return [_] *)
  if not (ty_has_regions_in_set regions ty) then { V.value = V.AIgnored; ty }
  else
    let value : V.avalue =
      match (v.V.value, ty) with
      | V.Primitive cv, (T.Bool | T.Char | T.Integer _ | T.Str) ->
          V.APrimitive cv
      | V.Adt adt, T.Adt (id, region_params, tys) ->
          (* Retrieve the types of the fields *)
          let field_types =
            Subst.ctx_adt_value_get_instantiated_field_rtypes ctx adt id
              region_params tys
          in
          (* Project over the field values *)
          let fields_types = List.combine adt.V.field_values field_types in
          let proj_fields =
            List.map
              (fun (fv, fty) ->
                apply_proj_borrows check_symbolic_no_ended ctx fresh_reborrow
                  regions ancestors_regions fv fty)
              fields_types
          in
          V.AAdt { V.variant_id = adt.V.variant_id; field_values = proj_fields }
      | V.Bottom, _ -> raise (Failure "Unreachable")
      | V.Borrow bc, T.Ref (r, ref_ty, kind) ->
          if
            (* Check if the region is in the set of projected regions (note that
             * we never project over static regions) *)
            region_in_set r regions
          then
            (* In the set *)
            let bc =
              match (bc, kind) with
              | V.MutBorrow (bid, bv), T.Mut ->
                  (* Remember the borrowed value we are about to project as a meta-value *)
                  let mv = bv in
                  (* Apply the projection on the borrowed value *)
                  let bv =
                    apply_proj_borrows check_symbolic_no_ended ctx
                      fresh_reborrow regions ancestors_regions bv ref_ty
                  in
                  V.AMutBorrow (mv, bid, bv)
              | V.SharedBorrow (_, bid), T.Shared -> V.ASharedBorrow bid
              | V.ReservedMutBorrow _, _ ->
                  raise
                    (Failure
                       "Can't apply a proj_borrow over a reserved mutable \
                        borrow")
              | _ -> raise (Failure "Unreachable")
            in
            V.ABorrow bc
          else
            (* Not in the set: ignore *)
            let bc =
              match (bc, kind) with
              | V.MutBorrow (bid, bv), T.Mut ->
                  (* Apply the projection on the borrowed value *)
                  let bv =
                    apply_proj_borrows check_symbolic_no_ended ctx
                      fresh_reborrow regions ancestors_regions bv ref_ty
                  in
                  (* If the borrow id is in the ancestor's regions, we still need
                   * to remember it *)
                  let opt_bid =
                    if region_in_set r ancestors_regions then Some bid else None
                  in
                  (* Return *)
                  V.AIgnoredMutBorrow (opt_bid, bv)
              | V.SharedBorrow (_, bid), T.Shared ->
                  (* Lookup the shared value *)
                  let ek = ek_all in
                  let sv = lookup_loan ek bid ctx in
                  let asb =
                    match sv with
                    | _, Concrete (V.SharedLoan (_, sv))
                    | _, Abstract (V.ASharedLoan (_, sv, _)) ->
                        apply_proj_borrows_on_shared_borrow ctx fresh_reborrow
                          regions sv ref_ty
                    | _ -> raise (Failure "Unexpected")
                  in
                  V.AProjSharedBorrow asb
              | V.ReservedMutBorrow _, _ ->
                  raise
                    (Failure
                       "Can't apply a proj_borrow over a reserved mutable \
                        borrow")
              | _ -> raise (Failure "Unreachable")
            in
            V.ABorrow bc
      | V.Loan _, _ -> raise (Failure "Unreachable")
      | V.Symbolic s, _ ->
          (* Check that the projection doesn't contain already ended regions,
           * if necessary *)
          if check_symbolic_no_ended then (
            let ty1 = s.V.sv_ty in
            let rset1 = ctx.ended_regions in
            let ty2 = ty in
            let rset2 = regions in
            log#ldebug
              (lazy
                ("projections_intersect:" ^ "\n- ty1: " ^ rty_to_string ctx ty1
               ^ "\n- rset1: "
                ^ T.RegionId.Set.to_string None rset1
                ^ "\n- ty2: " ^ rty_to_string ctx ty2 ^ "\n- rset2: "
                ^ T.RegionId.Set.to_string None rset2
                ^ "\n"));
            assert (not (projections_intersect ty1 rset1 ty2 rset2)));
          V.ASymbolic (V.AProjBorrows (s, ty))
      | _ ->
          log#lerror
            (lazy
              ("apply_proj_borrows: unexpected inputs:\n- input value: "
              ^ typed_value_to_string ctx v
              ^ "\n- proj rty: " ^ rty_to_string ctx ty));
          raise (Failure "Unreachable")
    in
    { V.value; V.ty }

let symbolic_expansion_non_borrow_to_value (sv : V.symbolic_value)
    (see : V.symbolic_expansion) : V.typed_value =
  let ty = Subst.erase_regions sv.V.sv_ty in
  let value =
    match see with
    | SePrimitive cv -> V.Primitive cv
    | SeAdt (variant_id, field_values) ->
        let field_values =
          List.map mk_typed_value_from_symbolic_value field_values
        in
        V.Adt { V.variant_id; V.field_values }
    | SeMutRef (_, _) | SeSharedRef (_, _) ->
        raise (Failure "Unexpected symbolic reference expansion")
  in
  { V.value; V.ty }

let symbolic_expansion_non_shared_borrow_to_value (sv : V.symbolic_value)
    (see : V.symbolic_expansion) : V.typed_value =
  match see with
  | SeMutRef (bid, bv) ->
      let ty = Subst.erase_regions sv.V.sv_ty in
      let bv = mk_typed_value_from_symbolic_value bv in
      let value = V.Borrow (V.MutBorrow (bid, bv)) in
      { V.value; ty }
  | SeSharedRef (_, _) ->
      raise (Failure "Unexpected symbolic shared reference expansion")
  | _ -> symbolic_expansion_non_borrow_to_value sv see

(** Apply (and reduce) a projector over loans to a value.

    TODO: detailed comments. See [apply_proj_borrows]
*)
let apply_proj_loans_on_symbolic_expansion (regions : T.RegionId.Set.t)
    (see : V.symbolic_expansion) (original_sv_ty : T.rty) : V.typed_avalue =
  (* Sanity check: if we have a proj_loans over a symbolic value, it should
   * contain regions which we will project *)
  assert (ty_has_regions_in_set regions original_sv_ty);
  (* Match *)
  let (value, ty) : V.avalue * T.rty =
    match (see, original_sv_ty) with
    | SePrimitive _, (T.Bool | T.Char | T.Integer _ | T.Str) ->
        (V.AIgnored, original_sv_ty)
    | SeAdt (variant_id, field_values), T.Adt (_id, _region_params, _tys) ->
        (* Project over the field values *)
        let field_values =
          List.map
            (mk_aproj_loans_value_from_symbolic_value regions)
            field_values
        in
        (V.AAdt { V.variant_id; field_values }, original_sv_ty)
    | SeMutRef (bid, spc), T.Ref (r, ref_ty, T.Mut) ->
        (* Sanity check *)
        assert (spc.V.sv_ty = ref_ty);
        (* Apply the projector to the borrowed value *)
        let child_av = mk_aproj_loans_value_from_symbolic_value regions spc in
        (* Check if the region is in the set of projected regions (note that
         * we never project over static regions) *)
        if region_in_set r regions then
          (* In the set: keep *)
          (V.ALoan (V.AMutLoan (bid, child_av)), ref_ty)
        else
          (* Not in the set: ignore *)
          (V.ALoan (V.AIgnoredMutLoan (bid, child_av)), ref_ty)
    | SeSharedRef (bids, spc), T.Ref (r, ref_ty, T.Shared) ->
        (* Sanity check *)
        assert (spc.V.sv_ty = ref_ty);
        (* Apply the projector to the borrowed value *)
        let child_av = mk_aproj_loans_value_from_symbolic_value regions spc in
        (* Check if the region is in the set of projected regions (note that
         * we never project over static regions) *)
        if region_in_set r regions then
          (* In the set: keep *)
          let shared_value = mk_typed_value_from_symbolic_value spc in
          (V.ALoan (V.ASharedLoan (bids, shared_value, child_av)), ref_ty)
        else
          (* Not in the set: ignore *)
          (V.ALoan (V.AIgnoredSharedLoan child_av), ref_ty)
    | _ -> raise (Failure "Unreachable")
  in
  { V.value; V.ty }

(** Auxiliary function. See [give_back_value].

    Apply reborrows to a context.

    The [reborrows] input is a list of pairs (shared loan id, id to insert
    in the shared loan).
    This function is used when applying projectors on shared borrows: when
    doing so, we might need to reborrow subvalues from the shared value.
    For instance:
    {[
      fn f<'a,'b,'c>(x : &'a 'b 'c u32)
    ]}
    When introducing the abstractions for 'a, 'b and 'c, we apply a projector
    on some value [shared_borrow l : &'a &'b &'c u32].
    In the 'a abstraction, this shared borrow gets projected. However, when
    reducing the projectors for the 'b and 'c abstractions, we need to make
    sure that the borrows living in regions 'b and 'c live as long as those
    regions. This is done by looking up the shared value and applying reborrows
    on the borrows we find there (note that those reborrows apply on shared
    borrows - easy - and mutable borrows - in this case, we reborrow the whole
    borrow: [mut_borrow ... ~~> shared_loan {...} (mut_borrow ...)]).
*)
let apply_reborrows (reborrows : (V.BorrowId.id * V.BorrowId.id) list)
    (ctx : C.eval_ctx) : C.eval_ctx =
  (* This is a bit brutal, but whenever we insert a reborrow, we remove
   * it from the list. This allows us to check that all the reborrows were
   * applied before returning.
   * We might reimplement that in a more efficient manner by using maps. *)
  let reborrows = ref reborrows in

  (* Check if a value is a mutable borrow, and return its identifier if
     it is the case *)
  let get_borrow_in_mut_borrow (v : V.typed_value) : V.BorrowId.id option =
    match v.V.value with
    | V.Borrow lc -> (
        match lc with
        | V.SharedBorrow (_, _) | V.ReservedMutBorrow _ -> None
        | V.MutBorrow (id, _) -> Some id)
    | _ -> None
  in

  (* Add the proper reborrows to a set of borrow ids (for a shared loan) *)
  let insert_reborrows bids =
    (* Find the reborrows to apply *)
    let insert, reborrows' =
      List.partition (fun (bid, _) -> V.BorrowId.Set.mem bid bids) !reborrows
    in
    reborrows := reborrows';
    let insert = List.map snd insert in
    (* Insert the borrows *)
    List.fold_left (fun bids bid -> V.BorrowId.Set.add bid bids) bids insert
  in

  (* Get the list of reborrows for a given borrow id *)
  let get_reborrows_for_bid bid =
    (* Find the reborrows to apply *)
    let insert, reborrows' =
      List.partition (fun (bid', _) -> bid' = bid) !reborrows
    in
    reborrows := reborrows';
    List.map snd insert
  in

  let borrows_to_set bids =
    List.fold_left
      (fun bids bid -> V.BorrowId.Set.add bid bids)
      V.BorrowId.Set.empty bids
  in

  (* Insert reborrows for a given borrow id into a given set of borrows *)
  let insert_reborrows_for_bid bids bid =
    (* Find the reborrows to apply *)
    let insert = get_reborrows_for_bid bid in
    (* Insert the borrows *)
    List.fold_left (fun bids bid -> V.BorrowId.Set.add bid bids) bids insert
  in

  let obj =
    object
      inherit [_] C.map_eval_ctx as super

      (** We may need to reborrow mutable borrows. Note that this doesn't
          happen for aborrows *)
      method! visit_typed_value env v =
        match v.V.value with
        | V.Borrow (V.MutBorrow (bid, bv)) ->
            let insert = get_reborrows_for_bid bid in
            let nbc = super#visit_MutBorrow env bid bv in
            let nbc = { v with V.value = V.Borrow nbc } in
            if insert = [] then (* No reborrows: do nothing special *)
              nbc
            else
              (* There are reborrows: insert a shared loan *)
              let insert = borrows_to_set insert in
              let value = V.Loan (V.SharedLoan (insert, nbc)) in
              let ty = v.V.ty in
              { V.value; ty }
        | _ -> super#visit_typed_value env v

      (** We reimplement {!visit_loan_content} (rather than one of the sub-
          functions) on purpose: exhaustive matches are good for maintenance *)
      method! visit_loan_content env lc =
        match lc with
        | V.SharedLoan (bids, sv) ->
            (* Insert the reborrows *)
            let bids = insert_reborrows bids in
            (* Check if the contained value is a mutable borrow, in which
             * case we might need to reborrow it by adding more borrow ids
             * to the current set of borrows - by doing this small
             * manipulation here, we accumulate the borrow ids in the same
             * shared loan, right above the mutable borrow, and avoid
             * stacking shared loans (note that doing this is not a problem
             * from a soundness point of view, but it is a bit ugly...) *)
            let bids =
              match get_borrow_in_mut_borrow sv with
              | None -> bids
              | Some bid -> insert_reborrows_for_bid bids bid
            in
            (* Update and explore *)
            super#visit_SharedLoan env bids sv
        | V.MutLoan bid ->
            (* Nothing special to do *)
            super#visit_MutLoan env bid

      method! visit_aloan_content env lc =
        match lc with
        | V.ASharedLoan (bids, sv, av) ->
            (* Insert the reborrows *)
            let bids = insert_reborrows bids in
            (* Similarly to the non-abstraction case: check if the shared
             * value is a mutable borrow, to eventually insert more reborrows *)
            (* Update and explore *)
            let bids =
              match get_borrow_in_mut_borrow sv with
              | None -> bids
              | Some bid -> insert_reborrows_for_bid bids bid
            in
            (* Update and explore *)
            super#visit_ASharedLoan env bids sv av
        | V.AIgnoredSharedLoan _
        | V.AMutLoan (_, _)
        | V.AEndedMutLoan { given_back = _; child = _; given_back_meta = _ }
        | V.AEndedSharedLoan (_, _)
        | V.AIgnoredMutLoan (_, _)
        | V.AEndedIgnoredMutLoan
            { given_back = _; child = _; given_back_meta = _ } ->
            (* Nothing particular to do *)
            super#visit_aloan_content env lc
    end
  in

  (* Visit *)
  let ctx = obj#visit_eval_ctx () ctx in
  (* Check that there are no reborrows remaining *)
  assert (!reborrows = []);
  (* Return *)
  ctx

let prepare_reborrows (config : C.config) (allow_reborrows : bool) :
    (V.BorrowId.id -> V.BorrowId.id) * (C.eval_ctx -> C.eval_ctx) =
  let reborrows : (V.BorrowId.id * V.BorrowId.id) list ref = ref [] in
  (* The function to generate and register fresh reborrows *)
  let fresh_reborrow (bid : V.BorrowId.id) : V.BorrowId.id =
    if allow_reborrows then (
      let bid' = C.fresh_borrow_id () in
      reborrows := (bid, bid') :: !reborrows;
      bid')
    else raise (Failure "Unexpected reborrow")
  in
  (* The function to apply the reborrows in a context *)
  let apply_registered_reborrows (ctx : C.eval_ctx) : C.eval_ctx =
    match config.C.mode with
    | C.ConcreteMode ->
        assert (!reborrows = []);
        ctx
    | C.SymbolicMode ->
        (* Apply the reborrows *)
        apply_reborrows !reborrows ctx
  in
  (fresh_reborrow, apply_registered_reborrows)

let apply_proj_borrows_on_input_value (config : C.config) (ctx : C.eval_ctx)
    (regions : T.RegionId.Set.t) (ancestors_regions : T.RegionId.Set.t)
    (v : V.typed_value) (ty : T.rty) : C.eval_ctx * V.typed_avalue =
  let check_symbolic_no_ended = true in
  let allow_reborrows = true in
  (* Prepare the reborrows *)
  let fresh_reborrow, apply_registered_reborrows =
    prepare_reborrows config allow_reborrows
  in
  (* Apply the projector *)
  let av =
    apply_proj_borrows check_symbolic_no_ended ctx fresh_reborrow regions
      ancestors_regions v ty
  in
  (* Apply the reborrows *)
  let ctx = apply_registered_reborrows ctx in
  (* Return *)
  (ctx, av)
