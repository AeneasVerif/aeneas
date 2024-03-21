open Types
open Values
open Contexts
module Subst = Substitute
module Assoc = AssociatedTypes
open TypesUtils
open InterpreterUtils
open InterpreterBorrowsCore
open Errors

(** The local logger *)
let log = Logging.projectors_log

(** [ty] shouldn't contain erased regions *)
let rec apply_proj_borrows_on_shared_borrow (meta : Meta.meta) (ctx : eval_ctx)
    (fresh_reborrow : BorrowId.id -> BorrowId.id) (regions : RegionId.Set.t)
    (v : typed_value) (ty : rty) : abstract_shared_borrows =
  (* Sanity check - TODO: move those elsewhere (here we perform the check at every
   * recursive call which is a bit overkill...) *)
  let ety = Subst.erase_regions ty in
  cassert (ty_is_rty ty && ety = v.ty) meta "TODO: error message";
  (* Project - if there are no regions from the abstraction in the type, return [_] *)
  if not (ty_has_regions_in_set regions ty) then []
  else
    match (v.value, ty) with
    | VLiteral _, TLiteral _ -> []
    | VAdt adt, TAdt (id, generics) ->
        (* Retrieve the types of the fields *)
        let field_types =
          Assoc.ctx_adt_value_get_inst_norm_field_rtypes meta ctx adt id generics
        in

        (* Project over the field values *)
        let fields_types = List.combine adt.field_values field_types in
        let proj_fields =
          List.map
            (fun (fv, fty) ->
              apply_proj_borrows_on_shared_borrow meta ctx fresh_reborrow regions fv
                fty)
            fields_types
        in
        List.concat proj_fields
    | VBottom, _ -> craise meta "Unreachable"
    | VBorrow bc, TRef (r, ref_ty, kind) ->
        (* Retrieve the bid of the borrow and the asb of the projected borrowed value *)
        let bid, asb =
          (* Not in the set: dive *)
          match (bc, kind) with
          | VMutBorrow (bid, bv), RMut ->
              (* Apply the projection on the borrowed value *)
              let asb =
                apply_proj_borrows_on_shared_borrow meta ctx fresh_reborrow regions
                  bv ref_ty
              in
              (bid, asb)
          | VSharedBorrow bid, RShared ->
              (* Lookup the shared value *)
              let ek = ek_all in
              let sv = lookup_loan meta ek bid ctx in
              let asb =
                match sv with
                | _, Concrete (VSharedLoan (_, sv))
                | _, Abstract (ASharedLoan (_, sv, _)) ->
                    apply_proj_borrows_on_shared_borrow meta ctx fresh_reborrow
                      regions sv ref_ty
                | _ -> craise meta "Unexpected"
              in
              (bid, asb)
          | VReservedMutBorrow _, _ ->
              craise
                meta
                   "Can't apply a proj_borrow over a reserved mutable borrow"
          | _ -> craise meta "Unreachable"
        in
        let asb =
          (* Check if the region is in the set of projected regions (note that
           * we never project over static regions) *)
          if region_in_set r regions then
            let bid' = fresh_reborrow bid in
            AsbBorrow bid' :: asb
          else asb
        in
        asb
    | VLoan _, _ -> craise meta "Unreachable"
    | VSymbolic s, _ ->
        (* Check that the projection doesn't contain ended regions *)
        cassert (not (projections_intersect meta s.sv_ty ctx.ended_regions ty regions)) meta "TODO: error message";
        [ AsbProjReborrows (s, ty) ]
    | _ -> craise meta "Unreachable"

let rec apply_proj_borrows (meta : Meta.meta) (check_symbolic_no_ended : bool) (ctx : eval_ctx)
    (fresh_reborrow : BorrowId.id -> BorrowId.id) (regions : RegionId.Set.t)
    (ancestors_regions : RegionId.Set.t) (v : typed_value) (ty : rty) :
    typed_avalue =
  (* Sanity check - TODO: move this elsewhere (here we perform the check at every
   * recursive call which is a bit overkill...) *)
  let ety = Substitute.erase_regions ty in
  cassert (ty_is_rty ty && ety = v.ty) meta "TODO: error message";
  (* Project - if there are no regions from the abstraction in the type, return [_] *)
  if not (ty_has_regions_in_set regions ty) then { value = AIgnored; ty }
  else
    let value : avalue =
      match (v.value, ty) with
      | VLiteral _, TLiteral _ -> AIgnored
      | VAdt adt, TAdt (id, generics) ->
          (* Retrieve the types of the fields *)
          let field_types =
            Assoc.ctx_adt_value_get_inst_norm_field_rtypes meta ctx adt id generics
          in
          (* Project over the field values *)
          let fields_types = List.combine adt.field_values field_types in
          let proj_fields =
            List.map
              (fun (fv, fty) ->
                apply_proj_borrows meta check_symbolic_no_ended ctx fresh_reborrow
                  regions ancestors_regions fv fty)
              fields_types
          in
          AAdt { variant_id = adt.variant_id; field_values = proj_fields }
      | VBottom, _ -> craise meta "Unreachable"
      | VBorrow bc, TRef (r, ref_ty, kind) ->
          if
            (* Check if the region is in the set of projected regions (note that
             * we never project over static regions) *)
            region_in_set r regions
          then
            (* In the set *)
            let bc =
              match (bc, kind) with
              | VMutBorrow (bid, bv), RMut ->
                  (* Apply the projection on the borrowed value *)
                  let bv =
                    apply_proj_borrows meta check_symbolic_no_ended ctx
                      fresh_reborrow regions ancestors_regions bv ref_ty
                  in
                  AMutBorrow (bid, bv)
              | VSharedBorrow bid, RShared ->
                  (* Rem.: we don't need to also apply the projection on the
                     borrowed value, because for as long as the abstraction
                     lives then the shared borrow lives, which means that the
                     whole value is borrowed (and thus immutable).
                     This is not the case if the current borrow is not to be
                     projected to the current abstraction: if this happens,
                     then maybe there are borrows *inside* the shared value
                     which belong to the current abstraction, meaning we
                     need to lookup the shared value and project it (see the
                     other branch of the [if then else]).
                  *)
                  ASharedBorrow bid
              | VReservedMutBorrow _, _ ->
                  craise
                    meta
                       "Can't apply a proj_borrow over a reserved mutable \
                        borrow"
              | _ -> craise meta "Unreachable"
            in
            ABorrow bc
          else
            (* Not in the set: ignore the borrow, but project the borrowed
               value (maybe some borrows *inside* the borrowed value are in
               the region set) *)
            let bc =
              match (bc, kind) with
              | VMutBorrow (bid, bv), RMut ->
                  (* Apply the projection on the borrowed value *)
                  let bv =
                    apply_proj_borrows meta check_symbolic_no_ended ctx
                      fresh_reborrow regions ancestors_regions bv ref_ty
                  in
                  (* If the borrow id is in the ancestor's regions, we still need
                   * to remember it *)
                  let opt_bid =
                    if region_in_set r ancestors_regions then Some bid else None
                  in
                  (* Return *)
                  AIgnoredMutBorrow (opt_bid, bv)
              | VSharedBorrow bid, RShared ->
                  (* Lookup the shared value *)
                  let ek = ek_all in
                  let sv = lookup_loan meta ek bid ctx in
                  let asb =
                    match sv with
                    | _, Concrete (VSharedLoan (_, sv))
                    | _, Abstract (ASharedLoan (_, sv, _)) ->
                        apply_proj_borrows_on_shared_borrow meta ctx fresh_reborrow
                          regions sv ref_ty
                    | _ -> craise meta "Unexpected"
                  in
                  AProjSharedBorrow asb
              | VReservedMutBorrow _, _ ->
                  craise
                    meta
                       "Can't apply a proj_borrow over a reserved mutable \
                        borrow"
              | _ -> craise meta "Unreachable"
            in
            ABorrow bc
      | VLoan _, _ -> craise meta "Unreachable"
      | VSymbolic s, _ ->
          (* Check that the projection doesn't contain already ended regions,
           * if necessary *)
          if check_symbolic_no_ended then (
            let ty1 = s.sv_ty in
            let rset1 = ctx.ended_regions in
            let ty2 = ty in
            let rset2 = regions in
            log#ldebug
              (lazy
                ("projections_intersect:" ^ "\n- ty1: " ^ ty_to_string ctx ty1
               ^ "\n- rset1: "
                ^ RegionId.Set.to_string None rset1
                ^ "\n- ty2: " ^ ty_to_string ctx ty2 ^ "\n- rset2: "
                ^ RegionId.Set.to_string None rset2
                ^ "\n"));
            cassert (not (projections_intersect meta ty1 rset1 ty2 rset2))) meta "TODO: error message";
          ASymbolic (AProjBorrows (s, ty))
      | _ ->
          log#lerror
            (lazy
              ("apply_proj_borrows: unexpected inputs:\n- input value: "
              ^ typed_value_to_string meta ctx v
              ^ "\n- proj rty: " ^ ty_to_string ctx ty));
          craise meta "Unreachable"
    in
    { value; ty }

let symbolic_expansion_non_borrow_to_value (meta : Meta.meta) (sv : symbolic_value)
    (see : symbolic_expansion) : typed_value =
  let ty = Subst.erase_regions sv.sv_ty in
  let value =
    match see with
    | SeLiteral cv -> VLiteral cv
    | SeAdt (variant_id, field_values) ->
        let field_values =
          List.map mk_typed_value_from_symbolic_value field_values
        in
        VAdt { variant_id; field_values }
    | SeMutRef (_, _) | SeSharedRef (_, _) ->
        craise meta "Unexpected symbolic reference expansion"
  in
  { value; ty }

let symbolic_expansion_non_shared_borrow_to_value (meta : Meta.meta) (sv : symbolic_value)
    (see : symbolic_expansion) : typed_value =
  match see with
  | SeMutRef (bid, bv) ->
      let ty = Subst.erase_regions sv.sv_ty in
      let bv = mk_typed_value_from_symbolic_value bv in
      let value = VBorrow (VMutBorrow (bid, bv)) in
      { value; ty }
  | SeSharedRef (_, _) ->
      craise meta "Unexpected symbolic shared reference expansion"
  | _ -> symbolic_expansion_non_borrow_to_value meta sv see

(** Apply (and reduce) a projector over loans to a value.

    TODO: detailed comments. See [apply_proj_borrows]
*)
let apply_proj_loans_on_symbolic_expansion (meta : Meta.meta) (regions : RegionId.Set.t)
    (ancestors_regions : RegionId.Set.t) (see : symbolic_expansion)
    (original_sv_ty : rty) : typed_avalue =
  (* Sanity check: if we have a proj_loans over a symbolic value, it should
   * contain regions which we will project *)
  cassert (ty_has_regions_in_set regions original_sv_ty) meta "TODO: error message";
  (* Match *)
  let (value, ty) : avalue * ty =
    match (see, original_sv_ty) with
    | SeLiteral _, TLiteral _ -> (AIgnored, original_sv_ty)
    | SeAdt (variant_id, field_values), TAdt (_id, _generics) ->
        (* Project over the field values *)
        let field_values =
          List.map
            (mk_aproj_loans_value_from_symbolic_value regions)
            field_values
        in
        (AAdt { variant_id; field_values }, original_sv_ty)
    | SeMutRef (bid, spc), TRef (r, ref_ty, RMut) ->
        (* Sanity check *)
        cassert (spc.sv_ty = ref_ty) meta "TODO: error message";
        (* Apply the projector to the borrowed value *)
        let child_av = mk_aproj_loans_value_from_symbolic_value regions spc in
        (* Check if the region is in the set of projected regions (note that
         * we never project over static regions) *)
        if region_in_set r regions then
          (* In the set: keep *)
          (ALoan (AMutLoan (bid, child_av)), ref_ty)
        else
          (* Not in the set: ignore *)
          (* If the borrow id is in the ancestor's regions, we still need
           * to remember it *)
          let opt_bid =
            if region_in_set r ancestors_regions then Some bid else None
          in
          (ALoan (AIgnoredMutLoan (opt_bid, child_av)), ref_ty)
    | SeSharedRef (bids, spc), TRef (r, ref_ty, RShared) ->
        (* Sanity check *)
        cassert (spc.sv_ty = ref_ty) meta "TODO: error message";
        (* Apply the projector to the borrowed value *)
        let child_av = mk_aproj_loans_value_from_symbolic_value regions spc in
        (* Check if the region is in the set of projected regions (note that
         * we never project over static regions) *)
        if region_in_set r regions then
          (* In the set: keep *)
          let shared_value = mk_typed_value_from_symbolic_value spc in
          (ALoan (ASharedLoan (bids, shared_value, child_av)), ref_ty)
        else
          (* Not in the set: ignore *)
          (ALoan (AIgnoredSharedLoan child_av), ref_ty)
    | _ -> craise meta "Unreachable"
  in
  { value; ty }

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
let apply_reborrows (meta : Meta.meta) (reborrows : (BorrowId.id * BorrowId.id) list)
    (ctx : eval_ctx) : eval_ctx =
  (* This is a bit brutal, but whenever we insert a reborrow, we remove
   * it from the list. This allows us to check that all the reborrows were
   * applied before returning.
   * We might reimplement that in a more efficient manner by using maps. *)
  let reborrows = ref reborrows in

  (* Check if a value is a mutable borrow, and return its identifier if
     it is the case *)
  let get_borrow_in_mut_borrow (v : typed_value) : BorrowId.id option =
    match v.value with
    | VBorrow lc -> (
        match lc with
        | VSharedBorrow _ | VReservedMutBorrow _ -> None
        | VMutBorrow (id, _) -> Some id)
    | _ -> None
  in

  (* Add the proper reborrows to a set of borrow ids (for a shared loan) *)
  let insert_reborrows bids =
    (* Find the reborrows to apply *)
    let insert, reborrows' =
      List.partition (fun (bid, _) -> BorrowId.Set.mem bid bids) !reborrows
    in
    reborrows := reborrows';
    let insert = List.map snd insert in
    (* Insert the borrows *)
    List.fold_left (fun bids bid -> BorrowId.Set.add bid bids) bids insert
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
      (fun bids bid -> BorrowId.Set.add bid bids)
      BorrowId.Set.empty bids
  in

  (* Insert reborrows for a given borrow id into a given set of borrows *)
  let insert_reborrows_for_bid bids bid =
    (* Find the reborrows to apply *)
    let insert = get_reborrows_for_bid bid in
    (* Insert the borrows *)
    List.fold_left (fun bids bid -> BorrowId.Set.add bid bids) bids insert
  in

  let obj =
    object
      inherit [_] map_eval_ctx as super

      (** We may need to reborrow mutable borrows. Note that this doesn't
          happen for aborrows *)
      method! visit_typed_value env v =
        match v.value with
        | VBorrow (VMutBorrow (bid, bv)) ->
            let insert = get_reborrows_for_bid bid in
            let nbc = super#visit_VMutBorrow env bid bv in
            let nbc = { v with value = VBorrow nbc } in
            if insert = [] then (* No reborrows: do nothing special *)
              nbc
            else
              (* There are reborrows: insert a shared loan *)
              let insert = borrows_to_set insert in
              let value = VLoan (VSharedLoan (insert, nbc)) in
              let ty = v.ty in
              { value; ty }
        | _ -> super#visit_typed_value env v

      (** We reimplement {!visit_loan_content} (rather than one of the sub-
          functions) on purpose: exhaustive matches are good for maintenance *)
      method! visit_loan_content env lc =
        match lc with
        | VSharedLoan (bids, sv) ->
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
            super#visit_VSharedLoan env bids sv
        | VMutLoan bid ->
            (* Nothing special to do *)
            super#visit_VMutLoan env bid

      method! visit_aloan_content env lc =
        match lc with
        | ASharedLoan (bids, sv, av) ->
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
        | AIgnoredSharedLoan _
        | AMutLoan (_, _)
        | AEndedMutLoan { given_back = _; child = _; given_back_meta = _ }
        | AEndedSharedLoan (_, _)
        | AIgnoredMutLoan (_, _)
        | AEndedIgnoredMutLoan
            { given_back = _; child = _; given_back_meta = _ } ->
            (* Nothing particular to do *)
            super#visit_aloan_content env lc
    end
  in

  (* Visit *)
  let ctx = obj#visit_eval_ctx () ctx in
  (* Check that there are no reborrows remaining *)
  cassert (!reborrows = []) meta "TODO: error message";
  (* Return *)
  ctx

let prepare_reborrows (meta : Meta.meta) (config : config) (allow_reborrows : bool) :
    (BorrowId.id -> BorrowId.id) * (eval_ctx -> eval_ctx) =
  let reborrows : (BorrowId.id * BorrowId.id) list ref = ref [] in
  (* The function to generate and register fresh reborrows *)
  let fresh_reborrow (bid : BorrowId.id) : BorrowId.id =
    if allow_reborrows then (
      let bid' = fresh_borrow_id () in
      reborrows := (bid, bid') :: !reborrows;
      bid')
    else craise meta "Unexpected reborrow"
  in
  (* The function to apply the reborrows in a context *)
  let apply_registered_reborrows (ctx : eval_ctx) : eval_ctx =
    match config.mode with
    | ConcreteMode ->
        cassert (!reborrows = []) meta "TODO: error message";
        ctx
    | SymbolicMode ->
        (* Apply the reborrows *)
        apply_reborrows meta !reborrows ctx
  in
  (fresh_reborrow, apply_registered_reborrows)

(** [ty] shouldn't have erased regions *)
let apply_proj_borrows_on_input_value (meta : Meta.meta) (config : config) (ctx : eval_ctx)
    (regions : RegionId.Set.t) (ancestors_regions : RegionId.Set.t)
    (v : typed_value) (ty : rty) : eval_ctx * typed_avalue =
  cassert (ty_is_rty ty) meta "TODO: error message";
  let check_symbolic_no_ended = true in
  let allow_reborrows = true in
  (* Prepare the reborrows *)
  let fresh_reborrow, apply_registered_reborrows =
    prepare_reborrows meta config allow_reborrows
  in
  (* Apply the projector *)
  let av =
    apply_proj_borrows meta check_symbolic_no_ended ctx fresh_reborrow regions
      ancestors_regions v ty
  in
  (* Apply the reborrows *)
  let ctx = apply_registered_reborrows ctx in
  (* Return *)
  (ctx, av)
