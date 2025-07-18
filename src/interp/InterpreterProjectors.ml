open Types
open Values
open Contexts
module Subst = Substitute
module Assoc = AssociatedTypes
open TypesUtils
open ValuesUtils
open InterpreterUtils
open InterpreterBorrowsCore
open Errors

(** The local logger *)
let log = Logging.projectors_log

(** [ty] shouldn't contain erased regions *)
let rec apply_proj_borrows_on_shared_borrow (span : Meta.span) (ctx : eval_ctx)
    (fresh_reborrow : BorrowId.id -> BorrowId.id) (v : typed_value)
    (proj_ty : proj_ty) (outlive_proj_ty : proj_ty) : abstract_shared_borrows =
  (* Project - if there are no regions from the abstraction in the type, return [_] *)
  if not (ty_has_free_regions proj_ty) then []
  else
    match (v.value, proj_ty, outlive_proj_ty) with
    | VLiteral _, TLiteral _, TLiteral _ -> []
    | ( VAdt adt,
        TAdt { id; generics },
        TAdt { id = id'; generics = outlive_generics } ) ->
        sanity_check __FILE__ __LINE__ (id = id') span;

        (* Retrieve the types of the fields *)
        let get_field_types =
          Assoc.ctx_adt_get_inst_norm_field_rtypes span ctx id adt.variant_id
        in
        let field_types = get_field_types generics in
        let field_outlive_types = get_field_types outlive_generics in

        (* Project over the field values *)
        let fields_types =
          Collections.List.combine3 adt.field_values field_types
            field_outlive_types
        in
        let proj_fields =
          List.map
            (fun (fv, fty, f_outlive_ty) ->
              apply_proj_borrows_on_shared_borrow span ctx fresh_reborrow fv fty
                f_outlive_ty)
            fields_types
        in
        List.concat proj_fields
    | VBottom, _, _ -> craise __FILE__ __LINE__ span "Unreachable"
    | VBorrow bc, TRef (r, ref_ty, kind), TRef (r', ref_ty', kind') ->
        sanity_check __FILE__ __LINE__ (kind = kind') span;
        sanity_check __FILE__ __LINE__ (r' = RErased) span;

        (* Retrieve the bid of the borrow and the asb of the projected borrowed value *)
        let bid, asb =
          (* Not in the set: dive *)
          match (bc, kind) with
          | VMutBorrow (bid, bv), RMut ->
              (* Apply the projection on the borrowed value *)
              let asb =
                apply_proj_borrows_on_shared_borrow span ctx fresh_reborrow bv
                  ref_ty ref_ty'
              in
              (bid, asb)
          | VSharedBorrow bid, RShared ->
              (* Lookup the shared value *)
              let ek = ek_all in
              let sv = lookup_loan span ek bid ctx in
              let asb =
                match sv with
                | _, Concrete (VSharedLoan (_, sv))
                | _, Abstract (ASharedLoan (_, _, sv, _)) ->
                    apply_proj_borrows_on_shared_borrow span ctx fresh_reborrow
                      sv ref_ty ref_ty'
                | _ -> craise __FILE__ __LINE__ span "Unexpected"
              in
              (bid, asb)
          | VReservedMutBorrow _, _ ->
              craise __FILE__ __LINE__ span
                "Can't apply a proj_borrow over a reserved mutable borrow"
          | _ -> craise __FILE__ __LINE__ span "Unreachable"
        in
        let asb =
          (* Check if the region is in the set of projected regions (note that
           * we never project over static regions) *)
          if region_is_free r then
            let bid' = fresh_reborrow bid in
            AsbBorrow bid' :: asb
          else asb
        in
        asb
    | VLoan _, _, _ -> craise __FILE__ __LINE__ span "Unreachable"
    | VSymbolic s, _, _ ->
        (* Check that the projection doesn't contain ended regions (i.e.,
           the symbolic value doesn't contain bottom) *)
        sanity_check __FILE__ __LINE__
          (not (symbolic_value_contains_bottom span ctx s))
          span;
        [ AsbProjReborrows { sv_id = s.sv_id; proj_ty; outlive_proj_ty } ]
    | _ -> craise __FILE__ __LINE__ span "Unreachable"

let rec apply_proj_borrows (span : Meta.span) (check_symbolic_no_ended : bool)
    (ctx : eval_ctx) (fresh_reborrow : BorrowId.id -> BorrowId.id)
    (v : typed_value) (proj_ty : proj_ty) (outlive_proj_ty : proj_ty) :
    typed_avalue =
  (* Project - if there are no regions from the abstraction in the type, return [_] *)
  if not (ty_has_free_regions proj_ty) then
    { value = AIgnored (Some v); ty = proj_ty }
  else
    let value : avalue =
      match (v.value, proj_ty, outlive_proj_ty) with
      | VLiteral _, TLiteral _, TLiteral _ -> AIgnored (Some v)
      | ( VAdt adt,
          TAdt { id; generics },
          TAdt { id = id'; generics = outlive_generics } ) ->
          sanity_check __FILE__ __LINE__ (id = id') span;

          (* Retrieve the types of the fields *)
          let get_field_types =
            Assoc.ctx_adt_get_inst_norm_field_rtypes span ctx id adt.variant_id
          in
          let field_types = get_field_types generics in
          let field_outlive_types = get_field_types outlive_generics in

          (* Project over the field values *)
          let fields_types =
            Collections.List.combine3 adt.field_values field_types
              field_outlive_types
          in
          let proj_fields =
            List.map
              (fun (fv, fty, f_outlive_ty) ->
                apply_proj_borrows span check_symbolic_no_ended ctx
                  fresh_reborrow fv fty f_outlive_ty)
              fields_types
          in
          AAdt { variant_id = adt.variant_id; field_values = proj_fields }
      | VBottom, _, _ -> craise __FILE__ __LINE__ span "Unreachable"
      | VBorrow bc, TRef (r, ref_ty, kind), TRef (r', ref_ty', kind') ->
          sanity_check __FILE__ __LINE__ (kind = kind') span;
          sanity_check __FILE__ __LINE__ (r' = RErased) span;

          if
            (* Check if the region is in the set of projected regions (note that
               we never project over static regions) *)
            region_is_free r
          then
            (* In the set *)
            let bc =
              match (bc, kind) with
              | VMutBorrow (bid, bv), RMut ->
                  (* Apply the projection on the borrowed value *)
                  let bv =
                    apply_proj_borrows span check_symbolic_no_ended ctx
                      fresh_reborrow bv ref_ty ref_ty'
                  in
                  AMutBorrow (PNone, bid, bv)
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
                  ASharedBorrow (PNone, bid)
              | VReservedMutBorrow _, _ ->
                  craise __FILE__ __LINE__ span
                    "Can't apply a proj_borrow over a reserved mutable borrow"
              | _ -> craise __FILE__ __LINE__ span "Unreachable"
            in
            ABorrow bc
          else
            (* Not in the set: ignore the borrow, but project the borrowed
               value (the projection type is not empty, so there should be
               some borrows *inside* the borrowed value that need to be projected) *)
            let bc =
              match (bc, kind) with
              | VMutBorrow (bid, bv), RMut ->
                  (* Apply the projection on the borrowed value *)
                  let bv =
                    apply_proj_borrows span check_symbolic_no_ended ctx
                      fresh_reborrow bv ref_ty ref_ty'
                  in
                  (* We need to remember the borrow, even though we ignore it *)
                  let opt_bid = Some bid in
                  (* Return *)
                  AIgnoredMutBorrow (opt_bid, ref_ty', bv)
              | VSharedBorrow bid, RShared ->
                  (* Lookup the shared value *)
                  let ek = ek_all in
                  let sv = lookup_loan span ek bid ctx in
                  let asb =
                    match sv with
                    | _, Concrete (VSharedLoan (_, sv))
                    | _, Abstract (ASharedLoan (_, _, sv, _)) ->
                        apply_proj_borrows_on_shared_borrow span ctx
                          fresh_reborrow sv ref_ty ref_ty'
                    | _ -> craise __FILE__ __LINE__ span "Unexpected"
                  in
                  AProjSharedBorrow asb
              | VReservedMutBorrow _, _ ->
                  craise __FILE__ __LINE__ span
                    "Can't apply a proj_borrow over a reserved mutable borrow"
              | _ -> craise __FILE__ __LINE__ span "Unreachable"
            in
            ABorrow bc
      | VLoan _, _, _ -> craise __FILE__ __LINE__ span "Unreachable"
      | VSymbolic s, _, _ ->
          (* Check that the projection doesn't contain already ended regions,
             if necessary *)
          if check_symbolic_no_ended then
            sanity_check __FILE__ __LINE__
              (not (symbolic_value_contains_bottom span ctx s))
              span;
          ASymbolic
            ( PNone,
              AProjBorrows ({ sv_id = s.sv_id; proj_ty; outlive_proj_ty }, [])
            )
      | _ ->
          log#ltrace
            (lazy
              ("apply_proj_borrows: unexpected inputs:\n- input value: "
              ^ typed_value_to_string ~span:(Some span) ctx v
              ^ "\n- proj_ty: " ^ ty_to_string ctx proj_ty));
          internal_error __FILE__ __LINE__ span
    in
    { value; ty = proj_ty }

let symbolic_expansion_non_borrow_to_value (span : Meta.span)
    (sv : symbolic_value) (see : symbolic_expansion) : typed_value =
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
        craise __FILE__ __LINE__ span "Unexpected symbolic reference expansion"
  in
  { value; ty }

let symbolic_expansion_non_shared_borrow_to_value (span : Meta.span)
    (sv : symbolic_value) (see : symbolic_expansion) : typed_value =
  match see with
  | SeMutRef (bid, bv) ->
      let ty = Subst.erase_regions sv.sv_ty in
      let bv = mk_typed_value_from_symbolic_value bv in
      let value = VBorrow (VMutBorrow (bid, bv)) in
      { value; ty }
  | SeSharedRef (_, _) ->
      craise __FILE__ __LINE__ span
        "Unexpected symbolic shared reference expansion"
  | _ -> symbolic_expansion_non_borrow_to_value span sv see

(** Apply (and reduce) a projector over loans to a value.

    Remark: we need the evaluation context only to access the type declarations.
    Remark: the projection type should have been normalized (i.e., the regions
    we should project should be free regions of id 0, and the regions we want to
    ignore should have been erased).

    TODO: detailed comments. See [apply_proj_borrows] *)
let apply_proj_loans_on_symbolic_expansion (span : Meta.span)
    (see : symbolic_expansion) (proj_ty : proj_ty) (outlive_proj_ty : proj_ty)
    (ctx : eval_ctx) : typed_avalue =
  (* Sanity check: if we have a proj_loans over a symbolic value, it should
   * contain regions which we will project *)
  sanity_check __FILE__ __LINE__ (ty_has_free_regions proj_ty) span;
  (* Match *)
  let (value, ty) : avalue * ty =
    match (see, proj_ty, outlive_proj_ty) with
    | SeLiteral lit, TLiteral _, TLiteral _ ->
        (AIgnored (Some { value = VLiteral lit; ty = proj_ty }), proj_ty)
    | ( SeAdt (variant_id, field_values),
        TAdt { id = adt_id; generics },
        TAdt { id = adt_id'; generics = outlive_generics } ) ->
        sanity_check __FILE__ __LINE__ (adt_id = adt_id') span;

        (* Project over the field values *)
        let get_field_types =
          AssociatedTypes.ctx_adt_get_inst_norm_field_rtypes span ctx adt_id
            variant_id
        in
        let field_types = get_field_types generics in
        let field_outlive_types = get_field_types outlive_generics in
        let field_values =
          Collections.List.map3 mk_aproj_loans_value_from_symbolic_value
            field_values field_types field_outlive_types
        in
        (AAdt { variant_id; field_values }, proj_ty)
    | SeMutRef (bid, spc), TRef (r, ref_ty, RMut), TRef (r', ref_ty', RMut) ->
        (* Sanity check *)
        sanity_check __FILE__ __LINE__ (spc.sv_ty = ref_ty) span;
        sanity_check __FILE__ __LINE__ (region_is_erased r') span;

        (* Apply the projector to the borrowed value *)
        let child_av =
          mk_aproj_loans_value_from_symbolic_value spc ref_ty ref_ty'
        in
        (* Check if the region is in the set of projected regions (note that
           we never project over static regions) *)
        if region_is_free r then
          (* In the set: keep *)
          (ALoan (AMutLoan (PNone, bid, child_av)), ref_ty)
        else
          (* Not in the set: check if the inner type has regions we might
             need to project. *)
          (* If the borrow id is in the ancestor's regions, we still need
           * to remember it *)
          let opt_bid = if ty_has_free_regions ref_ty then Some bid else None in
          (ALoan (AIgnoredMutLoan (opt_bid, ref_ty', child_av)), ref_ty)
    | ( SeSharedRef (bids, spc),
        TRef (r, ref_ty, RShared),
        TRef (r', ref_ty', RShared) ) ->
        (* Sanity check *)
        sanity_check __FILE__ __LINE__ (spc.sv_ty = ref_ty) span;
        sanity_check __FILE__ __LINE__ (region_is_erased r') span;

        (* Apply the projector to the borrowed value *)
        let child_av =
          mk_aproj_loans_value_from_symbolic_value spc ref_ty ref_ty'
        in
        (* Check if the region is in the set of projected regions (note that
           we never project over static regions) *)
        if region_is_free r then
          (* In the set: keep *)
          let shared_value = mk_typed_value_from_symbolic_value spc in
          (ALoan (ASharedLoan (PNone, bids, shared_value, child_av)), ref_ty)
        else
          (* Not in the set: ignore *)
          (ALoan (AIgnoredSharedLoan child_av), ref_ty)
    | _ -> craise __FILE__ __LINE__ span "Unreachable"
  in
  { value; ty }

(** Auxiliary function. See [give_back_value].

    Apply reborrows to a context.

    The [reborrows] input is a list of pairs (shared loan id, id to insert in
    the shared loan). This function is used when applying projectors on shared
    borrows: when doing so, we might need to reborrow subvalues from the shared
    value. For instance:
    {[
      fn f<'a,'b,'c>(x : &'a 'b 'c u32)
    ]}
    When introducing the abstractions for 'a, 'b and 'c, we apply a projector on
    some value [shared_borrow l : &'a &'b &'c u32]. In the 'a abstraction, this
    shared borrow gets projected. However, when reducing the projectors for the
    'b and 'c abstractions, we need to make sure that the borrows living in
    regions 'b and 'c live as long as those regions. This is done by looking up
    the shared value and applying reborrows on the borrows we find there (note
    that those reborrows apply on shared borrows - easy - and mutable borrows -
    in this case, we reborrow the whole borrow:
    [mut_borrow ... ~~> shared_loan {...} (mut_borrow ...)]). *)
let apply_reborrows (span : Meta.span)
    (reborrows : (BorrowId.id * BorrowId.id) list) (ctx : eval_ctx) : eval_ctx =
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

      (** We may need to reborrow mutable borrows. Note that this doesn't happen
          for aborrows *)
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
        | ASharedLoan (pm, bids, sv, av) ->
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
            super#visit_ASharedLoan env pm bids sv av
        | AIgnoredSharedLoan _ | AMutLoan _
        | AEndedMutLoan { given_back = _; child = _; given_back_meta = _ }
        | AEndedSharedLoan _ | AIgnoredMutLoan _
        | AEndedIgnoredMutLoan
            { given_back = _; child = _; given_back_meta = _ } ->
            (* Nothing particular to do *)
            super#visit_aloan_content env lc
    end
  in

  (* Visit *)
  let ctx = obj#visit_eval_ctx () ctx in
  (* Check that there are no reborrows remaining *)
  sanity_check __FILE__ __LINE__ (!reborrows = []) span;
  (* Return *)
  ctx

let prepare_reborrows (config : config) (span : Meta.span)
    (allow_reborrows : bool) :
    (BorrowId.id -> BorrowId.id) * (eval_ctx -> eval_ctx) =
  let reborrows : (BorrowId.id * BorrowId.id) list ref = ref [] in
  (* The function to generate and register fresh reborrows *)
  let fresh_reborrow (bid : BorrowId.id) : BorrowId.id =
    if allow_reborrows then (
      let bid' = fresh_borrow_id () in
      reborrows := (bid, bid') :: !reborrows;
      bid')
    else craise __FILE__ __LINE__ span "Unexpected reborrow"
  in
  (* The function to apply the reborrows in a context *)
  let apply_registered_reborrows (ctx : eval_ctx) : eval_ctx =
    match config.mode with
    | ConcreteMode ->
        sanity_check __FILE__ __LINE__ (!reborrows = []) span;
        ctx
    | SymbolicMode ->
        (* Apply the reborrows *)
        apply_reborrows span !reborrows ctx
  in
  (fresh_reborrow, apply_registered_reborrows)

(** [ty] shouldn't have erased regions *)
let apply_proj_borrows_on_input_value (config : config) (span : Meta.span)
    (ctx : eval_ctx) (v : typed_value) (proj_ty : proj_ty)
    (outlive_proj_ty : proj_ty) : eval_ctx * typed_avalue =
  let check_symbolic_no_ended = true in
  let allow_reborrows = true in
  (* Prepare the reborrows *)
  let fresh_reborrow, apply_registered_reborrows =
    prepare_reborrows config span allow_reborrows
  in
  (* Apply the projector *)
  let av =
    apply_proj_borrows span check_symbolic_no_ended ctx fresh_reborrow v proj_ty
      outlive_proj_ty
  in
  (* Apply the reborrows *)
  let ctx = apply_registered_reborrows ctx in
  (* Return *)
  (ctx, av)
