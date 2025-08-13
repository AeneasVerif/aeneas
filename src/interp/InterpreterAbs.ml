open Types
open Values
open Contexts
open ValuesUtils
open TypesUtils
open InterpreterUtils
open InterpreterBorrowsCore
open InterpreterBorrows

(** The local logger *)
let log = Logging.abs_log

let convert_value_to_abstractions (span : Meta.span) (abs_kind : abs_kind)
    ~(can_end : bool) ~(destructure_shared_values : bool) (ctx : eval_ctx)
    (v : tvalue) : abs list =
  [%ltrace tvalue_to_string ctx v];
  (* Convert the value to a list of avalues *)
  let absl = ref [] in
  let push_abs (r_id : RegionId.id) (avalues : typed_avalue list) : unit =
    if avalues = [] then ()
    else begin
      (* Create the abs - note that we keep the order of the avalues as it is
         (unlike the environments) *)
      [%ldebug
        "avalues:\n"
        ^ String.concat "\n"
            (List.map
               (fun (v : typed_avalue) ->
                 typed_avalue_to_string ctx v ^ " : " ^ ty_to_string ctx v.ty)
               avalues)];
      let abs =
        {
          abs_id = fresh_abstraction_id ();
          kind = abs_kind;
          can_end;
          parents = AbstractionId.Set.empty;
          original_parents = [];
          regions = { owned = RegionId.Set.singleton r_id };
          avalues;
        }
      in
      [%ldebug "abs:\n" ^ abs_to_string span ctx abs];
      Invariants.opt_type_check_abs span ctx abs;
      (* Add to the list of abstractions *)
      absl := abs :: !absl
    end
  in

  (* [group]: group in one abstraction (because we dived into a borrow/loan)

     We return one typed-value for the shared values: when we encounter a shared
     loan, we need to compute the value which will be shared. If [destructure_shared_values]
     is [true], this shared value will be stripped of its shared loans.
  *)
  let rec to_avalues ~(allow_borrows : bool) ~(inside_borrowed : bool)
      ~(group : bool) (r_id : RegionId.id) (v : tvalue) :
      typed_avalue list * tvalue =
    (* Debug *)
    [%ldebug "\n- value: " ^ tvalue_to_string ~span:(Some span) ctx v];

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
                   (to_avalues ~allow_borrows ~inside_borrowed ~group r_id)
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
                    to_avalues ~allow_borrows ~inside_borrowed ~group r_id fv
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
        [%cassert] span (ty_no_regions ref_ty)
          "Nested borrows are not supported yet";
        (* Sanity check *)
        [%sanity_check] span allow_borrows;
        (* Convert the borrow content *)
        match bc with
        | VSharedBorrow (bid, sid) ->
            [%cassert] span (ty_no_regions ref_ty)
              "Nested borrows are not supported yet";
            let ty = TRef (RVar (Free r_id), ref_ty, kind) in
            let value = ABorrow (ASharedBorrow (PNone, bid, sid)) in
            ([ { value; ty } ], v)
        | VMutBorrow (bid, bv) ->
            (* We don't support nested borrows for now *)
            [%cassert] span
              (not (value_has_borrows (Some span) ctx bv.value))
              "Nested borrows are not supported yet";
            (* Create an avalue to push - note that we use [AIgnore] for the inner avalue *)
            let ty = TRef (RVar (Free r_id), ref_ty, kind) in
            let ignored = mk_aignored span ref_ty None in
            let av = ABorrow (AMutBorrow (PNone, bid, ignored)) in
            let av = { value = av; ty } in
            (* Continue exploring, looking for loans (and forbidding borrows,
               because we don't support nested borrows for now) *)
            let avl, bv =
              to_avalues ~allow_borrows:false ~inside_borrowed:true ~group:true
                r_id bv
            in
            let value = { v with value = VBorrow (VMutBorrow (bid, bv)) } in
            (av :: avl, value)
        | VReservedMutBorrow _ ->
            (* This borrow should have been activated *)
            [%craise] span "Unexpected")
    | VLoan lc -> (
        match lc with
        | VSharedLoan (bids, sv) ->
            (* We don't support nested borrows for now *)
            [%cassert] span
              (not (value_has_borrows (Some span) ctx sv.value))
              "Nested borrows are not supported yet";
            (* Push the avalue *)
            [%cassert] span (ty_no_regions ty)
              "Nested borrows are not supported yet";
            (* We use [AIgnore] for the inner value *)
            let ignored = mk_aignored span ty None in
            (* For avalues, a loan has the type borrow (see the comments in [avalue]) *)
            let ty = mk_ref_ty (RVar (Free r_id)) ty RShared in
            (* Rem.: the shared value might contain loans *)
            let avl, sv =
              to_avalues ~allow_borrows:false ~inside_borrowed:true ~group:true
                r_id sv
            in
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
            [%cassert] span (ty_no_regions ty)
              "Nested borrows are not supported yet";
            (* We use [AIgnore] for the inner value *)
            let ignored = mk_aignored span ty in
            (* For avalues, a loan has the type borrow (see the comments in [avalue]) *)
            let ty = mk_ref_ty (RVar (Free r_id)) ty RMut in
            let av = ALoan (AMutLoan (PNone, bid, ignored None)) in
            let av = { value = av; ty } in
            ([ av ], v))
    | VSymbolic sv ->
        (* Check that there are no nested borrows in the symbolic value -
           we don't support this case yet *)
        [%cassert] span
          (not
             (ty_has_nested_borrows (Some span) ctx.type_ctx.type_infos sv.sv_ty))
          "Nested borrows are not supported yet";

        (* If we don't need to group the borrows into one region (because the
           symbolic value is inside a mutable borrow for instance) check that
           none of the regions used by the symbolic value have ended. *)
        [%sanity_check] span
          (group || not (symbolic_value_has_ended_regions ctx.ended_regions sv));

        (* If we group the borrows: simply introduce a projector.
           Otherwise, introduce one abstraction per region *)
        if group then
          (* Check if the type contains regions: if not, simply ignore
             it (there are no projections to introduce) *)
          if TypesUtils.ty_no_regions sv.sv_ty then ([], v)
          else
            (* Substitute the regions in the type *)
            let visitor =
              object
                inherit [_] map_ty

                method! visit_RVar _ var =
                  match var with
                  | Free _ -> RVar (Free r_id)
                  | Bound _ -> [%internal_error] span
              end
            in
            let ty = visitor#visit_ty () sv.sv_ty in
            let proj : symbolic_proj = { sv_id = sv.sv_id; proj_ty = ty } in
            let nv = ASymbolic (PNone, AProjBorrows { proj; loans = [] }) in
            let nv : typed_avalue = { value = nv; ty } in
            ([ nv ], v)
        else
          (* Introduce one abstraction per live region *)
          let regions, ty = refresh_live_regions_in_ty span ctx sv.sv_ty in
          RegionId.Map.iter
            (fun _ rid ->
              let proj : symbolic_proj = { sv_id = sv.sv_id; proj_ty = ty } in
              let nv = ASymbolic (PNone, AProjBorrows { proj; loans = [] }) in
              let nv : typed_avalue = { value = nv; ty } in
              push_abs rid [ nv ])
            regions;
          ([], v)
  in

  (* Generate the avalues *)
  let r_id = fresh_region_id () in
  let values, _ =
    to_avalues ~allow_borrows:true ~inside_borrowed:false ~group:false r_id v
  in
  (* Introduce an abstraction for the returned values *)
  push_abs r_id values;
  (* Return *)
  List.rev !absl

(** Simplify the duplicated shared borrows in a region abstraction.

    {[
      abs { SB l0, SB l0 } ~> abs { SB l0 }
    ]}

    Note that this function supports projection markers: when merging two
    borrows we take the union of the markers. *)
let abs_simplify_duplicated_borrows (span : Meta.span) (ctx : eval_ctx)
    (abs : abs) : abs =
  (* Sanity check: the abstraction has been destructured *)
  (if !Config.sanity_checks then
     let destructure_shared_values = true in
     [%sanity_check] span
       (abs_is_destructured span destructure_shared_values ctx abs));

  let join_pm (pm0 : proj_marker) (pm1 : proj_marker) : proj_marker =
    match (pm0, pm1) with
    | PNone, _ | _, PNone -> PNone
    | PLeft, PRight | PRight, PLeft -> PNone
    | PRight, PRight -> PRight
    | PLeft, PLeft -> PLeft
  in

  (* We first filter the borrows which are duplicated *)
  let shared_borrows = ref BorrowId.Map.empty in
  let keep_avalue (av : typed_avalue) : bool =
    match av.value with
    | ABorrow (ASharedBorrow (pm, bid, _)) -> begin
        match BorrowId.Map.find_opt bid !shared_borrows with
        | None ->
            shared_borrows := BorrowId.Map.add bid pm !shared_borrows;
            true
        | Some pm' ->
            let pm = join_pm pm pm' in
            shared_borrows := BorrowId.Map.add bid pm !shared_borrows;
            false
      end
    | _ -> true
  in
  let avalues = List.filter keep_avalue abs.avalues in

  (* We update the projection markers of the remaining borrows *)
  let update_avalue (av : typed_avalue) : typed_avalue =
    match av.value with
    | ABorrow (ASharedBorrow (_, bid, sid)) ->
        let pm = BorrowId.Map.find bid !shared_borrows in
        { av with value = ABorrow (ASharedBorrow (pm, bid, sid)) }
    | _ -> av
  in
  let avalues = List.map update_avalue avalues in

  (* Update the abstraction *)
  { abs with avalues }

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

          The children should be [AIgnored]. *)
  merge_ashared_borrows :
    borrow_id ->
    rty ->
    proj_marker ->
    shared_borrow_id ->
    rty ->
    proj_marker ->
    shared_borrow_id ->
    typed_avalue;
      (** Parameters:
          - [id]
          - [ty0]
          - [pm0]
          - [sid0]
          - [ty1]
          - [pm1]
          - [sid1] *)
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

          The children should be [AIgnored]. *)
  merge_ashared_loans :
    loan_id ->
    rty ->
    proj_marker ->
    tvalue ->
    typed_avalue ->
    rty ->
    proj_marker ->
    tvalue ->
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
          - [child1] *)
  merge_aborrow_projs :
    ty ->
    proj_marker ->
    aproj_borrows ->
    ty ->
    proj_marker ->
    aproj_borrows ->
    typed_avalue;
      (** Parameters:
          - [ty0]
          - [pm0]
          - [proj0]
          - [loans0]
          - [ty1]
          - [pm1]
          - [proj1]
          - [loans1] *)
  merge_aloan_projs :
    ty ->
    proj_marker ->
    aproj_loans ->
    ty ->
    proj_marker ->
    aproj_loans ->
    typed_avalue;
      (** Parameters:
          - [ty0]
          - [pm0]
          - [proj0]
          - [consumed0]
          - [borrows0]
          - [ty1]
          - [pm1]
          - [sv1]
          - [proj_ty1]
          - [children1] *)
}

(** Small utility: if a value doesn't have any marker, split it into two values
    with complementary markers. We use this for {!merge_abstractions}.

    We assume the value has been destructured (there are no nested loans, adts,
    the children are ignored, etc.). *)
let typed_avalue_split_marker (span : Meta.span) (ctx : eval_ctx)
    (av : typed_avalue) : typed_avalue list =
  let mk_split mk_value = [ mk_value PLeft; mk_value PRight ] in
  let mk_opt_split pm mk_value =
    if pm = PNone then mk_split mk_value else [ av ]
  in
  match av.value with
  | AAdt _ | ABottom | AIgnored _ -> [%internal_error] span
  | ABorrow bc -> (
      match bc with
      | AMutBorrow (pm, bid, child) ->
          [%sanity_check] span (is_aignored child.value);
          let mk_value pm =
            { av with value = ABorrow (AMutBorrow (pm, bid, child)) }
          in
          mk_opt_split pm mk_value
      | ASharedBorrow (pm, bid, sid) ->
          let mk_value pm =
            { av with value = ABorrow (ASharedBorrow (pm, bid, sid)) }
          in
          mk_opt_split pm mk_value
      | _ -> [%internal_error] span)
  | ALoan lc -> (
      match lc with
      | AMutLoan (pm, bid, child) ->
          [%sanity_check] span (is_aignored child.value);
          let mk_value pm =
            { av with value = ALoan (AMutLoan (pm, bid, child)) }
          in
          mk_opt_split pm mk_value
      | ASharedLoan (pm, bids, sv, child) ->
          [%sanity_check] span (is_aignored child.value);
          [%sanity_check] span
            (not (value_has_borrows (Some span) ctx sv.value));
          let mk_value pm =
            { av with value = ALoan (ASharedLoan (pm, bids, sv, child)) }
          in
          mk_opt_split pm mk_value
      | _ -> [%internal_error] span)
  | ASymbolic (pm, proj) -> (
      if pm <> PNone then [ av ]
      else
        match proj with
        | AProjBorrows { proj = _; loans } ->
            [%sanity_check] span (loans = []);
            let mk_value pm = { av with value = ASymbolic (pm, proj) } in
            mk_split mk_value
        | AProjLoans { proj = _; consumed; borrows } ->
            [%sanity_check] span (consumed = []);
            [%sanity_check] span (borrows = []);
            let mk_value pm = { av with value = ASymbolic (pm, proj) } in
            mk_split mk_value
        | AEndedProjLoans _ | AEndedProjBorrows _ | AEmpty ->
            [%internal_error] span)

let abs_split_markers (span : Meta.span) (ctx : eval_ctx) (abs : abs) : abs =
  {
    abs with
    avalues =
      List.concat (List.map (typed_avalue_split_marker span ctx) abs.avalues);
  }

(** Auxiliary function for {!merge_abstractions}.

    Phase 1 of the merge: we simplify all loan/borrow pairs, if a loan is in the
    left abstraction and its corresponding borrow is in the right abstraction.

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

    **Remark:** we assume the abstractions have been destructured and that the
    markers have been split (if markers are allowed). *)
let merge_abstractions_merge_loan_borrow_pairs (span : Meta.span)
    ~(allow_markers : bool) (ctx : eval_ctx) (abs0 : abs) (abs1 : abs) :
    typed_avalue list =
  [%ltrace ""];

  if !Config.sanity_checks then (
    let destructure_shared_values = true in
    [%sanity_check] span
      (abs_is_destructured span destructure_shared_values ctx abs0);
    [%sanity_check] span
      (abs_is_destructured span destructure_shared_values ctx abs1));

  (* Simplify the duplicated shared borrows *)
  let abs0 = abs_simplify_duplicated_borrows span ctx abs0 in
  let abs1 = abs_simplify_duplicated_borrows span ctx abs1 in

  (* Sanity check: no markers appear unless we allow merging duplicates.
     Also, the borrows must be disjoint, and the loans must be disjoint.
  *)
  if not allow_markers then (
    let visitor =
      object
        inherit [_] iter_abs
        method! visit_proj_marker _ pm = [%sanity_check] span (pm = PNone)
      end
    in
    visitor#visit_abs () abs0;
    visitor#visit_abs () abs1);

  (* Merge.

     We take all the values in the left abstraction and add the values from
     the right abstraction one at a time. Whenever we add a value, we go
     through all the *left* values in the abstraction to check if we need
     to eliminate a shared borrow because there is already a shared loan,
     or to check if we need to merge a mutable borrow and a mutable loan, etc.
  *)
  let left_avalues = ref abs0.avalues in
  let right_avalues = ref [] in

  (* Some preprocessing: save all the normalized types of the loan projectors in
     the left abstraction *)
  let left_norm_proj_loans = ref MarkedNormSymbProjSet.empty in
  List.iter
    (fun (av : typed_avalue) ->
      match av.value with
      | ASymbolic (pm, aproj) -> (
          match aproj with
          | AProjLoans { proj; consumed; borrows } ->
              [%sanity_check] span (consumed = []);
              [%sanity_check] span (borrows = []);
              let norm_proj_ty =
                normalize_proj_ty abs0.regions.owned proj.proj_ty
              in
              left_norm_proj_loans :=
                MarkedNormSymbProjSet.add
                  { pm; sv_id = proj.sv_id; norm_proj_ty }
                  !left_norm_proj_loans
          | _ -> ())
      | _ -> ())
    abs0.avalues;

  let push_right_avalue (av : typed_avalue) : unit =
    right_avalues := av :: !right_avalues
  in

  let add_avalue (av : typed_avalue) : unit =
    match av.value with
    | ALoan _ ->
        (* We simply add the value: we only merge loans coming from the *left*
         (this one comes from the right) with borrows coming from the *right*. *)
        push_right_avalue av
    | ABorrow bc ->
        (* We may need to merge it *)
        begin
          match bc with
          | AMutBorrow (pm, bid, child) ->
              [%sanity_check] span (is_aignored child.value);
              let rec merge (avl : typed_avalue list) : typed_avalue list * bool
                  =
                match avl with
                | [] -> ([], true)
                | av :: avl -> (
                    match av.value with
                    | ALoan (AMutLoan (pm', bid', _))
                      when pm = pm' && bid = bid' -> (avl, false)
                    | _ ->
                        let avl, keep = merge avl in
                        (av :: avl, keep))
              in
              let avalues, keep = merge !left_avalues in
              left_avalues := avalues;
              if keep then push_right_avalue av else ()
          | ASharedBorrow (pm, bid, _) ->
              let rec keep (avl : typed_avalue list) : bool =
                match avl with
                | [] -> true
                | av :: avl -> (
                    match av.value with
                    | ALoan (ASharedLoan (pm', bid', _, _))
                      when pm = pm' && bid = bid' -> false
                    | _ -> keep avl)
              in
              let keep = keep !left_avalues in
              if keep then push_right_avalue av else ()
          | AIgnoredMutBorrow _
          | AEndedMutBorrow _
          | AEndedSharedBorrow
          | AEndedIgnoredMutBorrow _
          | AProjSharedBorrow _ -> [%craise] span "Unreachable"
        end
    | ASymbolic (pm, proj) -> begin
        match proj with
        | AProjLoans _ ->
            (* We simply add the value: we only merge loans coming from the *left*
               (this one comes from the right) with borrows coming from the *right*. *)
            push_right_avalue av
        | AProjBorrows { proj; loans } ->
            [%sanity_check] span (loans = []);
            (* Check if we need to eliminate it *)
            let norm_proj_ty =
              normalize_proj_ty abs1.regions.owned proj.proj_ty
            in
            if
              MarkedNormSymbProjSet.mem
                { pm; sv_id = proj.sv_id; norm_proj_ty }
                !left_norm_proj_loans
            then
              (* Eliminate: we need to filter the left avalues to remove the loan projector *)
              left_avalues :=
                List.filter
                  (fun (av : typed_avalue) ->
                    match av.value with
                    | ASymbolic (pm', proj') -> (
                        match proj' with
                        | AProjLoans { proj = proj'; _ } ->
                            if
                              proj'.sv_id = proj.sv_id && pm' = pm
                              && normalize_proj_ty abs0.regions.owned
                                   proj'.proj_ty
                                 = norm_proj_ty
                            then false
                            else true
                        | _ -> true)
                    | _ -> true)
                  !left_avalues
            else
              (* Do not eliminate *)
              push_right_avalue av
        | AEndedProjLoans _ | AEndedProjBorrows _ | AEmpty ->
            [%craise] span "Unreachable"
      end
    | AAdt _ | ABottom | AIgnored _ -> [%craise] span "Unreachable"
  in
  List.iter add_avalue abs1.avalues;

  (* We are done *)
  !left_avalues @ List.rev !right_avalues

(** Auxiliary function for {!merge_abstractions}.

    Phase 2 of the merge: we remove markers, by merging pairs of the same
    element with different markers into one element without markers.

    Example:
    {[
      |MB l0|, MB l1, ︙MB l0︙
           ~~>
      MB l0, MB l1
    ]} *)
let merge_abstractions_merge_markers (span : Meta.span)
    (merge_funs : merge_duplicates_funcs) (ctx : eval_ctx)
    (owned_regions : RegionId.Set.t) (avalues : typed_avalue list) :
    typed_avalue list =
  [%ltrace
    "- avalues:\n"
    ^ String.concat ", " (List.map (typed_avalue_to_string ctx) avalues)];

  (* We simply iterate through the list of avalues create during the first phase,
     and progressively add them back: if we find a value with a complementary marker,
     we merge the values together, otherwise we add it to the list of values. *)
  let complementary_markers pm0 pm1 =
    (pm0 = PLeft && pm1 = PRight) || (pm0 = PRight && pm1 = PLeft)
  in

  (* Some utility functions *)
  (* Merge two aborrow contents - return [Some] if they were merged into a single value,
     return [None] otherwise.
   *)
  let try_merge_aborrow_contents (ty0 : rty) (bc0 : aborrow_content) (ty1 : rty)
      (bc1 : aborrow_content) : typed_avalue option =
    match (bc0, bc1) with
    | AMutBorrow (pm0, id0, child0), AMutBorrow (pm1, id1, child1)
      when id0 = id1 ->
        [%sanity_check] span (complementary_markers pm0 pm1);
        Some (merge_funs.merge_amut_borrows id0 ty0 pm0 child0 ty1 pm1 child1)
    | ASharedBorrow (pm0, id0, sid0), ASharedBorrow (pm1, id1, sid1)
      when id0 = id1 ->
        [%sanity_check] span (complementary_markers pm0 pm1);
        Some (merge_funs.merge_ashared_borrows id0 ty0 pm0 sid0 ty1 pm1 sid1)
    | _ ->
        (* Nothing to merge *)
        None
  in

  let try_merge_aloan_contents (ty0 : rty) (lc0 : aloan_content) (ty1 : rty)
      (lc1 : aloan_content) : typed_avalue option =
    match (lc0, lc1) with
    | AMutLoan (pm0, id0, child0), AMutLoan (pm1, id1, child1) when id0 = id1 ->
        [%sanity_check] span (complementary_markers pm0 pm1);
        (* Merge *)
        Some (merge_funs.merge_amut_loans id0 ty0 pm0 child0 ty1 pm1 child1)
    | ASharedLoan (pm0, id0, sv0, child0), ASharedLoan (pm1, id1, sv1, child1)
      when id0 = id1 ->
        [%sanity_check] span (complementary_markers pm0 pm1);
        (* Merge *)
        Some
          (merge_funs.merge_ashared_loans id0 ty0 pm0 sv0 child0 ty1 pm1 sv1
             child1)
    | _ ->
        (* Nothing to merge *)
        None
  in

  let try_merge_projs ((ty0, pm0, proj0) : ty * proj_marker * aproj)
      ((ty1, pm1, proj1) : ty * proj_marker * aproj) : typed_avalue option =
    match (proj0, proj1) with
    | AProjBorrows proj0, AProjBorrows proj1
      when proj0.proj.sv_id = proj1.proj.sv_id
           && projections_intersect span owned_regions proj0.proj.proj_ty
                owned_regions proj1.proj.proj_ty ->
        [%sanity_check] span (complementary_markers pm0 pm1);
        (* Merge *)
        Some (merge_funs.merge_aborrow_projs ty0 pm0 proj0 ty1 pm1 proj1)
    | AProjLoans proj0, AProjLoans proj1
      when proj0.proj.sv_id = proj1.proj.sv_id
           && projections_intersect span owned_regions proj0.proj.proj_ty
                owned_regions proj1.proj.proj_ty ->
        [%sanity_check] span (complementary_markers pm0 pm1);
        (* Merge *)
        Some (merge_funs.merge_aloan_projs ty0 pm0 proj0 ty1 pm1 proj1)
    | _ ->
        (* Nothing to merge *)
        None
  in

  (* Attempt to merge two avalues, if they are mergeable.

     Return [Some] with the result of the merge if it occurred, and [None]
     if the two values can't be merged (because they are of two different
     kinds for instance). *)
  let try_merge_avalues (av0 : typed_avalue) (av1 : typed_avalue) :
      typed_avalue option =
    match (av0.value, av1.value) with
    | ALoan c0, ALoan c1 -> try_merge_aloan_contents av0.ty c0 av1.ty c1
    | ABorrow c0, ABorrow c1 -> try_merge_aborrow_contents av0.ty c0 av1.ty c1
    | ASymbolic (pm0, proj0), ASymbolic (pm1, proj1) ->
        try_merge_projs (av0.ty, pm0, proj0) (av1.ty, pm1, proj1)
    | _ -> None
  in

  let merged = ref [] in
  let add_avalue (av : typed_avalue) : unit =
    let rec add avl =
      match avl with
      | [] -> [ av ]
      | av' :: avl -> (
          match try_merge_avalues av av' with
          | None ->
              (* No merge: continue *)
              av' :: add avl
          | Some av'' ->
              (* The two values were merged together: introduce the merged value
               and stop the exploration *)
              av'' :: avl)
    in
    merged := add !merged
  in

  List.iter add_avalue avalues;

  (* We're done *)
  !merged

(** Auxiliary function.

    Merge two abstractions into one, without updating the context. *)
let merge_abstractions (span : Meta.span) (abs_kind : abs_kind) (can_end : bool)
    (merge_funs : merge_duplicates_funcs option) (ctx : eval_ctx) (abs0 : abs)
    (abs1 : abs) : abs =
  [%ltrace
    "- abs0:\n"
    ^ abs_to_string span ctx abs0
    ^ "\n\n- abs1:\n"
    ^ abs_to_string span ctx abs1];
  (* Sanity check: we can't merge an abstraction with itself *)
  [%sanity_check] span (abs0.abs_id <> abs1.abs_id);

  (* Check that the abstractions are destructured (i.e., there are no nested
     values, etc.) *)
  if !Config.sanity_checks then (
    let destructure_shared_values = true in
    [%sanity_check] span
      (abs_is_destructured span destructure_shared_values ctx abs0);
    [%sanity_check] span
      (abs_is_destructured span destructure_shared_values ctx abs1));

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
    { owned }
  in

  (* Phase 1: split the markers (note that the presence of markers is controlled
     by [merge_funs]: if it is [Some] then there can be markers, otherwise there
     can't be).

     We do so because it makes it easier to implement the merge, in cases like this:
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
  let allow_markers = Option.is_some merge_funs in
  let abs0, abs1 =
    if allow_markers then
      (abs_split_markers span ctx abs0, abs_split_markers span ctx abs1)
    else (abs0, abs1)
  in

  (* Phase 2: simplify the loans coming from the left abstraction with
     the borrows coming from the right abstraction. *)
  let avalues =
    merge_abstractions_merge_loan_borrow_pairs span ~allow_markers ctx abs0 abs1
  in

  (* Phase 3: we now remove markers, by merging pairs of the same element with
     different markers into one element. To do so, we linearly traverse the list
     of avalues created through the first phase. *)
  let avalues =
    match merge_funs with
    | None -> avalues
    | Some merge_funs ->
        merge_abstractions_merge_markers span merge_funs ctx regions.owned
          avalues
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
  [%sanity_check] span (abs_is_destructured span true ctx abs);
  (* Return *)
  abs

(** Merge the regions in a context to a single region *)
let ctx_merge_regions (ctx : eval_ctx) (rid : RegionId.id)
    (rids : RegionId.Set.t) : eval_ctx =
  let rsubst x = if RegionId.Set.mem x rids then rid else x in
  let env = Substitute.env_subst_rids rsubst ctx.env in
  { ctx with env }

(** End the shared loans in a given abstraction which do not have corresponding
    shared borrows in the context *)
let end_endable_shared_loans_at_abs (span : Meta.span) (ctx : eval_ctx)
    (abs_id : AbstractionId.id) : eval_ctx =
  (* Compute the set of shared borrows appearing in the context *)
  let bids = (fst (compute_ctx_ids ctx)).borrow_ids in

  (* Update the shared borrows in the region abstraction - we assume the
     region abstraction has been destructured
  *)
  let abs = ctx_lookup_abs ctx abs_id in
  let keep_value (av : typed_avalue) : bool =
    match av.value with
    | ALoan (ASharedLoan (_, bid, _, child)) ->
        [%sanity_check] span (is_aignored child.value);
        BorrowId.Set.mem bid bids
    | _ -> true
  in

  let avalues = List.filter keep_value abs.avalues in
  let abs = { abs with avalues } in
  fst (ctx_subst_abs span ctx abs_id abs)

let merge_into_first_abstraction (span : Meta.span) (abs_kind : abs_kind)
    (can_end : bool) (merge_funs : merge_duplicates_funcs option)
    (ctx : eval_ctx) (abs_id0 : AbstractionId.id) (abs_id1 : AbstractionId.id) :
    eval_ctx * AbstractionId.id =
  (* Small sanity check *)
  [%sanity_check] span (abs_id0 <> abs_id1);

  (* Lookup the abstractions *)
  let abs0 = ctx_lookup_abs ctx abs_id0 in
  let abs1 = ctx_lookup_abs ctx abs_id1 in

  (* Merge them *)
  let nabs =
    merge_abstractions span abs_kind can_end merge_funs ctx abs0 abs1
  in
  Invariants.opt_type_check_abs span ctx nabs;

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

  (* End the loans in the region abstraction which don't have corresponding borrows anymore *)
  let ctx = end_endable_shared_loans_at_abs span ctx nabs.abs_id in

  (* Return *)
  (ctx, nabs.abs_id)

(** Reorder the loans and borrows inside the fresh abstractions.

    See {!reorder_fresh_abs}. *)
let reorder_loans_borrows_in_fresh_abs (span : Meta.span) (allow_markers : bool)
    (old_abs_ids : AbstractionId.Set.t) (ctx : eval_ctx) : eval_ctx =
  let reorder_in_fresh_abs (abs : abs) : abs =
    (* Split between the loans and borrows, and between the concrete
       and symbolic values. *)
    let is_borrow (av : typed_avalue) : bool =
      match av.value with
      | ABorrow _ | ASymbolic (_, AProjBorrows _) -> true
      | ALoan _ | ASymbolic (_, AProjLoans _) -> false
      | _ -> [%craise] span "Unexpected"
    in
    let is_concrete (av : typed_avalue) : bool =
      match av.value with
      | ABorrow _ | ALoan _ -> true
      | ASymbolic (_, (AProjBorrows _ | AProjLoans _)) -> false
      | _ -> [%craise] span "Unexpected"
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
      | ABorrow (AMutBorrow (pm, bid, _) | ASharedBorrow (pm, bid, _)) ->
          [%sanity_check] span (allow_markers || pm = PNone);
          bid
      | _ -> [%craise] span "Unexpected"
    in
    let get_loan_id (av : typed_avalue) : BorrowId.id =
      match av.value with
      | ALoan (AMutLoan (pm, lid, _)) ->
          [%sanity_check] span (allow_markers || pm = PNone);
          lid
      | ALoan (ASharedLoan (pm, lid, _, _)) ->
          [%sanity_check] span (allow_markers || pm = PNone);
          lid
      | _ -> [%craise] span "Unexpected"
    in
    let get_symbolic_id (av : typed_avalue) : SymbolicValueId.id =
      match av.value with
      | ASymbolic (pm, aproj) -> begin
          [%sanity_check] span (allow_markers || pm = PNone);
          match aproj with
          | AProjLoans { proj; _ } | AProjBorrows { proj; _ } -> proj.sv_id
          | _ -> [%craise] span "Unexpected"
        end
      | _ -> [%craise] span "Unexpected"
    in
    let compare_pair :
        'a. ('a -> 'a -> int) -> 'a * typed_avalue -> 'a * typed_avalue -> int =
     fun compare_id x y ->
      let fst = compare_id (fst x) (fst y) in
      [%cassert] span (fst <> 0)
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
    | _ -> [%internal_error] span
  in
  let fresh_abs = List.sort cmp fresh_abs |> List.rev in

  (* Reconstruct the environment *)
  let env = fresh_abs @ env in

  { ctx with env }

let reorder_fresh_abs (span : Meta.span) (allow_markers : bool)
    (old_abs_ids : AbstractionId.Set.t) (ctx : eval_ctx) : eval_ctx =
  reorder_loans_borrows_in_fresh_abs span allow_markers old_abs_ids ctx
  |> reorder_fresh_abs_aux span old_abs_ids
