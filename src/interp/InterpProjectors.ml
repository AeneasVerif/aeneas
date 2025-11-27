open Types
open Values
open Contexts
module Subst = Substitute
open TypesUtils
open ValuesUtils
open InterpUtils
open InterpBorrowsCore

(** The local logger *)
let log = Logging.projectors_log

(** [ty] shouldn't contain erased regions *)
let rec apply_proj_borrows_on_shared_borrow (span : Meta.span) (ctx : eval_ctx)
    (regions : RegionId.Set.t) (v : tvalue) (ty : ty) : abstract_shared_borrows
    =
  (* Sanity check - TODO: move those elsewhere (here we perform the check at every
   * recursive call which is a bit overkill...) *)
  let ety = Subst.erase_regions ty in
  [%sanity_check] span (ty_is_rty ty && ety = v.ty);
  (* Project - if there are no regions from the abstraction in the type, return [_] *)
  if not (ty_has_regions_in_set regions ty) then []
  else
    match (v.value, ty) with
    | VLiteral _, TLiteral _ -> []
    | VAdt adt, TAdt { id; generics } ->
        (* Retrieve the types of the fields *)
        let field_types =
          ctx_adt_get_instantiated_field_types span ctx id adt.variant_id
            generics
        in

        (* Project over the field values *)
        let fields_types = List.combine adt.fields field_types in
        let proj_fields =
          List.map
            (fun (fv, fty) ->
              apply_proj_borrows_on_shared_borrow span ctx regions fv fty)
            fields_types
        in
        List.concat proj_fields
    | VBottom, _ -> [%craise] span "Unreachable"
    | VBorrow bc, TRef (r, ref_ty, kind) ->
        (* Retrieve the bid of the borrow and the asb of the projected borrowed value *)
        let bid, asb =
          (* Not in the set: dive *)
          match (bc, kind) with
          | VMutBorrow (bid, bv), RMut ->
              (* Apply the projection on the borrowed value *)
              let asb =
                apply_proj_borrows_on_shared_borrow span ctx regions bv ref_ty
              in
              (bid, asb)
          | VSharedBorrow (bid, _), RShared ->
              (* Lookup the shared value *)
              let ek = ek_all in
              let sv = ctx_lookup_loan span ek bid ctx in
              let asb =
                match sv with
                | _, Concrete (VSharedLoan (_, sv))
                | _, Abstract (ASharedLoan (_, _, sv, _)) ->
                    apply_proj_borrows_on_shared_borrow span ctx regions sv
                      ref_ty
                | _ -> [%craise] span "Unexpected"
              in
              (bid, asb)
          | VReservedMutBorrow _, _ ->
              [%craise] span
                "Can't apply a proj_borrow over a reserved mutable borrow"
          | _ -> [%craise] span "Unreachable"
        in
        let asb =
          (* Check if the region is in the set of projected regions (note that
           * we never project over static regions) *)
          if region_in_set r regions then
            let sid' = ctx.fresh_shared_borrow_id () in
            AsbBorrow (bid, sid') :: asb
          else asb
        in
        asb
    | VLoan _, _ -> [%craise] span "Unreachable"
    | VSymbolic s, _ ->
        (* Check that the projection doesn't contain ended regions *)
        [%sanity_check] span
          (not
             (projections_intersect span ctx.ended_regions s.sv_ty regions ty));
        [ AsbProjReborrows { sv_id = s.sv_id; proj_ty = ty } ]
    | _ -> [%craise] span "Unreachable"

let rec apply_proj_borrows (span : Meta.span) (check_symbolic_no_ended : bool)
    (ctx : eval_ctx) (regions : RegionId.Set.t) (v : tvalue) (ty : rty) :
    tavalue =
  (* Sanity check - TODO: move this elsewhere (here we perform the check at every
   * recursive call which is a bit overkill...) *)
  let ety = Substitute.erase_regions ty in
  [%sanity_check] span (ty_is_rty ty && ety = v.ty);
  (* Project - if there are no regions from the abstraction in the type, return [_] *)
  if not (ty_has_regions_in_set regions ty) then
    { value = AIgnored (Some v); ty }
  else
    let value : avalue =
      match (v.value, ty) with
      | VLiteral _, TLiteral _ -> AIgnored (Some v)
      | VAdt adt, TAdt { id; generics } ->
          (* Retrieve the types of the fields *)
          let field_types =
            ctx_adt_get_instantiated_field_types span ctx id adt.variant_id
              generics
          in
          (* Project over the field values *)
          let fields_types = List.combine adt.fields field_types in
          let proj_fields =
            List.map
              (fun (fv, fty) ->
                apply_proj_borrows span check_symbolic_no_ended ctx regions fv
                  fty)
              fields_types
          in
          AAdt { variant_id = adt.variant_id; fields = proj_fields }
      | VBottom, _ -> [%craise] span "Unreachable"
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
                    apply_proj_borrows span check_symbolic_no_ended ctx regions
                      bv ref_ty
                  in
                  AMutBorrow (PNone, bid, bv)
              | VSharedBorrow (bid, sid), RShared ->
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
                  ASharedBorrow (PNone, bid, sid)
              | VReservedMutBorrow _, _ ->
                  [%craise] span
                    "Can't apply a proj_borrow over a reserved mutable borrow"
              | _ -> [%craise] span "Unreachable"
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
                    apply_proj_borrows span check_symbolic_no_ended ctx regions
                      bv ref_ty
                  in
                  (* If the referenced type contains the region, we still need
                   * to remember it *)
                  let opt_bid =
                    if ty_has_regions_in_set regions ref_ty then Some bid
                    else None
                  in
                  (* Return *)
                  AIgnoredMutBorrow (opt_bid, bv)
              | VSharedBorrow (bid, _), RShared ->
                  (* Lookup the shared value *)
                  let ek = ek_all in
                  let sv = ctx_lookup_loan span ek bid ctx in
                  let asb =
                    match sv with
                    | _, Concrete (VSharedLoan (_, sv))
                    | _, Abstract (ASharedLoan (_, _, sv, _)) ->
                        apply_proj_borrows_on_shared_borrow span ctx regions sv
                          ref_ty
                    | _ -> [%craise] span "Unexpected"
                  in
                  AProjSharedBorrow asb
              | VReservedMutBorrow _, _ ->
                  [%craise] span
                    "Can't apply a proj_borrow over a reserved mutable borrow"
              | _ -> [%craise] span "Unreachable"
            in
            ABorrow bc
      | VLoan _, _ -> [%craise] span "Unreachable"
      | VSymbolic s, _ ->
          (* Check that the projection doesn't contain already ended regions,
           * if necessary *)
          if check_symbolic_no_ended then (
            let ty1 = s.sv_ty in
            let rset1 = ctx.ended_regions in
            let ty2 = ty in
            let rset2 = regions in
            [%ltrace
              "- ty1: " ^ ty_to_string ctx ty1 ^ "\n- rset1: "
              ^ RegionId.Set.to_string None rset1
              ^ "\n- ty2: " ^ ty_to_string ctx ty2 ^ "\n- rset2: "
              ^ RegionId.Set.to_string None rset2
              ^ "\n"];
            [%sanity_check] span
              (not (projections_intersect span rset1 ty1 rset2 ty2)));
          ASymbolic
            ( PNone,
              AProjBorrows
                { proj = { sv_id = s.sv_id; proj_ty = ty }; loans = [] } )
      | _ ->
          [%ltrace
            "unexpected inputs:\n- input value: "
            ^ tvalue_to_string ~span:(Some span) ctx v
            ^ "\n- proj rty: " ^ ty_to_string ctx ty];
          [%internal_error] span
    in
    { value; ty }

let rec apply_eproj_borrows (span : Meta.span) (check_symbolic_no_ended : bool)
    (ctx : eval_ctx) (regions : RegionId.Set.t) (v : tvalue) (ty : rty) :
    tevalue =
  (* Sanity check - TODO: move this elsewhere (here we perform the check at every
   * recursive call which is a bit overkill...) *)
  let ety = Substitute.erase_regions ty in
  [%sanity_check] span (ty_is_rty ty && ety = v.ty);
  (* Project - if there are no regions from the abstraction in the type, return [_] *)
  if not (ty_has_regions_in_set regions ty) then { value = EIgnored; ty }
  else
    let value : evalue =
      match (v.value, ty) with
      | VLiteral _, TLiteral _ -> EIgnored
      | VAdt adt, TAdt { id; generics } ->
          (* Retrieve the types of the fields *)
          let field_types =
            ctx_adt_get_instantiated_field_types span ctx id adt.variant_id
              generics
          in
          (* Project over the field values *)
          let fields_types = List.combine adt.fields field_types in
          let proj_fields =
            List.map
              (fun (fv, fty) ->
                apply_eproj_borrows span check_symbolic_no_ended ctx regions fv
                  fty)
              fields_types
          in
          EAdt { variant_id = adt.variant_id; fields = proj_fields }
      | VBottom, _ -> [%craise] span "Unreachable"
      | VBorrow bc, TRef (r, ref_ty, kind) ->
          if
            (* Check if the region is in the set of projected regions (note that
             * we never project over static regions) *)
            region_in_set r regions
          then
            (* In the set *)
            match (bc, kind) with
            | VMutBorrow (bid, bv), RMut ->
                (* Apply the projection on the borrowed value *)
                let bv' =
                  apply_eproj_borrows span check_symbolic_no_ended ctx regions
                    bv ref_ty
                in
                EBorrow (EMutBorrow (PNone, bid, bv'))
            | VSharedBorrow (_, _), RShared ->
                (* We do not need to track shared borrows *)
                EIgnored
            | VReservedMutBorrow _, _ ->
                [%craise] span
                  "Can't apply a proj_borrow over a reserved mutable borrow"
            | _ -> [%craise] span "Unreachable"
          else begin
            (* Not in the set: ignore the borrow, but project the borrowed
               value (maybe some borrows *inside* the borrowed value are in
               the region set) *)
            match (bc, kind) with
            | VMutBorrow (bid, bv), RMut ->
                (* Apply the projection on the borrowed value *)
                let bv =
                  apply_eproj_borrows span check_symbolic_no_ended ctx regions
                    bv ref_ty
                in
                (* If the referenced type contains the region, we still need
                 * to remember it *)
                let opt_bid =
                  if ty_has_regions_in_set regions ref_ty then Some bid
                  else None
                in
                (* Return *)
                EBorrow (EIgnoredMutBorrow (opt_bid, bv))
            | VSharedBorrow (_, _), RShared ->
                (* We ignore shared borrows *)
                EIgnored
            | VReservedMutBorrow _, _ ->
                [%craise] span
                  "Can't apply a proj_borrow over a reserved mutable borrow"
            | _ -> [%craise] span "Unreachable"
          end
      | VLoan _, _ -> [%craise] span "Unreachable"
      | VSymbolic s, _ ->
          (* Check that the projection doesn't contain already ended regions,
           * if necessary *)
          if check_symbolic_no_ended then (
            let ty1 = s.sv_ty in
            let rset1 = ctx.ended_regions in
            let ty2 = ty in
            let rset2 = regions in
            [%ltrace
              "- ty1: " ^ ty_to_string ctx ty1 ^ "\n- rset1: "
              ^ RegionId.Set.to_string None rset1
              ^ "\n- ty2: " ^ ty_to_string ctx ty2 ^ "\n- rset2: "
              ^ RegionId.Set.to_string None rset2
              ^ "\n"];
            [%sanity_check] span
              (not (projections_intersect span rset1 ty1 rset2 ty2)));
          (* Only introduce a projection if the value contains mutable
             borrows which intersect the current regions *)
          let type_infos = ctx.type_ctx.type_infos in
          if ty_has_mut_borrow_for_region_in_set type_infos regions ty then
            ESymbolic
              ( PNone,
                EProjBorrows
                  { proj = { sv_id = s.sv_id; proj_ty = ty }; loans = [] } )
          else EIgnored
      | _ ->
          [%ltrace
            "unexpected inputs:\n- input value: "
            ^ tvalue_to_string ~span:(Some span) ctx v
            ^ "\n- proj rty: " ^ ty_to_string ctx ty];
          [%internal_error] span
    in
    { value; ty }

let symbolic_expansion_non_borrow_to_value (span : Meta.span)
    (sv : symbolic_value) (see : symbolic_expansion) : tvalue =
  let ty = Subst.erase_regions sv.sv_ty in
  let value =
    match see with
    | SeLiteral cv -> VLiteral cv
    | SeAdt (variant_id, fields) ->
        let fields = List.map mk_tvalue_from_symbolic_value fields in
        VAdt { variant_id; fields }
    | SeMutRef (_, _) | SeSharedRef (_, _) ->
        [%craise] span "Unexpected symbolic reference expansion"
  in
  { value; ty }

let symbolic_expansion_non_shared_borrow_to_value (span : Meta.span)
    (sv : symbolic_value) (see : symbolic_expansion) : tvalue =
  match see with
  | SeMutRef (bid, bv) ->
      let ty = Subst.erase_regions sv.sv_ty in
      let bv = mk_tvalue_from_symbolic_value bv in
      let value = VBorrow (VMutBorrow (bid, bv)) in
      { value; ty }
  | SeSharedRef (_, _) ->
      [%craise] span "Unexpected symbolic shared reference expansion"
  | _ -> symbolic_expansion_non_borrow_to_value span sv see

(** Apply (and reduce) a projector over loans to a value.

    Remark: we need the evaluation context only to access the type declarations.

    TODO: detailed comments. See [apply_proj_borrows] *)
let apply_proj_loans_on_symbolic_expansion (span : Meta.span)
    (regions : RegionId.Set.t) (see : symbolic_expansion) (original_sv_ty : rty)
    (proj_ty : rty) (ctx : eval_ctx) : tavalue =
  (* Sanity check: if we have a proj_loans over a symbolic value, it should
   * contain regions which we will project *)
  [%sanity_check] span (ty_has_regions_in_set regions original_sv_ty);
  (* Match *)
  let (value, ty) : avalue * ty =
    match (see, proj_ty) with
    | SeLiteral lit, TLiteral _ ->
        ( AIgnored (Some { value = VLiteral lit; ty = original_sv_ty }),
          original_sv_ty )
    | SeAdt (variant_id, fields), TAdt { id = adt_id; generics } ->
        (* Project over the field values *)
        let field_types =
          ctx_adt_get_instantiated_field_types span ctx adt_id variant_id
            generics
        in
        let fields =
          List.map2
            (mk_aproj_loans_value_from_symbolic_value regions)
            fields field_types
        in
        (AAdt { variant_id; fields }, original_sv_ty)
    | SeMutRef (bid, spc), TRef (r, ref_ty, RMut) ->
        (* Sanity check *)
        [%sanity_check] span (spc.sv_ty = ref_ty);
        (* Apply the projector to the borrowed value *)
        let child_av =
          mk_aproj_loans_value_from_symbolic_value regions spc ref_ty
        in
        (* Check if the region is in the set of projected regions (note that
         * we never project over static regions) *)
        if region_in_set r regions then
          (* In the set: keep *)
          (ALoan (AMutLoan (PNone, bid, child_av)), ref_ty)
        else
          (* Not in the set: ignore *)
          (* If the type of the referenced value contains the region, we still
             need to remember it *)
          let opt_bid =
            if ty_has_regions_in_set regions ref_ty then Some bid else None
          in
          (ALoan (AIgnoredMutLoan (opt_bid, child_av)), ref_ty)
    | SeSharedRef (bid, spc), TRef (r, ref_ty, RShared) ->
        (* Sanity check *)
        [%sanity_check] span (spc.sv_ty = ref_ty);
        (* Apply the projector to the borrowed value *)
        let child_av =
          mk_aproj_loans_value_from_symbolic_value regions spc ref_ty
        in
        (* Check if the region is in the set of projected regions (note that
         * we never project over static regions) *)
        if region_in_set r regions then
          (* In the set: keep *)
          let shared_value = mk_tvalue_from_symbolic_value spc in
          (ALoan (ASharedLoan (PNone, bid, shared_value, child_av)), ref_ty)
        else
          (* Not in the set: ignore *)
          (ALoan (AIgnoredSharedLoan child_av), ref_ty)
    | _ -> [%craise] span "Unreachable"
  in
  { value; ty }

let apply_eproj_loans_on_symbolic_expansion (span : Meta.span)
    (regions : RegionId.Set.t) (see : symbolic_expansion) (original_sv_ty : rty)
    (proj_ty : rty) (ctx : eval_ctx) : tevalue =
  (* Sanity check: if we have a proj_loans over a symbolic value, it should
   * contain regions which we will project *)
  [%sanity_check] span (ty_has_regions_in_set regions original_sv_ty);
  let type_infos = ctx.type_ctx.type_infos in
  (* Match *)
  let (value, ty) : evalue * ty =
    match (see, proj_ty) with
    | SeLiteral _, TLiteral _ -> (EIgnored, original_sv_ty)
    | SeAdt (variant_id, fields), TAdt { id = adt_id; generics } ->
        (* Project over the field values *)
        let field_types =
          ctx_adt_get_instantiated_field_types span ctx adt_id variant_id
            generics
        in
        let fields =
          List.map2
            (mk_eproj_loans_value_from_symbolic_value type_infos regions)
            fields field_types
        in
        (EAdt { variant_id; fields }, original_sv_ty)
    | SeMutRef (bid, spc), TRef (r, ref_ty, RMut) ->
        (* Sanity check *)
        [%sanity_check] span (spc.sv_ty = ref_ty);
        (* Apply the projector to the borrowed value *)
        let child_av =
          mk_eproj_loans_value_from_symbolic_value type_infos regions spc ref_ty
        in
        (* Check if the region is in the set of projected regions (note that
         * we never project over static regions) *)
        if region_in_set r regions then
          (* In the set: keep *)
          (ELoan (EMutLoan (PNone, bid, child_av)), ref_ty)
        else
          (* Not in the set: ignore *)
          (* If the type of the referenced value contains the region, we still
             need to remember it *)
          let opt_bid =
            if ty_has_regions_in_set regions ref_ty then Some bid else None
          in
          (ELoan (EIgnoredMutLoan (opt_bid, child_av)), ref_ty)
    | SeSharedRef (_, _), TRef (_, _, RShared) ->
        (* We ignore shared borrows/loans in the abstraction expressions *)
        (EIgnored, proj_ty)
    | _ -> [%craise] span "Unreachable"
  in
  { value; ty }

(** [ty] shouldn't have erased regions *)
let apply_proj_borrows_on_input_value (span : Meta.span) (ctx : eval_ctx)
    (regions : RegionId.Set.t) (v : tvalue) (ty : rty) : tavalue =
  [%sanity_check] span (ty_is_rty ty);
  let check_symbolic_no_ended = true in
  apply_proj_borrows span check_symbolic_no_ended ctx regions v ty

let apply_eproj_borrows_on_input_value (span : Meta.span) (ctx : eval_ctx)
    (regions : RegionId.Set.t) (v : tvalue) (ty : rty) : tevalue =
  [%sanity_check] span (ty_is_rty ty);
  let check_symbolic_no_ended = true in
  apply_eproj_borrows span check_symbolic_no_ended ctx regions v ty
