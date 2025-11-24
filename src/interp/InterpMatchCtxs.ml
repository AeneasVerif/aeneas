(** This module implements support to match contexts for loops.

    The matching functions are used for instance to compute joins, or to check
    if two contexts are equivalent (modulo conversion). *)

open Types
open Values
open Contexts
open TypesUtils
open ValuesUtils
open Cps
open InterpUtils
open InterpBorrowsCore
open InterpAbs
open InterpJoinCore
module S = SynthesizeSymbolic

(** The local logger *)
let log = Logging.match_ctxs_log

let compute_abs_borrows_loans_maps (span : Meta.span) (explore : abs -> bool)
    (ctx : eval_ctx) (env : env) : abs_borrows_loans_maps =
  let abs_ids = ref [] in
  let abs_to_borrows = ref AbsId.Map.empty in
  let abs_to_non_unique_borrows = ref AbsId.Map.empty in
  let abs_to_loans = ref AbsId.Map.empty in
  let abs_to_borrow_projs = ref AbsId.Map.empty in
  let abs_to_loan_projs = ref AbsId.Map.empty in
  let borrow_to_abs = ref MarkedUniqueBorrowId.Map.empty in
  let non_unique_borrow_to_abs = ref MarkedBorrowId.Map.empty in
  let loan_to_abs = ref MarkedLoanId.Map.empty in
  let borrow_proj_to_abs = ref MarkedNormSymbProj.Map.empty in
  let loan_proj_to_abs = ref MarkedNormSymbProj.Map.empty in

  let module R (M : Collections.Map) (S : Collections.Set) = struct
    (*
       [check_singleton_sets]: check that the mapping maps to a singleton.
       We need to tweak the behavior of the sanity checks because
       of the following cases:
       - when computing the map from borrow ids (with marker) to the region
         abstractions they belong to, the marked borrow ids can map to a single
         region abstraction, i.e., to a singleton set of region abstraction ids
       - however, when computing the mapping from region abstractions to
         the borrow ids they contain, this time we do map abstraction ids
         to sets which can compute strictly more than one value
       Also: note that it is possible to copy symbolic values containing borrows
       (if those borrows are shared borrows for instance).
    *)
    let register_mapping (to_string : M.key -> S.elt -> string)
        (check_singleton_sets : bool) (map : S.t M.t ref) (id0 : M.key)
        (id1 : S.elt) : unit =
      (* Update the mapping *)
      map :=
        M.update id0
          (fun ids ->
            match ids with
            | None -> Some (S.singleton id1)
            | Some ids ->
                (* Check that we are allowed to map id0 to a set which is not
                   a singleton *)
                if check_singleton_sets then
                  [%craise] span
                    ("Internal error, please file an issue.\n\
                      Key already registered: " ^ to_string id0 id1);
                (* Check that the mapping was not already registered *)
                if S.mem id1 ids then
                  [%craise] span
                    ("Internal error, please file an issue.\n\
                      Found an already registered mapping: " ^ to_string id0 id1
                    );
                (* Update *)
                Some (S.add id1 ids))
          !map

    let register_abs_id (id : AbsId.id) (map : S.t AbsId.Map.t ref) =
      if AbsId.Map.mem id !map then () else map := AbsId.Map.add id S.empty !map
  end in
  let module RAbsUniqueBorrow = R (AbsId.Map) (MarkedUniqueBorrowId.Set) in
  let module RAbsBorrow = R (AbsId.Map) (MarkedBorrowId.Set) in
  let module RAbsLoan = R (AbsId.Map) (MarkedLoanId.Set) in
  let module RBorrowAbs = R (MarkedBorrowId.Map) (AbsId.Set) in
  let module RUniqueBorrowAbs = R (MarkedUniqueBorrowId.Map) (AbsId.Set) in
  let module RLoanAbs = R (MarkedLoanId.Map) (AbsId.Set) in
  let module RAbsSymbProj = R (AbsId.Map) (MarkedNormSymbProj.Set) in
  let module RSymbProjAbs = R (MarkedNormSymbProj.Map) (AbsId.Set) in
  let register_abs_id abs_id =
    RAbsUniqueBorrow.register_abs_id abs_id abs_to_borrows;
    RAbsBorrow.register_abs_id abs_id abs_to_non_unique_borrows;
    RAbsLoan.register_abs_id abs_id abs_to_loans;
    RAbsSymbProj.register_abs_id abs_id abs_to_borrow_projs;
    RAbsSymbProj.register_abs_id abs_id abs_to_loan_projs
  in
  let uborrow_to_string (pm, bid, sid) =
    let b =
      match sid with
      | None -> "mut_borrow@" ^ BorrowId.to_string bid
      | Some sid ->
          "shared_borrow@" ^ BorrowId.to_string bid ^ "(^"
          ^ SharedBorrowId.to_string sid
          ^ ")"
    in
    Print.Values.add_proj_marker pm b
  in
  let borrow_to_string (pm, bid) =
    "borrow@" ^ BorrowId.to_string bid |> Print.Values.add_proj_marker pm
  in
  let loan_to_string (pm, bid) =
    "loan@" ^ BorrowId.to_string bid |> Print.Values.add_proj_marker pm
  in
  let abs_id_to_string aid = "abs@" ^ AbsId.to_string aid in
  let binding_to_string fmt0 fmt1 x0 x1 = fmt0 x0 ^ " -> " ^ fmt1 x1 in
  let borrow_proj_to_string x =
    "@borrow_proj(" ^ marked_norm_symb_proj_to_string ctx x ^ ")"
  in
  let loan_proj_to_string x =
    "@loan_proj(" ^ marked_norm_symb_proj_to_string ctx x ^ ")"
  in
  let register_borrow_id (abs : abs) pm bid sid =
    RAbsUniqueBorrow.register_mapping
      (binding_to_string abs_id_to_string uborrow_to_string)
      false abs_to_borrows abs.abs_id (pm, bid, sid);
    RAbsBorrow.register_mapping
      (binding_to_string abs_id_to_string borrow_to_string)
      false abs_to_non_unique_borrows abs.abs_id (pm, bid);
    RUniqueBorrowAbs.register_mapping
      (binding_to_string uborrow_to_string abs_id_to_string)
      true borrow_to_abs (pm, bid, sid) abs.abs_id;
    RBorrowAbs.register_mapping
      (binding_to_string borrow_to_string abs_id_to_string)
      false non_unique_borrow_to_abs (pm, bid) abs.abs_id
  in

  let register_loan_id (abs : abs) pm bid =
    RAbsLoan.register_mapping
      (binding_to_string abs_id_to_string loan_to_string)
      false abs_to_loans abs.abs_id (pm, bid);
    RLoanAbs.register_mapping
      (binding_to_string loan_to_string abs_id_to_string)
      true loan_to_abs (pm, bid) abs.abs_id
  in
  let register_borrow_proj abs pm (proj : symbolic_proj) =
    let norm_proj_ty = normalize_proj_ty abs.regions.owned proj.proj_ty in
    let proj : marked_norm_symb_proj =
      { pm; sv_id = proj.sv_id; norm_proj_ty }
    in
    RAbsSymbProj.register_mapping
      (binding_to_string abs_id_to_string borrow_proj_to_string)
      false abs_to_borrow_projs abs.abs_id proj;
    (* This mapping is *actually* injective because we refresh symbolic values
       with borrows when copying them. See [InterpExpressions.copy_value]. *)
    RSymbProjAbs.register_mapping
      (binding_to_string borrow_proj_to_string abs_id_to_string)
      true borrow_proj_to_abs proj abs.abs_id
  in
  let register_loan_proj abs pm (proj : symbolic_proj) =
    let norm_proj_ty = normalize_proj_ty abs.regions.owned proj.proj_ty in
    let proj : marked_norm_symb_proj =
      { pm; sv_id = proj.sv_id; norm_proj_ty }
    in
    RAbsSymbProj.register_mapping
      (binding_to_string abs_id_to_string loan_proj_to_string)
      false abs_to_loan_projs abs.abs_id proj;
    RSymbProjAbs.register_mapping
      (binding_to_string loan_proj_to_string abs_id_to_string)
      true loan_proj_to_abs proj abs.abs_id
  in

  let explore_abs =
    object (self : 'self)
      inherit [_] iter_tavalue as super

      (** Make sure we don't register the ignored ids *)
      method! visit_aloan_content (abs, pm) lc =
        [%sanity_check] span (pm = PNone);
        match lc with
        | AMutLoan (npm, lid, child) ->
            (* Add the current marker when visiting the loan id *)
            self#visit_loan_id (abs, npm) lid;
            (* Recurse with the old marker *)
            super#visit_tavalue (abs, pm) child
        | ASharedLoan (npm, lid, sv, child) ->
            (* Add the current marker when visiting the loan ids and the shared value *)
            self#visit_loan_id (abs, npm) lid;
            self#visit_tvalue (abs, npm) sv;
            (* Recurse with the old marker *)
            self#visit_tavalue (abs, pm) child
        | AIgnoredMutLoan (_, child)
        | AEndedIgnoredMutLoan { child; given_back = _; given_back_meta = _ }
        | AIgnoredSharedLoan child ->
            [%sanity_check] span (pm = PNone);
            (* Ignore the id of the loan, if there is *)
            self#visit_tavalue (abs, pm) child
        | AEndedMutLoan { child; given_back; given_back_meta = _ } ->
            [%cassert] span (is_aignored child.value) "Not implemented yet";
            [%cassert] span (is_aignored given_back.value) "Not implemented yet"
        | AEndedSharedLoan (sv, child) ->
            (* TODO: there may be a problem here, because we need the marker which was
               in [ASharedLoan] to explore the shared value and register its borrows.
               For now we check that there are no loans/borrows inside. *)
            [%cassert] span
              (not (tvalue_has_loans_or_borrows (Some span) ctx sv))
              "Not implemented yet";
            self#visit_tavalue (abs, pm) child

      (** Make sure we don't register the ignored ids *)
      method! visit_aborrow_content (abs, pm) bc =
        [%sanity_check] span (pm = PNone);
        match bc with
        | AMutBorrow (npm, bid, child) ->
            (* Add the current marker when visiting the borrow id *)
            register_borrow_id abs npm bid None;
            (* Recurse with the old marker *)
            self#visit_tavalue (abs, pm) child
        | ASharedBorrow (npm, bid, sid) ->
            (* Add the current marker when visiting the borrow id *)
            register_borrow_id abs npm bid (Some sid)
        | AProjSharedBorrow _ ->
            [%sanity_check] span (pm = PNone);
            (* Process those normally *)
            super#visit_aborrow_content (abs, pm) bc
        | AIgnoredMutBorrow (_, child)
        | AEndedIgnoredMutBorrow { child; given_back = _; given_back_meta = _ }
          ->
            [%sanity_check] span (pm = PNone);
            (* Ignore the id of the borrow, if there is *)
            self#visit_tavalue (abs, pm) child
        | AEndedMutBorrow _ | AEndedSharedBorrow -> [%craise] span "Unreachable"

      method! visit_borrow_id _ _ = [%internal_error] span
      method! visit_loan_id (abs, pm) lid = register_loan_id abs pm lid

      method! visit_ASymbolic (abs, _) pm proj =
        match proj with
        | AProjLoans { proj; consumed; borrows } ->
            [%sanity_check] span (consumed = []);
            [%sanity_check] span (borrows = []);
            register_loan_proj abs pm proj
        | AProjBorrows { proj; loans } ->
            [%sanity_check] span (loans = []);
            register_borrow_proj abs pm proj
        | AEndedProjLoans { proj = _; consumed; borrows } ->
            [%sanity_check] span (consumed = []);
            [%sanity_check] span (borrows = [])
        | AEndedProjBorrows { mvalues = _; loans } ->
            [%sanity_check] span (loans = [])
        | AEmpty -> ()
    end
  in

  env_iter_abs
    (fun abs ->
      register_abs_id abs.abs_id;
      if explore abs then (
        abs_to_borrows :=
          AbsId.Map.add abs.abs_id MarkedUniqueBorrowId.Set.empty
            !abs_to_borrows;
        abs_to_non_unique_borrows :=
          AbsId.Map.add abs.abs_id MarkedBorrowId.Set.empty
            !abs_to_non_unique_borrows;
        abs_to_loans :=
          AbsId.Map.add abs.abs_id MarkedLoanId.Set.empty !abs_to_loans;
        abs_ids := abs.abs_id :: !abs_ids;
        List.iter (explore_abs#visit_tavalue (abs, PNone)) abs.avalues)
      else ())
    env;

  (* Rem.: there is no need to reverse the abs ids, because we explored the environment
     starting with the freshest values and abstractions *)
  {
    abs_ids = !abs_ids;
    abs_to_borrows = !abs_to_borrows;
    abs_to_non_unique_borrows = !abs_to_non_unique_borrows;
    abs_to_loans = !abs_to_loans;
    borrow_to_abs = !borrow_to_abs;
    non_unique_borrow_to_abs = !non_unique_borrow_to_abs;
    loan_to_abs = !loan_to_abs;
    abs_to_borrow_projs = !abs_to_borrow_projs;
    abs_to_loan_projs = !abs_to_loan_projs;
    borrow_proj_to_abs = !borrow_proj_to_abs;
    loan_proj_to_abs = !loan_proj_to_abs;
  }

(** Match two types during a join.

    TODO: probably don't need to take [match_regions] as input anymore. *)
let rec match_types (span : Meta.span) (ctx0 : eval_ctx) (ctx1 : eval_ctx)
    (match_distinct_types : ty -> ty -> ty)
    (match_regions : region -> region -> region) (ty0 : ty) (ty1 : ty) : ty =
  let match_rec =
    match_types span ctx0 ctx1 match_distinct_types match_regions
  in
  match (ty0, ty1) with
  | ( TAdt { id = id0; generics = generics0 },
      TAdt { id = id1; generics = generics1 } ) ->
      [%sanity_check] span (id0 = id1);
      [%sanity_check] span (generics0.const_generics = generics1.const_generics);
      [%sanity_check] span (generics0.trait_refs = generics1.trait_refs);
      let id = id0 in
      let const_generics = generics1.const_generics in
      let trait_refs = generics1.trait_refs in
      let regions =
        List.map
          (fun (id0, id1) -> match_regions id0 id1)
          (List.combine generics0.regions generics1.regions)
      in
      let types =
        List.map
          (fun (ty0, ty1) -> match_rec ty0 ty1)
          (List.combine generics0.types generics1.types)
      in
      let generics = { regions; types; const_generics; trait_refs } in
      TAdt { id; generics }
  | TVar vid0, TVar vid1 ->
      [%sanity_check] span (vid0 = vid1);
      let vid = vid0 in
      TVar vid
  | TLiteral lty0, TLiteral lty1 ->
      [%sanity_check] span (lty0 = lty1);
      ty0
  | TNever, TNever -> ty0
  | TRef (r0, ty0, k0), TRef (r1, ty1, k1) ->
      let r = match_regions r0 r1 in
      let ty = match_rec ty0 ty1 in
      [%sanity_check] span (k0 = k1);
      let k = k0 in
      TRef (r, ty, k)
  | _ -> match_distinct_types ty0 ty1

module MakeMatcher (M : PrimMatcher) : Matcher = struct
  let span = M.span

  let rec match_tvalues (ctx0 : eval_ctx) (ctx1 : eval_ctx) (v0 : tvalue)
      (v1 : tvalue) : tvalue =
    [%ldebug
      "- v0: " ^ tvalue_to_string ctx0 v0 ^ "\n- v1: "
      ^ tvalue_to_string ctx1 v1];
    let match_rec = match_tvalues ctx0 ctx1 in
    let ty = M.match_etys ctx0 ctx1 v0.ty v1.ty in
    (* Using ValuesUtils.value_ has_borrows on purpose here: we want
       to make explicit the fact that, though we have to pick
       one of the two contexts (ctx0 here) to call value_has_borrows,
       it doesn't matter here. *)
    let value_has_borrows =
      ValuesUtils.value_has_borrows (Some span) ctx0.type_ctx.type_infos
    in
    match (v0.value, v1.value) with
    | VLiteral lv0, VLiteral lv1 ->
        if lv0 = lv1 then v1
        else M.match_distinct_literals match_rec ctx0 ctx1 ty lv0 lv1
    | VAdt av0, VAdt av1 ->
        if av0.variant_id = av1.variant_id then
          let fields = List.combine av0.fields av1.fields in
          let fields = List.map (fun (f0, f1) -> match_rec f0 f1) fields in
          let value : value = VAdt { variant_id = av0.variant_id; fields } in
          { value; ty = v1.ty }
        else M.match_distinct_adts match_rec ctx0 ctx1 ty v0.ty av0 v1.ty av1
    | VBottom, VBottom -> v0
    | VBorrow bc0, VBorrow bc1 ->
        let bc =
          match (bc0, bc1) with
          | VSharedBorrow (bid0, sid0), VSharedBorrow (bid1, sid1) ->
              let bid, sid =
                M.match_shared_borrows match_rec ctx0 ctx1 ty bid0 sid0 bid1
                  sid1
              in
              VSharedBorrow (bid, sid)
          | VMutBorrow (bid0, bv0), VMutBorrow (bid1, bv1) ->
              let bv = match_rec bv0 bv1 in

              [%cassert] M.span
                (not
                   (ValuesUtils.value_has_borrows (Some span)
                      ctx0.type_ctx.type_infos bv.value))
                "The join of nested borrows is not supported yet";
              let bid, bv =
                M.match_mut_borrows match_rec ctx0 ctx1 ty bid0 bv0 bid1 bv1 bv
              in
              VMutBorrow (bid, bv)
          | VReservedMutBorrow _, _
          | _, VReservedMutBorrow _
          | VSharedBorrow _, VMutBorrow _
          | VMutBorrow _, VSharedBorrow _ ->
              (* If we get here, either there is a typing inconsistency, or we are
                 trying to match a reserved borrow, which shouldn't happen because
                 reserved borrow should be eliminated very quickly - they are introduced
                 just before function calls which activate them *)
              [%craise] M.span "Unexpected"
        in
        { value = VBorrow bc; ty }
    | VLoan lc0, VLoan lc1 -> begin
        match (lc0, lc1) with
        | VSharedLoan (id0, sv0), VSharedLoan (id1, sv1) ->
            let sv = match_rec sv0 sv1 in
            [%cassert] M.span
              (not (value_has_borrows sv.value))
              "The join of nested borrows is not supported yet";
            M.match_shared_loans match_rec ctx0 ctx1 ty id0 id1 sv
        | VMutLoan id0, VMutLoan id1 ->
            M.match_mut_loans match_rec ctx0 ctx1 ty id0 id1
        | VSharedLoan _, VMutLoan _ | VMutLoan _, VSharedLoan _ ->
            (* TODO: *)
            [%craise] M.span "Unimplemented"
      end
    | VSymbolic sv0, VSymbolic sv1 ->
        [%cassert] M.span
          (not
             (ety_has_nested_borrows (Some span) ctx0.type_ctx.type_infos v0.ty))
          "Nested borrows are not supported yet.";
        [%cassert] M.span
          (not
             (ety_has_nested_borrows (Some span) ctx1.type_ctx.type_infos v1.ty))
          "Nested borrows are not supported yet.";
        (* Match *)
        let sv = M.match_symbolic_values match_rec ctx0 ctx1 sv0 sv1 in
        { v1 with value = VSymbolic sv }
    | VLoan (VMutLoan id), _ ->
        M.match_mut_loan_with_other match_rec ctx0 ctx1 ~loan_is_left:true ty id
          v1
    | _, VLoan (VMutLoan id) ->
        M.match_mut_loan_with_other match_rec ctx0 ctx1 ~loan_is_left:false ty
          id v0
    | VLoan (VSharedLoan (id, sv)), _ ->
        M.match_shared_loan_with_other match_rec ctx0 ctx1 ~loan_is_left:true ty
          id sv v1
    | _, VLoan (VSharedLoan (id, sv)) ->
        M.match_shared_loan_with_other match_rec ctx0 ctx1 ~loan_is_left:false
          ty id sv v0
    | VSymbolic sv, _ ->
        M.match_symbolic_with_other match_rec ctx0 ctx1 ~symbolic_is_left:true
          sv v1
    | _, VSymbolic sv ->
        M.match_symbolic_with_other match_rec ctx0 ctx1 ~symbolic_is_left:false
          sv v0
    | VBottom, _ ->
        M.match_bottom_with_other match_rec ctx0 ctx1 ~bottom_is_left:true v1
    | _, VBottom ->
        M.match_bottom_with_other match_rec ctx0 ctx1 ~bottom_is_left:false v0
    | _ ->
        [%ltrace
          "Unexpected match case:\n- value0: "
          ^ tvalue_to_string ~span:(Some M.span) ctx0 v0
          ^ "\n- value1: "
          ^ tvalue_to_string ~span:(Some M.span) ctx1 v1];
        [%internal_error] M.span

  and match_tavalues (ctx0 : eval_ctx) (ctx1 : eval_ctx) (v0 : tavalue)
      (v1 : tavalue) : tavalue =
    [%ltrace
      "- value0: "
      ^ tavalue_to_string ~span:(Some M.span) ctx0 v0
      ^ "\n- value1: "
      ^ tavalue_to_string ~span:(Some M.span) ctx1 v1];

    (* Using ValuesUtils.value_has_borrows on purpose here: we want
       to make explicit the fact that, though we have to pick
       one of the two contexts (ctx0 here) to call value_has_borrows,
       it doesn't matter here. *)
    let value_has_borrows =
      ValuesUtils.value_has_borrows (Some span) ctx0.type_ctx.type_infos
    in

    let match_rec = match_tvalues ctx0 ctx1 in
    let match_arec = match_tavalues ctx0 ctx1 in
    let ty = M.match_rtys ctx0 ctx1 v0.ty v1.ty in
    match (v0.value, v1.value) with
    | AAdt av0, AAdt av1 ->
        if av0.variant_id = av1.variant_id then
          let fields = List.combine av0.fields av1.fields in
          let fields = List.map (fun (f0, f1) -> match_arec f0 f1) fields in
          let value : avalue = AAdt { variant_id = av0.variant_id; fields } in
          { value; ty }
        else (* Merge *)
          M.match_distinct_aadts match_rec ctx0 ctx1 v0.ty av0 v1.ty av1 ty
    | AIgnored _, AIgnored _ -> mk_aignored M.span ty None
    | ABorrow bc0, ABorrow bc1 -> (
        [%ltrace "borrows"];
        match (bc0, bc1) with
        | ASharedBorrow (pm0, bid0, sid0), ASharedBorrow (pm1, bid1, sid1) ->
            [%ltrace "shared borrows"];
            M.match_ashared_borrows match_rec ctx0 ctx1 v0.ty pm0 bid0 sid0
              v1.ty pm1 bid1 sid1 ty
        | AMutBorrow (pm0, bid0, av0), AMutBorrow (pm1, bid1, av1) ->
            [%ltrace "mut borrows"];
            [%ltrace "mut borrows: matching children values"];
            let av = match_arec av0 av1 in
            [%ltrace "mut borrows: matched children values"];
            M.match_amut_borrows match_rec ctx0 ctx1 v0.ty pm0 bid0 av0 v1.ty
              pm1 bid1 av1 ty av
        | AIgnoredMutBorrow _, AIgnoredMutBorrow _ ->
            (* The abstractions are destructured: we shouldn't get there *)
            [%craise] M.span "Unexpected"
        | AProjSharedBorrow asb0, AProjSharedBorrow asb1 -> (
            match (asb0, asb1) with
            | [], [] ->
                (* This case actually stands for ignored shared borrows, when
                   there are no nested borrows *)
                v0
            | _ ->
                (* We should get there only if there are nested borrows *)
                [%craise] M.span "Unexpected")
        | _ ->
            (* TODO: getting there is not necessarily inconsistent (it may
               just be because the environments don't match) so we may want
               to call a specific function (which could raise the proper
               exception).
               Rem.: we shouldn't get to the ended borrow cases, because
               an abstraction should never contain ended borrows unless
               we are *currently* ending it, in which case we need
               to completely end it before continuing.
            *)
            [%craise] M.span "Unexpected")
    | ALoan lc0, ALoan lc1 -> (
        [%ltrace "loans"];
        (* TODO: maybe we should enforce that the ids are always exactly the same -
           without matching *)
        match (lc0, lc1) with
        | ASharedLoan (pm0, id0, sv0, av0), ASharedLoan (pm1, id1, sv1, av1) ->
            [%ltrace "shared loans"];
            let sv = match_rec sv0 sv1 in
            let av = match_arec av0 av1 in
            [%sanity_check] M.span (not (value_has_borrows sv.value));
            M.match_ashared_loans match_rec ctx0 ctx1 v0.ty pm0 id0 sv0 av0
              v1.ty pm1 id1 sv1 av1 ty sv av
        | AMutLoan (pm0, id0, av0), AMutLoan (pm1, id1, av1) ->
            [%ltrace "mut loans"];
            [%ltrace "mut loans: matching children values"];
            let av = match_arec av0 av1 in
            [%ltrace "mut loans: matched children values"];
            M.match_amut_loans match_rec ctx0 ctx1 v0.ty pm0 id0 av0 v1.ty pm1
              id1 av1 ty av
        | AIgnoredMutLoan _, AIgnoredMutLoan _
        | AIgnoredSharedLoan _, AIgnoredSharedLoan _ ->
            (* Those should have been filtered when destructuring the abstractions -
               they are necessary only when there are nested borrows *)
            [%craise] M.span "Unreachable"
        | _ -> [%craise] M.span "Unreachable")
    | ASymbolic (pm0, proj0), ASymbolic (pm1, proj1) -> begin
        match (proj0, proj1) with
        | ( AProjBorrows ({ proj = proj0; _ } as pborrows0),
            AProjBorrows ({ proj = proj1; _ } as pborrows1) ) ->
            let proj_ty = M.match_rtys ctx0 ctx1 proj0.proj_ty proj1.proj_ty in
            M.match_aproj_borrows match_rec ctx0 ctx1 v0.ty pm0 pborrows0 v1.ty
              pm1 pborrows1 ty proj_ty
        | ( AProjLoans ({ proj = proj0; _ } as ploans0),
            AProjLoans ({ proj = proj1; _ } as ploans1) ) ->
            let proj_ty = M.match_rtys ctx0 ctx1 proj0.proj_ty proj1.proj_ty in
            M.match_aproj_loans match_rec ctx0 ctx1 v0.ty pm0 ploans0 v1.ty pm1
              ploans1 ty proj_ty
        | _ -> [%craise] M.span "Unreachable"
      end
    | _ -> M.match_avalues match_rec ctx0 ctx1 v0 v1
end

module MakeJoinMatcher (S : MatchJoinState) : PrimMatcher = struct
  (** Small utility *)
  let span = S.span

  let push_abs (abs : abs) : unit = S.nabs := abs :: !S.nabs
  let push_absl (absl : abs list) : unit = List.iter push_abs absl

  let add_symbolic_value (sv_id : SymbolicValueId.id) (left : tvalue)
      (right : tvalue) : unit =
    S.symbolic_to_value :=
      SymbolicValueId.Map.add sv_id (left, right) !S.symbolic_to_value

  let add_fresh_symbolic_value_from_no_regions_ty (ctx : eval_ctx) ty
      (left : tvalue) (right : tvalue) : tvalue =
    let sv = mk_fresh_symbolic_tvalue_from_no_regions_ty span ctx ty in
    let sv_id = [%add_loc] symbolic_tvalue_get_id span sv in
    add_symbolic_value sv_id left right;
    sv

  let add_fresh_symbolic_value (ctx : eval_ctx) ty (left : tvalue)
      (right : tvalue) : tvalue =
    let sv = mk_fresh_symbolic_tvalue span ctx ty in
    let sv_id = [%add_loc] symbolic_tvalue_get_id span sv in
    add_symbolic_value sv_id left right;
    sv

  let rec refresh_fresh_symbolic_values_in_joined_value (ctx : eval_ctx)
      (v : tvalue) : tvalue =
    let refresh = refresh_fresh_symbolic_values_in_joined_value ctx in
    let value =
      match v.value with
      | VLiteral _ -> v.value
      | VBottom -> [%craise] span "Unexpected"
      | VAdt { variant_id; fields } ->
          let fields = List.map refresh fields in
          VAdt { variant_id; fields }
      | VBorrow bc -> (
          match bc with
          | VSharedBorrow _ | VReservedMutBorrow _ -> v.value
          | VMutBorrow (bid, v) -> VBorrow (VMutBorrow (bid, refresh v)))
      | VLoan lc -> (
          match lc with
          | VSharedLoan (lid, sv) -> VLoan (VSharedLoan (lid, refresh sv))
          | VMutLoan _ -> v.value)
      | VSymbolic sv -> (
          [%cassert] span
            (not (ty_has_borrows (Some span) ctx.type_ctx.type_infos sv.sv_ty))
            "Not implemented";
          (* Refresh the symbolic value.

             Look up the symbolic value to check if it was introduced by a join. *)
          match SymbolicValueId.Map.find_opt sv.sv_id !S.symbolic_to_value with
          | None ->
              (* The symbolic value is not fresh: let's just copy it *)
              (add_fresh_symbolic_value ctx sv.sv_ty v v).value
          | Some (lv, rv) ->
              (* Introduce a fresh symbolic value which derives from the same values *)
              (add_fresh_symbolic_value ctx sv.sv_ty lv rv).value)
    in
    { v with value }

  let match_etys _ _ ty0 ty1 =
    [%sanity_check] span (ty0 = ty1);
    ty0

  let match_rtys _ _ ty0 ty1 =
    (* The types must be equal - in effect, this forbids to match symbolic
       values containing borrows *)
    [%sanity_check] span (ty0 = ty1);
    ty0

  let match_distinct_literals (_ : tvalue_matcher) (ctx0 : eval_ctx)
      (_ : eval_ctx) (ty : ety) (v0 : literal) (v1 : literal) : tvalue =
    add_fresh_symbolic_value_from_no_regions_ty ctx0 ty
      { value = VLiteral v0; ty }
      { value = VLiteral v1; ty }

  (* Helper *)
  let no_loans_no_bottoms_to_symbolic_value_with_borrows (ctx0 : eval_ctx)
      (ctx1 : eval_ctx) (v0 : tvalue) (v1 : tvalue) : tvalue =
    [%sanity_check] span (not (tvalue_has_loans v0));
    [%sanity_check] span (not (tvalue_has_bottom ctx0 v0));
    [%sanity_check] span (not (tvalue_has_loans v1));
    [%sanity_check] span (not (tvalue_has_bottom ctx1 v1));

    (* Introduce a fresh region id for each erased region appearing in the type.

       TODO: we might have to do some unification to determine whether some
       regions should be equal or not. *)
    let fresh_regions, ty_with_regions =
      ty_refresh_regions (Some span) ctx0.fresh_region_id v0.ty
    in

    (* Introduce a fresh symbolic value for the join *)
    let sv = add_fresh_symbolic_value ctx0 ty_with_regions v0 v1 in
    let sv_s = tvalue_as_symbolic span sv in

    (* Project the ADTs into different region abstractions *)
    let project (rid : RegionId.id) =
      let regions = RegionId.Set.singleton rid in
      let avl0, output0 =
        convert_value_to_output_avalues span ctx0 PLeft v0 regions
          ty_with_regions
      in
      let avl1, output1 =
        convert_value_to_output_avalues span ctx1 PRight v1 regions
          ty_with_regions
      in
      let av : tavalue =
        let proj : symbolic_proj =
          { sv_id = sv_s.sv_id; proj_ty = ty_with_regions }
        in
        let value =
          ASymbolic (PNone, AProjLoans { proj; consumed = []; borrows = [] })
        in
        { value; ty = ty_with_regions }
      in

      (* Create the abstraction expression *)
      let cont : abs_cont option =
        if S.with_abs_conts then
          if
            TypesUtils.ty_has_mut_borrows ctx0.type_ctx.type_infos
              ty_with_regions
          then
            (* We used to generate a continuation of the following shape:
               {[
                 join(|(s0 <: Option<&'a mut (T)>)|, Option::Some (︙MB l0))︙) :=
                 ⌊s1 <: Option<&'a mut (T)>⌋
               ]}

               but joins in abstraction outputs are a bit annoying to handle
               when merging continuations, so now we generate something like this:

               {[
                 (|(s0 <: Option<&'a mut (T)>)|, Option::Some (︙MB l0))︙) :=
                 let x := ⌊s1 <: Option<&'a mut (T)>⌋ in
                 (x, x)
               ]}

               TODO: generalize the merge of continuations and revert the changes.
            *)
            let input : tevalue =
              let proj : esymbolic_proj =
                { sv_id = sv_s.sv_id; proj_ty = ty_with_regions }
              in
              let value =
                ESymbolic
                  (PNone, EProjLoans { proj; consumed = []; borrows = [] })
              in
              let input = { value; ty = ty_with_regions } in

              (* Create the let-binding *)
              let fvar = mk_fresh_abs_fvar ty_with_regions in
              let pair = mk_etuple [ fvar; fvar ] in
              let pat = mk_epat_from_fvar fvar in
              mk_let span regions pat input pair
            in

            let output = mk_simpl_etuple [ output0; output1 ] in
            Some { output = Some output; input = Some input }
          else
            Some
              {
                output = Some (mk_simpl_etuple []);
                input = Some (mk_simpl_etuple []);
              }
        else None
      in

      (* Generate the abstraction *)
      let abs =
        {
          abs_id = ctx0.fresh_abs_id ();
          kind = S.fresh_abs_kind;
          can_end = true;
          parents = AbsId.Set.empty;
          original_parents = [];
          regions = { owned = RegionId.Set.singleton rid };
          avalues = avl0 @ avl1 @ [ av ];
          cont;
        }
      in
      [%ldebug "Pushing abs:\n" ^ abs_to_string span ctx0 abs];
      push_abs abs
    in
    List.iter project fresh_regions;

    (* *)
    sv

  (* Helper *)
  let to_symbolic_value_with_borrows (ctx0 : eval_ctx) (ctx1 : eval_ctx)
      (v0 : tvalue) (v1 : tvalue) : tvalue =
    if tvalue_has_bottom ctx0 v0 || tvalue_has_bottom ctx1 v1 then (
      (* We have to pay attention to the case where we need to join a value containing *outer*
         loans with a value containing bottoms. For instance, when joining:
         {[
           v -> bottom   U   v -> SL l 0
         ]}

         A problem is that we can't move [SL l 0] to a region abstraction or an
         anonymous values, because it is an **outer** loan: doing so would allow the
         loan to live indefinitely, and in particuler we would be allowed to
         overwrite [v] without ending it.

         A possibility is to force [l] to end, but then it might lead to a borrow
         checking issue later on, when trying to use the borrow [l]. Our solution is
         to use a shared loan containing the value bottom, leading to the following
         environment:

         {[
           v -> SL l' bottom
           abs { SB l', SL l 0 }
         ]}

         This way, the borrow [l] is preserved, but upon overwriting [v] we have to
         en [l'], which in turns requires ending [l]. We also can't *read* from [v],
         because after we ended the loan, [v] maps to [bottom] (we can only write to
         it). Also note that the shared borrow [l'] can't be used in any way (in
         particular, it can't be dereferenced).

         Finally, this solution works for mutable borrows/loans:
         {[
           v -> bottom   U   v -> ML l

             ~>

           v -> SL l' bottom
           abs { SB l', ML l }
         ]} *)
      let has_outer_loans =
        tvalue_has_outer_loans v0 || tvalue_has_outer_loans v1
      in
      (* Move the values to region abstractions *)
      let abs_kind = S.fresh_abs_kind in
      let to_absl pm ctx v =
        let absl =
          convert_value_to_abstractions span abs_kind ~can_end:true ctx v
        in
        List.map (abs_add_marker span ctx pm) absl
      in
      let absl = to_absl PLeft ctx0 v0 @ to_absl PRight ctx1 v1 in
      (* If there are outer loans, wrap the bottom inside a shared loan, and add
         a corresponding borrow to all the region abstractions *)
      let v = mk_bottom span (erase_regions v0.ty) in
      let v, absl =
        if has_outer_loans then
          let lid = ctx0.fresh_borrow_id () in
          let absl =
            List.map
              (fun (abs : abs) ->
                let rid = RegionId.Set.choose abs.regions.owned in
                let sb : tavalue =
                  {
                    value =
                      ABorrow
                        (ASharedBorrow
                           (PNone, lid, ctx0.fresh_shared_borrow_id ()));
                    ty = TRef (RVar (Free rid), v0.ty, RShared);
                  }
                in
                { abs with avalues = sb :: abs.avalues })
              absl
          in
          let v : tvalue =
            { value = VLoan (VSharedLoan (lid, v)); ty = v.ty }
          in
          (v, absl)
        else (v, absl)
      in
      List.iter push_abs absl;
      v)
    else if tvalue_has_outer_loans v0 || tvalue_has_outer_loans v1 then (
      (* Note the values can't contain bottoms (the case where they contain
         bottom values is handled above) *)
      (* We put everything in the same region *)
      let rid = ctx0.fresh_region_id () in
      let avl0, input0 =
        convert_value_to_input_avalues span ctx0 PLeft v0 rid
      in
      let avl1, input1 =
        convert_value_to_input_avalues span ctx1 PRight v1 rid
      in
      [%cassert] span (ty_no_regions v0.ty) "Not implemented yet";
      let _, ty = ty_refresh_regions (Some span) (fun _ -> rid) v0.ty in

      let lid = ctx0.fresh_borrow_id () in
      if tvalue_has_mutable_loans v0 || tvalue_has_mutable_loans v1 then (
        let ref_ty = mk_ref_ty (RVar (Free rid)) ty RMut in
        let av : tavalue =
          let value =
            ABorrow (AMutBorrow (PNone, lid, mk_aignored span ty None))
          in
          { value; ty = ref_ty }
        in
        let output : tevalue =
          let value = EBorrow (EMutBorrow (PNone, lid, mk_eignored ty)) in
          { value; ty = ref_ty }
        in
        let input : tevalue =
          (* We need this to make sure no values are filtered when translating *)
          let wrap (v : tevalue) : tevalue =
            { value = EMutBorrowInput v; ty = ref_ty }
          in
          let value = EJoinMarkers (wrap input0, wrap input1) in
          let ty = input0.ty in
          { value; ty }
        in

        (* Create the abstraction expression *)
        let cont : abs_cont option =
          if S.with_abs_conts then
            Some { output = Some output; input = Some input }
          else None
        in

        let abs =
          {
            abs_id = ctx0.fresh_abs_id ();
            kind = S.fresh_abs_kind;
            can_end = true;
            parents = AbsId.Set.empty;
            original_parents = [];
            regions = { owned = RegionId.Set.singleton rid };
            avalues = av :: (avl0 @ avl1);
            cont;
          }
        in
        push_abs abs;

        let value = VLoan (VMutLoan lid) in
        let ty = v0.ty in
        { value; ty })
      else [%craise] span "Not implemented yet")
    else no_loans_no_bottoms_to_symbolic_value_with_borrows ctx0 ctx1 v0 v1

  let match_distinct_adts (_ : tvalue_matcher) (ctx0 : eval_ctx)
      (ctx1 : eval_ctx) (ty : ety) (ty0 : ty) (adt0 : adt_value) (ty1 : ty)
      (adt1 : adt_value) : tvalue =
    [%cassert] span
      (not (ety_has_nested_borrows (Some span) ctx0.type_ctx.type_infos ty))
      "Nested borrows are not supported yet.";

    let v0 : tvalue = { value = VAdt adt0; ty = ty0 } in
    let v1 : tvalue = { value = VAdt adt1; ty = ty1 } in

    (* For now we treat the case with borrows separately *)
    to_symbolic_value_with_borrows ctx0 ctx1 v0 v1

  let match_shared_borrows match_rec (ctx0 : eval_ctx) (ctx1 : eval_ctx)
      (ty : ety) (bid0 : borrow_id) (sid0 : shared_borrow_id) (bid1 : borrow_id)
      (sid1 : shared_borrow_id) : borrow_id * shared_borrow_id =
    if bid0 = bid1 then
      (* We always generate a fresh borrow id: borrows may be duplicated, and
         we have to make sure that shared borrow ids remain unique.
       *)
      let sid = ctx0.fresh_shared_borrow_id () in
      (bid0, sid)
    else
      (* We replace bid0 and bid1 with a fresh borrow id, and introduce
         an abstraction which links all of them:
         {[
           { SB bid0, SB bid1, SL bid2 }
         ]}
      *)
      let rid = ctx0.fresh_region_id () in
      let bid2 = ctx0.fresh_borrow_id () in

      (* Update the type of the shared loan to use the fresh region *)
      let _, bv_ty, kind = ty_as_ref ty in
      let borrow_ty = mk_ref_ty (RVar (Free rid)) bv_ty kind in

      (* Generate the avalues for the abstraction *)
      let mk_aborrow (pm : proj_marker) (bid : borrow_id)
          (sid : shared_borrow_id) : tavalue =
        let value = ABorrow (ASharedBorrow (pm, bid, sid)) in
        { value; ty = borrow_ty }
      in
      let borrows =
        [ mk_aborrow PLeft bid0 sid0; mk_aborrow PRight bid1 sid1 ]
      in

      (* Lookup the shared values and match them *)
      let sv0 = ctx_lookup_shared_value span ctx0 bid0 in
      let sv1 = ctx_lookup_shared_value span ctx1 bid1 in
      let sv = match_rec sv0 sv1 in

      let loan = ASharedLoan (PNone, bid2, sv, mk_aignored span bv_ty None) in
      (* Note that an aloan has a borrow type *)
      let loan : tavalue = { value = ALoan loan; ty = borrow_ty } in

      let avalues = List.append borrows [ loan ] in

      (* Create the abstraction expression *)
      let cont : abs_cont option =
        if S.with_abs_conts then
          let output = Some (mk_etuple []) in
          let input = Some (mk_etuple []) in
          Some { output; input }
        else None
      in

      (* Generate the abstraction *)
      let abs =
        {
          abs_id = ctx0.fresh_abs_id ();
          kind = S.fresh_abs_kind;
          can_end = true;
          parents = AbsId.Set.empty;
          original_parents = [];
          regions = { owned = RegionId.Set.singleton rid };
          avalues;
          cont;
        }
      in
      push_abs abs;

      (* Return the new borrow *)
      (* We always generate a fresh borrow id: borrows may be duplicated, and
         we have to make sure that shared borrow ids remain unique.
      *)
      let sid = ctx0.fresh_shared_borrow_id () in
      (bid2, sid)

  let match_mut_borrows (_ : tvalue_matcher) (ctx0 : eval_ctx) (_ : eval_ctx)
      (ty : ety) (bid0 : borrow_id) (bv0 : tvalue) (bid1 : borrow_id)
      (bv1 : tvalue) (bv : tvalue) : borrow_id * tvalue =
    (* We distinguish two cases, depending on whether the borrow ids are the same
       or not. *)
    if bid0 = bid1 then (
      (* TODO: this is deprecated.

         If the merged value is not the same as the original value, we introduce
         an abstraction:

         {[
           { MB bid0, ML bid' }  // where bid' fresh
         ]}

         and we use bid' for the borrow id that we return.

         We do this because we want to make sure that, whenever a mutably
         borrowed value is modified in a loop iteration, then there is
         a fresh abstraction between this borrowed value and the fixed
         abstractions (this is tantamount to introducing a reborrow).

         Example:
         ========
         {[
           fn clear(v: &mut Vec<u32>) {
               let mut i = 0;
               while i < v.len() {
                   v[i] = 0;
                   i += 1;
               }
           }
         ]}

         When entering the loop, we have the following environment:
         {[
           abs'0 { ML l0 } // input abstraction
           v -> MB l0 s0
           i -> 0
         ]}

         At every iteration, we update the symbolic value of the vector [v]
         (i.e., [s0]).

         For now, because the translation of the loop is responsible of the
         execution of the end of the function (up to the [return]), we want
         the loop to reborrow the vector [v]: this way, the forward loop
         function returns nothing (it returns what [clear] returns, that is
         to say [unit]) while the backward loop function gives back a new value
         for [v] (i.e., a new symbolic value which will replace [s0]).

         By introducing the fresh region abstraction wet get:
         {[
           abs'0 { ML l0 } // input abstraction
           abs'1 { MB l0, ML l1 } // fresh abstraction
           v -> MB l1 s1
           i -> 0
         ]}


         In the future, we will also compute joins at the *loop exits*: when we
         do so, we won't introduce reborrows like above: the forward loop function
         will update [v], while the backward loop function will return nothing.
      *)
      [%cassert] span
        (not
           (ValuesUtils.value_has_borrows (Some span) ctx0.type_ctx.type_infos
              bv.value))
        "Nested borrows are not supported yet";

      (bid0, bv))
    else
      (* We replace bid0 and bid1 with a fresh borrow id (bid2), and introduce
         an abstraction which links all of them. This time we have to introduce
         markers:
         {[
           { |MB bid0|, ︙MB bid1︙, ML bid2 }
         ]}
      *)
      let rid = ctx0.fresh_region_id () in
      let bid2 = ctx0.fresh_borrow_id () in

      (* [bv] is the result of the join  *)
      let _, bv_ty, kind = ty_as_ref ty in
      let sv = bv in

      let borrow_ty = mk_ref_ty (RVar (Free rid)) bv_ty kind in

      (* Generate the avalues for the abstraction *)
      let mk_aborrow (pm : proj_marker) (bid : borrow_id) (bv : tvalue) :
          tavalue =
        let bv_ty = bv.ty in
        [%cassert] span (ty_no_regions bv_ty)
          "Nested borrows are not supported yet";
        let value =
          ABorrow (AMutBorrow (pm, bid, mk_aignored span bv_ty None))
        in
        { value; ty = borrow_ty }
      in
      let borrows = [ mk_aborrow PLeft bid0 bv0; mk_aborrow PRight bid1 bv1 ] in

      let loan = AMutLoan (PNone, bid2, mk_aignored span bv_ty None) in
      (* Note that an aloan has a borrow type *)
      let loan : tavalue = { value = ALoan loan; ty = borrow_ty } in

      let avalues = List.append borrows [ loan ] in

      (* Generate the abstraction expression.

         We need to duplicate the input (loan) but we can't have twice the same loan
         in an abstraction expression, so we create something of the shape:
         {[
           output := (|MB bid0|, ︙MB bid1︙)
           input := let x = ML bid2 in (x, x)
         ]}
      *)
      let owned = RegionId.Set.singleton rid in
      let cont : abs_cont option =
        if S.with_abs_conts then
          let input : tevalue =
            let loan = EMutLoan (PNone, bid2, mk_eignored bv_ty) in
            (* Note that an eloan has a borrow type *)
            let loan : tevalue = { value = ELoan loan; ty = borrow_ty } in

            (* Create the let-binding *)
            let fvar = mk_fresh_abs_fvar borrow_ty in
            let pair = mk_etuple [ fvar; fvar ] in
            let pat = mk_epat_from_fvar fvar in
            mk_let span owned pat loan pair
          in
          let output : tevalue =
            let mk_output (pm : proj_marker) (bid : borrow_id) (bv : tvalue) :
                tevalue =
              let bv_ty = bv.ty in
              [%cassert] span (ty_no_regions bv_ty)
                "Nested borrows are not supported yet";
              let value = EBorrow (EMutBorrow (pm, bid, mk_eignored bv_ty)) in
              { value; ty = borrow_ty }
            in
            mk_etuple [ mk_output PLeft bid0 bv0; mk_output PRight bid1 bv1 ]
          in
          Some { output = Some output; input = Some input }
        else None
      in

      (* Generate the abstraction *)
      let abs =
        {
          abs_id = ctx0.fresh_abs_id ();
          kind = S.fresh_abs_kind;
          can_end = true;
          parents = AbsId.Set.empty;
          original_parents = [];
          regions = { owned };
          avalues;
          cont;
        }
      in
      push_abs abs;

      (* Return the new borrow *)
      (bid2, sv)

  let match_shared_loans (_ : tvalue_matcher) (ctx0 : eval_ctx)
      (_ctx1 : eval_ctx) (ty : ety) (id0 : loan_id) (id1 : loan_id)
      (sv : tvalue) : tvalue =
    (* Remark: if we dive inside data-structures (by using a shared borrow) the shared
       values might themselves contain shared loans, which need to be matched. For this
       reason, we destructure the shared values (see {!destructure_abs}).  *)
    if id0 = id1 then { value = VLoan (VSharedLoan (id0, sv)); ty }
    else begin
      (* Sanity checks *)
      [%cassert] span
        (not (ety_has_nested_borrows (Some span) ctx0.type_ctx.type_infos ty))
        "Nested borrows are not supported yet.";

      (* We need to introduce a fresh shared loan. *)
      let rid = ctx0.fresh_region_id () in
      let nbid = ctx0.fresh_borrow_id () in

      let kind = RShared in
      let bv_ty = ty in
      let borrow_ty = mk_ref_ty (RVar (Free rid)) bv_ty kind in

      let borrow_av =
        let ty = borrow_ty in
        let value =
          ABorrow (ASharedBorrow (PNone, nbid, ctx0.fresh_shared_borrow_id ()))
        in
        mk_tavalue span ty value
      in

      let mk_loan_av (pm : proj_marker) (lid : loan_id) : tavalue =
        let ty = borrow_ty in
        (* TODO: we could probably do something more general which doesn't
           require duplicating the symbolic value *)
        let sv' = refresh_fresh_symbolic_values_in_joined_value ctx0 sv in
        let value =
          ALoan (ASharedLoan (pm, lid, sv', mk_aignored span bv_ty None))
        in
        mk_tavalue span ty value
      in

      let avalues =
        [ borrow_av; mk_loan_av PLeft id0; mk_loan_av PRight id1 ]
      in

      let owned = RegionId.Set.singleton rid in
      [%sanity_check] span (not S.with_abs_conts);
      let cont : abs_cont option =
        if S.with_abs_conts then
          Some { output = Some (mk_etuple []); input = Some (mk_etuple []) }
        else None
      in

      (* Generate the abstraction *)
      let abs =
        {
          abs_id = ctx0.fresh_abs_id ();
          kind = S.fresh_abs_kind;
          can_end = true;
          parents = AbsId.Set.empty;
          original_parents = [];
          regions = { owned };
          avalues;
          cont;
        }
      in
      push_abs abs;

      (* Return the new loan *)
      { value = VLoan (VSharedLoan (nbid, sv)); ty }
    end

  let match_mut_loans (_match_rec : tvalue_matcher) (ctx0 : eval_ctx)
      (_ctx1 : eval_ctx) (ty : ety) (id0 : loan_id) (id1 : loan_id) : tvalue =
    if id0 = id1 then { value = VLoan (VMutLoan id0); ty }
    else begin
      (* Sanity checks *)
      [%cassert] span
        (not (ety_has_nested_borrows (Some span) ctx0.type_ctx.type_infos ty))
        "Nested borrows are not supported yet.";

      (* We need to introduce a fresh loan and a fresh region abstraction *)
      let rid = ctx0.fresh_region_id () in
      let nbid = ctx0.fresh_borrow_id () in

      let kind = RMut in
      let bv_ty = ty in
      let borrow_ty = mk_ref_ty (RVar (Free rid)) bv_ty kind in

      let borrow_av =
        let ty = borrow_ty in
        let value =
          ABorrow (AMutBorrow (PNone, nbid, mk_aignored span bv_ty None))
        in
        mk_tavalue span ty value
      in

      let mk_loan_av (pm : proj_marker) (lid : loan_id) : tavalue =
        let ty = borrow_ty in
        let value = ALoan (AMutLoan (pm, lid, mk_aignored span bv_ty None)) in
        mk_tavalue span ty value
      in

      let avalues =
        [ borrow_av; mk_loan_av PLeft id0; mk_loan_av PRight id1 ]
      in

      let owned = RegionId.Set.singleton rid in
      let cont : abs_cont option =
        if S.with_abs_conts then
          let input : tevalue =
            let mk_loan pm lid =
              let loan = EMutLoan (pm, lid, mk_eignored bv_ty) in
              (* Note that an eloan has a borrow type *)
              { value = ELoan loan; ty = borrow_ty }
            in
            let lv = mk_loan PLeft id0 in
            let rv = mk_loan PRight id1 in
            let v = EJoinMarkers (lv, rv) in
            { value = v; ty = borrow_ty }
          in
          let output : tevalue =
            let value = EBorrow (EMutBorrow (PNone, nbid, mk_eignored bv_ty)) in
            { value; ty = borrow_ty }
          in
          Some { output = Some output; input = Some input }
        else None
      in

      (* Generate the abstraction *)
      let abs =
        {
          abs_id = ctx0.fresh_abs_id ();
          kind = S.fresh_abs_kind;
          can_end = true;
          parents = AbsId.Set.empty;
          original_parents = [];
          regions = { owned };
          avalues;
          cont;
        }
      in
      push_abs abs;

      (* Return the new loan *)
      { value = VLoan (VMutLoan nbid); ty }
    end

  let match_symbolic_values (_ : tvalue_matcher) (ctx0 : eval_ctx)
      (ctx1 : eval_ctx) (sv0 : symbolic_value) (sv1 : symbolic_value) :
      symbolic_value =
    let id0 = sv0.sv_id in
    let id1 = sv1.sv_id in
    if id0 = id1 then (
      (* Sanity check *)
      [%sanity_check] span (sv0 = sv1);
      (* We keep the same id, but we need to register the mapping *)
      add_symbolic_value id0
        (mk_tvalue_from_symbolic_value sv0)
        (mk_tvalue_from_symbolic_value sv1);
      (* Return *)
      sv0)
    else (
      (* The caller should have checked that the symbolic values don't contain
         nested borrows, but we can check more *)
      [%sanity_check] span
        (not
           (ety_has_nested_borrows (Some span) ctx0.type_ctx.type_infos
              sv0.sv_ty));
      (* TODO: the symbolic values may contain bottoms: we're being conservatice,
         and fail (for now) if part of a symbolic value contains a bottom.
         A more general approach would be to introduce a symbolic value
         with some ended regions. *)
      [%sanity_check] span
        ((not (symbolic_value_has_ended_regions ctx0.ended_regions sv0))
        && not (symbolic_value_has_ended_regions ctx1.ended_regions sv1));
      (* If the symbolic values contain regions, we need to introduce abstractions *)
      if ty_has_borrows (Some span) ctx0.type_ctx.type_infos sv0.sv_ty then (
        (* Let's say we join:
           {[
             s0 : S<'0, '1>
             s1 : S<'2, '3>
           ]}

           We introduce a fresh symbolic value with fresh regions, as well as
           one abstraction per region. It looks like so:
           {[
             join s0 s1 ~> s2 : S<'a, 'b>,
               A0('a) {
                 |proj_borrows (s0 <: S<'a, 'b>)|,
                 !proj_borrows (s1 <: S<'a, 'b>)!,
                 proj_loans (s2 : S<'a, 'b>)
               }
               A1('b) {
                 |proj_borrows (s0 <: S<'a, 'b>)|,
                 !proj_borrows (s1 <: S<'a, 'b>)!,
                 proj_loans (s2 : S<'a, 'b>)
               }
           ]}
        *)
        (* Introduce one region abstraction per region appearing in the symbolic value *)
        let fresh_regions, proj_ty =
          ty_refresh_regions (Some span) ctx0.fresh_region_id sv0.sv_ty
        in
        let svj =
          add_fresh_symbolic_value ctx0 proj_ty
            { value = VSymbolic sv0; ty = sv0.sv_ty }
            { value = VSymbolic sv1; ty = sv1.sv_ty }
        in
        let proj_s0 = mk_aproj_borrows PLeft sv0.sv_id proj_ty in
        let proj_s1 = mk_aproj_borrows PRight sv1.sv_id proj_ty in
        let svj = get_symbolic_tvalue span svj in
        let proj_svj = mk_aproj_loans PNone svj.sv_id proj_ty in
        let avalues = [ proj_s0; proj_s1; proj_svj ] in
        List.iter
          (fun rid ->
            let owned = RegionId.Set.singleton rid in
            (* The abstraction expression continuation *)
            let cont : abs_cont option =
              if S.with_abs_conts then
                (* The continuation should be of the shape (this is similar to
                   the case of mutable borrows):
                   {[
                     output := (|proj_borrows (s0 <: ...)|, ︙proj_borrows (s1 <: ...︙)
                     input := let x = proj_loans (s2 : ...) in (x, x)
                   ]}

                   Note that we introduce projections only if the symbolic values
                   contain mutable borrows for the projected regions. Otherwise
                   we ignore them.
                *)
                if
                  ty_has_mut_borrow_for_region_in_set ctx0.type_ctx.type_infos
                    owned proj_ty
                then
                  let proj_s0 = mk_eproj_borrows PLeft sv0.sv_id proj_ty in
                  let proj_s1 = mk_eproj_borrows PRight sv1.sv_id proj_ty in
                  let proj_svj = mk_eproj_loans PNone svj.sv_id proj_ty in
                  let input : tevalue =
                    let loan = proj_svj in
                    (* Create the let-binding *)
                    let fvar = mk_fresh_abs_fvar proj_ty in
                    let pair = mk_etuple [ fvar; fvar ] in
                    let pat = mk_epat_from_fvar fvar in
                    mk_let span owned pat loan pair
                  in
                  let output : tevalue = mk_etuple [ proj_s0; proj_s1 ] in
                  Some { output = Some output; input = Some input }
                else
                  Some
                    {
                      output = Some (mk_simpl_etuple []);
                      input = Some (mk_simpl_etuple []);
                    }
              else None
            in
            (* Create the abstraction *)
            let abs =
              {
                abs_id = ctx0.fresh_abs_id ();
                kind = S.fresh_abs_kind;
                can_end = true;
                parents = AbsId.Set.empty;
                original_parents = [];
                regions = { owned };
                avalues;
                cont;
              }
            in
            push_abs abs)
          fresh_regions;
        svj)
      else
        (* Otherwise we simply introduce a fresh symbolic value *)
        let sv =
          add_fresh_symbolic_value ctx0 sv0.sv_ty
            { value = VSymbolic sv0; ty = sv0.sv_ty }
            { value = VSymbolic sv1; ty = sv1.sv_ty }
        in
        get_symbolic_tvalue span sv)

  let match_symbolic_with_other (_ : tvalue_matcher) (ctx0 : eval_ctx)
      (ctx1 : eval_ctx) ~(symbolic_is_left : bool) (sv : symbolic_value)
      (v : tvalue) : tvalue =
    let sv = mk_tvalue_from_symbolic_value sv in
    let v0, v1 = if symbolic_is_left then (sv, v) else (v, sv) in
    to_symbolic_value_with_borrows ctx0 ctx1 v0 v1

  let match_bottom_with_other (_ : tvalue_matcher) (ctx0 : eval_ctx)
      (ctx1 : eval_ctx) ~(bottom_is_left : bool) (v : tvalue) : tvalue =
    let value_is_left = not bottom_is_left in
    (* If there are outer loans in the non-bottom value, raise an exception.
       Otherwise, convert it to an abstraction and return [Bottom].
    *)
    let with_borrows = false in
    match
      InterpBorrowsCore.get_first_outer_loan_or_borrow_in_value with_borrows v
    with
    | Some (BorrowContent _) ->
        (* Can't get there: we only ask for outer *loans* *)
        [%craise] span "Unreachable"
    | Some (LoanContent lc) -> (
        match lc with
        | VSharedLoan (id, _) | VMutLoan id ->
            if value_is_left then raise (ValueMatchFailure (LoanInLeft id))
            else raise (ValueMatchFailure (LoanInRight id)))
    | None ->
        (* Convert the value to an abstraction *)
        let ctx = if value_is_left then ctx0 else ctx1 in
        let absl =
          convert_value_to_abstractions span S.fresh_abs_kind ~can_end:true ctx
            v
        in
        (* Add a marker to the abstraction indicating the provenance of the value *)
        let pm = if value_is_left then PLeft else PRight in
        let absl = List.map (abs_add_marker span ctx0 pm) absl in
        push_absl absl;
        (* Return [Bottom] *)
        mk_bottom span v.ty

  let match_shared_loan_with_other (match_rec : tvalue_matcher)
      (ctx0 : eval_ctx) (_ctx1 : eval_ctx) ~(loan_is_left : bool) (ty : ety)
      (lid : loan_id) (shared_value : tvalue) (other : tvalue) : tvalue =
    (* Sanity checks *)
    [%cassert] span
      (not (ety_has_nested_borrows (Some span) ctx0.type_ctx.type_infos ty))
      "Nested borrows are not supported yet.";
    [%cassert] span
      (not
         (ValuesUtils.value_has_loans_or_borrows (Some span)
            ctx0.type_ctx.type_infos shared_value.value))
      "Unimplemented";
    [%cassert] span
      (not
         (ValuesUtils.value_has_loans_or_borrows (Some span)
            ctx0.type_ctx.type_infos other.value))
      "Unimplemented";

    (* Join the inner value *)
    let joined_value = match_rec shared_value other in

    (* We need to introduce a fresh shared loan. *)
    let rid = ctx0.fresh_region_id () in
    let nbid = ctx0.fresh_borrow_id () in

    let kind = RShared in
    let bv_ty = ty in
    let borrow_ty = mk_ref_ty (RVar (Free rid)) bv_ty kind in

    let borrow_av =
      let ty = borrow_ty in
      let value =
        ABorrow (ASharedBorrow (PNone, nbid, ctx0.fresh_shared_borrow_id ()))
      in
      mk_tavalue span ty value
    in

    let loan_av : tavalue =
      let ty = borrow_ty in
      let pm = if loan_is_left then PLeft else PRight in
      let value =
        ALoan (ASharedLoan (pm, lid, shared_value, mk_aignored span bv_ty None))
      in
      mk_tavalue span ty value
    in

    let avalues = [ borrow_av; loan_av ] in

    let owned = RegionId.Set.singleton rid in
    let cont : abs_cont option =
      if S.with_abs_conts then
        Some { output = Some (mk_etuple []); input = Some (mk_etuple []) }
      else None
    in

    (* Generate the abstraction *)
    let abs =
      {
        abs_id = ctx0.fresh_abs_id ();
        kind = S.fresh_abs_kind;
        can_end = true;
        parents = AbsId.Set.empty;
        original_parents = [];
        regions = { owned };
        avalues;
        cont;
      }
    in
    push_abs abs;

    (* Return the new loan *)
    { value = VLoan (VSharedLoan (nbid, joined_value)); ty }

  let match_mut_loan_with_other (_match_rec : tvalue_matcher) (ctx0 : eval_ctx)
      (ctx1 : eval_ctx) ~(loan_is_left : bool) (ty : ety) (lid : loan_id)
      (other : tvalue) : tvalue =
    (* Sanity checks *)
    [%cassert] span
      (not (ety_has_nested_borrows (Some span) ctx0.type_ctx.type_infos ty))
      "Nested borrows are not supported yet.";
    [%cassert] span
      (not (tvalue_has_borrows (Some span) ctx0 other))
      "Not implemented";

    let loan_ctx, other_ctx, loan_pm, other_pm =
      if loan_is_left then (ctx0, ctx1, PLeft, PRight)
      else (ctx1, ctx0, PRight, PLeft)
    in

    [%ldebug
      "- loan id: " ^ BorrowId.to_string lid ^ "\n- ty: "
      ^ ty_to_string loan_ctx ty ^ "\n- other:\n"
      ^ tvalue_to_string other_ctx other
      ^ "\n- other.ty: "
      ^ ty_to_string other_ctx other.ty];

    (* We need to introduce a fresh loan and a fresh region abstraction *)
    let rid = ctx0.fresh_region_id () in
    let nbid = ctx0.fresh_borrow_id () in

    let kind = RMut in
    let bv_ty = ty in
    let borrow_ty = mk_ref_ty (RVar (Free rid)) bv_ty kind in

    let borrow_av =
      let ty = borrow_ty in
      let value =
        ABorrow (AMutBorrow (PNone, nbid, mk_aignored span bv_ty None))
      in
      mk_tavalue span ty value
    in

    let loan_av : tavalue =
      let ty = borrow_ty in
      let value =
        ALoan (AMutLoan (loan_pm, lid, mk_aignored span bv_ty None))
      in
      mk_tavalue span ty value
    in

    let other_avl, other_input =
      convert_value_to_input_avalues span other_ctx other_pm other rid
    in

    let avalues = [ borrow_av; loan_av ] @ other_avl in

    let owned = RegionId.Set.singleton rid in
    let cont : abs_cont option =
      if S.with_abs_conts then
        let input : tevalue =
          let loan : tevalue =
            let loan = EMutLoan (loan_pm, lid, mk_eignored bv_ty) in
            (* Note that an eloan has a borrow type *)
            { value = ELoan loan; ty = borrow_ty }
          in
          let other_input : tevalue =
            (* We need this to make sure no values are filtered when translating *)
            { value = EMutBorrowInput other_input; ty = borrow_ty }
          in
          let lv, rv =
            if loan_is_left then (loan, other_input) else (other_input, loan)
          in
          let v = EJoinMarkers (lv, rv) in
          { value = v; ty = borrow_ty }
        in
        let output : tevalue =
          let value = EBorrow (EMutBorrow (PNone, nbid, mk_eignored bv_ty)) in
          { value; ty = borrow_ty }
        in
        Some { output = Some output; input = Some input }
      else None
    in

    (* Generate the abstraction *)
    let abs =
      {
        abs_id = ctx0.fresh_abs_id ();
        kind = S.fresh_abs_kind;
        can_end = true;
        parents = AbsId.Set.empty;
        original_parents = [];
        regions = { owned };
        avalues;
        cont;
      }
    in
    push_abs abs;

    (* Return the new loan *)
    { value = VLoan (VMutLoan nbid); ty }

  (* As explained in comments: we don't use the join matcher to join avalues,
     only concrete values *)

  let match_distinct_aadts _ _ _ _ _ _ _ = [%craise] span "Unreachable"
  let match_ashared_borrows _ _ _ _ _ _ = [%craise] span "Unreachable"
  let match_amut_borrows _ _ _ _ _ _ _ _ _ _ = [%craise] span "Unreachable"

  let match_ashared_loans _ _ _ _ _ _ _ _ _ _ _ _ _ =
    [%craise] span "Unreachable"

  let match_amut_loans _ _ _ _ _ _ _ _ _ _ = [%craise] span "Unreachable"
  let match_aproj_borrows _ _ _ _ _ _ _ _ _ _ = [%craise] span "Unreachable"
  let match_aproj_loans _ _ _ _ _ _ _ _ _ _ = [%craise] span "Unreachable"
  let match_avalues _ _ _ _ = [%craise] span "Unreachable"
end

module MakeCheckEquivMatcher (S : MatchCheckEquivState) : CheckEquivMatcher =
struct
  let span = S.span

  module MkGetSetM (Id : Identifiers.Id) = struct
    module Inj = Id.InjSubst

    let add (msg : string) (m : Inj.t ref) (k0 : Id.id) (k1 : Id.id) =
      (* Check if k0 is already registered as a key *)
      match Inj.find_opt k0 !m with
      | None ->
          (* Not registered: check if k1 is in the set of values,
             otherwise add the binding *)
          if Inj.Set.mem k1 (Inj.elements !m) then
            raise
              (Distinct
                 (msg ^ "adding [k0=" ^ Id.to_string k0 ^ " -> k1="
                ^ Id.to_string k1 ^ " ]: k1 already in the set of elements"))
          else (
            m := Inj.add k0 k1 !m;
            k1)
      | Some k1' ->
          (* It is: check that the bindings are consistent *)
          if k1 <> k1' then raise (Distinct (msg ^ "already a binding for k0"))
          else k1

    let match_e (msg : string) (m : Inj.t ref) (k0 : Id.id) (k1 : Id.id) : Id.id
        =
      (* TODO: merge the add and merge functions *)
      add msg m k0 k1

    let match_el (msg : string) (m : Inj.t ref) (kl0 : Id.id list)
        (kl1 : Id.id list) : Id.id list =
      List.map (fun (k0, k1) -> match_e msg m k0 k1) (List.combine kl0 kl1)

    (** Figuring out mappings between sets of ids is hard in all generality...
        We use the fact that the fresh ids should have been generated the same
        way (i.e., in the same order) and match the ids two by two in increasing
        order. *)
    let match_es (msg : string) (m : Inj.t ref) (ks0 : Id.Set.t)
        (ks1 : Id.Set.t) : Id.Set.t =
      Id.Set.of_list
        (match_el msg m (Id.Set.elements ks0) (Id.Set.elements ks1))
  end

  module GetSetRid = MkGetSetM (RegionId)

  let match_rid = GetSetRid.match_e "match_rid: " S.rid_map
  let match_rids = GetSetRid.match_es "match_rids: " S.rid_map

  module GetSetBid = MkGetSetM (BorrowId)

  let match_blid msg = GetSetBid.match_e msg S.blid_map
  let match_blidl msg = GetSetBid.match_el msg S.blid_map
  let match_blids msg = GetSetBid.match_es msg S.blid_map

  let match_borrow_id =
    if S.check_equiv then match_blid "match_borrow_id: "
    else GetSetBid.match_e "match_borrow_id: " S.borrow_id_map

  let match_borrow_idl =
    if S.check_equiv then match_blidl "match_borrow_idl: "
    else GetSetBid.match_el "match_borrow_idl: " S.borrow_id_map

  let match_borrow_ids =
    if S.check_equiv then match_blids "match_borrow_ids: "
    else GetSetBid.match_es "match_borrow_ids: " S.borrow_id_map

  let match_loan_id =
    if S.check_equiv then match_blid "match_loan_id: "
    else GetSetBid.match_e "match_loan_id: " S.loan_id_map

  let match_loan_idl =
    if S.check_equiv then match_blidl "match_loan_idl: "
    else GetSetBid.match_el "match_loan_idl: " S.loan_id_map

  let match_loan_ids =
    if S.check_equiv then match_blids "match_loan_ids: "
    else GetSetBid.match_es "match_loan_ids: " S.loan_id_map

  module GetSetSid = MkGetSetM (SymbolicValueId)
  module GetSetAid = MkGetSetM (AbsId)

  let match_aid = GetSetAid.match_e "match_aid: " S.aid_map
  let match_aidl = GetSetAid.match_el "match_aidl: " S.aid_map
  let match_aids = GetSetAid.match_es "match_aids: " S.aid_map

  (** *)
  let match_etys (_ : eval_ctx) (_ : eval_ctx) ty0 ty1 =
    if ty0 <> ty1 then raise (Distinct "match_etys") else ty0

  let match_rtys (ctx0 : eval_ctx) (ctx1 : eval_ctx) ty0 ty1 =
    let match_distinct_types _ _ = raise (Distinct "match_rtys") in
    let match_regions r0 r1 =
      match (r0, r1) with
      | RStatic, RStatic -> r1
      | RVar (Free rid0), RVar (Free rid1) ->
          let rid = match_rid rid0 rid1 in
          RVar (Free rid)
      | _ -> raise (Distinct "match_rtys")
    in
    match_types span ctx0 ctx1 match_distinct_types match_regions ty0 ty1

  let match_distinct_literals (_ : tvalue_matcher) (ctx0 : eval_ctx)
      (_ : eval_ctx) (ty : ety) (_ : literal) (_ : literal) : tvalue =
    mk_fresh_symbolic_tvalue_from_no_regions_ty span ctx0 ty

  let match_distinct_adts (_ : tvalue_matcher) (_ : eval_ctx) (_ : eval_ctx)
      (_ty : ety) _ (_adt0 : adt_value) _ (_adt1 : adt_value) : tvalue =
    raise (Distinct "match_distinct_adts")

  let match_shared_borrows (match_tvalues : tvalue -> tvalue -> tvalue)
      (ctx0 : eval_ctx) (ctx1 : eval_ctx) (_ty : ety) (bid0 : borrow_id)
      (_sid0 : shared_borrow_id) (bid1 : borrow_id) (_sid1 : shared_borrow_id) :
      borrow_id * shared_borrow_id =
    [%ldebug
      "bid0: " ^ BorrowId.to_string bid0 ^ ", bid1: " ^ BorrowId.to_string bid1];

    let bid = match_borrow_id bid0 bid1 in
    (* If we don't check for equivalence (i.e., we apply a fixed-point),
       we lookup the shared values and match them.
    *)
    let _ =
      if S.check_equiv then ()
      else
        let v0 = S.lookup_shared_value_in_ctx0 bid0 in
        let v1 = S.lookup_shared_value_in_ctx1 bid1 in
        [%ldebug
          "looked up values:" ^ "sv0: "
          ^ tvalue_to_string ~span:(Some span) ctx0 v0
          ^ ", sv1: "
          ^ tvalue_to_string ~span:(Some span) ctx1 v1];

        let _ = match_tvalues v0 v1 in
        ()
    in
    (* The shared borrow id doesn't really matter but it's always safer to refresh it *)
    (bid, ctx0.fresh_shared_borrow_id ())

  let match_mut_borrows (_ : tvalue_matcher) (_ : eval_ctx) (_ : eval_ctx)
      (_ty : ety) (bid0 : borrow_id) (_bv0 : tvalue) (bid1 : borrow_id)
      (_bv1 : tvalue) (bv : tvalue) : borrow_id * tvalue =
    let bid = match_borrow_id bid0 bid1 in
    (bid, bv)

  let match_shared_loans (_ : tvalue_matcher) (_ : eval_ctx) (_ : eval_ctx)
      (ty : ety) (id0 : loan_id) (id1 : loan_id) (sv : tvalue) : tvalue =
    let id = match_loan_id id0 id1 in
    { value = VLoan (VSharedLoan (id, sv)); ty }

  let match_mut_loans (_ : tvalue_matcher) (_ : eval_ctx) (_ : eval_ctx)
      (ty : ety) (bid0 : loan_id) (bid1 : loan_id) : tvalue =
    let bid = match_loan_id bid0 bid1 in
    { value = VLoan (VMutLoan bid); ty }

  let match_symbolic_values (_ : tvalue_matcher) (ctx0 : eval_ctx)
      (ctx1 : eval_ctx) (sv0 : symbolic_value) (sv1 : symbolic_value) :
      symbolic_value =
    let id0 = sv0.sv_id in
    let id1 = sv1.sv_id in

    [%ldebug
      "sv0: "
      ^ SymbolicValueId.to_string id0
      ^ ", sv1: "
      ^ SymbolicValueId.to_string id1];

    (* If we don't check for equivalence, we also update the map from sids
       to values *)
    if S.check_equiv then
      (* Create the joined symbolic value *)
      let sv_id =
        GetSetSid.match_e "match_symbolic_values: ids: " S.sid_map id0 id1
      in
      let sv_ty = match_rtys ctx0 ctx1 sv0.sv_ty sv1.sv_ty in
      let sv = { sv_id; sv_ty } in
      sv
    else (
      (* Check: fixed values are fixed *)
      [%sanity_check] span
        (id0 = id1 || not (SymbolicValueId.InjSubst.mem id0 !S.sid_map));

      (* Update the symbolic value mapping *)
      let sv1 = mk_tvalue_from_symbolic_value sv1 in

      (* Update the symbolic value mapping *)
      S.sid_to_value_map :=
        SymbolicValueId.Map.add_strict_or_unchanged id0 sv1 !S.sid_to_value_map;

      (* Return - the returned value is not used: we can return whatever
         we want *)
      sv0)

  let match_symbolic_with_other (_ : tvalue_matcher) (_ : eval_ctx)
      (_ : eval_ctx) ~(symbolic_is_left : bool) (sv : symbolic_value)
      (v : tvalue) : tvalue =
    if S.check_equiv then raise (Distinct "match_symbolic_with_other")
    else (
      [%sanity_check] span symbolic_is_left;
      let id = sv.sv_id in
      (* Check: fixed values are fixed *)
      [%sanity_check] span (not (SymbolicValueId.InjSubst.mem id !S.sid_map));
      (* Update the binding for the target symbolic value *)
      S.sid_to_value_map :=
        SymbolicValueId.Map.add_strict_or_unchanged id v !S.sid_to_value_map;
      (* Return - the returned value is not used, so we can return whatever we want *)
      v)

  let match_bottom_with_other (_ : tvalue_matcher) (ctx0 : eval_ctx)
      (ctx1 : eval_ctx) ~(bottom_is_left : bool) (v : tvalue) : tvalue =
    (* It can happen that some variables get initialized in some branches
       and not in some others, which causes problems when matching. *)
    (* TODO: the returned value is not used, while it should: in generality it
       should be ok to match a fixed-point with the environment we get at
       a continue, where the fixed point contains some bottom values. *)
    let value_is_left = not bottom_is_left in
    let ctx = if value_is_left then ctx0 else ctx1 in
    if
      bottom_is_left && not (value_has_loans_or_borrows (Some span) ctx v.value)
    then mk_bottom span v.ty
    else
      raise
        (Distinct
           ("match_bottom_with_other:\n- bottom value is in left environment: "
           ^ Print.bool_to_string bottom_is_left
           ^ "\n- value to match with bottom:\n" ^ show_tvalue v))

  let match_shared_loan_with_other (_ : tvalue_matcher) (_ : eval_ctx)
      (_ : eval_ctx) ~(loan_is_left : bool) (_ : ety) (_ : loan_id) (_ : tvalue)
      (_ : tvalue) : tvalue =
    let _ = loan_is_left in
    raise (Distinct "match_mut_loan_with_other")

  let match_mut_loan_with_other (_ : tvalue_matcher) (_ : eval_ctx)
      (_ : eval_ctx) ~(loan_is_left : bool) (_ : ety) (_ : loan_id) (_ : tvalue)
      : tvalue =
    let _ = loan_is_left in
    raise (Distinct "match_mut_loan_with_other")

  let match_distinct_aadts _ _ _ _ _ _ _ =
    raise (Distinct "match_distinct_adts")

  let match_ashared_borrows (_ : tvalue_matcher) (ctx0 : eval_ctx)
      (_ : eval_ctx) _ty0 pm0 bid0 _sid0 _ty1 pm1 bid1 _sid1 ty : tavalue =
    (* We are checking whether that two environments are equivalent:
       there shouldn't be any projection markers *)
    [%sanity_check] span (pm0 = PNone && pm1 = PNone);
    let bid = match_borrow_id bid0 bid1 in
    (* It's always safer to refresh shared borrow ids *)
    let sid = ctx0.fresh_shared_borrow_id () in
    let value = ABorrow (ASharedBorrow (PNone, bid, sid)) in
    { value; ty }

  let match_amut_borrows (_ : tvalue_matcher) (_ : eval_ctx) (_ : eval_ctx) _ty0
      pm0 bid0 _av0 _ty1 pm1 bid1 _av1 ty av : tavalue =
    (* We are checking whether that two environments are equivalent:
       there shouldn't be any projection markers *)
    [%sanity_check] span (pm0 = PNone && pm1 = PNone);
    let bid = match_borrow_id bid0 bid1 in
    let value = ABorrow (AMutBorrow (PNone, bid, av)) in
    { value; ty }

  let match_ashared_loans (_ : tvalue_matcher) (_ : eval_ctx) (_ : eval_ctx)
      _ty0 pm0 id0 _v0 _av0 _ty1 pm1 id1 _v1 _av1 ty v av : tavalue =
    (* We are checking whether that two environments are equivalent:
       there shouldn't be any projection markers *)
    [%sanity_check] span (pm0 = PNone && pm1 = PNone);
    let bid = match_loan_id id0 id1 in
    let value = ALoan (ASharedLoan (PNone, bid, v, av)) in
    { value; ty }

  let match_amut_loans (_ : tvalue_matcher) (ctx0 : eval_ctx) (ctx1 : eval_ctx)
      _ty0 pm0 id0 _av0 _ty1 pm1 id1 _av1 ty av : tavalue =
    (* We are checking whether that two environments are equivalent:
       there shouldn't be any projection markers *)
    [%sanity_check] span (pm0 = PNone && pm1 = PNone);
    [%ldebug
      "- id0: " ^ BorrowId.to_string id0 ^ "\n- id1: " ^ BorrowId.to_string id1
      ^ "\n- ty: " ^ ty_to_string ctx0 ty ^ "\n- av: "
      ^ tavalue_to_string ~span:(Some span) ctx1 av];

    let id = match_loan_id id0 id1 in
    let value = ALoan (AMutLoan (PNone, id, av)) in
    { value; ty }

  let match_aproj_borrows (match_values : tvalue_matcher) (ctx0 : eval_ctx)
      (ctx1 : eval_ctx) _ty0 pm0 (proj0 : aproj_borrows) _ty1 pm1
      (proj1 : aproj_borrows) ty proj_ty : tavalue =
    [%sanity_check] span (pm0 = PNone && pm1 = PNone);
    let { proj = proj0; loans = loans0 } : aproj_borrows = proj0 in
    let { proj = proj1; loans = loans1 } : aproj_borrows = proj1 in
    [%sanity_check] span (loans0 = [] && loans1 = []);
    (* We only want to match the ids of the symbolic values, but in order
       to call [match_symbolic_values] we need to have types... *)
    let sv0 = { sv_id = proj0.sv_id; sv_ty = proj0.proj_ty } in
    let sv1 = { sv_id = proj1.sv_id; sv_ty = proj1.proj_ty } in
    let sv = match_symbolic_values match_values ctx0 ctx1 sv0 sv1 in
    let proj : symbolic_proj = { sv_id = sv.sv_id; proj_ty } in
    { value = ASymbolic (PNone, AProjBorrows { proj; loans = [] }); ty }

  let match_aproj_loans (match_values : tvalue_matcher) (ctx0 : eval_ctx)
      (ctx1 : eval_ctx) _ty0 pm0 (proj0 : aproj_loans) _ty1 pm1
      (proj1 : aproj_loans) ty proj_ty : tavalue =
    [%sanity_check] span (pm0 = PNone && pm1 = PNone);
    let { proj = proj0; consumed = consumed0; borrows = borrows0 } : aproj_loans
        =
      proj0
    in
    let { proj = proj1; consumed = consumed1; borrows = borrows1 } : aproj_loans
        =
      proj1
    in
    [%sanity_check] span (consumed0 = [] && consumed1 = []);
    [%sanity_check] span (borrows0 = [] && borrows1 = []);
    (* We only want to match the ids of the symbolic values, but in order
       to call [match_symbolic_values] we need to have types... *)
    let sv0 = { sv_id = proj0.sv_id; sv_ty = proj0.proj_ty } in
    let sv1 = { sv_id = proj1.sv_id; sv_ty = proj1.proj_ty } in
    let sv = match_symbolic_values match_values ctx0 ctx1 sv0 sv1 in
    let proj : symbolic_proj = { sv_id = sv.sv_id; proj_ty } in
    let proj = AProjLoans { proj; consumed = []; borrows = [] } in
    { value = ASymbolic (PNone, proj); ty }

  let match_avalues (_ : tvalue_matcher) (ctx0 : eval_ctx) (ctx1 : eval_ctx) v0
      v1 =
    [%ldebug
      "avalues don't match:\n- v0: "
      ^ tavalue_to_string ~span:(Some span) ctx0 v0
      ^ "\n- v1: "
      ^ tavalue_to_string ~span:(Some span) ctx1 v1];
    raise (Distinct "match_avalues")
end

let match_ctxs (span : Meta.span) ~(check_equiv : bool)
    ?(check_kind : bool = true) ?(check_can_end : bool = true)
    (fixed_ids : ids_sets) (lookup_shared_value_in_ctx0 : BorrowId.id -> tvalue)
    (lookup_shared_value_in_ctx1 : BorrowId.id -> tvalue) (ctx0 : eval_ctx)
    (ctx1 : eval_ctx) : ids_maps option =
  [%ltrace
    "\n- fixed_ids:\n" ^ show_ids_sets fixed_ids ^ "\n\n- ctx0:\n"
    ^ eval_ctx_to_string ~span:(Some span) ~filter:false ctx0
    ^ "\n\n- ctx1:\n"
    ^ eval_ctx_to_string ~span:(Some span) ~filter:false ctx1
    ^ "\n"];

  (* Initialize the maps and instantiate the matcher *)
  let module IdMap (Id : Identifiers.Id) = struct
    let mk_map_ref (ids : Id.Set.t) : Id.InjSubst.t ref =
      ref
        (Id.InjSubst.of_list (List.map (fun x -> (x, x)) (Id.Set.elements ids)))
  end in
  let rid_map =
    let module IdMap = IdMap (RegionId) in
    IdMap.mk_map_ref fixed_ids.rids
  in
  let blid_map =
    let module IdMap = IdMap (BorrowId) in
    IdMap.mk_map_ref fixed_ids.blids
  in
  let borrow_id_map =
    let module IdMap = IdMap (BorrowId) in
    IdMap.mk_map_ref fixed_ids.borrow_ids
  in
  let loan_id_map =
    let module IdMap = IdMap (BorrowId) in
    IdMap.mk_map_ref fixed_ids.loan_ids
  in
  let aid_map =
    let module IdMap = IdMap (AbsId) in
    IdMap.mk_map_ref fixed_ids.aids
  in
  let sid_map =
    let module IdMap = IdMap (SymbolicValueId) in
    IdMap.mk_map_ref fixed_ids.sids
  in
  (* In case we don't try to check equivalence but want to compute a mapping
     from a source context to a target context, we use a map from symbolic
     value ids to values (rather than to ids).
  *)
  let sid_to_value_map : tvalue SymbolicValueId.Map.t ref =
    ref SymbolicValueId.Map.empty
  in

  let module S : MatchCheckEquivState = struct
    let span = span
    let check_equiv = check_equiv
    let rid_map = rid_map
    let blid_map = blid_map
    let borrow_id_map = borrow_id_map
    let loan_id_map = loan_id_map
    let sid_map = sid_map
    let sid_to_value_map = sid_to_value_map
    let aid_map = aid_map
    let lookup_shared_value_in_ctx0 = lookup_shared_value_in_ctx0
    let lookup_shared_value_in_ctx1 = lookup_shared_value_in_ctx1
  end in
  let module CEM = MakeCheckEquivMatcher (S) in
  let module M = MakeMatcher (CEM) in
  (* Match the environments - we assume that they have the same structure
     (and fail if they don't) *)

  (* Small utility: check that ids are fixed/mapped to themselves *)
  let ids_are_fixed (ids : ids_sets) : bool =
    let {
      aids;
      blids = _;
      borrow_ids;
      loan_ids;
      shared_loans_to_values = _;
      unique_borrow_ids;
      shared_borrow_ids = _;
      non_unique_shared_borrow_ids = _;
      dids;
      rids;
      sids;
    } =
      ids
    in
    AbsId.Set.subset aids fixed_ids.aids
    && BorrowId.Set.subset borrow_ids fixed_ids.borrow_ids
    && UniqueBorrowIdSet.subset unique_borrow_ids fixed_ids.unique_borrow_ids
    && BorrowId.Set.subset loan_ids fixed_ids.loan_ids
    && DummyVarId.Set.subset dids fixed_ids.dids
    && RegionId.Set.subset rids fixed_ids.rids
    && SymbolicValueId.Set.subset sids fixed_ids.sids
  in

  (* Rem.: this function raises exceptions of type [Distinct] *)
  let match_abstractions (abs0 : abs) (abs1 : abs) : unit =
    let {
      abs_id = abs_id0;
      kind = kind0;
      can_end = can_end0;
      parents = parents0;
      original_parents = original_parents0;
      regions = { owned = regions0 };
      avalues = avalues0;
      (* We ignore the continuations *)
      cont = _;
    } =
      abs0
    in

    let {
      abs_id = abs_id1;
      kind = kind1;
      can_end = can_end1;
      parents = parents1;
      original_parents = original_parents1;
      regions = { owned = regions1 };
      avalues = avalues1;
      (* We ignore the continuations *)
      cont = _;
    } =
      abs1
    in

    let _ = CEM.match_aid abs_id0 abs_id1 in
    if check_kind && kind0 <> kind1 then
      raise (Distinct "match_abstractions: kind");
    if check_can_end && can_end0 <> can_end1 then
      raise (Distinct "match_abstractions: can_end");
    let _ = CEM.match_aids parents0 parents1 in
    let _ = CEM.match_aidl original_parents0 original_parents1 in
    let _ = CEM.match_rids regions0 regions1 in

    [%ldebug "match_abstractions: matching values"];
    let _ =
      if List.length avalues0 <> List.length avalues1 then
        raise
          (Distinct "Region abstractions with not the same number of values")
      else
        List.map
          (fun (v0, v1) -> M.match_tavalues ctx0 ctx1 v0 v1)
          (List.combine avalues0 avalues1)
    in
    [%ldebug "match_abstractions: values matched OK"];
    ()
  in

  (* Rem.: this function raises exceptions of type [Distinct] *)
  let rec match_envs (env0 : env) (env1 : env) : unit =
    [%ldebug
      "match_envs:\n\n- fixed_ids:\n" ^ show_ids_sets fixed_ids
      ^ "\n\n- rid_map: "
      ^ RegionId.InjSubst.show_t !rid_map
      ^ "\n- blid_map: "
      ^ BorrowId.InjSubst.show_t !blid_map
      ^ "\n- sid_map: "
      ^ SymbolicValueId.InjSubst.show_t !sid_map
      ^ "\n- aid_map: "
      ^ AbsId.InjSubst.show_t !aid_map
      ^ "\n\n- ctx0:\n"
      ^ eval_ctx_to_string ~span:(Some span) ~filter:false
          { ctx0 with env = List.rev env0 }
      ^ "\n\n- ctx1:\n"
      ^ eval_ctx_to_string ~span:(Some span) ~filter:false
          { ctx1 with env = List.rev env1 }
      ^ "\n\n"];

    match (env0, env1) with
    | EBinding (BDummy b0, v0) :: env0', EBinding (BDummy b1, v1) :: env1' ->
        (* Sanity check: if the dummy value is an old value, the bindings must
           be the same and their values equal (and the borrows/loans/symbolic *)
        if DummyVarId.Set.mem b0 fixed_ids.dids then (
          (* Fixed values: the values must be equal *)
          [%sanity_check] span (b0 = b1);
          [%sanity_check] span (v0 = v1);
          (* The ids present in the left value must be fixed *)
          let ids, _ = compute_tvalue_ids v0 in
          [%sanity_check] span ((not S.check_equiv) || ids_are_fixed ids));
        (* We still match the values - allows to compute mappings (which
           are the identity actually) *)
        let _ = M.match_tvalues ctx0 ctx1 v0 v1 in
        match_envs env0' env1'
    | EBinding (BVar b0, v0) :: env0', EBinding (BVar b1, v1) :: env1' ->
        [%sanity_check] span (b0 = b1);
        (* Match the values *)
        let _ = M.match_tvalues ctx0 ctx1 v0 v1 in
        (* Continue *)
        match_envs env0' env1'
    | EAbs abs0 :: env0', EAbs abs1 :: env1' ->
        [%ldebug
          "match_envs: matching abs:\n- abs0: "
          ^ abs_to_string span ctx0 abs0
          ^ "\n- abs1: "
          ^ abs_to_string span ctx1 abs1];
        (* Same as for the dummy values: there are two cases *)
        if AbsId.Set.mem abs0.abs_id fixed_ids.aids then (
          [%ldebug "match_envs: matching abs: fixed abs"];
          (* Still in the prefix: the abstractions must be the same *)
          [%sanity_check] span (abs0 = abs1);
          (* Their ids must be fixed *)
          let ids, _ = compute_abs_ids abs0 in
          [%sanity_check] span ((not S.check_equiv) || ids_are_fixed ids);
          (* Continue *)
          match_envs env0' env1')
        else (
          [%ldebug "match_envs: matching abs: not fixed abs"];
          (* Match the values *)
          match_abstractions abs0 abs1;
          (* Continue *)
          match_envs env0' env1')
    | [], [] ->
        (* Done *)
        ()
    | _ ->
        (* The elements don't match *)
        raise (Distinct "match_ctxs: match_envs: env elements don't match")
  in

  (* Match the environments.

     Rem.: we don't match the ended regions (would it make any sense actually?) *)
  try
    (* Remove the frame delimiter (the first element of an environment is a frame delimiter) *)
    let env0 = List.rev ctx0.env in
    let env1 = List.rev ctx1.env in
    let env0, env1 =
      match (env0, env1) with
      | EFrame :: env0, EFrame :: env1 -> (env0, env1)
      | _ -> [%craise] span "Unreachable"
    in

    match_envs env0 env1;
    let maps =
      {
        aid_map = !aid_map;
        blid_map = !blid_map;
        borrow_id_map = !borrow_id_map;
        loan_id_map = !loan_id_map;
        rid_map = !rid_map;
        sid_map = !sid_map;
        sid_to_value_map = !sid_to_value_map;
      }
    in
    Some maps
  with
  | Distinct msg ->
      [%ltrace "distinct: " ^ msg];
      None
  | ValueMatchFailure k ->
      [%ltrace "distinct: ValueMatchFailure" ^ show_updt_env_kind k];
      None

let ctxs_are_equivalent (span : Meta.span) (fixed_ids : ids_sets)
    (ctx0 : eval_ctx) (ctx1 : eval_ctx) : bool =
  let lookup_shared_value _ = [%craise] span "Unreachable" in
  Option.is_some
    (match_ctxs span ~check_equiv:true fixed_ids lookup_shared_value
       lookup_shared_value ctx0 ctx1)

let prepare_match_ctx_with_target (config : config) (span : Meta.span)
    (fresh_abs_kind : abs_kind) (src_ctx : eval_ctx) : cm_fun =
 fun tgt_ctx ->
  (* Debug *)
  [%ldebug
    "- src_ctx: "
    ^ eval_ctx_to_string ~span:(Some span) src_ctx
    ^ "\n- tgt_ctx: "
    ^ eval_ctx_to_string ~span:(Some span) tgt_ctx];
  (* End the loans which lead to mismatches when joining *)
  let rec reorganize_join_tgt : cm_fun =
   fun tgt_ctx ->
    (* We match only the values which appear in both environments *)
    let dummy_ids0 = env_get_dummy_var_ids src_ctx.env in
    let dummy_ids1 = env_get_dummy_var_ids tgt_ctx.env in
    let dummy_ids = DummyVarId.Set.inter dummy_ids0 dummy_ids1 in
    let abs_ids = compute_fixed_abs_ids src_ctx tgt_ctx in

    let filt_src_env, _, _ = ctx_split span abs_ids dummy_ids src_ctx in
    let filt_tgt_env, _, _ = ctx_split span abs_ids dummy_ids tgt_ctx in

    [%ldebug
      "reorganize_join_tgt:" ^ "\n- filt_src_ctx: "
      ^ env_to_string span src_ctx filt_src_env
      ^ "\n- filt_tgt_ctx: "
      ^ env_to_string span tgt_ctx filt_tgt_env];

    (* Remove the abstractions *)
    let filter (ee : env_elem) : bool =
      match ee with
      | EBinding _ -> true
      | EAbs _ | EFrame -> false
    in
    let filt_src_env = List.filter filter filt_src_env in
    let filt_tgt_env = List.filter filter filt_tgt_env in

    (* Match the values to check if there are loans to eliminate *)
    let nabs = ref [] in

    let module S : MatchJoinState = struct
      let span = span
      let fresh_abs_kind = fresh_abs_kind
      let nabs = nabs

      (* We're only preparing the match by ending loans, etc., and shouldn't introduce
         fresh region abstractions: this parameter is not relevant (and we set it to
         false by default).
      *)
      let with_abs_conts = false
      let symbolic_to_value = ref SymbolicValueId.Map.empty
    end in
    let module JM = MakeJoinMatcher (S) in
    let module M = MakeMatcher (JM) in
    try
      (* Match the bindings which appear in both environments *)
      (* TODO: we shouldn't filter the locals (they should appear in both envs)? *)
      let src_dummy_ids = env_get_dummy_var_ids filt_src_env in
      let src_local_ids = env_get_local_ids filt_src_env in
      let tgt_dummy_ids = env_get_dummy_var_ids filt_tgt_env in
      let tgt_local_ids = env_get_local_ids filt_tgt_env in
      let dummy_ids = DummyVarId.Set.inter src_dummy_ids tgt_dummy_ids in
      let local_ids =
        Expressions.LocalId.Set.inter src_local_ids tgt_local_ids
      in
      (* We need to filter the environments further *)
      let keep (e : env_elem) : bool =
        match e with
        | EBinding (BDummy id, _) when DummyVarId.Set.mem id dummy_ids -> true
        | EBinding (BVar v, _)
          when Expressions.LocalId.Set.mem v.index local_ids -> true
        | _ -> false
      in
      let filt_src_env = List.filter keep filt_src_env in
      let filt_tgt_env = List.filter keep filt_tgt_env in
      [%sanity_check] span (List.length filt_src_env = List.length filt_tgt_env);
      let _ =
        List.iter
          (fun (var0, var1) ->
            match (var0, var1) with
            | EBinding (BDummy b0, v0), EBinding (BDummy b1, v1) ->
                [%sanity_check] span (b0 = b1);
                let _ = M.match_tvalues src_ctx tgt_ctx v0 v1 in
                ()
            | EBinding (BVar b0, v0), EBinding (BVar b1, v1) ->
                [%sanity_check] span (b0 = b1);
                let _ = M.match_tvalues src_ctx tgt_ctx v0 v1 in
                ()
            | _ -> [%craise] span "Unexpected")
          (List.combine filt_src_env filt_tgt_env)
      in
      (* No exception was thrown: continue *)
      [%ldebug
        "reorganize_join_tgt: done with borrows/loans:" ^ "\n- filt_src_ctx: "
        ^ env_to_string span src_ctx filt_src_env
        ^ "\n- filt_tgt_ctx: "
        ^ env_to_string span tgt_ctx filt_tgt_env];
      (tgt_ctx, fun e -> e)
    with ValueMatchFailure e ->
      (* Exception: end the corresponding borrows, and continue *)
      let ctx, cc =
        match e with
        | LoanInRight bid ->
            [%ldebug "LoanInRight: " ^ BorrowId.to_string bid];
            InterpBorrows.end_loan config span bid tgt_ctx
        | LoansInRight bids ->
            [%ldebug "LoansInRight: " ^ BorrowId.Set.to_string None bids];
            InterpBorrows.end_loans config span bids tgt_ctx
        | AbsInRight _ | AbsInLeft _ | LoanInLeft _ | LoansInLeft _ ->
            [%craise] span "Unexpected"
      in
      comp cc (reorganize_join_tgt ctx)
  in
  (* Apply the reorganization *)
  let ctx, cc = reorganize_join_tgt tgt_ctx in
  Invariants.check_invariants span ctx;
  (ctx, cc)
