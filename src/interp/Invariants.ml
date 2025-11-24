(* The following module defines functions to check that some invariants
 * are always maintained by evaluation contexts *)

open Types
open Values
open Contexts
open TypesUtils
open InterpUtils
open InterpBorrowsCore

(** The local logger *)
let log = Logging.invariants_log

type borrow_info = {
  loan_kind : ref_kind;
  loan_in_abs : bool;  (** true if the loan was found in an abstraction *)
  found_borrow : bool;
      (** [true] if we found the borrow (note that we start by registering the
          loans appearing in the context, and then check that all corresponding
          borrows appear: we thus don't need a [found_loan] field).

          This is only useful for mutable borrows, as any mutable loan has a
          unique corresponding mutable borrow (and vice-versa). *)
  shared_borrow_ids : SharedBorrowId.Set.t;
      (** For shared borrows: the set of unique shared borrow ids found in the
          context *)
}
[@@deriving show]

type outer_borrow_info = {
  outer_borrow : bool;  (** true if the value is borrowed *)
  outer_shared : bool;  (** true if the value is borrowed as shared *)
}

let set_outer_mut (info : outer_borrow_info) : outer_borrow_info =
  { info with outer_borrow = true }

let set_outer_shared (_info : outer_borrow_info) : outer_borrow_info =
  { outer_borrow = true; outer_shared = true }

let ids_reprs_to_string (indent : string) (reprs : BorrowId.id BorrowId.Map.t) :
    string =
  BorrowId.Map.to_string (Some indent) BorrowId.to_string reprs

let borrows_infos_to_string (indent : string)
    (infos : borrow_info BorrowId.Map.t) : string =
  BorrowId.Map.to_string (Some indent) show_borrow_info infos

type borrow_kind = BMut | BShared | BReserved

(** Check that:
    - loans and borrows are correctly related
    - a two-phase borrow can't point to a value inside an abstraction *)
let check_loans_borrows_relation_invariant (span : Meta.span) (ctx : eval_ctx) :
    unit =
  (* We do this in two phases:
     - we first register the loans
     - then register the borrows *)
  (* Link all the borrow ids to a borrow information *)
  let borrows_infos : borrow_info BorrowId.Map.t ref = ref BorrowId.Map.empty in
  let shared_borrow_ids = ref SharedBorrowId.Set.empty in
  let context_to_string () : string =
    eval_ctx_to_string ~span:(Some span) ctx
    ^ "\n- info:\n"
    ^ borrows_infos_to_string "  " !borrows_infos
  in
  (* Ignored loans - when we find an ignored loan while building the borrows_infos
     map, we register it in this list; once the borrows_infos map is completely
     built, we check that all the borrow ids of the ignored loans are in this
     map *)
  let ignored_loans : (ref_kind * BorrowId.id) list ref = ref [] in

  (* First, register all the loans *)
  (* Some utilities to register the loans *)
  let register_ignored_loan (rkind : ref_kind) (bid : BorrowId.id) : unit =
    ignored_loans := (rkind, bid) :: !ignored_loans
  in

  let register_shared_loan (loan_in_abs : bool) (bid : BorrowId.id) : unit =
    let infos = !borrows_infos in
    (* Insert the loan info *)
    let info =
      {
        loan_kind = RShared;
        loan_in_abs;
        found_borrow = false;
        shared_borrow_ids = SharedBorrowId.Set.empty;
      }
    in
    let infos = BorrowId.Map.add bid info infos in
    (* Update *)
    borrows_infos := infos
  in

  let register_mut_loan (loan_in_abs : bool) (bid : BorrowId.id) : unit =
    let infos = !borrows_infos in
    (* Sanity checks *)
    [%sanity_check] span (not (BorrowId.Map.mem bid infos));
    (* Add the mapping for the loan info *)
    let info =
      {
        loan_kind = RMut;
        loan_in_abs;
        found_borrow = false;
        shared_borrow_ids = SharedBorrowId.Set.empty;
      }
    in
    let infos = BorrowId.Map.add bid info infos in
    (* Update *)
    borrows_infos := infos
  in

  let loans_visitor =
    object
      inherit [_] iter_eval_ctx as super

      method! visit_EBinding _ binder v =
        let inside_abs = false in
        super#visit_EBinding inside_abs binder v

      method! visit_EAbs _ abs =
        let inside_abs = true in
        super#visit_EAbs inside_abs abs

      method! visit_loan_content inside_abs lc =
        (* Register the loan *)
        let _ =
          match lc with
          | VSharedLoan (bid, _) -> register_shared_loan inside_abs bid
          | VMutLoan bid -> register_mut_loan inside_abs bid
        in
        (* Continue exploring *)
        super#visit_loan_content inside_abs lc

      method! visit_aloan_content inside_abs lc =
        let _ =
          match lc with
          | AMutLoan (_, bid, _) -> register_mut_loan inside_abs bid
          | ASharedLoan (_, bid, _, _) -> register_shared_loan inside_abs bid
          | AIgnoredMutLoan (Some bid, _) -> register_ignored_loan RMut bid
          | AIgnoredMutLoan (None, _)
          | AIgnoredSharedLoan _
          | AEndedMutLoan { given_back = _; child = _; given_back_meta = _ }
          | AEndedSharedLoan (_, _)
          | AEndedIgnoredMutLoan
              { given_back = _; child = _; given_back_meta = _ } ->
              (* Do nothing *)
              ()
        in
        (* Continue exploring *)
        super#visit_aloan_content inside_abs lc
    end
  in

  (* Visit *)
  let inside_abs = false in
  loans_visitor#visit_eval_ctx inside_abs ctx;

  (* Then, register all the borrows *)
  (* Some utilities to register the borrows *)
  let find_info (bid : BorrowId.id) : borrow_info =
    match BorrowId.Map.find_opt bid !borrows_infos with
    | Some info -> info
    | None ->
        [%craise] span
          ("Internal error: please find an issue.\n\nCould not find borrow b@"
         ^ BorrowId.to_string bid)
  in

  let update_info (bid : BorrowId.id) (info : borrow_info) : unit =
    (* Update the info *)
    let infos =
      BorrowId.Map.update bid
        (fun x ->
          match x with
          | Some _ -> Some info
          | None -> [%craise] span "Unreachable")
        !borrows_infos
    in
    borrows_infos := infos
  in

  let register_ignored_borrow = register_ignored_loan in

  let register_borrow (kind : borrow_kind) (bid : BorrowId.id)
      (sid : SharedBorrowId.id option) : unit =
    [%sanity_check] span (kind = BMut || Option.is_some sid);
    (* Lookup the info *)
    let info = find_info bid in
    (* Check that the borrow kind is consistent *)
    (match (info.loan_kind, kind) with
    | RShared, (BShared | BReserved) | RMut, BMut -> ()
    | _ -> [%craise] span "Invariant not satisfied");
    (* Check that shared borrow ids are unique *)
    (match sid with
    | None -> ()
    | Some sid ->
        [%sanity_check] span
          (not (SharedBorrowId.Set.mem sid !shared_borrow_ids));
        shared_borrow_ids := SharedBorrowId.Set.add sid !shared_borrow_ids);
    (* A reserved borrow can't point to a value inside an abstraction *)
    [%sanity_check] span (kind <> BReserved || not info.loan_in_abs);
    (* Insert the borrow id *)
    [%sanity_check] span (info.loan_kind = RShared || not info.found_borrow);
    [%sanity_check] span
      (match sid with
      | None -> true
      | Some sid -> not (SharedBorrowId.Set.mem sid info.shared_borrow_ids));
    let info =
      {
        info with
        found_borrow = true;
        shared_borrow_ids =
          (match sid with
          | None -> info.shared_borrow_ids
          | Some sid -> SharedBorrowId.Set.add sid info.shared_borrow_ids);
      }
    in
    (* Update the info in the map *)
    update_info bid info
  in

  let borrows_visitor =
    object
      inherit [_] iter_eval_ctx as super

      method! visit_abstract_shared_borrow _ asb =
        match asb with
        | AsbBorrow (bid, sid) -> register_borrow BShared bid (Some sid)
        | AsbProjReborrows _ -> ()

      method! visit_borrow_content env bc =
        (* Register the loan *)
        let _ =
          match bc with
          | VSharedBorrow (bid, sid) -> register_borrow BShared bid (Some sid)
          | VMutBorrow (bid, _) -> register_borrow BMut bid None
          | VReservedMutBorrow (bid, sid) ->
              register_borrow BReserved bid (Some sid)
        in
        (* Continue exploring *)
        super#visit_borrow_content env bc

      method! visit_aborrow_content env bc =
        let _ =
          match bc with
          | AMutBorrow (_, bid, _) -> register_borrow BMut bid None
          | ASharedBorrow (_, bid, sid) ->
              register_borrow BShared bid (Some sid)
          | AIgnoredMutBorrow (Some bid, _) -> register_ignored_borrow RMut bid
          | AIgnoredMutBorrow (None, _)
          | AEndedMutBorrow _
          | AEndedIgnoredMutBorrow _
          | AEndedSharedBorrow
          | AProjSharedBorrow _ ->
              (* Do nothing *)
              ()
        in
        (* Continue exploring *)
        super#visit_aborrow_content env bc
    end
  in

  (* Visit *)
  borrows_visitor#visit_eval_ctx () ctx;

  (* Debugging *)
  [%ldebug "About to check context invariant:\n" ^ context_to_string ()];

  (* Finally, check that everything is consistant *)
  (* First, check all the ignored loans are present at the proper place *)
  List.iter
    (fun (rkind, bid) ->
      let info = find_info bid in
      [%sanity_check] span (info.loan_kind = rkind))
    !ignored_loans;

  (* Then, check the borrow infos *)
  BorrowId.Map.iter
    (fun _ (info : borrow_info) ->
      (* If the loan is a mutable loan, then the corresponding borrow must appear somewhere *)
      [%sanity_check] span (info.loan_kind <> RMut || info.found_borrow))
    !borrows_infos

(** Check that:
    - borrows/loans can't contain ⊥ or reserved mut borrows
    - shared loans can't contain mutable loans *)
let check_borrowed_values_invariant (span : Meta.span) (ctx : eval_ctx) : unit =
  let visitor =
    object
      inherit [_] iter_eval_ctx as super

      method! visit_VBottom info =
        (* No ⊥ inside borrowed values *)
        [%sanity_check] span
          (Config.allow_bottom_below_borrow || not info.outer_borrow)

      method! visit_loan_content info lc =
        (* Update the info *)
        let info =
          match lc with
          | VSharedLoan (_, _) -> set_outer_shared info
          | VMutLoan _ ->
              (* No mutable loan inside a shared loan *)
              [%sanity_check] span (not info.outer_shared);
              set_outer_mut info
        in
        (* Continue exploring *)
        super#visit_loan_content info lc

      method! visit_borrow_content info bc =
        (* Update the info *)
        let info =
          match bc with
          | VSharedBorrow _ -> set_outer_shared info
          | VReservedMutBorrow _ ->
              [%sanity_check] span (not info.outer_borrow);
              set_outer_shared info
          | VMutBorrow (_, _) -> set_outer_mut info
        in
        (* Continue exploring *)
        super#visit_borrow_content info bc

      method! visit_aloan_content info lc =
        (* Update the info *)
        let info =
          match lc with
          | AMutLoan (_, _, _) -> set_outer_mut info
          | ASharedLoan (_, _, _, _) -> set_outer_shared info
          | AEndedMutLoan { given_back = _; child = _; given_back_meta = _ } ->
              set_outer_mut info
          | AEndedSharedLoan (_, _) -> set_outer_shared info
          | AIgnoredMutLoan (_, _) -> set_outer_mut info
          | AEndedIgnoredMutLoan
              { given_back = _; child = _; given_back_meta = _ } ->
              set_outer_mut info
          | AIgnoredSharedLoan _ -> set_outer_shared info
        in
        (* Continue exploring *)
        super#visit_aloan_content info lc

      method! visit_aborrow_content info bc =
        (* Update the info *)
        let info =
          match bc with
          | AMutBorrow (_, _, _) -> set_outer_mut info
          | ASharedBorrow _ | AEndedSharedBorrow -> set_outer_shared info
          | AIgnoredMutBorrow _ | AEndedMutBorrow _ | AEndedIgnoredMutBorrow _
            -> set_outer_mut info
          | AProjSharedBorrow _ -> set_outer_shared info
        in
        (* Continue exploring *)
        super#visit_aborrow_content info bc
    end
  in

  (* Explore *)
  let info = { outer_borrow = false; outer_shared = false } in
  visitor#visit_eval_ctx info ctx

let check_literal_type (span : Meta.span) (cv : literal) (ty : literal_type) :
    unit =
  match (cv, ty) with
  | VScalar (SignedScalar (sv_ty, _)), TInt int_ty ->
      [%sanity_check] span (sv_ty = int_ty)
  | VScalar (UnsignedScalar (sv_ty, _)), TUInt int_ty ->
      [%sanity_check] span (sv_ty = int_ty)
  | VBool _, TBool | VChar _, TChar -> ()
  | _ -> [%craise] span "Erroneous typing"

(** If [lookups] is [true] whenever we encounter a loan/borrow we lookup the
    corresponding borrow/loan to check its type. This only works when checking
    non-partial environments. *)
let check_typing_invariant_visitor span ctx (lookups : bool) =
  (* TODO: the type of aloans doens't make sense: they have a type
   * of the shape [& (mut) T] where they should have type [T]...
   * This messes a bit the type invariant checks when checking the
   * children. In order to isolate the problem (for future modifications)
   * we introduce this function, so that we can easily spot all the involved
   * places.
   *)
  let aloan_get_expected_child_type (ty : ty) : ty =
    let _, ty, _ = ty_get_ref ty in
    ty
  in
  (* The types with erased regions of the symbolic values that we find *)
  let sv_etys = ref SymbolicValueId.Map.empty in
  let check_symbolic_value_type sv_id ty =
    let ty = Substitute.erase_regions ty in
    match SymbolicValueId.Map.find_opt sv_id !sv_etys with
    | None -> sv_etys := SymbolicValueId.Map.add sv_id ty !sv_etys
    | Some ty1 -> [%sanity_check] span (ty1 = ty)
  in
  object
    inherit [_] iter_eval_ctx as super
    method! visit_abs _ abs = super#visit_abs (Some abs) abs

    method! visit_EBinding info binder v =
      (* We also check that the regions are erased *)
      [%sanity_check] span (ty_is_ety v.ty);
      super#visit_EBinding info binder v

    method! visit_symbolic_value inside_abs v =
      (* Check that the types have regions *)
      [%sanity_check] span (ty_is_rty v.sv_ty);
      super#visit_symbolic_value inside_abs v

    method! visit_tvalue info tv =
      (* Check that the types have erased regions *)
      [%sanity_check] span (ty_is_ety tv.ty);
      (* Check the current pair (value, type) *)
      (match (tv.value, tv.ty) with
      | VLiteral cv, TLiteral ty -> check_literal_type span cv ty
      (* ADT case *)
      | VAdt av, TAdt { id = TAdtId def_id; generics } ->
          (* Retrieve the definition to check the variant id, the number of
           * parameters, etc. *)
          let def = ctx_lookup_type_decl span ctx def_id in
          (* Check the number of parameters *)
          [%sanity_check] span
            (List.length generics.regions = List.length def.generics.regions);
          [%sanity_check] span
            (List.length generics.types = List.length def.generics.types);
          (* Check that the variant id is consistent *)
          (match (av.variant_id, def.kind) with
          | Some variant_id, Enum variants ->
              [%sanity_check] span
                (VariantId.to_int variant_id < List.length variants)
          | None, Struct _ -> ()
          | _ -> [%craise] span "Erroneous typing");
          (* Check that the field types are correct *)
          let field_types =
            Substitute.type_decl_get_instantiated_field_etypes def av.variant_id
              generics
          in
          let fields_with_types = List.combine av.fields field_types in
          List.iter
            (fun ((v, ty) : tvalue * ty) -> [%sanity_check] span (v.ty = ty))
            fields_with_types
      (* Tuple case *)
      | VAdt av, TAdt { id = TTuple; generics } ->
          [%sanity_check] span (generics.regions = []);
          [%sanity_check] span (generics.const_generics = []);
          [%sanity_check] span (av.variant_id = None);
          (* Check that the fields have the proper values - and check that there
           * are as many fields as field types at the same time *)
          let fields_with_types = List.combine av.fields generics.types in
          List.iter
            (fun ((v, ty) : tvalue * ty) -> [%sanity_check] span (v.ty = ty))
            fields_with_types
      (* Builtin type case *)
      | VAdt av, TAdt { id = TBuiltin aty_id; generics } -> (
          [%sanity_check] span (av.variant_id = None);
          match
            ( aty_id,
              av.fields,
              generics.regions,
              generics.types,
              generics.const_generics )
          with
          (* Box *)
          | TBox, [ inner_value ], [], [ inner_ty ], [] ->
              [%sanity_check] span (inner_value.ty = inner_ty)
          | TArray, inner_values, _, [ inner_ty ], [ cg ] ->
              (* *)
              [%sanity_check] span
                (List.for_all
                   (fun (v : tvalue) -> v.ty = inner_ty)
                   inner_values);
              (* The length is necessarily concrete *)
              let len =
                Scalars.get_val
                  (ValuesUtils.literal_as_scalar
                     (TypesUtils.const_generic_as_literal cg))
              in
              [%sanity_check] span (Z.of_int (List.length inner_values) = len)
          | (TSlice | TStr), _, _, _, _ -> [%craise] span "Unexpected"
          | _ -> [%craise] span "Erroneous type")
      | VBottom, _ -> (* Nothing to check *) ()
      | VBorrow bc, TRef (_, ref_ty, rkind) -> (
          match (bc, rkind) with
          | VSharedBorrow (bid, _), RShared | VReservedMutBorrow (bid, _), RMut
            -> (
              if
                (* Lookup the borrowed value to check it has the proper type.
                   Note that we ignore the marker: we will check it when
                   checking the loan itself. *)
                lookups
              then
                let _, glc = ctx_lookup_loan span ek_all bid ctx in
                match glc with
                | Concrete (VSharedLoan (_, sv))
                | Abstract (ASharedLoan (_, _, sv, _)) ->
                    [%sanity_check] span (sv.ty = ref_ty)
                | _ -> [%craise] span "Inconsistent context")
          | VMutBorrow (_, bv), RMut ->
              [%sanity_check] span
                ((* Check that the borrowed value has the proper type *)
                 bv.ty = ref_ty)
          | _ -> [%craise] span "Erroneous typing")
      | VLoan lc, ty -> (
          match lc with
          | VSharedLoan (_, sv) -> [%sanity_check] span (sv.ty = ty)
          | VMutLoan bid -> (
              if lookups then
                (* Lookup the borrowed value to check it has the proper type. *)
                let glc = lookup_borrow span ek_all (UMut bid) ctx in
                match glc with
                | Concrete (VMutBorrow (_, bv)) ->
                    [%sanity_check] span (bv.ty = ty)
                | Abstract (AMutBorrow (_, _, sv)) ->
                    [%sanity_check] span (Substitute.erase_regions sv.ty = ty)
                | _ -> [%craise] span "Inconsistent context"))
      | VSymbolic sv, ty ->
          check_symbolic_value_type sv.sv_id sv.sv_ty;
          let ty' = Substitute.erase_regions sv.sv_ty in
          [%sanity_check] span (ty' = ty)
      | _ -> [%craise] span "Erroneous typing");
      (* Continue exploring to inspect the subterms *)
      super#visit_tvalue info tv

    (* TODO: there is a lot of duplication with {!visit_tvalue}
     * which is quite annoying. There might be a way of factorizing
     * that by factorizing the definitions of value and avalue, but
     * the generation of visitors then doesn't work properly (TODO:
     * report that). Still, it is actually not that problematic
     * because this code shouldn't change a lot in the future,
     * so the cost of maintenance should be pretty low.
     *)
    method! visit_tavalue info atv =
      (* Check that the types have regions *)
      [%sanity_check] span (ty_is_rty atv.ty);
      (* Check the current pair (value, type) *)
      (match (atv.value, atv.ty) with
      (* ADT case *)
      | AAdt av, TAdt { id = TAdtId def_id; generics } ->
          (* Retrieve the definition to check the variant id, the number of
           * parameters, etc. *)
          let def = ctx_lookup_type_decl span ctx def_id in
          (* Check the number of parameters *)
          [%sanity_check] span
            (List.length generics.regions = List.length def.generics.regions);
          [%sanity_check] span
            (List.length generics.types = List.length def.generics.types);
          [%sanity_check] span
            (List.length generics.const_generics
            = List.length def.generics.const_generics);
          (* Check that the variant id is consistent *)
          (match (av.variant_id, def.kind) with
          | Some variant_id, Enum variants ->
              [%sanity_check] span
                (VariantId.to_int variant_id < List.length variants)
          | None, Struct _ -> ()
          | _ -> [%craise] span "Erroneous typing");
          (* Check that the field types are correct *)
          let field_types =
            Substitute.type_decl_get_instantiated_field_types def av.variant_id
              generics
          in
          let fields_with_types = List.combine av.fields field_types in
          List.iter
            (fun ((v, ty) : tavalue * ty) -> [%sanity_check] span (v.ty = ty))
            fields_with_types
      (* Tuple case *)
      | AAdt av, TAdt { id = TTuple; generics } ->
          [%sanity_check] span (generics.regions = []);
          [%sanity_check] span (generics.const_generics = []);
          [%sanity_check] span (av.variant_id = None);
          (* Check that the fields have the proper values - and check that there
           * are as many fields as field types at the same time *)
          let fields_with_types = List.combine av.fields generics.types in
          List.iter
            (fun ((v, ty) : tavalue * ty) -> [%sanity_check] span (v.ty = ty))
            fields_with_types
      (* Builtin type case *)
      | AAdt av, TAdt { id = TBuiltin aty_id; generics } -> (
          [%sanity_check] span (av.variant_id = None);
          match
            ( aty_id,
              av.fields,
              generics.regions,
              generics.types,
              generics.const_generics )
          with
          (* Box *)
          | TBox, [ boxed_value ], [], [ boxed_ty ], [] ->
              [%sanity_check] span (boxed_value.ty = boxed_ty)
          | _ -> [%craise] span "Erroneous type")
      | ABorrow bc, TRef (region, ref_ty, rkind) -> (
          let abs = Option.get info in
          (* Check the borrow content *)
          match (bc, rkind) with
          | AMutBorrow (_, _, av), RMut ->
              (* Check that the region is owned by the abstraction *)
              [%sanity_check] span (region_is_owned abs region);
              (* Check that the child value has the proper type *)
              [%sanity_check] span (av.ty = ref_ty)
          | ASharedBorrow (_, bid, _), RShared -> (
              (* Check that the region is owned by the abstraction *)
              [%sanity_check] span (region_is_owned abs region);
              if lookups then
                (* Lookup the borrowed value to check it has the proper type *)
                let _, glc = ctx_lookup_loan span ek_all bid ctx in
                match glc with
                | Concrete (VSharedLoan (_, sv))
                | Abstract (ASharedLoan (_, _, sv, _)) ->
                    [%sanity_check] span
                      (sv.ty = Substitute.erase_regions ref_ty)
                | _ -> [%craise] span "Inconsistent context")
          | AIgnoredMutBorrow (_opt_bid, av), RMut ->
              [%sanity_check] span (av.ty = ref_ty)
          | ( AEndedIgnoredMutBorrow { given_back; child; given_back_meta = _ },
              RMut ) ->
              [%sanity_check] span (given_back.ty = ref_ty);
              [%sanity_check] span (child.ty = ref_ty)
          | AProjSharedBorrow _, RShared -> ()
          | _ -> [%craise] span "Inconsistent context")
      | ALoan lc, aty -> (
          let abs = Option.get info in
          match lc with
          | AMutLoan (_, bid, child_av) | AIgnoredMutLoan (Some bid, child_av)
            -> (
              (* Check that the region is owned by the abstraction *)
              let region, _, _ = ty_as_ref aty in
              begin
                match lc with
                | AMutLoan _ ->
                    [%sanity_check] span (region_is_owned abs region)
                | _ -> ()
              end;
              let borrowed_aty = aloan_get_expected_child_type aty in
              [%sanity_check] span (child_av.ty = borrowed_aty);
              if lookups then
                (* Lookup the borrowed value to check it has the proper type *)
                let glc = lookup_borrow span ek_all (UMut bid) ctx in
                match glc with
                | Concrete (VMutBorrow (_, bv)) ->
                    [%sanity_check] span
                      (bv.ty = Substitute.erase_regions borrowed_aty)
                | Abstract (AMutBorrow (_, _, sv)) ->
                    [%sanity_check] span
                      (Substitute.erase_regions sv.ty
                      = Substitute.erase_regions borrowed_aty)
                | _ -> [%craise] span "Inconsistent context")
          | AIgnoredMutLoan (None, child_av) ->
              let borrowed_aty = aloan_get_expected_child_type aty in
              [%sanity_check] span (child_av.ty = borrowed_aty)
          | ASharedLoan (_, _, sv, child_av) | AEndedSharedLoan (sv, child_av)
            ->
              (* Check that the region is owned by the abstraction *)
              let region, _, _ = ty_as_ref aty in
              [%sanity_check] span (region_is_owned abs region);
              let borrowed_aty = aloan_get_expected_child_type aty in
              [%sanity_check] span
                (sv.ty = Substitute.erase_regions borrowed_aty);
              (* TODO: the type of aloans doesn't make sense, see above *)
              [%sanity_check] span (child_av.ty = borrowed_aty)
          | AEndedMutLoan { given_back; child; given_back_meta = _ }
          | AEndedIgnoredMutLoan { given_back; child; given_back_meta = _ } ->
              (* Check that the region is owned by the abstraction *)
              let region, _, _ = ty_as_ref aty in
              begin
                match lc with
                | AEndedMutLoan _ ->
                    [%sanity_check] span (region_is_owned abs region)
                | _ -> ()
              end;
              let borrowed_aty = aloan_get_expected_child_type aty in
              [%sanity_check] span (given_back.ty = borrowed_aty);
              [%sanity_check] span (child.ty = borrowed_aty)
          | AIgnoredSharedLoan child_av ->
              [%sanity_check] span
                (child_av.ty = aloan_get_expected_child_type aty))
      | ASymbolic (_, aproj), ty -> (
          match aproj with
          | AProjLoans { proj; _ } ->
              check_symbolic_value_type proj.sv_id ty;
              let abs = Option.get info in
              [%sanity_check] span
                (ty_has_regions_in_set abs.regions.owned proj.proj_ty)
          | AProjBorrows { proj; _ } ->
              check_symbolic_value_type proj.sv_id ty;
              [%sanity_check] span (ty_has_free_regions proj.proj_ty)
          | AEndedProjLoans { proj = _; consumed; borrows } ->
              List.iter
                (fun (_, proj) ->
                  match proj with
                  | AProjBorrows { proj; _ } | AProjLoans { proj; _ } ->
                      [%sanity_check] span (proj.proj_ty = ty)
                  | AEndedProjBorrows _ | AEmpty -> ()
                  | _ -> [%craise] span "Unexpected")
                (consumed @ borrows)
          | AEndedProjBorrows _ | AEmpty -> ())
      | AIgnored _, _ -> ()
      | _ ->
          [%ltrace
            "Erroneous typing:" ^ "\n- raw value: " ^ show_tavalue atv
            ^ "\n- value: "
            ^ tavalue_to_string ~span:(Some span) ctx atv
            ^ "\n- type: " ^ ty_to_string ctx atv.ty];
          [%internal_error] span);
      (* Continue exploring to inspect the subterms *)
      super#visit_tavalue info atv
  end

let check_typing_invariant (span : Meta.span) (ctx : eval_ctx) (lookups : bool)
    : unit =
  (check_typing_invariant_visitor span ctx lookups)#visit_eval_ctx
    (None : abs option)
    ctx

type proj_borrows_info = {
  abs_id : AbsId.id;
  regions : RegionId.Set.t;
  proj_ty : rty;  (** The regions shouldn't be erased *)
  as_shared_value : bool;  (** True if the value is below a shared borrow *)
}
[@@deriving show]

type proj_loans_info = {
  abs_id : AbsId.id;
  regions : RegionId.Set.t;
  proj_ty : rty;
}
[@@deriving show]

type sv_info = {
  env_count : int;
  aproj_borrows : proj_borrows_info list;
  aproj_loans : proj_loans_info list;
}
[@@deriving show]

let proj_borrows_info_to_string (ctx : eval_ctx) (info : proj_borrows_info) :
    string =
  let { abs_id; regions; proj_ty; as_shared_value } = info in
  "{ abs_id = " ^ AbsId.to_string abs_id ^ "; regions = "
  ^ RegionId.Set.to_string None regions
  ^ "; proj_ty = " ^ ty_to_string ctx proj_ty ^ "; as_shared_value = "
  ^ Print.bool_to_string as_shared_value
  ^ "}"

let proj_loans_info_to_string (ctx : eval_ctx) (info : proj_loans_info) : string
    =
  let { abs_id; regions; proj_ty } = info in
  "{ abs_id = " ^ AbsId.to_string abs_id ^ "; regions = "
  ^ RegionId.Set.to_string None regions
  ^ "; proj_ty = " ^ ty_to_string ctx proj_ty ^ "}"

let sv_info_to_string (ctx : eval_ctx) (info : sv_info) : string =
  let { env_count = _; aproj_borrows; aproj_loans } = info in
  "{\n  aproj_borrows = ["
  ^ String.concat ", "
      (List.map (proj_borrows_info_to_string ctx) aproj_borrows)
  ^ "];\n  aproj_loans = ["
  ^ String.concat ", " (List.map (proj_loans_info_to_string ctx) aproj_loans)
  ^ "]\n}"

(** Check the invariants over the symbolic values.

    - a symbolic value can't be both in proj_borrows and in the concrete env
      (this is why we preemptively expand copyable symbolic values)
    - if a symbolic value contains regions: there is at most one occurrence of
      this value in the concrete env
    - if there is an aproj_borrows in the environment, there must also be a
      corresponding aproj_loans
    - aproj_loans are mutually disjoint
    - TODO: aproj_borrows are mutually disjoint
    - the union of the aproj_loans contains the aproj_borrows applied on the
      same symbolic values
    - all symbolic evalues should contain mutable borrows/loans *)
let check_symbolic_values (span : Meta.span) (ctx : eval_ctx) : unit =
  (* Small utility *)
  let module M = SymbolicValueId.Map in
  let infos : sv_info M.t ref = ref M.empty in
  let lookup_info (sv_id : symbolic_value_id) : sv_info =
    match M.find_opt sv_id !infos with
    | Some info -> info
    | None -> { env_count = 0; aproj_borrows = []; aproj_loans = [] }
  in
  let update_info (sv_id : symbolic_value_id) (info : sv_info) =
    infos := M.add sv_id info !infos
  in
  let add_env_sv (sv_id : symbolic_value_id) : unit =
    let info = lookup_info sv_id in
    let info = { info with env_count = info.env_count + 1 } in
    update_info sv_id info
  in
  let add_aproj_borrows abs_id regions (proj : symbolic_proj) as_shared_value :
      unit =
    let sv_id = proj.sv_id in
    let info = lookup_info sv_id in
    let binfo = { abs_id; regions; proj_ty = proj.proj_ty; as_shared_value } in
    let info = { info with aproj_borrows = binfo :: info.aproj_borrows } in
    update_info sv_id info
  in
  let add_aproj_loans abs_id regions (proj : symbolic_proj) : unit =
    let sv = proj.sv_id in
    let info = lookup_info sv in
    let linfo = { abs_id; regions; proj_ty = proj.proj_ty } in
    let info = { info with aproj_loans = linfo :: info.aproj_loans } in
    update_info sv info
  in
  (* Visitor *)
  let obj =
    object
      inherit [_] iter_eval_ctx as super
      method! visit_abs _ abs = super#visit_abs (Some abs) abs
      method! visit_VSymbolic _ sv = add_env_sv sv.sv_id

      method! visit_abstract_shared_borrow abs asb =
        let abs = Option.get abs in
        match asb with
        | AsbBorrow _ -> ()
        | AsbProjReborrows proj ->
            add_aproj_borrows abs.abs_id abs.regions.owned proj true

      method! visit_aproj abs aproj =
        (let abs = Option.get abs in
         match aproj with
         | AProjLoans { proj; _ } ->
             add_aproj_loans abs.abs_id abs.regions.owned proj
         | AProjBorrows { proj; _ } ->
             add_aproj_borrows abs.abs_id abs.regions.owned proj false
         | AEndedProjLoans _ | AEndedProjBorrows _ | AEmpty -> ());
        super#visit_aproj abs aproj

      method! visit_eproj abs eproj =
        (let abs = Option.get abs in
         match eproj with
         | EProjLoans { proj; consumed = _; borrows = _ }
         | EProjBorrows { proj; loans = _ } ->
             (* Symbolic projections in evalues should be over values which contain
                mutable borrows/loans *)
             if
               not
                 (ty_has_mut_borrow_for_region_in_set ctx.type_ctx.type_infos
                    abs.regions.owned proj.proj_ty)
             then (
               [%ldebug
                 "Abs contains evalues with no mutable borrows/loans:\n"
                 ^ abs_to_string span ctx abs ^ "\n\nProblematic eproj:\n"
                 ^ eproj_to_string ctx eproj];
               [%internal_error] span)
         | EEndedProjLoans _ | EEndedProjBorrows _ | EEmpty -> ());
        super#visit_eproj abs eproj
    end
  in
  (* Collect the information *)
  obj#visit_eval_ctx None ctx;

  (* Check *)
  let check_info id info =
    [%ldebug
      "checking info (sid: )"
      ^ SymbolicValueId.to_string id
      ^ ":\n" ^ sv_info_to_string ctx info];
    if info.aproj_borrows = [] && info.aproj_loans = [] then ()
    else (
      (* TODO: check that:
       * - the borrows are mutually disjoint
       *)
      (* The borrows of a symbolic value must come from somewhere: if we find a
         symbolic values with live borrows (and particular a projection over the
         borrows of a symbolic value), there *must* be a projection over its loans
         (otherwise its borrows don't have corresponding loans). *)
      [%sanity_check] span (info.aproj_borrows = [] || info.aproj_loans <> []);
      (* Check that the loan projections don't intersect and compute
         the normalized union of those projections *)
      let aproj_loans =
        List.map
          (fun (linfo : proj_loans_info) ->
            normalize_proj_ty linfo.regions linfo.proj_ty)
          info.aproj_loans
      in

      (* There should be at least one loan proj *)
      let loan_proj_union =
        match aproj_loans with
        | [] -> [%internal_error] span
        | loan_proj_union :: aproj_loans ->
            List.fold_left
              (fun loan_proj_union proj_ty ->
                norm_proj_tys_union span loan_proj_union proj_ty)
              loan_proj_union aproj_loans
      in

      (* Check that the union of the loan projectors contains the borrow projections. *)
      let aproj_borrows =
        List.map
          (fun (linfo : proj_borrows_info) ->
            normalize_proj_ty linfo.regions linfo.proj_ty)
          info.aproj_borrows
      in
      match aproj_borrows with
      | [] -> (* Nothing to do *) ()
      | borrow_proj_union :: aproj_borrows ->
          let borrow_proj_union =
            List.fold_left
              (fun borrow_proj_union proj_ty ->
                norm_proj_tys_union span borrow_proj_union proj_ty)
              borrow_proj_union aproj_borrows
          in
          [%sanity_check] span
            (norm_proj_ty_contains span loan_proj_union borrow_proj_union))
  in

  M.iter check_info !infos

(** Check that all abstraction ids are unique *)
let check_unique_abs_ids (span : Meta.span) (ctx : eval_ctx) : unit =
  let ids = ref AbsId.Set.empty in
  env_iter_abs
    (fun (abs : abs) ->
      [%sanity_check] span (not (AbsId.Set.mem abs.abs_id !ids));
      ids := AbsId.Set.add abs.abs_id !ids)
    ctx.env

let check_invariants (span : Meta.span) (ctx : eval_ctx) : unit =
  if !Config.sanity_checks then (
    [%ltrace
      "Checking invariants in context:\n"
      ^ eval_ctx_to_string ~span:(Some span) ctx];
    check_loans_borrows_relation_invariant span ctx;
    check_borrowed_values_invariant span ctx;
    check_typing_invariant span ctx true;
    check_symbolic_values span ctx;
    check_unique_abs_ids span ctx)

let check_typing_invariant (span : Meta.span) (ctx : eval_ctx) : unit =
  if !Config.sanity_checks then check_typing_invariant span ctx true

let opt_type_check_abs (span : Meta.span) (ctx : eval_ctx) (abs : abs) : unit =
  if !Config.sanity_checks then
    (check_typing_invariant_visitor span ctx false)#visit_abs None abs

let opt_type_check_absl (span : Meta.span) (ctx : eval_ctx) (absl : abs list) :
    unit =
  if !Config.sanity_checks then
    List.iter
      ((check_typing_invariant_visitor span ctx false)#visit_abs None)
      absl
