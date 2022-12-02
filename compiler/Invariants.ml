(* The following module defines functions to check that some invariants
 * are always maintained by evaluation contexts *)

module T = Types
module PV = PrimitiveValues
module V = Values
module E = Expressions
module C = Contexts
module Subst = Substitute
module A = LlbcAst
module L = Logging
open Cps
open TypesUtils
open InterpreterUtils
open InterpreterBorrowsCore

(** The local logger *)
let log = L.invariants_log

type borrow_info = {
  loan_kind : T.ref_kind;
  loan_in_abs : bool;
  (* true if the loan was found in an abstraction *)
  loan_ids : V.BorrowId.Set.t;
  borrow_ids : V.BorrowId.Set.t;
}
[@@deriving show]

type outer_borrow_info = {
  outer_borrow : bool;
  (* true if the value is borrowed *)
  outer_shared : bool; (* true if the value is borrowed as shared *)
}

let set_outer_mut (info : outer_borrow_info) : outer_borrow_info =
  { info with outer_borrow = true }

let set_outer_shared (_info : outer_borrow_info) : outer_borrow_info =
  { outer_borrow = true; outer_shared = true }

let ids_reprs_to_string (indent : string)
    (reprs : V.BorrowId.id V.BorrowId.Map.t) : string =
  V.BorrowId.Map.to_string (Some indent) V.BorrowId.to_string reprs

let borrows_infos_to_string (indent : string)
    (infos : borrow_info V.BorrowId.Map.t) : string =
  V.BorrowId.Map.to_string (Some indent) show_borrow_info infos

type borrow_kind = Mut | Shared | Reserved

(** Check that:
    - loans and borrows are correctly related
    - a two-phase borrow can't point to a value inside an abstraction
 *)
let check_loans_borrows_relation_invariant (ctx : C.eval_ctx) : unit =
  (* Link all the borrow ids to a representant - necessary because of shared
   * borrows/loans *)
  let ids_reprs : V.BorrowId.id V.BorrowId.Map.t ref =
    ref V.BorrowId.Map.empty
  in
  (* Link all the id representants to a borrow information *)
  let borrows_infos : borrow_info V.BorrowId.Map.t ref =
    ref V.BorrowId.Map.empty
  in
  let context_to_string () : string =
    eval_ctx_to_string ctx ^ "- representants:\n"
    ^ ids_reprs_to_string "  " !ids_reprs
    ^ "\n- info:\n"
    ^ borrows_infos_to_string "  " !borrows_infos
  in
  (* Ignored loans - when we find an ignored loan while building the borrows_infos
   * map, we register it in this list; once the borrows_infos map is completely
   * built, we check that all the borrow ids of the ignored loans are in this
   * map *)
  let ignored_loans : (T.ref_kind * V.BorrowId.id) list ref = ref [] in

  (* first, register all the loans *)
  (* Some utilities to register the loans *)
  let register_ignored_loan (rkind : T.ref_kind) (bid : V.BorrowId.id) : unit =
    ignored_loans := (rkind, bid) :: !ignored_loans
  in

  let register_shared_loan (loan_in_abs : bool) (bids : V.BorrowId.Set.t) : unit
      =
    let reprs = !ids_reprs in
    let infos = !borrows_infos in
    (* Use the first borrow id as representant *)
    let repr_bid = V.BorrowId.Set.min_elt bids in
    assert (not (V.BorrowId.Map.mem repr_bid infos));
    (* Insert the mappings to the representant *)
    let reprs =
      V.BorrowId.Set.fold
        (fun bid reprs ->
          assert (not (V.BorrowId.Map.mem bid reprs));
          V.BorrowId.Map.add bid repr_bid reprs)
        bids reprs
    in
    (* Insert the loan info *)
    let info =
      {
        loan_kind = T.Shared;
        loan_in_abs;
        loan_ids = bids;
        borrow_ids = V.BorrowId.Set.empty;
      }
    in
    let infos = V.BorrowId.Map.add repr_bid info infos in
    (* Update *)
    ids_reprs := reprs;
    borrows_infos := infos
  in

  let register_mut_loan (loan_in_abs : bool) (bid : V.BorrowId.id) : unit =
    let reprs = !ids_reprs in
    let infos = !borrows_infos in
    (* Sanity checks *)
    assert (not (V.BorrowId.Map.mem bid reprs));
    assert (not (V.BorrowId.Map.mem bid infos));
    (* Add the mapping for the representant *)
    let reprs = V.BorrowId.Map.add bid bid reprs in
    (* Add the mapping for the loan info *)
    let info =
      {
        loan_kind = T.Mut;
        loan_in_abs;
        loan_ids = V.BorrowId.Set.singleton bid;
        borrow_ids = V.BorrowId.Set.empty;
      }
    in
    let infos = V.BorrowId.Map.add bid info infos in
    (* Update *)
    ids_reprs := reprs;
    borrows_infos := infos
  in

  let loans_visitor =
    object
      inherit [_] C.iter_eval_ctx as super

      method! visit_Var _ binder v =
        let inside_abs = false in
        super#visit_Var inside_abs binder v

      method! visit_Abs _ abs =
        let inside_abs = true in
        super#visit_Abs inside_abs abs

      method! visit_loan_content inside_abs lc =
        (* Register the loan *)
        let _ =
          match lc with
          | V.SharedLoan (bids, _) -> register_shared_loan inside_abs bids
          | V.MutLoan bid -> register_mut_loan inside_abs bid
        in
        (* Continue exploring *)
        super#visit_loan_content inside_abs lc

      method! visit_aloan_content inside_abs lc =
        let _ =
          match lc with
          | V.AMutLoan (bid, _) -> register_mut_loan inside_abs bid
          | V.ASharedLoan (bids, _, _) -> register_shared_loan inside_abs bids
          | V.AIgnoredMutLoan (Some bid, _) -> register_ignored_loan T.Mut bid
          | V.AIgnoredMutLoan (None, _)
          | V.AIgnoredSharedLoan _
          | V.AEndedMutLoan { given_back = _; child = _; given_back_meta = _ }
          | V.AEndedSharedLoan (_, _)
          | V.AEndedIgnoredMutLoan
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
  let find_info (bid : V.BorrowId.id) : borrow_info =
    (* Find the representant *)
    match V.BorrowId.Map.find_opt bid !ids_reprs with
    | Some repr_bid ->
        (* Lookup the info *)
        V.BorrowId.Map.find repr_bid !borrows_infos
    | None ->
        let err =
          "find_info: could not find the representant of borrow "
          ^ V.BorrowId.to_string bid ^ ":\nContext:\n" ^ context_to_string ()
        in
        log#serror err;
        raise (Failure err)
  in

  let update_info (bid : V.BorrowId.id) (info : borrow_info) : unit =
    (* Find the representant *)
    let repr_bid = V.BorrowId.Map.find bid !ids_reprs in
    (* Update the info *)
    let infos =
      V.BorrowId.Map.update repr_bid
        (fun x ->
          match x with
          | Some _ -> Some info
          | None -> raise (Failure "Unreachable"))
        !borrows_infos
    in
    borrows_infos := infos
  in

  let register_ignored_borrow = register_ignored_loan in

  let register_borrow (kind : borrow_kind) (bid : V.BorrowId.id) : unit =
    (* Lookup the info *)
    let info = find_info bid in
    (* Check that the borrow kind is consistent *)
    (match (info.loan_kind, kind) with
    | T.Shared, (Shared | Reserved) | T.Mut, Mut -> ()
    | _ -> raise (Failure "Invariant not satisfied"));
    (* A reserved borrow can't point to a value inside an abstraction *)
    assert (kind <> Reserved || not info.loan_in_abs);
    (* Insert the borrow id *)
    let borrow_ids = info.borrow_ids in
    assert (not (V.BorrowId.Set.mem bid borrow_ids));
    let info = { info with borrow_ids = V.BorrowId.Set.add bid borrow_ids } in
    (* Update the info in the map *)
    update_info bid info
  in

  let borrows_visitor =
    object
      inherit [_] C.iter_eval_ctx as super

      method! visit_abstract_shared_borrow _ asb =
        match asb with
        | V.AsbBorrow bid -> register_borrow Shared bid
        | V.AsbProjReborrows _ -> ()

      method! visit_borrow_content env bc =
        (* Register the loan *)
        let _ =
          match bc with
          | V.SharedBorrow bid -> register_borrow Shared bid
          | V.MutBorrow (bid, _) -> register_borrow Mut bid
          | V.ReservedMutBorrow bid -> register_borrow Reserved bid
        in
        (* Continue exploring *)
        super#visit_borrow_content env bc

      method! visit_aborrow_content env bc =
        let _ =
          match bc with
          | V.AMutBorrow (bid, _) -> register_borrow Mut bid
          | V.ASharedBorrow bid -> register_borrow Shared bid
          | V.AIgnoredMutBorrow (Some bid, _) -> register_ignored_borrow Mut bid
          | V.AIgnoredMutBorrow (None, _)
          | V.AEndedMutBorrow _ | V.AEndedIgnoredMutBorrow _
          | V.AEndedSharedBorrow | V.AProjSharedBorrow _ ->
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
  log#ldebug
    (lazy ("\nAbout to check context invariant:\n" ^ context_to_string ()));

  (* Finally, check that everything is consistant *)
  (* First, check all the ignored loans are present at the proper place *)
  List.iter
    (fun (rkind, bid) ->
      let info = find_info bid in
      assert (info.loan_kind = rkind))
    !ignored_loans;

  (* Then, check the borrow infos *)
  V.BorrowId.Map.iter
    (fun _ info ->
      (* Note that we can't directly compare the sets - I guess they are
       * different depending on the order in which we add the elements... *)
      assert (
        V.BorrowId.Set.elements info.loan_ids
        = V.BorrowId.Set.elements info.borrow_ids);
      match info.loan_kind with
      | T.Mut -> assert (V.BorrowId.Set.cardinal info.loan_ids = 1)
      | T.Shared -> ())
    !borrows_infos

(** Check that:
    - borrows/loans can't contain ⊥ or reserved mut borrows
    - shared loans can't contain mutable loans
 *)
let check_borrowed_values_invariant (ctx : C.eval_ctx) : unit =
  let visitor =
    object
      inherit [_] C.iter_eval_ctx as super

      method! visit_Bottom info =
        (* No ⊥ inside borrowed values *)
        assert (Config.allow_bottom_below_borrow || not info.outer_borrow)

      method! visit_ABottom _info =
        (* ⊥ inside an abstraction is not the same as in a regular value *)
        ()

      method! visit_loan_content info lc =
        (* Update the info *)
        let info =
          match lc with
          | V.SharedLoan (_, _) -> set_outer_shared info
          | V.MutLoan _ ->
              (* No mutable loan inside a shared loan *)
              assert (not info.outer_shared);
              set_outer_mut info
        in
        (* Continue exploring *)
        super#visit_loan_content info lc

      method! visit_borrow_content info bc =
        (* Update the info *)
        let info =
          match bc with
          | V.SharedBorrow _ -> set_outer_shared info
          | V.ReservedMutBorrow _ ->
              assert (not info.outer_borrow);
              set_outer_shared info
          | V.MutBorrow (_, _) -> set_outer_mut info
        in
        (* Continue exploring *)
        super#visit_borrow_content info bc

      method! visit_aloan_content info lc =
        (* Update the info *)
        let info =
          match lc with
          | V.AMutLoan (_, _) -> set_outer_mut info
          | V.ASharedLoan (_, _, _) -> set_outer_shared info
          | V.AEndedMutLoan { given_back = _; child = _; given_back_meta = _ }
            ->
              set_outer_mut info
          | V.AEndedSharedLoan (_, _) -> set_outer_shared info
          | V.AIgnoredMutLoan (_, _) -> set_outer_mut info
          | V.AEndedIgnoredMutLoan
              { given_back = _; child = _; given_back_meta = _ } ->
              set_outer_mut info
          | V.AIgnoredSharedLoan _ -> set_outer_shared info
        in
        (* Continue exploring *)
        super#visit_aloan_content info lc

      method! visit_aborrow_content info bc =
        (* Update the info *)
        let info =
          match bc with
          | V.AMutBorrow (_, _) -> set_outer_mut info
          | V.ASharedBorrow _ | V.AEndedSharedBorrow -> set_outer_shared info
          | V.AIgnoredMutBorrow _ | V.AEndedMutBorrow _
          | V.AEndedIgnoredMutBorrow _ ->
              set_outer_mut info
          | V.AProjSharedBorrow _ -> set_outer_shared info
        in
        (* Continue exploring *)
        super#visit_aborrow_content info bc
    end
  in

  (* Explore *)
  let info = { outer_borrow = false; outer_shared = false } in
  visitor#visit_eval_ctx info ctx

let check_primitive_value_type (cv : V.primitive_value) (ty : T.ety) : unit =
  match (cv, ty) with
  | PV.Scalar sv, T.Integer int_ty -> assert (sv.int_ty = int_ty)
  | PV.Bool _, T.Bool | PV.Char _, T.Char | PV.String _, T.Str -> ()
  | _ -> raise (Failure "Erroneous typing")

let check_typing_invariant (ctx : C.eval_ctx) : unit =
  (* TODO: the type of aloans doens't make sense: they have a type
   * of the shape [& (mut) T] where they should have type [T]...
   * This messes a bit the type invariant checks when checking the
   * children. In order to isolate the problem (for future modifications)
   * we introduce function, so that we can easily spot all the involved
   * places.
   * *)
  let aloan_get_expected_child_type (ty : 'r T.ty) : 'r T.ty =
    let _, ty, _ = ty_get_ref ty in
    ty
  in

  let visitor =
    object
      inherit [_] C.iter_eval_ctx as super
      method! visit_abs _ abs = super#visit_abs (Some abs) abs

      method! visit_typed_value info tv =
        (* Check the current pair (value, type) *)
        (match (tv.V.value, tv.V.ty) with
        | V.Primitive cv, ty -> check_primitive_value_type cv ty
        (* ADT case *)
        | V.Adt av, T.Adt (T.AdtId def_id, regions, tys) ->
            (* Retrieve the definition to check the variant id, the number of
             * parameters, etc. *)
            let def = C.ctx_lookup_type_decl ctx def_id in
            (* Check the number of parameters *)
            assert (List.length regions = List.length def.region_params);
            assert (List.length tys = List.length def.type_params);
            (* Check that the variant id is consistent *)
            (match (av.V.variant_id, def.T.kind) with
            | Some variant_id, T.Enum variants ->
                assert (T.VariantId.to_int variant_id < List.length variants)
            | None, T.Struct _ -> ()
            | _ -> raise (Failure "Erroneous typing"));
            (* Check that the field types are correct *)
            let field_types =
              Subst.type_decl_get_instantiated_field_etypes def av.V.variant_id
                tys
            in
            let fields_with_types =
              List.combine av.V.field_values field_types
            in
            List.iter
              (fun ((v, ty) : V.typed_value * T.ety) -> assert (v.V.ty = ty))
              fields_with_types
        (* Tuple case *)
        | V.Adt av, T.Adt (T.Tuple, regions, tys) ->
            assert (regions = []);
            assert (av.V.variant_id = None);
            (* Check that the fields have the proper values - and check that there
             * are as many fields as field types at the same time *)
            let fields_with_types = List.combine av.V.field_values tys in
            List.iter
              (fun ((v, ty) : V.typed_value * T.ety) -> assert (v.V.ty = ty))
              fields_with_types
        (* Assumed type case *)
        | V.Adt av, T.Adt (T.Assumed aty_id, regions, tys) -> (
            assert (av.V.variant_id = None || aty_id = T.Option);
            match (aty_id, av.V.field_values, regions, tys) with
            (* Box *)
            | T.Box, [ inner_value ], [], [ inner_ty ]
            | T.Option, [ inner_value ], [], [ inner_ty ] ->
                assert (inner_value.V.ty = inner_ty)
            | T.Option, _, [], [ _ ] ->
                (* Option::None: nothing to check *)
                ()
            | T.Vec, fvs, [], [ vec_ty ] ->
                List.iter
                  (fun (v : V.typed_value) -> assert (v.ty = vec_ty))
                  fvs
            | _ -> raise (Failure "Erroneous type"))
        | V.Bottom, _ -> (* Nothing to check *) ()
        | V.Borrow bc, T.Ref (_, ref_ty, rkind) -> (
            match (bc, rkind) with
            | V.SharedBorrow bid, T.Shared | V.ReservedMutBorrow bid, T.Mut -> (
                (* Lookup the borrowed value to check it has the proper type *)
                let _, glc = lookup_loan ek_all bid ctx in
                match glc with
                | Concrete (V.SharedLoan (_, sv))
                | Abstract (V.ASharedLoan (_, sv, _)) ->
                    assert (sv.V.ty = ref_ty)
                | _ -> raise (Failure "Inconsistent context"))
            | V.MutBorrow (_, bv), T.Mut ->
                assert (
                  (* Check that the borrowed value has the proper type *)
                  bv.V.ty = ref_ty)
            | _ -> raise (Failure "Erroneous typing"))
        | V.Loan lc, ty -> (
            match lc with
            | V.SharedLoan (_, sv) -> assert (sv.V.ty = ty)
            | V.MutLoan bid -> (
                (* Lookup the borrowed value to check it has the proper type *)
                let glc = lookup_borrow ek_all bid ctx in
                match glc with
                | Concrete (V.MutBorrow (_, bv)) -> assert (bv.V.ty = ty)
                | Abstract (V.AMutBorrow (_, sv)) ->
                    assert (Subst.erase_regions sv.V.ty = ty)
                | _ -> raise (Failure "Inconsistent context")))
        | V.Symbolic sv, ty ->
            let ty' = Subst.erase_regions sv.V.sv_ty in
            assert (ty' = ty)
        | _ -> raise (Failure "Erroneous typing"));
        (* Continue exploring to inspect the subterms *)
        super#visit_typed_value info tv

      (* TODO: there is a lot of duplication with {!visit_typed_value}
       * which is quite annoying. There might be a way of factorizing
       * that by factorizing the definitions of value and avalue, but
       * the generation of visitors then doesn't work properly (TODO:
       * report that). Still, it is actually not that problematic
       * because this code shouldn't change a lot in the future,
       * so the cost of maintenance should be pretty low.
       * *)
      method! visit_typed_avalue info atv =
        (* Check the current pair (value, type) *)
        (match (atv.V.value, atv.V.ty) with
        (* ADT case *)
        | V.AAdt av, T.Adt (T.AdtId def_id, regions, tys) ->
            (* Retrieve the definition to check the variant id, the number of
             * parameters, etc. *)
            let def = C.ctx_lookup_type_decl ctx def_id in
            (* Check the number of parameters *)
            assert (List.length regions = List.length def.region_params);
            assert (List.length tys = List.length def.type_params);
            (* Check that the variant id is consistent *)
            (match (av.V.variant_id, def.T.kind) with
            | Some variant_id, T.Enum variants ->
                assert (T.VariantId.to_int variant_id < List.length variants)
            | None, T.Struct _ -> ()
            | _ -> raise (Failure "Erroneous typing"));
            (* Check that the field types are correct *)
            let field_types =
              Subst.type_decl_get_instantiated_field_rtypes def av.V.variant_id
                regions tys
            in
            let fields_with_types =
              List.combine av.V.field_values field_types
            in
            List.iter
              (fun ((v, ty) : V.typed_avalue * T.rty) -> assert (v.V.ty = ty))
              fields_with_types
        (* Tuple case *)
        | V.AAdt av, T.Adt (T.Tuple, regions, tys) ->
            assert (regions = []);
            assert (av.V.variant_id = None);
            (* Check that the fields have the proper values - and check that there
             * are as many fields as field types at the same time *)
            let fields_with_types = List.combine av.V.field_values tys in
            List.iter
              (fun ((v, ty) : V.typed_avalue * T.rty) -> assert (v.V.ty = ty))
              fields_with_types
        (* Assumed type case *)
        | V.AAdt av, T.Adt (T.Assumed aty_id, regions, tys) -> (
            assert (av.V.variant_id = None);
            match (aty_id, av.V.field_values, regions, tys) with
            (* Box *)
            | T.Box, [ boxed_value ], [], [ boxed_ty ] ->
                assert (boxed_value.V.ty = boxed_ty)
            | _ -> raise (Failure "Erroneous type"))
        | V.ABottom, _ -> (* Nothing to check *) ()
        | V.ABorrow bc, T.Ref (_, ref_ty, rkind) -> (
            match (bc, rkind) with
            | V.AMutBorrow (_, av), T.Mut ->
                (* Check that the child value has the proper type *)
                assert (av.V.ty = ref_ty)
            | V.ASharedBorrow bid, T.Shared -> (
                (* Lookup the borrowed value to check it has the proper type *)
                let _, glc = lookup_loan ek_all bid ctx in
                match glc with
                | Concrete (V.SharedLoan (_, sv))
                | Abstract (V.ASharedLoan (_, sv, _)) ->
                    assert (sv.V.ty = Subst.erase_regions ref_ty)
                | _ -> raise (Failure "Inconsistent context"))
            | V.AIgnoredMutBorrow (_opt_bid, av), T.Mut ->
                assert (av.V.ty = ref_ty)
            | ( V.AEndedIgnoredMutBorrow
                  { given_back_loans_proj; child; given_back_meta = _ },
                T.Mut ) ->
                assert (given_back_loans_proj.V.ty = ref_ty);
                assert (child.V.ty = ref_ty)
            | V.AProjSharedBorrow _, T.Shared -> ()
            | _ -> raise (Failure "Inconsistent context"))
        | V.ALoan lc, aty -> (
            match lc with
            | V.AMutLoan (bid, child_av) | V.AIgnoredMutLoan (Some bid, child_av)
              -> (
                let borrowed_aty = aloan_get_expected_child_type aty in
                assert (child_av.V.ty = borrowed_aty);
                (* Lookup the borrowed value to check it has the proper type *)
                let glc = lookup_borrow ek_all bid ctx in
                match glc with
                | Concrete (V.MutBorrow (_, bv)) ->
                    assert (bv.V.ty = Subst.erase_regions borrowed_aty)
                | Abstract (V.AMutBorrow (_, sv)) ->
                    assert (
                      Subst.erase_regions sv.V.ty
                      = Subst.erase_regions borrowed_aty)
                | _ -> raise (Failure "Inconsistent context"))
            | V.AIgnoredMutLoan (None, child_av) ->
                let borrowed_aty = aloan_get_expected_child_type aty in
                assert (child_av.V.ty = borrowed_aty)
            | V.ASharedLoan (_, sv, child_av) | V.AEndedSharedLoan (sv, child_av)
              ->
                let borrowed_aty = aloan_get_expected_child_type aty in
                assert (sv.V.ty = Subst.erase_regions borrowed_aty);
                (* TODO: the type of aloans doesn't make sense, see above *)
                assert (child_av.V.ty = borrowed_aty)
            | V.AEndedMutLoan { given_back; child; given_back_meta = _ }
            | V.AEndedIgnoredMutLoan { given_back; child; given_back_meta = _ }
              ->
                let borrowed_aty = aloan_get_expected_child_type aty in
                assert (given_back.V.ty = borrowed_aty);
                assert (child.V.ty = borrowed_aty)
            | V.AIgnoredSharedLoan child_av ->
                assert (child_av.V.ty = aloan_get_expected_child_type aty))
        | V.ASymbolic aproj, ty -> (
            let ty1 = Subst.erase_regions ty in
            match aproj with
            | V.AProjLoans (sv, _) ->
                let ty2 = Subst.erase_regions sv.V.sv_ty in
                assert (ty1 = ty2);
                (* Also check that the symbolic values contain regions of interest -
                 * otherwise they should have been reduced to [_] *)
                let abs = Option.get info in
                assert (ty_has_regions_in_set abs.regions sv.V.sv_ty)
            | V.AProjBorrows (sv, proj_ty) ->
                let ty2 = Subst.erase_regions sv.V.sv_ty in
                assert (ty1 = ty2);
                (* Also check that the symbolic values contain regions of interest -
                 * otherwise they should have been reduced to [_] *)
                let abs = Option.get info in
                assert (ty_has_regions_in_set abs.regions proj_ty)
            | V.AEndedProjLoans (_msv, given_back_ls) ->
                List.iter
                  (fun (_, proj) ->
                    match proj with
                    | V.AProjBorrows (_sv, ty') -> assert (ty' = ty)
                    | V.AEndedProjBorrows _ | V.AIgnoredProjBorrows -> ()
                    | _ -> raise (Failure "Unexpected"))
                  given_back_ls
            | V.AEndedProjBorrows _ | V.AIgnoredProjBorrows -> ())
        | V.AIgnored, _ -> ()
        | _ -> raise (Failure "Erroneous typing"));
        (* Continue exploring to inspect the subterms *)
        super#visit_typed_avalue info atv
    end
  in
  visitor#visit_eval_ctx (None : V.abs option) ctx

type proj_borrows_info = {
  abs_id : V.AbstractionId.id;
  regions : T.RegionId.Set.t;
  proj_ty : T.rty;
  as_shared_value : bool;  (** True if the value is below a shared borrow *)
}
[@@deriving show]

type proj_loans_info = {
  abs_id : V.AbstractionId.id;
  regions : T.RegionId.Set.t;
}
[@@deriving show]

type sv_info = {
  ty : T.rty;
  env_count : int;
  aproj_borrows : proj_borrows_info list;
  aproj_loans : proj_loans_info list;
}
[@@deriving show]

(** Check the invariants over the symbolic values.
    
    - a symbolic value can't be both in proj_borrows and in the concrete env
      (this is why we preemptively expand copyable symbolic values)
    - if a symbolic value contains regions: there is at most one occurrence
      of this value in the concrete env
    - if there is an aproj_borrows in the environment, there must also be a
      corresponding aproj_loans
    - aproj_loans are mutually disjoint
    - TODO: aproj_borrows are mutually disjoint
    - the union of the aproj_loans contains the aproj_borrows applied on the
      same symbolic values
 *)
let check_symbolic_values (ctx : C.eval_ctx) : unit =
  (* Small utility *)
  let module M = V.SymbolicValueId.Map in
  let infos : sv_info M.t ref = ref M.empty in
  let lookup_info (sv : V.symbolic_value) : sv_info =
    match M.find_opt sv.V.sv_id !infos with
    | Some info -> info
    | None ->
        { ty = sv.sv_ty; env_count = 0; aproj_borrows = []; aproj_loans = [] }
  in
  let update_info (sv : V.symbolic_value) (info : sv_info) =
    infos := M.add sv.sv_id info !infos
  in
  let add_env_sv (sv : V.symbolic_value) : unit =
    let info = lookup_info sv in
    let info = { info with env_count = info.env_count + 1 } in
    update_info sv info
  in
  let add_aproj_borrows (sv : V.symbolic_value) abs_id regions proj_ty
      as_shared_value : unit =
    let info = lookup_info sv in
    let binfo = { abs_id; regions; proj_ty; as_shared_value } in
    let info = { info with aproj_borrows = binfo :: info.aproj_borrows } in
    update_info sv info
  in
  let add_aproj_loans (sv : V.symbolic_value) abs_id regions : unit =
    let info = lookup_info sv in
    let linfo = { abs_id; regions } in
    let info = { info with aproj_loans = linfo :: info.aproj_loans } in
    update_info sv info
  in
  (* Visitor *)
  let obj =
    object
      inherit [_] C.iter_eval_ctx as super
      method! visit_abs _ abs = super#visit_abs (Some abs) abs
      method! visit_Symbolic _ sv = add_env_sv sv

      method! visit_abstract_shared_borrow abs asb =
        let abs = Option.get abs in
        match asb with
        | V.AsbBorrow _ -> ()
        | AsbProjReborrows (sv, proj_ty) ->
            add_aproj_borrows sv abs.abs_id abs.regions proj_ty true

      method! visit_aproj abs aproj =
        (let abs = Option.get abs in
         match aproj with
         | AProjLoans (sv, _) -> add_aproj_loans sv abs.abs_id abs.regions
         | AProjBorrows (sv, proj_ty) ->
             add_aproj_borrows sv abs.abs_id abs.regions proj_ty false
         | AEndedProjLoans _ | AEndedProjBorrows _ | AIgnoredProjBorrows -> ());
        super#visit_aproj abs aproj
    end
  in
  (* Collect the information *)
  obj#visit_eval_ctx None ctx;
  log#ldebug
    (lazy
      ("check_symbolic_values: collected information:\n"
      ^ V.SymbolicValueId.Map.to_string (Some "  ") show_sv_info !infos));
  (* Check *)
  let check_info _id info =
    (* TODO: check that:
     * - the borrows are mutually disjoint
     *)
    (* A symbolic value can't be both in the regular environment and inside
     * projectors of borrows in abstractions *)
    assert (info.env_count = 0 || info.aproj_borrows = []);
    (* A symbolic value containing borrows can't be duplicated (i.e., copied):
     * it must be expanded first *)
    if ty_has_borrows ctx.type_context.type_infos info.ty then
      assert (info.env_count <= 1);
    (* A duplicated symbolic value is necessarily primitively copyable *)
    assert (info.env_count <= 1 || ty_is_primitively_copyable info.ty);

    assert (info.aproj_borrows = [] || info.aproj_loans <> []);
    (* At the same time:
     * - check that the loans don't intersect
     * - compute the set of regions for which we project loans
     *)
    (* Check that the loan projectors contain the region projectors *)
    let loan_regions =
      List.fold_left
        (fun regions linfo ->
          let regions =
            T.RegionId.Set.fold
              (fun rid regions ->
                assert (not (T.RegionId.Set.mem rid regions));
                T.RegionId.Set.add rid regions)
              regions linfo.regions
          in
          regions)
        T.RegionId.Set.empty info.aproj_loans
    in
    (* Check that the union of the loan projectors contains the borrow projections. *)
    List.iter
      (fun binfo ->
        assert (
          projection_contains info.ty loan_regions binfo.proj_ty binfo.regions))
      info.aproj_borrows;
    ()
  in

  M.iter check_info !infos

let check_invariants (ctx : C.eval_ctx) : unit =
  if !Config.check_invariants then (
    log#ldebug (lazy "Checking invariants");
    check_loans_borrows_relation_invariant ctx;
    check_borrowed_values_invariant ctx;
    check_typing_invariant ctx;
    check_symbolic_values ctx)
  else log#ldebug (lazy "Not checking invariants (check is not activated)")

(** Same as {!check_invariants}, but written in CPS *)
let cf_check_invariants : cm_fun =
 fun cf ctx ->
  check_invariants ctx;
  cf ctx
