(* The following module defines functions to check that some invariants
 * are always maintained by evaluation contexts *)

module T = Types
module V = Values
module E = Expressions
module C = Contexts
module Subst = Substitute
module A = CfimAst
module L = Logging
open TypesUtils
open InterpreterUtils
open InterpreterBorrowsCore

(** The local logger *)
let log = L.invariants_log

type borrow_info = {
  loan_kind : T.ref_kind;
  loan_in_abs : bool;
  (* true if the loan was found in an abstraction *)
  loan_ids : V.BorrowId.set_t;
  borrow_ids : V.BorrowId.set_t;
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

(* TODO: we need to factorize print functions for sets *)
let ids_reprs_to_string (indent : string)
    (reprs : V.BorrowId.id V.BorrowId.Map.t) : string =
  let bindings = V.BorrowId.Map.bindings reprs in
  let bindings =
    List.map
      (fun (id, repr_id) ->
        indent ^ V.BorrowId.to_string id ^ " -> " ^ V.BorrowId.to_string repr_id)
      bindings
  in
  String.concat "\n" bindings

let borrows_infos_to_string (indent : string)
    (infos : borrow_info V.BorrowId.Map.t) : string =
  let bindings = V.BorrowId.Map.bindings infos in
  let bindings =
    List.map (fun (_, info) -> indent ^ show_borrow_info info) bindings
  in
  String.concat "\n" bindings

type borrow_kind = Mut | Shared | Inactivated

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

  let register_shared_loan (loan_in_abs : bool) (bids : V.BorrowId.set_t) : unit
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
          | V.AIgnoredMutLoan (bid, _) -> register_ignored_loan T.Mut bid
          | V.AIgnoredSharedLoan _
          | V.AEndedMutLoan { given_back = _; child = _ }
          | V.AEndedSharedLoan (_, _)
          | V.AEndedIgnoredMutLoan { given_back = _; child = _ } ->
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
          ^ V.BorrowId.to_string bid ^ "\n" ^ context_to_string ()
        in
        log#serror err;
        failwith err
  in

  let update_info (bid : V.BorrowId.id) (info : borrow_info) : unit =
    (* Find the representant *)
    let repr_bid = V.BorrowId.Map.find bid !ids_reprs in
    (* Update the info *)
    let infos =
      V.BorrowId.Map.update repr_bid
        (fun x ->
          match x with Some _ -> Some info | None -> failwith "Unreachable")
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
    | T.Shared, (Shared | Inactivated) | T.Mut, Mut -> ()
    | _ -> failwith "Invariant not satisfied");
    (* An inactivated borrow can't point to a value inside an abstraction *)
    assert (kind <> Inactivated || not info.loan_in_abs);
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

      method! visit_abstract_shared_borrows _ asb =
        let visit asb =
          match asb with
          | V.AsbBorrow bid -> register_borrow Shared bid
          | V.AsbProjReborrows _ -> ()
        in
        List.iter visit asb

      method! visit_borrow_content env bc =
        (* Register the loan *)
        let _ =
          match bc with
          | V.SharedBorrow bid -> register_borrow Shared bid
          | V.MutBorrow (bid, _) -> register_borrow Mut bid
          | V.InactivatedMutBorrow bid -> register_borrow Inactivated bid
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
          | V.AEndedIgnoredMutBorrow _ | V.AProjSharedBorrow _ ->
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
    - borrows/loans can't contain ⊥ or inactivated mut borrows
    - shared loans can't contain mutable loans
 *)
let check_borrowed_values_invariant (ctx : C.eval_ctx) : unit =
  let visitor =
    object
      inherit [_] C.iter_eval_ctx as super

      method! visit_Bottom info =
        (* No ⊥ inside borrowed values *)
        assert (not info.outer_borrow)

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
          | V.InactivatedMutBorrow _ ->
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
          | V.AEndedMutLoan { given_back = _; child = _ } -> set_outer_mut info
          | V.AEndedSharedLoan (_, _) -> set_outer_shared info
          | V.AIgnoredMutLoan (_, _) -> set_outer_mut info
          | V.AEndedIgnoredMutLoan { given_back = _; child = _ } ->
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
          | V.ASharedBorrow _ -> set_outer_shared info
          | V.AIgnoredMutBorrow _ | V.AEndedIgnoredMutBorrow _ ->
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

let check_constant_value_type (cv : V.constant_value) (ty : T.ety) : unit =
  match (cv, ty) with
  | V.Scalar sv, T.Integer int_ty -> assert (sv.int_ty = int_ty)
  | V.Bool _, T.Bool | V.Char _, T.Char | V.String _, T.Str -> ()
  | _ -> failwith "Erroneous typing"

let check_typing_invariant (ctx : C.eval_ctx) : unit =
  (* TODO: the type of aloans doens't make sense: they have a type
   * of the shape `& (mut) T` where they should have type `T`...
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

      method! visit_typed_value info tv =
        (* Check the current pair (value, type) *)
        (match (tv.V.value, tv.V.ty) with
        | V.Concrete cv, ty -> check_constant_value_type cv ty
        (* ADT case *)
        | V.Adt av, T.Adt (T.AdtId def_id, regions, tys) ->
            (* Retrieve the definition to check the variant id, the number of
             * parameters, etc. *)
            let def = C.ctx_lookup_type_def ctx def_id in
            (* Check the number of parameters *)
            assert (List.length regions = List.length def.region_params);
            assert (List.length tys = List.length def.type_params);
            (* Check that the variant id is consistent *)
            (match (av.V.variant_id, def.T.kind) with
            | Some variant_id, T.Enum variants ->
                assert (T.VariantId.to_int variant_id < List.length variants)
            | None, T.Struct _ -> ()
            | _ -> failwith "Erroneous typing");
            (* Check that the field types are correct *)
            let field_types =
              Subst.type_def_get_instantiated_field_etypes def av.V.variant_id
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
            assert (av.V.variant_id = None);
            match (aty_id, av.V.field_values, regions, tys) with
            (* Box *)
            | T.Box, [ boxed_value ], [], [ boxed_ty ] ->
                assert (boxed_value.V.ty = boxed_ty)
            | _ -> failwith "Erroneous type")
        | V.Bottom, _ -> (* Nothing to check *) ()
        | V.Borrow bc, T.Ref (_, ref_ty, rkind) -> (
            match (bc, rkind) with
            | V.SharedBorrow bid, T.Shared | V.InactivatedMutBorrow bid, T.Mut
              -> (
                (* Lookup the borrowed value to check it has the proper type *)
                let _, glc = lookup_loan ek_all bid ctx in
                match glc with
                | Concrete (V.SharedLoan (_, sv))
                | Abstract (V.ASharedLoan (_, sv, _)) ->
                    assert (sv.V.ty = ref_ty)
                | _ -> failwith "Inconsistent context")
            | V.MutBorrow (_, bv), T.Mut ->
                assert (
                  (* Check that the borrowed value has the proper type *)
                  bv.V.ty = ref_ty)
            | _ -> failwith "Erroneous typing")
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
                | _ -> failwith "Inconsistent context"))
        | V.Symbolic sv, ty ->
            let ty' = Subst.erase_regions sv.V.sv_ty in
            assert (ty' = ty)
        | _ -> failwith "Erroneous typing");
        (* Continue exploring to inspect the subterms *)
        super#visit_typed_value info tv

      (* TODO: there is a lot of duplication with [visit_typed_value]
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
        | V.AConcrete cv, ty ->
            check_constant_value_type cv (Subst.erase_regions ty)
        (* ADT case *)
        | V.AAdt av, T.Adt (T.AdtId def_id, regions, tys) ->
            (* Retrieve the definition to check the variant id, the number of
             * parameters, etc. *)
            let def = C.ctx_lookup_type_def ctx def_id in
            (* Check the number of parameters *)
            assert (List.length regions = List.length def.region_params);
            assert (List.length tys = List.length def.type_params);
            (* Check that the variant id is consistent *)
            (match (av.V.variant_id, def.T.kind) with
            | Some variant_id, T.Enum variants ->
                assert (T.VariantId.to_int variant_id < List.length variants)
            | None, T.Struct _ -> ()
            | _ -> failwith "Erroneous typing");
            (* Check that the field types are correct *)
            let field_types =
              Subst.type_def_get_instantiated_field_rtypes def av.V.variant_id
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
            | _ -> failwith "Erroneous type")
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
                | _ -> failwith "Inconsistent context")
            | V.AIgnoredMutBorrow (_opt_bid, av), T.Mut ->
                assert (av.V.ty = ref_ty)
            | V.AEndedIgnoredMutBorrow { given_back_loans_proj; child }, T.Mut
              ->
                assert (given_back_loans_proj.V.ty = ref_ty);
                assert (child.V.ty = ref_ty)
            | V.AProjSharedBorrow _, T.Shared -> ()
            | _ -> failwith "Inconsistent context")
        | V.ALoan lc, aty -> (
            match lc with
            | V.AMutLoan (bid, child_av) | V.AIgnoredMutLoan (bid, child_av)
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
                | _ -> failwith "Inconsistent context")
            | V.ASharedLoan (_, sv, child_av) | V.AEndedSharedLoan (sv, child_av)
              ->
                let borrowed_aty = aloan_get_expected_child_type aty in
                assert (sv.V.ty = Subst.erase_regions borrowed_aty);
                (* TODO: the type of aloans doesn't make sense, see above *)
                assert (child_av.V.ty = borrowed_aty)
            | V.AEndedMutLoan { given_back; child }
            | V.AEndedIgnoredMutLoan { given_back; child } ->
                let borrowed_aty = aloan_get_expected_child_type aty in
                assert (given_back.V.ty = borrowed_aty);
                assert (child.V.ty = borrowed_aty)
            | V.AIgnoredSharedLoan child_av ->
                assert (child_av.V.ty = aloan_get_expected_child_type aty))
        | V.ASymbolic aproj, ty -> (
            let ty1 = Subst.erase_regions ty in
            match aproj with
            | V.AProjLoans sv | V.AProjBorrows (sv, _) ->
                let ty2 = Subst.erase_regions sv.V.sv_ty in
                assert (ty1 = ty2)
            | V.AEndedProjLoans | V.AEndedProjBorrows -> ())
        | V.AIgnored, _ -> ()
        | _ -> failwith "Erroneous typing");
        (* Continue exploring to inspect the subterms *)
        super#visit_typed_avalue info atv
    end
  in
  visitor#visit_eval_ctx () ctx

let check_invariants (ctx : C.eval_ctx) : unit =
  check_loans_borrows_relation_invariant ctx;
  check_borrowed_values_invariant ctx;
  check_typing_invariant ctx
