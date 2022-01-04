(* The following module defines functions to check that some invariants
 * are always maintained by evaluation contexts *)

module T = Types
module V = Values
module E = Expressions
module C = Contexts
module Subst = Substitute
module A = CfimAst
module L = Logging
open InterpreterUtils
open Errors

let debug_invariants : bool ref = ref false

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

let borrows_infos_to_string (infos : borrow_info V.BorrowId.Map.t) : string =
  let bindings = V.BorrowId.Map.bindings infos in
  let bindings = List.map (fun (_, info) -> show_borrow_info info) bindings in
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

  (* First, register all the loans *)
  (* Some utilities to register the loans *)
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
          | V.AEndedMutLoan { given_back = _; child = _ }
          | V.AEndedSharedLoan (_, _)
          | V.AIgnoredMutLoan (_, _) (* We might want to do something here *)
          | V.AEndedIgnoredMutLoan { given_back = _; child = _ }
          | V.AIgnoredSharedLoan _ ->
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
    let repr_bid = V.BorrowId.Map.find bid !ids_reprs in
    (* Lookup the info *)
    V.BorrowId.Map.find repr_bid !borrows_infos
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
          | V.AIgnoredMutBorrow _ | V.AProjSharedBorrow _ ->
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
  if !debug_invariants then (
    L.log#ldebug
      (lazy
        ("\nAbout to check context invariant:\n" ^ eval_ctx_to_string ctx ^ "\n"));
    L.log#ldebug
      (lazy
        ("\nBorrows information:\n"
        ^ borrows_infos_to_string !borrows_infos
        ^ "\n")));

  (* Finally, check that everything is consistant *)
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
          | V.AIgnoredMutBorrow _ -> set_outer_mut info
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
            let def = T.TypeDefId.nth ctx.type_context def_id in
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
              ->
                (* Lookup the borrowed value to check it has the proper type *)
                raise Unimplemented
            | V.MutBorrow (_, bv), T.Mut -> assert (bv.V.ty = ref_ty)
            | _ -> failwith "Erroneous typing")
        | V.Loan lc, _ -> raise Unimplemented
        | V.Symbolic spc, ty ->
            let ty' = Subst.erase_regions spc.V.svalue.V.sv_ty in
            assert (ty' = ty)
        | _ -> failwith "Erroneous typing");
        (* Continue exploring to inspect the subterms *)
        super#visit_typed_value info tv

      method! visit_typed_avalue info atv = raise Unimplemented
    end
  in
  visitor#visit_eval_ctx () ctx

let check_invariants (ctx : C.eval_ctx) : unit =
  check_loans_borrows_relation_invariant ctx;
  check_borrowed_values_invariant ctx;
  check_typing_invariant ctx
