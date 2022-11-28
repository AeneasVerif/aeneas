module T = Types
module PV = PrimitiveValues
module V = Values
module E = Expressions
module C = Contexts
module Subst = Substitute
module A = LlbcAst
module L = Logging
open TypesUtils
open ValuesUtils
module Inv = Invariants
module S = SynthesizeSymbolic
module UF = UnionFind
open Utils
open Cps
open InterpreterUtils
open InterpreterBorrows
open InterpreterProjectors
open InterpreterExpansion
open InterpreterPaths
open InterpreterExpressions

(** The local logger *)
let log = L.loops_log

type cnt_thresholds = {
  aid : V.AbstractionId.id;
  sid : V.SymbolicValueId.id;
  bid : V.BorrowId.id;
  did : C.DummyVarId.id;
  rid : T.RegionId.id;
}

(* TODO: document.
   TODO: we might not use the bounds properly, use sets instead.
   TODO: actually, bounds are good
*)
type match_ctx = {
  ctx : C.eval_ctx;
  aids : V.AbstractionId.Set.t;
  sids : V.SymbolicValueId.Set.t;
  bids : V.BorrowId.Set.t;
}

let mk_match_ctx (ctx : C.eval_ctx) : match_ctx =
  let aids = V.AbstractionId.Set.empty in
  let sids = V.SymbolicValueId.Set.empty in
  let bids = V.BorrowId.Set.empty in
  { ctx; aids; sids; bids }

type updt_env_kind =
  | EndAbsInSrc of V.AbstractionId.id
  | EndBorrowsInSrc of V.BorrowId.Set.t
  | EndBorrowInSrc of V.BorrowId.id
  | EndBorrowInTgt of V.BorrowId.id
  | EndBorrowsInTgt of V.BorrowId.Set.t

(** Utility exception *)
exception ValueMatchFailure of updt_env_kind

type joined_ctx_or_update = (match_ctx, updt_env_kind) result

(** Union Find *)
module UnionFind = UF.Make (UF.StoreMap)

(** A small utility *)
type abs_borrows_loans_maps = {
  abs_ids : V.AbstractionId.id list;
  abs_to_borrows : V.BorrowId.Set.t V.AbstractionId.Map.t;
  abs_to_loans : V.BorrowId.Set.t V.AbstractionId.Map.t;
  borrow_to_abs : V.AbstractionId.id V.BorrowId.Map.t;
  loan_to_abs : V.AbstractionId.id V.BorrowId.Map.t;
}

(** Compute various maps linking the abstractions and the borrows/loans they contain.

    The [explore] function is used to filter abstractions.
 *)
let compute_abs_borrows_loans_maps (explore : V.abs -> bool) (env : C.env) :
    abs_borrows_loans_maps =
  let abs_ids = ref [] in
  let abs_to_borrows = ref V.AbstractionId.Map.empty in
  let abs_to_loans = ref V.AbstractionId.Map.empty in
  let borrow_to_abs = ref V.BorrowId.Map.empty in
  let loan_to_abs = ref V.BorrowId.Map.empty in

  let register_borrow_id abs_id bid =
    abs_to_borrows :=
      V.AbstractionId.Map.update abs_id
        (fun bids -> Some (V.BorrowId.Set.add bid (Option.get bids)))
        !abs_to_borrows;
    assert (not (V.BorrowId.Map.mem bid !borrow_to_abs));
    borrow_to_abs := V.BorrowId.Map.add bid abs_id !borrow_to_abs
  in

  let register_loan_id abs_id bid =
    abs_to_loans :=
      V.AbstractionId.Map.update abs_id
        (fun bids -> Some (V.BorrowId.Set.add bid (Option.get bids)))
        !abs_to_loans;
    assert (not (V.BorrowId.Map.mem bid !loan_to_abs));
    loan_to_abs := V.BorrowId.Map.add bid abs_id !loan_to_abs
  in

  let explore_abs =
    object (self : 'self)
      inherit [_] V.iter_typed_avalue as super

      (** Make sure we don't register the ignored ids *)
      method! visit_aloan_content abs_id lc =
        match lc with
        | AMutLoan _ | ASharedLoan _ ->
            (* Process those normally *)
            super#visit_aloan_content abs_id lc
        | AIgnoredMutLoan (_, child)
        | AEndedIgnoredMutLoan { child; given_back = _; given_back_meta = _ }
        | AIgnoredSharedLoan child ->
            (* Ignore the id of the loan, if there is *)
            self#visit_typed_avalue abs_id child
        | AEndedMutLoan _ | AEndedSharedLoan _ -> raise (Failure "Unreachable")

      (** Make sure we don't register the ignored ids *)
      method! visit_aborrow_content abs_id bc =
        match bc with
        | AMutBorrow _ | ASharedBorrow _ | AProjSharedBorrow _ ->
            (* Process those normally *)
            super#visit_aborrow_content abs_id bc
        | AIgnoredMutBorrow (_, child)
        | AEndedIgnoredMutBorrow
            { child; given_back_loans_proj = _; given_back_meta = _ } ->
            (* Ignore the id of the borrow, if there is *)
            self#visit_typed_avalue abs_id child
        | AEndedMutBorrow _ | AEndedSharedBorrow ->
            raise (Failure "Unreachable")

      method! visit_borrow_id abs_id bid = register_borrow_id abs_id bid
      method! visit_loan_id abs_id lid = register_loan_id abs_id lid
    end
  in

  List.iter
    (fun (ee : C.env_elem) ->
      match ee with
      | Var _ | Frame -> ()
      | Abs abs ->
          let abs_id = abs.abs_id in
          if explore abs then (
            abs_to_borrows :=
              V.AbstractionId.Map.add abs_id V.BorrowId.Set.empty
                !abs_to_borrows;
            abs_to_loans :=
              V.AbstractionId.Map.add abs_id V.BorrowId.Set.empty !abs_to_loans;
            abs_ids := abs.abs_id :: !abs_ids;
            List.iter (explore_abs#visit_typed_avalue abs.abs_id) abs.avalues)
          else ())
    env;

  {
    abs_ids = List.rev !abs_ids;
    abs_to_borrows = !abs_to_borrows;
    abs_to_loans = !abs_to_loans;
    borrow_to_abs = !borrow_to_abs;
    loan_to_abs = !loan_to_abs;
  }

(** Collapse an environment.

    We do this to simplify an environment, for the purpose of finding a loop
    fixed point.

    We do the following:
    - we look for all the *new* dummy values (we use id thresholds to decide
      wether a value is new or not - the ids generated by our counters are
      monotonic), and we convert to abstractions (if they contain loans or
      borrows)
    - whenever there is a new abstraction in the context, and some of its
      its borrows are associated to loans in another new abstraction, we
      merge them.
    In effect, this allows us to merge newly introduced abstractions/borrows
    with their parent abstractions.
 *)
let collapse_ctx (loop_id : V.LoopId.id) (thresh : cnt_thresholds)
    (ctx0 : C.eval_ctx) : C.eval_ctx =
  let abs_kind = V.Loop loop_id in
  let can_end = true in
  let is_fresh_abs_id (id : V.AbstractionId.id) : bool =
    V.AbstractionId.Ord.compare thresh.aid id >= 0
  in
  let is_fresh_did (id : C.DummyVarId.id) : bool =
    C.DummyVarId.Ord.compare thresh.did id >= 0
  in
  (* Convert the dummy values to abstractions *)
  (* Note that we preserve the order of the dummy values: we replace them with
     abstractions in place - this makes matching easier *)
  let env =
    List.concat
      (List.map
         (fun ee ->
           match ee with
           | C.Abs _ | C.Frame | C.Var (VarBinder _, _) -> [ ee ]
           | C.Var (DummyBinder id, v) ->
               if is_fresh_did id then
                 let absl =
                   convert_value_to_abstractions abs_kind can_end ctx0 v
                 in
                 List.map (fun abs -> C.Abs abs) absl
               else [ ee ])
         ctx0.env)
  in

  (* Explore all the *new* abstractions, and compute various maps *)
  let explore (abs : V.abs) = is_fresh_abs_id abs.abs_id in
  let ids_maps = compute_abs_borrows_loans_maps explore env in
  let {
    abs_ids;
    abs_to_borrows;
    abs_to_loans = _;
    borrow_to_abs = _;
    loan_to_abs;
  } =
    ids_maps
  in

  (* Use the maps to merge the abstractions together *)
  let merged_abs : V.AbstractionId.id UF.elem V.AbstractionId.Map.t =
    V.AbstractionId.Map.of_list (List.map (fun id -> (id, UF.make id)) abs_ids)
  in

  let ctx = ref { ctx0 with C.env } in

  (* Merge all the mergeable abs.

     We iterate over the abstractions, then over the borrows in the abstractions.
     We do this because we want to control the order in which abstractions
     are merged (the ids are iterated in increasing order). Otherwise, we
     could simply iterate over all the borrows in [borrow_to_abs]...
  *)
  List.iter
    (fun abs_id0 ->
      let bids = V.AbstractionId.Map.find abs_id0 abs_to_borrows in
      let bids = V.BorrowId.Set.elements bids in
      List.iter
        (fun bid ->
          match V.BorrowId.Map.find_opt bid loan_to_abs with
          | None -> (* Nothing to do *) ()
          | Some abs_id1 ->
              (* We need to merge - unless we have already merged *)
              (* First, find the representatives for the two abstractions (the
                 representative is the abstraction into which we merged) *)
              let abs_ref0 =
                UF.find (V.AbstractionId.Map.find abs_id0 merged_abs)
              in
              let abs_id0 = UF.get abs_ref0 in
              let abs_ref1 =
                UF.find (V.AbstractionId.Map.find abs_id1 merged_abs)
              in
              let abs_id1 = UF.get abs_ref1 in
              (* If the two ids are the same, it means the abstractions were already merged *)
              if abs_id0 = abs_id1 then ()
              else
                (* We actually need to merge the abstractions *)
                (* Lookup the abstractions *)
                let abs0 = C.ctx_lookup_abs !ctx abs_id0 in
                let abs1 = C.ctx_lookup_abs !ctx abs_id1 in
                (* Merge them - note that we take care to merge [abs0] into [abs1]
                   (the order is important).
                *)
                let nabs = merge_abstractions abs_kind can_end !ctx abs1 abs0 in
                (* Update the environment *)
                ctx := fst (C.ctx_subst_abs !ctx abs_id1 nabs);
                ctx := fst (C.ctx_remove_abs !ctx abs_id0);
                (* Update the union find *)
                let abs_ref_merged = UF.union abs_ref0 abs_ref1 in
                UF.set abs_ref_merged nabs.abs_id)
        bids)
    abs_ids;

  (* Return the new context *)
  !ctx

let rec match_types (check_regions : 'r -> 'r -> unit) (ctx : C.eval_ctx)
    (ty0 : 'r T.ty) (ty1 : 'r T.ty) : unit =
  let match_rec = match_types check_regions ctx in
  match (ty0, ty1) with
  | Adt (id0, regions0, tys0), Adt (id1, regions1, tys1) ->
      assert (id0 = id1);
      List.iter
        (fun (id0, id1) -> check_regions id0 id1)
        (List.combine regions0 regions1);
      List.iter (fun (ty0, ty1) -> match_rec ty0 ty1) (List.combine tys0 tys1)
  | TypeVar vid0, TypeVar vid1 -> assert (vid0 = vid1)
  | Bool, Bool | Char, Char | Never, Never | Str, Str -> ()
  | Integer int_ty0, Integer int_ty1 -> assert (int_ty0 = int_ty1)
  | Array ty0, Array ty1 | Slice ty0, Slice ty1 -> match_rec ty0 ty1
  | Ref (r0, ty0, k0), Ref (r1, ty1, k1) ->
      check_regions r0 r1;
      match_rec ty0 ty1;
      assert (k0 = k1)
  | _ -> raise (Failure "Unreachable")

let match_rtypes (rid_map : T.RegionId.InjSubst.t ref) (ctx : C.eval_ctx)
    (ty0 : T.rty) (ty1 : T.rty) : unit =
  let lookup_rid (id : T.RegionId.id) : T.RegionId.id =
    T.RegionId.InjSubst.find_with_default id id !rid_map
  in
  let check_regions r0 r1 =
    match (r0, r1) with
    | T.Static, T.Static -> ()
    | T.Var id0, T.Var id1 ->
        let id0 = lookup_rid id0 in
        assert (id0 = id1)
    | _ -> raise (Failure "Unexpected")
  in
  match_types check_regions ctx ty0 ty1

(** This function raises exceptions of kind {!ValueMatchFailue}.

    [convertible]: the function updates it to [false] if the result of the
    merge is not the result of an alpha-conversion. For instance, if we
    match two primitive values which are not equal, and thus introduce a
    symbolic value for the result:
    {[
      0 : u32, 1 : u32 ~~> s : u32     where s fresh
    ]}
 *)
let rec match_typed_values (config : C.config) (thresh : cnt_thresholds)
    (convertible : bool ref) (rid_map : T.RegionId.InjSubst.t ref)
    (bid_map : V.BorrowId.InjSubst.t ref)
    (sid_map : V.SymbolicValueId.InjSubst.t ref) (ctx : C.eval_ctx)
    (v0 : V.typed_value) (v1 : V.typed_value) : V.typed_value =
  let match_rec =
    match_typed_values config thresh convertible rid_map bid_map sid_map ctx
  in
  let lookup_bid (id : V.BorrowId.id) : V.BorrowId.id =
    V.BorrowId.InjSubst.find_with_default id id !bid_map
  in
  let lookup_bids (ids : V.BorrowId.Set.t) : V.BorrowId.Set.t =
    V.BorrowId.Set.map lookup_bid ids
  in
  let map_bid (id0 : V.BorrowId.id) (id1 : V.BorrowId.id) : V.BorrowId.id =
    assert (V.BorrowId.Ord.compare id0 thresh.bid >= 0);
    assert (V.BorrowId.Ord.compare id1 thresh.bid >= 0);
    assert (not (V.BorrowId.InjSubst.mem id0 !bid_map));
    bid_map := V.BorrowId.InjSubst.add id0 id1 !bid_map;
    id1
  in
  let lookup_sid (id : V.SymbolicValueId.id) : V.SymbolicValueId.id =
    match V.SymbolicValueId.InjSubst.find_opt id !sid_map with
    | None -> id
    | Some id -> id
  in
  assert (v0.V.ty = v1.V.ty);
  match (v0.V.value, v1.V.value) with
  | V.Primitive pv0, V.Primitive pv1 ->
      if pv0 = pv1 then v1 else raise (Failure "Unimplemented")
  | V.Adt av0, V.Adt av1 ->
      if av0.variant_id = av1.variant_id then
        let fields = List.combine av0.field_values av1.field_values in
        let field_values = List.map (fun (f0, f1) -> match_rec f0 f1) fields in
        let value : V.value =
          V.Adt { variant_id = av0.variant_id; field_values }
        in
        { V.value; ty = v1.V.ty }
      else (
        convertible := false;
        (* For now, we don't merge values which contain borrows *)
        (* TODO: *)
        raise (Failure "Unimplemented"))
  | Bottom, Bottom -> v1
  | Borrow bc0, Borrow bc1 ->
      let bc =
        match (bc0, bc1) with
        | SharedBorrow (mv0, bid0), SharedBorrow (mv1, bid1) ->
            let bid0 = lookup_bid bid0 in
            (* Not completely sure what to do with the meta-value. If a shared
               symbolic value gets expanded in a branch, it may be simplified
               (by being folded back to a symbolic value) upon doing the join,
               which as a result would lead to code where it is considered as
               mutable (which is sound). On the other hand, if we access a
               symbolic value in a loop, the translated loop should take it as
               input anyway, so maybe this actually leads to equivalent
               code.
            *)
            let mv = match_rec mv0 mv1 in
            let bid = if bid0 = bid1 then bid1 else map_bid bid0 bid1 in
            V.SharedBorrow (mv, bid)
        | MutBorrow (bid0, bv0), MutBorrow (bid1, bv1) ->
            let bid0 = lookup_bid bid0 in
            let bv = match_rec bv0 bv1 in
            let bid = if bid0 = bid1 then bid1 else map_bid bid0 bid1 in
            V.MutBorrow (bid, bv)
        | ReservedMutBorrow _, _
        | _, ReservedMutBorrow _
        | SharedBorrow _, MutBorrow _
        | MutBorrow _, SharedBorrow _ ->
            (* If we get here, either there is a typing inconsistency, or we are
               trying to match a reserved borrow, which shouldn't happen because
               reserved borrow should be eliminated very quickly - they are introduced
               just before function calls which activate them *)
            raise (Failure "Unexpected")
      in
      { V.value = V.Borrow bc; V.ty = v1.V.ty }
  | Loan lc0, Loan lc1 ->
      (* TODO: maybe we should enforce that the ids are always exactly the same -
         without matching *)
      let lc =
        match (lc0, lc1) with
        | SharedLoan (ids0, sv0), SharedLoan (ids1, sv1) ->
            let ids0 = lookup_bids ids0 in
            (* Not sure what to do if the ids don't match *)
            let ids =
              if ids0 = ids1 then ids1 else raise (Failure "Unimplemented")
            in
            let sv = match_rec sv0 sv1 in
            V.SharedLoan (ids, sv)
        | MutLoan id0, MutLoan id1 ->
            let id0 = lookup_bid id0 in
            let id = if id0 = id1 then id1 else map_bid id0 id1 in
            V.MutLoan id
        | SharedLoan _, MutLoan _ | MutLoan _, SharedLoan _ ->
            raise (Failure "Unreachable")
      in
      { V.value = Loan lc; ty = v1.V.ty }
  | Symbolic sv0, Symbolic sv1 ->
      (* TODO: id check mapping *)
      let id0 = lookup_sid sv0.sv_id in
      let id1 = sv1.sv_id in
      if id0 = id1 then (
        assert (sv0.sv_kind = sv1.sv_kind);
        (* Sanity check: the types should be the same *)
        match_rtypes rid_map ctx sv0.sv_ty sv1.sv_ty;
        (* Return *)
        v1)
      else (
        (* For now, we force all the symbolic values containing borrows to
           be eagerly expanded, and we don't support nested borrows *)
        assert (not (value_has_borrows ctx v0.V.value));
        assert (not (value_has_borrows ctx v1.V.value));
        raise (Failure "Unimplemented"))
  | Loan lc, _ -> (
      match lc with
      | SharedLoan (ids, _) -> raise (ValueMatchFailure (EndBorrowsInSrc ids))
      | MutLoan id -> raise (ValueMatchFailure (EndBorrowInSrc id)))
  | _, Loan lc -> (
      match lc with
      | SharedLoan (ids, _) -> raise (ValueMatchFailure (EndBorrowsInTgt ids))
      | MutLoan id -> raise (ValueMatchFailure (EndBorrowInTgt id)))
  | Symbolic _, _ -> raise (Failure "Unimplemented")
  | _, Symbolic _ -> raise (Failure "Unimplemented")
  | _ -> raise (Failure "Unreachable")

(*(** This function raises exceptions of kind {!ValueMatchFailue} *)
  let rec match_typed_avalues (config : C.config) (thresh : cnt_thresholds)
      (rid_map : T.RegionId.InjSubst.t ref) (bid_map : V.BorrowId.InjSubst.t ref)
      (sid_map : V.SymbolicValueId.InjSubst.t ref)
      (aid_map : V.AbstractionId.InjSubst.t ref) (ctx : C.eval_ctx)
      (v0 : V.typed_avalue) (v1 : V.typed_avalue) : V.typed_avalue =
    let match_rec =
      match_typed_avalues config thresh rid_map bid_map sid_map ctx
    in
    (* TODO: factorize those helpers with [match_typed_values] (write a functor?) *)
    let lookup_bid (id : V.BorrowId.id) : V.BorrowId.id =
      V.BorrowId.InjSubst.find_with_default id id !bid_map
    in
    let lookup_bids (ids : V.BorrowId.Set.t) : V.BorrowId.Set.t =
      V.BorrowId.Set.map lookup_bid ids
    in
    let map_bid (id0 : V.BorrowId.id) (id1 : V.BorrowId.id) : V.BorrowId.id =
      assert (V.BorrowId.Ord.compare id0 thresh.bid >= 0);
      assert (V.BorrowId.Ord.compare id1 thresh.bid >= 0);
      assert (not (V.BorrowId.InjSubst.mem id0 !bid_map));
      bid_map := V.BorrowId.InjSubst.add id0 id1 !bid_map;
      id1
    in
    let lookup_sid (id : V.SymbolicValueId.id) : V.SymbolicValueId.id =
      match V.SymbolicValueId.InjSubst.find_opt id !sid_map with
      | None -> id
      | Some id -> id
    in
    assert (v0.V.ty = v1.V.ty);
    match (v0.V.value, v1.V.value) with
    | V.APrimitive pv0, V.APrimitive pv1 ->
        if pv0 = pv1 then v1 else raise (Failure "Unimplemented")
    | V.AAdt av0, V.AAdt av1 ->
        if av0.variant_id = av1.variant_id then
          let fields = List.combine av0.field_values av1.field_values in
          let field_values = List.map (fun (f0, f1) -> match_rec f0 f1) fields in
          let value : V.value =
            V.Adt { variant_id = av0.variant_id; field_values }
          in
          { V.value; ty = v1.V.ty }
        else raise (Failure "Unimplemented")
    | Bottom, Bottom -> v1
    | Borrow bc0, Borrow bc1 ->
        let bc =
          match (bc0, bc1) with
          | SharedBorrow (mv0, bid0), SharedBorrow (mv1, bid1) ->
              let bid0 = lookup_bid bid0 in
              (* Not completely sure what to do with the meta-value. If a shared
                 symbolic value gets expanded in a branch, it may be simplified
                 (by being folded back to a symbolic value) upon doing the join,
                 which as a result would lead to code where it is considered as
                 mutable (which is sound). On the other hand, if we access a
                 symbolic value in a loop, the translated loop should take it as
                 input anyway, so maybe this actually leads to equivalent
                 code.
              *)
              let mv = match_rec mv0 mv1 in
              let bid = if bid0 = bid1 then bid1 else map_bid bid0 bid1 in
              V.SharedBorrow (mv, bid)
          | MutBorrow (bid0, bv0), MutBorrow (bid1, bv1) ->
              let bid0 = lookup_bid bid0 in
              let bv = match_rec bv0 bv1 in
              let bid = if bid0 = bid1 then bid1 else map_bid bid0 bid1 in
              V.MutBorrow (bid, bv)
          | ReservedMutBorrow _, _
          | _, ReservedMutBorrow _
          | SharedBorrow _, MutBorrow _
          | MutBorrow _, SharedBorrow _ ->
              (* If we get here, either there is a typing inconsistency, or we are
                 trying to match a reserved borrow, which shouldn't happen because
                 reserved borrow should be eliminated very quickly - they are introduced
                 just before function calls which activate them *)
              raise (Failure "Unexpected")
        in
        { V.value = V.Borrow bc; V.ty = v1.V.ty }
    | Loan lc0, Loan lc1 ->
        (* TODO: maybe we should enforce that the ids are always exactly the same -
           without matching *)
        let lc =
          match (lc0, lc1) with
          | SharedLoan (ids0, sv0), SharedLoan (ids1, sv1) ->
              let ids0 = lookup_bids ids0 in
              (* Not sure what to do if the ids don't match *)
              let ids =
                if ids0 = ids1 then ids1 else raise (Failure "Unimplemented")
              in
              let sv = match_rec sv0 sv1 in
              V.SharedLoan (ids, sv)
          | MutLoan id0, MutLoan id1 ->
              let id0 = lookup_bid id0 in
              let id = if id0 = id1 then id1 else map_bid id0 id1 in
              V.MutLoan id
          | SharedLoan _, MutLoan _ | MutLoan _, SharedLoan _ ->
              raise (Failure "Unreachable")
        in
        { V.value = Loan lc; ty = v1.V.ty }
    | Symbolic sv0, Symbolic sv1 ->
        (* TODO: id check mapping *)
        let id0 = lookup_sid sv0.sv_id in
        let id1 = sv1.sv_id in
        if id0 = id1 then (
          assert (sv0.sv_kind = sv1.sv_kind);
          (* Sanity check: the types should be the same *)
          match_rtypes rid_map ctx sv0.sv_ty sv1.sv_ty;
          (* Return *)
          v1)
        else (
          (* For now, we force all the symbolic values containing borrows to
             be eagerly expanded, and we don't support nested borrows *)
          assert (not (value_has_borrows ctx v0.V.value));
          assert (not (value_has_borrows ctx v1.V.value));
          raise (Failure "Unimplemented"))
    | Loan lc, _ -> (
        match lc with
        | SharedLoan (ids, _) -> raise (ValueMatchFailure (EndBorrowsInSrc ids))
        | MutLoan id -> raise (ValueMatchFailure (EndBorrowInSrc id)))
    | _, Loan lc -> (
        match lc with
        | SharedLoan (ids, _) -> raise (ValueMatchFailure (EndBorrowsInTgt ids))
        | MutLoan id -> raise (ValueMatchFailure (EndBorrowInTgt id)))
  | _ -> raise (Failure "Unreachable")*)

(** Apply substitutions in the first abstraction, then merge the abstractions together. *)
let subst_merge_abstractions (loop_id : V.LoopId.id) (thresh : cnt_thresholds)
    (rid_map : T.RegionId.InjSubst.t) (bid_map : V.BorrowId.InjSubst.t)
    (sid_map : V.SymbolicValueId.InjSubst.t) (ctx : C.eval_ctx) (abs0 : V.abs)
    (abs1 : V.abs) : V.abs =
  (* Apply the substitutions in the first abstraction *)
  let rsubst id =
    assert (T.RegionId.Ord.compare id thresh.rid >= 0);
    T.RegionId.InjSubst.find_with_default id id rid_map
  in
  let rvsubst id = id in
  let tsubst id = id in
  let ssubst id =
    assert (V.SymbolicValueId.Ord.compare id thresh.sid >= 0);
    V.SymbolicValueId.InjSubst.find_with_default id id sid_map
  in
  let bsubst id =
    assert (V.BorrowId.Ord.compare id thresh.bid >= 0);
    V.BorrowId.InjSubst.find_with_default id id bid_map
  in
  let asubst id = id in
  let abs0 =
    Substitute.abs_subst_ids rsubst rvsubst tsubst ssubst bsubst asubst abs0
  in

  (* Merge the two abstractions *)
  let abs_kind = V.Loop loop_id in
  let can_end = false in
  merge_abstractions abs_kind can_end ctx abs0 abs1

(** Merge a borrow with the abstraction containing the associated loan, where
    the abstraction must be a *loop abstraction* (we don't synthesize code during
    the operation).

    For instance:
    {[
      abs'0 { mut_loan l0 }
      x -> mut_borrow l0 sx

            ~~>

      abs'0 {}
      x -> ⊥
    ]}
 *)
let merge_borrow_with_parent_loop_abs (config : C.config) (bid : V.BorrowId.id)
    (ctx : C.eval_ctx) : C.eval_ctx =
  (* TODO: use the function from InterpreterBorrows *)
  failwith "Unimplemented"
(* (* Lookup the borrow *)
     let ek =
       { enter_shared_loans = false; enter_mut_borrows = false; enter_abs = false }
     in
     (* TODO: use [end_borrow_get_borrow]? *)
     match lookup_borrow ek bid ctx with
     | None -> ctx
   | Some b -> failwith "Unimplemented"*)

(** See {!merge_borrow_with_parent_loop_abs} *)
let rec merge_borrows_with_parent_loop_abs (config : C.config)
    (bids : V.BorrowId.Set.t) (ctx : C.eval_ctx) : C.eval_ctx =
  V.BorrowId.Set.fold
    (fun id ctx -> merge_borrow_with_parent_loop_abs config id ctx)
    bids ctx

(* TODO: we probably don't need an [match_ctx], and actually we might not use
   the bounds propertly.
   TODO: remove
*)
let match_ctx_with_target_old (config : C.config) (tgt_mctx : match_ctx) :
    cm_fun =
 fun cf src_ctx ->
  (* We first reorganize [ctx] so that we can match it with [tgt_mctx] *)
  (* First, collect all the borrows and abstractions which are in [ctx]
     and not in [tgt_mctx]: we need to end them *)
  let src_bids, src_aids =
    InterpreterBorrowsCore.compute_borrow_abs_ids_in_context src_ctx
  in
  let tgt_bids, tgt_aids =
    InterpreterBorrowsCore.compute_borrow_abs_ids_in_context tgt_mctx.ctx
  in
  let bids = V.BorrowId.Set.diff src_bids tgt_bids in
  let aids = V.AbstractionId.Set.diff src_aids tgt_aids in
  (* End those borrows and abstractions *)
  let cc = InterpreterBorrows.end_borrows config bids in
  let cc = comp cc (InterpreterBorrows.end_abstractions config aids) in
  (* In the target context, merge all the borrows introduced by the loop with
     their parent abstractions
  *)
  let tgt_ctx =
    merge_borrows_with_parent_loop_abs config
      (V.BorrowId.Set.diff tgt_bids src_bids)
      tgt_mctx.ctx
  in
  (* Replace the source context with the target context - TODO: explain
     why this works *)
  let cf_apply_match : cm_fun = fun cf _ -> cf tgt_ctx in
  let cc = comp cc cf_apply_match in
  (* Sanity check on the resulting context *)
  let cc = comp_check_ctx cc Inv.check_invariants in
  (* Apply and continue *)
  cc cf src_ctx

(** Join a context at the entry of a loop with a context upon reaching
    a continue in this loop.
 *)
let loop_join_entry_ctx_with_continue_ctx (ctx0 : match_ctx) (ctx1 : C.eval_ctx)
    : joined_ctx_or_update =
  failwith "Unimplemented"

(** See {!loop_join_entry_ctx_with_continue_ctx} *)
let rec loop_join_entry_ctx_with_continue_ctxs (ctx0 : match_ctx)
    (ctxs : C.eval_ctx list) : joined_ctx_or_update =
  match ctxs with
  | [] -> Ok ctx0
  | ctx1 :: ctxs -> (
      let res = loop_join_entry_ctx_with_continue_ctx ctx0 ctx1 in
      match res with
      | Error _ -> res
      | Ok ctx0 -> loop_join_entry_ctx_with_continue_ctxs ctx0 ctxs)

let compute_loop_entry_fixed_point (config : C.config)
    (eval_loop_body : st_cm_fun) (ctx0 : C.eval_ctx) : match_ctx =
  (* The continuation for when we exit the loop - we use it to register the
     environments upon loop *reentry*
  *)
  let ctxs = ref [] in
  let register_ctx ctx = ctxs := ctx :: !ctxs in
  let cf_exit_loop_body (res : statement_eval_res) : m_fun =
   fun ctx ->
    match res with
    | Return | Panic | Break _ -> None
    | Unit ->
        (* See the comment in {!eval_loop} *)
        raise (Failure "Unreachable")
    | Continue i ->
        (* For now we don't support continues to outer loops *)
        assert (i = 0);
        register_ctx ctx;
        None
    | EndEnterLoop | EndContinue ->
        (* We don't support nested loops for now *)
        raise (Failure "Nested loops are not supported for now")
  in
  (* Join the contexts at the loop entry *)
  (* TODO: return result:
   * - end borrows in ctx0
   * - ok: return joined env
   * TODO: keep initial env somewhere?
   * TODO: the returned env is an eval_ctx or smth else?
   * Maybe simply keep track of existentially quantified variables?
   *)
  let join_ctxs (ctx0 : match_ctx) : joined_ctx_or_update =
    let ctx1 = loop_join_entry_ctx_with_continue_ctxs ctx0 !ctxs in
    ctxs := [];
    ctx1
  in
  (* Check if two contexts are equivalent - modulo alpha conversion on the
     existentially quantified borrows/abstractions/symbolic values *)
  let equiv_ctxs (_ctx1 : match_ctx) (_ctx2 : match_ctx) : bool =
    failwith "Unimplemented"
  in
  let max_num_iter = Config.loop_fixed_point_max_num_iters in
  let rec compute_fixed_point (mctx : match_ctx) (i : int) : match_ctx =
    if i = 0 then
      raise
        (Failure
           ("Could not compute a loop fixed point in "
          ^ string_of_int max_num_iter ^ " iterations"))
    else
      (* The join on the environments may fail if we need to end some borrows/abstractions
         in the original context first: reorganize the original environment for as
         long as we need to *)
      let rec eval_iteration_then_join (mctx : match_ctx) =
        (* Evaluate the loop body *)
        let _ = eval_loop_body cf_exit_loop_body mctx.ctx in
        (* Check if the join succeeded, or if we need to end abstractions/borrows
           in the original environment first *)
        match join_ctxs mctx with
        | Error (EndAbsInSrc id) ->
            let ctx1 =
              InterpreterBorrows.end_abstraction_no_synth config id mctx.ctx
            in
            eval_iteration_then_join { mctx with ctx = ctx1 }
        | Error (EndBorrowInSrc id) ->
            let ctx1 =
              InterpreterBorrows.end_borrow_no_synth config id mctx.ctx
            in
            eval_iteration_then_join { mctx with ctx = ctx1 }
        | Error (EndBorrowsInSrc ids) ->
            let ctx1 =
              InterpreterBorrows.end_borrows_no_synth config ids mctx.ctx
            in
            eval_iteration_then_join { mctx with ctx = ctx1 }
        | Error (EndBorrowInTgt _ | EndBorrowsInTgt _) ->
            (* Shouldn't happen here *)
            raise (Failure "Unreachable")
        | Ok mctx1 ->
            (* The join succeeded: check if we reached a fixed point, otherwise
               iterate *)
            if equiv_ctxs mctx mctx1 then mctx1
            else compute_fixed_point mctx1 (i - 1)
      in
      eval_iteration_then_join mctx
  in
  compute_fixed_point (mk_match_ctx ctx0) max_num_iter

(** Evaluate a loop in concrete mode *)
let eval_loop_concrete (config : C.config) (eval_loop_body : st_cm_fun) :
    st_cm_fun =
 fun cf ctx ->
  (* Continuation for after we evaluate the loop body: depending the result
     of doing one loop iteration:
     - redoes a loop iteration
     - exits the loop
     - other...

     We need a specific function because of the {!Continue} case: in case we
     continue, we might have to reevaluate the current loop body with the
     new context (and repeat this an indefinite number of times).
  *)
  let rec reeval_loop_body (res : statement_eval_res) : m_fun =
    match res with
    | Return | Panic -> cf res
    | Break i ->
        (* Break out of the loop by calling the continuation *)
        let res = if i = 0 then Unit else Break (i - 1) in
        cf res
    | Continue 0 ->
        (* Re-evaluate the loop body *)
        eval_loop_body reeval_loop_body
    | Continue i ->
        (* Continue to an outer loop *)
        cf (Continue (i - 1))
    | Unit ->
        (* We can't get there.
         * Note that if we decide not to fail here but rather do
         * the same thing as for [Continue 0], we could make the
         * code slightly simpler: calling {!reeval_loop_body} with
         * {!Unit} would account for the first iteration of the loop.
         * We prefer to write it this way for consistency and sanity,
         * though. *)
        raise (Failure "Unreachable")
    | EndEnterLoop | EndContinue ->
        (* We can't get there: this is only used in symbolic mode *)
        raise (Failure "Unreachable")
  in

  (* Apply *)
  eval_loop_body reeval_loop_body ctx

(** Evaluate a loop in symbolic mode *)
let eval_loop_symbolic (config : C.config) (eval_loop_body : st_cm_fun) :
    st_cm_fun =
 fun cf ctx ->
  (* Compute the fixed point at the loop entrance *)
  let mctx = compute_loop_entry_fixed_point config eval_loop_body ctx in
  (* Synthesize the end of the function *)
  let end_expr = match_ctx_with_target_old config mctx (cf EndEnterLoop) ctx in
  (* Synthesize the loop body by evaluating it, with the continuation for
     after the loop starting at the *fixed point*, but with a special
     treatment for the [Break] and [Continue] cases *)
  let cf_loop : st_m_fun =
   fun res ctx ->
    match res with
    | Return | Panic -> cf res ctx
    | Break i ->
        (* Break out of the loop by calling the continuation *)
        let res = if i = 0 then Unit else Break (i - 1) in
        cf res ctx
    | Continue i ->
        (* We don't support nested loops for now *)
        assert (i = 0);
        match_ctx_with_target_old config mctx (cf EndContinue) ctx
    | Unit | EndEnterLoop | EndContinue ->
        (* For why we can't get [Unit], see the comments inside {!eval_loop_concrete}.
           For [EndEnterLoop] and [EndContinue]: we don't support nested loops for now.
        *)
        raise (Failure "Unreachable")
  in
  let loop_expr = eval_loop_body cf_loop mctx.ctx in
  (* Put together *)
  S.synthesize_loop end_expr loop_expr

(** Evaluate a loop *)
let eval_loop (config : C.config) (eval_loop_body : st_cm_fun) : st_cm_fun =
 fun cf ctx ->
  match config.C.mode with
  | ConcreteMode -> eval_loop_concrete config eval_loop_body cf ctx
  | SymbolicMode -> eval_loop_symbolic config eval_loop_body cf ctx
