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
open Cps
open InterpreterUtils
open InterpreterBorrows
open InterpreterExpressions

(** The local logger *)
let log = L.loops_log

type updt_env_kind =
  | AbsInLeft of V.AbstractionId.id
  | LoanInLeft of V.BorrowId.id
  | LoansInLeft of V.BorrowId.Set.t
  | AbsInRight of V.AbstractionId.id
  | LoanInRight of V.BorrowId.id
  | LoansInRight of V.BorrowId.Set.t

(** Utility exception *)
exception ValueMatchFailure of updt_env_kind

type ctx_or_update = (C.eval_ctx, updt_env_kind) result

(** Union Find *)
module UnionFind = UF.Make (UF.StoreMap)

(** A small utility -

    Rem.: some environments may be ill-formed (they may contain several times
    the same loan or borrow - this happens for instance when merging
    environments). This is the reason why we use sets in some places (for
    instance, [borrow_to_abs] maps to a *set* of ids).
*)
type abs_borrows_loans_maps = {
  abs_ids : V.AbstractionId.id list;
  abs_to_borrows : V.BorrowId.Set.t V.AbstractionId.Map.t;
  abs_to_loans : V.BorrowId.Set.t V.AbstractionId.Map.t;
  abs_to_borrows_loans : V.BorrowId.Set.t V.AbstractionId.Map.t;
  borrow_to_abs : V.AbstractionId.Set.t V.BorrowId.Map.t;
  loan_to_abs : V.AbstractionId.Set.t V.BorrowId.Map.t;
  borrow_loan_to_abs : V.AbstractionId.Set.t V.BorrowId.Map.t;
}

(** Compute various maps linking the abstractions and the borrows/loans they contain.

    The [explore] function is used to filter abstractions.

    [no_duplicates] checks that borrows/loans are not referenced more than once
    (see the documentation for {!abs_borrows_loans_maps}).
 *)
let compute_abs_borrows_loans_maps (no_duplicates : bool)
    (explore : V.abs -> bool) (env : C.env) : abs_borrows_loans_maps =
  let abs_ids = ref [] in
  let abs_to_borrows = ref V.AbstractionId.Map.empty in
  let abs_to_loans = ref V.AbstractionId.Map.empty in
  let abs_to_borrows_loans = ref V.AbstractionId.Map.empty in
  let borrow_to_abs = ref V.BorrowId.Map.empty in
  let loan_to_abs = ref V.BorrowId.Map.empty in
  let borrow_loan_to_abs = ref V.BorrowId.Map.empty in

  let module R (Id0 : Identifiers.Id) (Id1 : Identifiers.Id) = struct
    (*
       [check_singleton_sets]: check that the mapping maps to a singletong.
       [check_not_already_registered]: check if the mapping was not already registered.
    *)
    let register_mapping (check_singleton_sets : bool)
        (check_not_already_registered : bool) (map : Id1.Set.t Id0.Map.t ref)
        (id0 : Id0.id) (id1 : Id1.id) : unit =
      (* Sanity check *)
      (if check_singleton_sets || check_not_already_registered then
       match Id0.Map.find_opt id0 !map with
       | None -> ()
       | Some set ->
           assert (
             (not check_not_already_registered) || not (Id1.Set.mem id1 set)));
      (* Update the mapping *)
      map :=
        Id0.Map.update id0
          (fun ids ->
            match ids with
            | None -> Some (Id1.Set.singleton id1)
            | Some ids ->
                (* Sanity check *)
                assert (not check_singleton_sets);
                assert (
                  (not check_not_already_registered)
                  || not (Id1.Set.mem id1 ids));
                (* Update *)
                Some (Id1.Set.add id1 ids))
          !map
  end in
  let module RAbsBorrow = R (V.AbstractionId) (V.BorrowId) in
  let module RBorrowAbs = R (V.BorrowId) (V.AbstractionId) in
  let register_borrow_id abs_id bid =
    RAbsBorrow.register_mapping false no_duplicates abs_to_borrows abs_id bid;
    RAbsBorrow.register_mapping false false abs_to_borrows_loans abs_id bid;
    RBorrowAbs.register_mapping no_duplicates no_duplicates borrow_to_abs bid
      abs_id;
    RBorrowAbs.register_mapping false false borrow_loan_to_abs bid abs_id
  in

  let register_loan_id abs_id bid =
    RAbsBorrow.register_mapping false no_duplicates abs_to_loans abs_id bid;
    RAbsBorrow.register_mapping false false abs_to_borrows_loans abs_id bid;
    RBorrowAbs.register_mapping no_duplicates no_duplicates loan_to_abs bid
      abs_id;
    RBorrowAbs.register_mapping false false borrow_loan_to_abs bid abs_id
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
    abs_to_borrows_loans = !abs_to_borrows_loans;
    borrow_to_abs = !borrow_to_abs;
    loan_to_abs = !loan_to_abs;
    borrow_loan_to_abs = !borrow_loan_to_abs;
  }

(** Destructure all the new abstractions *)
let destructure_new_abs (loop_id : V.LoopId.id)
    (old_abs_ids : V.AbstractionId.Set.t) (ctx : C.eval_ctx) : C.eval_ctx =
  let abs_kind = V.Loop loop_id in
  let can_end = false in
  let destructure_shared_values = true in
  let is_fresh_abs_id (id : V.AbstractionId.id) : bool =
    not (V.AbstractionId.Set.mem id old_abs_ids)
  in
  let env =
    List.map
      (fun ee ->
        match ee with
        | C.Var _ | C.Frame -> ee
        | C.Abs abs ->
            if is_fresh_abs_id abs.abs_id then
              let abs =
                destructure_abs abs_kind can_end destructure_shared_values ctx
                  abs
              in
              C.Abs abs
            else ee)
      ctx.env
  in
  { ctx with env }

(** Collapse an environment.

    We do this to simplify an environment, for the purpose of finding a loop
    fixed point.

    We do the following:
    - we look for all the *new* dummy values (we use sets of old ids to decide
      wether a value is new or not)
    - whenever there is a new abstraction in the context, and some of its
      its borrows are associated to loans in another new abstraction, we
      merge them.
    In effect, this allows us to merge newly introduced abstractions/borrows
    with their parent abstractions.

    [merge_funs]: those are used to merge loans or borrows which appear in both
    abstractions (rem.: here we mean that, for instance, both abstractions
    contain a shared loan with id l0).
    This can happen when merging environments (note that such environments are not well-formed -
    they become well formed again after collapsing).
 *)
let collapse_ctx (loop_id : V.LoopId.id)
    (merge_funs : merge_duplicates_funcs option)
    (old_ids : InterpreterBorrowsCore.ctx_ids) (ctx0 : C.eval_ctx) : C.eval_ctx
    =
  let abs_kind = V.Loop loop_id in
  let can_end = false in
  let destructure_shared_values = true in
  let is_fresh_abs_id (id : V.AbstractionId.id) : bool =
    not (V.AbstractionId.Set.mem id old_ids.aids)
  in
  let is_fresh_did (id : C.DummyVarId.id) : bool =
    not (C.DummyVarId.Set.mem id old_ids.dids)
  in
  (* Convert the dummy values to abstractions, and destructure all the new
     abstractions at the same time (note that when we convert values to
     abstractions, the resulting abstraction should be destructured) *)
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
                   convert_value_to_abstractions abs_kind can_end
                     destructure_shared_values ctx0 v
                 in
                 List.map (fun abs -> C.Abs abs) absl
               else [ ee ])
         ctx0.env)
  in

  (* Explore all the *new* abstractions, and compute various maps *)
  let explore (abs : V.abs) = is_fresh_abs_id abs.abs_id in
  let ids_maps =
    compute_abs_borrows_loans_maps (merge_funs = None) explore env
  in
  let {
    abs_ids;
    abs_to_borrows;
    abs_to_loans = _;
    abs_to_borrows_loans;
    borrow_to_abs = _;
    loan_to_abs;
    borrow_loan_to_abs;
  } =
    ids_maps
  in

  (* Change the merging behaviour depending on the input parameters *)
  let abs_to_borrows, loan_to_abs =
    if merge_funs <> None then (abs_to_borrows_loans, borrow_loan_to_abs)
    else (abs_to_borrows, loan_to_abs)
  in

  (* Merge the abstractions together *)
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
          | Some abs_ids1 ->
              V.AbstractionId.Set.iter
                (fun abs_id1 ->
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
                    let nabs =
                      merge_abstractions abs_kind can_end merge_funs !ctx abs1
                        abs0
                    in
                    (* Update the environment *)
                    ctx := fst (C.ctx_subst_abs !ctx abs_id1 nabs);
                    ctx := fst (C.ctx_remove_abs !ctx abs_id0);
                    (* Update the union find *)
                    let abs_ref_merged = UF.union abs_ref0 abs_ref1 in
                    UF.set abs_ref_merged nabs.abs_id)
                abs_ids1)
        bids)
    abs_ids;

  (* Return the new context *)
  !ctx

(*(** Match two types during a join. This simply performs a sanity check. *)
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
  match_types check_regions ctx ty0 ty1 *)

(** See {!Match} *)
module type Matcher = sig
  (** The input primitive values are not equal *)
  val match_distinct_primitive_values :
    T.ety -> V.primitive_value -> V.primitive_value -> V.typed_value

  (** The input ADTs don't have the same variant *)
  val match_distinct_adts : T.ety -> V.adt_value -> V.adt_value -> V.typed_value

  (** The meta-value is the result of a match *)
  val match_shared_borrows :
    T.ety -> V.mvalue -> V.borrow_id -> V.borrow_id -> V.mvalue * V.borrow_id

  (** The input parameters are:
      - [ty]
      - [bid0]: first borrow id
      - [bv0]: first borrowed value
      - [bid1]
      - [bv1]
      - [bv]: the result of matching [bv0] with [bv1]
  *)
  val match_mut_borrows :
    T.ety ->
    V.borrow_id ->
    V.typed_value ->
    V.borrow_id ->
    V.typed_value ->
    V.typed_value ->
    V.borrow_id * V.typed_value

  (** Parameters:
      [ty]
      [ids0]
      [ids1]
      [v]: the result of matching the shared values coming from the two loans
   *)
  val match_shared_loans :
    T.ety ->
    V.loan_id_set ->
    V.loan_id_set ->
    V.typed_value ->
    V.loan_id_set * V.typed_value

  val match_mut_loans : T.ety -> V.loan_id -> V.loan_id -> V.loan_id

  (** There are no constraints on the input symbolic values *)
  val match_symbolic_values :
    V.symbolic_value -> V.symbolic_value -> V.symbolic_value

  (** Match a symbolic value with a value which is not symbolic.

      If the boolean is [true], it means the symbolic value comes from the
      left environment. Otherwise it comes from the right environment (it
      is important when throwing exceptions, for instance when we need to
      end loans in one of the two environments).
   *)
  val match_symbolic_with_other :
    bool -> V.symbolic_value -> V.typed_value -> V.typed_value

  (** The input ADTs don't have the same variant *)
  val match_distinct_aadts :
    T.rty -> V.adt_avalue -> T.rty -> V.adt_avalue -> V.typed_avalue

  (** Parameters:
      [ty0]
      [bid0]
      [ty1]
      [bid1]
   *)
  val match_ashared_borrows :
    T.rty -> V.borrow_id -> T.rty -> V.borrow_id -> V.typed_avalue

  (** Parameters:
      [ty0]
      [mv0]
      [bid0]
      [av0]
      [ty1]
      [mv1]
      [bid1]
      [av1]
      [mv]: result of matching mv0 and mv1
      [av]: result of matching av0 and av1
   *)
  val match_amut_borrows :
    T.rty ->
    V.mvalue ->
    V.borrow_id ->
    V.typed_avalue ->
    T.rty ->
    V.mvalue ->
    V.borrow_id ->
    V.typed_avalue ->
    V.mvalue ->
    V.typed_avalue ->
    V.typed_avalue

  (** Parameters:
      [ty0]
      [ids0]
      [v0]
      [av0]
      [ty1]
      [ids1]
      [v1]
      [av1]
      [v]: result of matching v0 and v1
      [av]: result of matching av0 and av1
   *)
  val match_ashared_loans :
    T.rty ->
    V.loan_id_set ->
    V.typed_value ->
    V.typed_avalue ->
    T.rty ->
    V.loan_id_set ->
    V.typed_value ->
    V.typed_avalue ->
    V.typed_value ->
    V.typed_avalue ->
    V.typed_avalue

  (** Parameters:
      [ty0]
      [id0]
      [av0]
      [ty1]
      [id1]
      [av1]
      [av]: result of matching av0 and av1
   *)
  val match_amut_loans :
    T.rty ->
    V.borrow_id ->
    V.typed_avalue ->
    T.rty ->
    V.borrow_id ->
    V.typed_avalue ->
    V.typed_avalue ->
    V.typed_avalue

  (** Match two arbitrary avalues whose constructors don't match (this function
      is typically used to raise the proper exception).
   *)
  val match_avalues : V.typed_avalue -> V.typed_avalue -> V.typed_avalue
end

(** Generic functor to implement matching functions between values, environments,
    etc.

    We use it for joins, to check if two environments are convertible, etc.
 *)
module Match (M : Matcher) = struct
  (** Match two values.

      Rem.: this function raises exceptions of type {!ValueMatchFailure}.
   *)
  let rec match_typed_values (ctx : C.eval_ctx) (v0 : V.typed_value)
      (v1 : V.typed_value) : V.typed_value =
    let match_rec = match_typed_values ctx in
    assert (v0.V.ty = v1.V.ty);
    match (v0.V.value, v1.V.value) with
    | V.Primitive pv0, V.Primitive pv1 ->
        if pv0 = pv1 then v1
        else (
          assert (v0.V.ty = v1.V.ty);
          M.match_distinct_primitive_values v0.V.ty pv0 pv1)
    | V.Adt av0, V.Adt av1 ->
        if av0.variant_id = av1.variant_id then
          let fields = List.combine av0.field_values av1.field_values in
          let field_values =
            List.map (fun (f0, f1) -> match_rec f0 f1) fields
          in
          let value : V.value =
            V.Adt { variant_id = av0.variant_id; field_values }
          in
          { V.value; ty = v1.V.ty }
        else (
          (* For now, we don't merge ADTs which contain borrows *)
          assert (not (value_has_borrows ctx v0.V.value));
          assert (not (value_has_borrows ctx v1.V.value));
          (* Merge *)
          M.match_distinct_adts v0.V.ty av0 av1)
    | Bottom, Bottom -> v0
    | Borrow bc0, Borrow bc1 ->
        let bc =
          match (bc0, bc1) with
          | SharedBorrow (mv0, bid0), SharedBorrow (mv1, bid1) ->
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
              assert (not (value_has_borrows ctx mv.V.value));
              let mv, bid = M.match_shared_borrows v0.V.ty mv bid0 bid1 in
              V.SharedBorrow (mv, bid)
          | MutBorrow (bid0, bv0), MutBorrow (bid1, bv1) ->
              let bv = match_rec bv0 bv1 in
              assert (not (value_has_borrows ctx bv.V.value));
              let bid, bv = M.match_mut_borrows v0.V.ty bid0 bv0 bid1 bv1 bv in
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
              let sv = match_rec sv0 sv1 in
              assert (not (value_has_borrows ctx sv.V.value));
              let ids, sv = M.match_shared_loans v0.V.ty ids0 ids1 sv in
              V.SharedLoan (ids, sv)
          | MutLoan id0, MutLoan id1 ->
              let id = M.match_mut_loans v0.V.ty id0 id1 in
              V.MutLoan id
          | SharedLoan _, MutLoan _ | MutLoan _, SharedLoan _ ->
              raise (Failure "Unreachable")
        in
        { V.value = Loan lc; ty = v1.V.ty }
    | Symbolic sv0, Symbolic sv1 ->
        (* For now, we force all the symbolic values containing borrows to
           be eagerly expanded, and we don't support nested borrows *)
        assert (not (value_has_borrows ctx v0.V.value));
        assert (not (value_has_borrows ctx v1.V.value));
        (* Match *)
        let sv = M.match_symbolic_values sv0 sv1 in
        { v1 with V.value = V.Symbolic sv }
    | Loan lc, _ -> (
        match lc with
        | SharedLoan (ids, _) -> raise (ValueMatchFailure (LoansInLeft ids))
        | MutLoan id -> raise (ValueMatchFailure (LoanInLeft id)))
    | _, Loan lc -> (
        match lc with
        | SharedLoan (ids, _) -> raise (ValueMatchFailure (LoansInRight ids))
        | MutLoan id -> raise (ValueMatchFailure (LoanInRight id)))
    | Symbolic sv, _ -> M.match_symbolic_with_other true sv v1
    | _, Symbolic sv -> M.match_symbolic_with_other false sv v0
    | _ -> raise (Failure "Unreachable")

  (** Match two avalues.

      Rem.: this function raises exceptions of type {!ValueMatchFailure}.
   *)
  and match_typed_avalues (ctx : C.eval_ctx) (v0 : V.typed_avalue)
      (v1 : V.typed_avalue) : V.typed_avalue =
    let match_rec = match_typed_values ctx in
    let match_arec = match_typed_avalues ctx in
    assert (v0.V.ty = v1.V.ty);
    match (v0.V.value, v1.V.value) with
    | V.APrimitive _, V.APrimitive _ ->
        (* We simply ignore - those are actually not used *)
        assert (v0.V.ty = v1.V.ty);
        mk_aignored v0.V.ty
    | V.AAdt av0, V.AAdt av1 ->
        if av0.variant_id = av1.variant_id then
          let fields = List.combine av0.field_values av1.field_values in
          let field_values =
            List.map (fun (f0, f1) -> match_arec f0 f1) fields
          in
          let value : V.avalue =
            V.AAdt { variant_id = av0.variant_id; field_values }
          in
          { V.value; ty = v1.V.ty }
        else (* Merge *)
          M.match_distinct_aadts v0.V.ty av0 v1.V.ty av1
    | ABottom, ABottom -> v0
    | ABorrow bc0, ABorrow bc1 -> (
        match (bc0, bc1) with
        | ASharedBorrow bid0, ASharedBorrow bid1 ->
            M.match_ashared_borrows v0.V.ty bid0 v1.V.ty bid1
        | AMutBorrow (mv0, bid0, av0), AMutBorrow (mv1, bid1, av1) ->
            (* Not sure what to do with the meta-value *)
            let mv = match_rec mv0 mv1 in
            let av = match_arec av0 av1 in
            M.match_amut_borrows v0.V.ty mv0 bid0 av0 v1.V.ty mv1 bid1 av1 mv av
        | AIgnoredMutBorrow _, AIgnoredMutBorrow _ ->
            (* The abstractions are destructured: we shouldn't get there *)
            raise (Failure "Unexpected")
        | AProjSharedBorrow asb0, AProjSharedBorrow asb1 -> (
            match (asb0, asb1) with
            | [], [] ->
                (* This case actually stands for ignored shared borrows, when
                   there are no nested borrows *)
                v0
            | _ ->
                (* We should get there only if there are nested borrows *)
                raise (Failure "Unexpected"))
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
            raise (Failure "Unexpected"))
    | ALoan lc0, ALoan lc1 -> (
        (* TODO: maybe we should enforce that the ids are always exactly the same -
           without matching *)
        match (lc0, lc1) with
        | ASharedLoan (ids0, sv0, av0), ASharedLoan (ids1, sv1, av1) ->
            let sv = match_rec sv0 sv1 in
            let av = match_arec av0 av1 in
            assert (not (value_has_borrows ctx sv.V.value));
            M.match_ashared_loans v0.V.ty ids0 sv0 av0 v1.V.ty ids1 sv1 av1 sv
              av
        | AMutLoan (id0, av0), AMutLoan (id1, av1) ->
            let av = match_arec av0 av1 in
            M.match_amut_loans v0.V.ty id0 av0 v1.V.ty id1 av1 av
        | AIgnoredMutLoan _, AIgnoredMutLoan _
        | AIgnoredSharedLoan _, AIgnoredSharedLoan _ ->
            (* Those should have been filtered when destructuring the abstractions -
               they are necessary only when there are nested borrows *)
            raise (Failure "Unreachable")
        | _ -> raise (Failure "Unreachable"))
    | ASymbolic _, ASymbolic _ ->
        (* For now, we force all the symbolic values containing borrows to
           be eagerly expanded, and we don't support nested borrows *)
        raise (Failure "Unreachable")
    | _ -> M.match_avalues v0 v1
end

(* Very annoying: functors only take modules as inputs... *)
module type MatchJoinState = sig
  (** The current context *)
  val ctx : C.eval_ctx

  (** The current loop *)
  val loop_id : V.LoopId.id

  (** The abstractions introduced when performing the matches *)
  val nabs : V.abs list ref
end

module MakeJoinMatcher (S : MatchJoinState) : Matcher = struct
  (** Small utility *)
  let push_abs (abs : V.abs) : unit = S.nabs := abs :: !S.nabs

  let match_distinct_primitive_values (ty : T.ety) (_ : V.primitive_value)
      (_ : V.primitive_value) : V.typed_value =
    mk_fresh_symbolic_typed_value_from_ety V.LoopJoin ty

  let match_distinct_adts (ty : T.ety) (adt0 : V.adt_value) (adt1 : V.adt_value)
      : V.typed_value =
    (* Check that the ADTs don't contain borrows - this is redundant with checks
       performed by the caller, but we prefer to be safe with regards to future
       updates
    *)
    let check_no_borrows (v : V.typed_value) =
      assert (not (value_has_borrows S.ctx v.V.value))
    in
    List.iter check_no_borrows adt0.field_values;
    List.iter check_no_borrows adt1.field_values;

    (* Check if there are loans: we request to end them *)
    let check_loans (left : bool) (fields : V.typed_value list) : unit =
      match InterpreterBorrowsCore.get_first_loan_in_values fields with
      | Some (V.SharedLoan (ids, _)) ->
          if left then raise (ValueMatchFailure (LoansInLeft ids))
          else raise (ValueMatchFailure (LoansInRight ids))
      | Some (V.MutLoan id) ->
          if left then raise (ValueMatchFailure (LoanInLeft id))
          else raise (ValueMatchFailure (LoanInRight id))
      | None -> ()
    in
    check_loans true adt0.field_values;
    check_loans false adt1.field_values;

    (* No borrows, no loans: we can introduce a symbolic value *)
    mk_fresh_symbolic_typed_value_from_ety V.LoopJoin ty

  let match_shared_borrows (ty : T.ety) (mv : V.mvalue) (bid0 : V.borrow_id)
      (bid1 : V.borrow_id) : V.mvalue * V.borrow_id =
    if bid0 = bid1 then (mv, bid0)
    else
      (* We replace bid0 and bid1 with a fresh borrow id, and introduce
         an abstraction which links all of them:
         {[
           { SB bid0, SB bid1, SL {bid2} }
         ]}
      *)
      let rid = C.fresh_region_id () in
      let bid2 = C.fresh_borrow_id () in

      (* Generate a fresh symbolic value for the shared value *)
      let sv = mk_fresh_symbolic_typed_value_from_ety V.LoopJoin ty in

      let _, bv_ty, kind = ty_as_ref ty in
      let borrow_ty =
        mk_ref_ty (T.Var rid) (ety_no_regions_to_rty bv_ty) kind
      in

      (* Generate the avalues for the abstraction *)
      let mk_aborrow (bid : V.borrow_id) : V.typed_avalue =
        let value = V.ABorrow (V.ASharedBorrow bid) in
        { V.value; ty = borrow_ty }
      in
      let borrows = [ mk_aborrow bid0; mk_aborrow bid1 ] in

      let loan =
        V.ASharedLoan
          ( V.BorrowId.Set.singleton bid2,
            sv,
            mk_aignored (ety_no_regions_to_rty bv_ty) )
      in
      (* Note that an aloan has a borrow type *)
      let loan = { V.value = V.ALoan loan; ty = borrow_ty } in

      let avalues = List.append borrows [ loan ] in

      (* Generate the abstraction *)
      let abs =
        {
          V.abs_id = C.fresh_abstraction_id ();
          kind = V.Loop S.loop_id;
          can_end = false;
          parents = V.AbstractionId.Set.empty;
          original_parents = [];
          regions = T.RegionId.Set.singleton rid;
          ancestors_regions = T.RegionId.Set.empty;
          avalues;
        }
      in
      push_abs abs;

      (* Return the new borrow *)
      (sv, bid2)

  let match_mut_borrows (ty : T.ety) (bid0 : V.borrow_id) (bv0 : V.typed_value)
      (bid1 : V.borrow_id) (bv1 : V.typed_value) (bv : V.typed_value) :
      V.borrow_id * V.typed_value =
    if bid0 = bid1 then (bid0, bv)
    else
      (* We replace bid0 and bid1 with a fresh borrow id, and introduce
         an abstraction which links all of them:
         {[
           { MB bid0, MB bid1, ML bid2 }
         ]}
      *)
      let rid = C.fresh_region_id () in
      let bid2 = C.fresh_borrow_id () in

      (* Generate a fresh symbolic value for the borrowed value *)
      let sv = mk_fresh_symbolic_typed_value_from_ety V.LoopJoin ty in

      let _, bv_ty, kind = ty_as_ref ty in
      let borrow_ty =
        mk_ref_ty (T.Var rid) (ety_no_regions_to_rty bv_ty) kind
      in

      (* Generate the avalues for the abstraction *)
      let mk_aborrow (bid : V.borrow_id) (bv : V.typed_value) : V.typed_avalue =
        let bv_ty = ety_no_regions_to_rty bv.V.ty in
        let value = V.ABorrow (V.AMutBorrow (bv, bid, mk_aignored bv_ty)) in
        { V.value; ty = borrow_ty }
      in
      let borrows = [ mk_aborrow bid0 bv0; mk_aborrow bid1 bv1 ] in

      let loan = V.AMutLoan (bid2, mk_aignored (ety_no_regions_to_rty bv_ty)) in
      (* Note that an aloan has a borrow type *)
      let loan = { V.value = V.ALoan loan; ty = borrow_ty } in

      let avalues = List.append borrows [ loan ] in

      (* Generate the abstraction *)
      let abs =
        {
          V.abs_id = C.fresh_abstraction_id ();
          kind = V.Loop S.loop_id;
          can_end = false;
          parents = V.AbstractionId.Set.empty;
          original_parents = [];
          regions = T.RegionId.Set.singleton rid;
          ancestors_regions = T.RegionId.Set.empty;
          avalues;
        }
      in
      push_abs abs;

      (* Return the new borrow *)
      (bid2, sv)

  let match_shared_loans (_ : T.ety) (ids0 : V.loan_id_set)
      (ids1 : V.loan_id_set) (sv : V.typed_value) :
      V.loan_id_set * V.typed_value =
    (* Check if the ids are the same - Rem.: we forbid the sets of loans
       to be different. However, if we dive inside data-structures (by
       using a shared borrow) the shared values might themselves contain
       shared loans, which need to be matched. For this reason, we destructure
       the shared values (see {!destructure_abs}).
    *)
    let extra_ids_left = V.BorrowId.Set.diff ids0 ids1 in
    let extra_ids_right = V.BorrowId.Set.diff ids1 ids0 in
    if not (V.BorrowId.Set.is_empty extra_ids_left) then
      raise (ValueMatchFailure (LoansInLeft extra_ids_left));
    if not (V.BorrowId.Set.is_empty extra_ids_right) then
      raise (ValueMatchFailure (LoansInRight extra_ids_right));

    (* This should always be true if we get here *)
    assert (ids0 = ids1);
    let ids = ids0 in

    (* Return *)
    (ids, sv)

  let match_mut_loans (_ : T.ety) (id0 : V.loan_id) (id1 : V.loan_id) :
      V.loan_id =
    if id0 = id1 then id0
    else
      (* We forbid this case for now: if we get there, we force to end
         both borrows *)
      raise (ValueMatchFailure (LoanInLeft id0))

  let match_symbolic_values (sv0 : V.symbolic_value) (sv1 : V.symbolic_value) :
      V.symbolic_value =
    let id0 = sv0.sv_id in
    let id1 = sv1.sv_id in
    if id0 = id1 then (
      (* Sanity check *)
      assert (sv0 = sv1);
      (* Return *)
      sv0)
    else (
      (* The caller should have checked that the symbolic values don't contain
         borrows *)
      assert (not (ty_has_borrows S.ctx.type_context.type_infos sv0.sv_ty));
      (* We simply introduce a fresh symbolic value *)
      mk_fresh_symbolic_value V.LoopJoin sv0.sv_ty)

  let match_symbolic_with_other (left : bool) (sv : V.symbolic_value)
      (v : V.typed_value) : V.typed_value =
    (* Check that:
       - there are no borrows in the symbolic value
       - there are no borrows in the "regular" value
       If there are loans in the regular value, raise an exception.
    *)
    assert (not (ty_has_borrows S.ctx.type_context.type_infos sv.sv_ty));
    assert (not (value_has_borrows S.ctx v.V.value));
    (match InterpreterBorrowsCore.get_first_loan_in_value v with
    | None -> ()
    | Some (SharedLoan (ids, _)) ->
        if left then raise (ValueMatchFailure (LoansInLeft ids))
        else raise (ValueMatchFailure (LoansInRight ids))
    | Some (MutLoan id) ->
        if left then raise (ValueMatchFailure (LoanInLeft id))
        else raise (ValueMatchFailure (LoanInRight id)));
    (* Return a fresh symbolic value *)
    mk_fresh_symbolic_typed_value V.LoopJoin sv.sv_ty

  let match_distinct_aadts _ _ _ _ = raise (Failure "Unreachable")
  let match_ashared_borrows _ _ _ _ = raise (Failure "Unreachable")
  let match_amut_borrows _ _ _ _ _ _ _ _ _ _ = raise (Failure "Unreachable")
  let match_ashared_loans _ _ _ _ _ _ _ _ _ _ = raise (Failure "Unreachable")
  let match_amut_loans _ _ _ _ _ _ _ = raise (Failure "Unreachable")
  let match_avalues _ _ = raise (Failure "Unreachable")
end

(** Collapse an environment, merging the duplicated borrows/loans.

    This function simply calls {!collapse_ctx} with the proper merging functions.
 *)
let collapse_ctx_with_merge (loop_id : V.LoopId.id)
    (old_ids : InterpreterBorrowsCore.ctx_ids) (ctx : C.eval_ctx) : C.eval_ctx =
  (* When we join environments, we may introduce duplicated *loans*: we thus
      don't implement merge functions for the borrows, only for the loans.

      For instance:
      {[
        // If we have:
        env0 = {
          abs0 { ML l0 }
          l -> MB l0 s0
        }

        env1 = {
          abs0 { ML l0 }
          abs1 { MB l0, ML l1 }
          l -> MB l1 s1
        }

        // Then:
        join env0 env1 = {
          abs0 { ML l0 }
          abs1 { MB l0, ML l1 }
          abs2 { MB l0, MB l1, ML l2 } // Introduced when merging the "l" binding
          l -> MB l2 s2
        }
      ]}

     Rem.: the merge functions raise exceptions (that we catch).
  *)
  let module S : MatchJoinState = struct
    let ctx = ctx
    let loop_id = loop_id
    let nabs = ref []
  end in
  let module JM = MakeJoinMatcher (S) in
  let module M = Match (JM) in
  let merge_amut_borrows _ _ _ _ _ _ _ = raise (Failure "Unexpected") in
  let merge_ashared_borrows _ _ _ = raise (Failure "Unexpected") in
  let merge_amut_loans id ty0 child0 _ty1 child1 =
    (* Sanity checks *)
    assert (is_aignored child0.V.value);
    assert (is_aignored child1.V.value);
    (* We simply need to introduce an [AMutLoan]. Some remarks:
       - the child is [AIgnored]
       - we need to pick some types. The types on the left and on the right
         may use different regions: it doesn't really matter (here, we pick
         the ones from the left).
    *)
    let ty = ty0 in
    let child = child0 in
    let value = V.ALoan (V.AMutLoan (id, child)) in
    { V.value; ty }
  in
  let merge_ashared_loans ids ty0 (sv0 : V.typed_value) child0 _ty1
      (sv1 : V.typed_value) child1 =
    (* Sanity checks *)
    assert (is_aignored child0.V.value);
    assert (is_aignored child1.V.value);
    (* Same remarks as for [merge_amut_loans].

       This time, however, we need to merge the shared values.
    *)
    assert (not (value_has_loans_or_borrows ctx sv0.V.value));
    assert (not (value_has_loans_or_borrows ctx sv1.V.value));
    let ty = ty0 in
    let child = child0 in
    let sv = M.match_typed_values ctx sv0 sv1 in
    let value = V.ALoan (V.ASharedLoan (ids, sv, child)) in
    { V.value; ty }
  in
  let merge_funcs =
    {
      merge_amut_borrows;
      merge_ashared_borrows;
      merge_amut_loans;
      merge_ashared_loans;
    }
  in
  try collapse_ctx loop_id (Some merge_funcs) old_ids ctx
  with ValueMatchFailure _ -> raise (Failure "Unexpected")

(** Join two contexts *)
let join_ctxs (loop_id : V.LoopId.id) (old_ids : InterpreterBorrowsCore.ctx_ids)
    (ctx0 : C.eval_ctx) (ctx1 : C.eval_ctx) : ctx_or_update =
  let env0 = List.rev ctx0.env in
  let env1 = List.rev ctx1.env in

  (* We need to pick a context for some functions like [match_typed_values]:
     the context is only used to lookup module data, so we can pick whichever
     we want.
     TODO: this is not very clean. Maybe we should just carry this data around.
  *)
  let ctx = ctx0 in

  let nabs = ref [] in

  (* Explore the environments.

     Note that they should have the same prefixes (they should start with
     old dummy values, old abstractions and bindings which have the same ids).
     Those old values and abstractions should actually be equal between the
     two environments.

     Rem.: this is important to make the match easy (we take care of preserving
     the structure of the environments, and ending the proper borrows/abstractions,
     etc.). We could also implement a more general join.
  *)
  let join_suffixes (env0 : C.env) (env1 : C.env) : C.env =
    (* Sanity check: there are no values/abstractions which should be in the prefix *)
    let check_valid (ee : C.env_elem) : unit =
      match ee with
      | C.Var (C.VarBinder _, _) ->
          (* Variables are necessarily in the prefix *)
          raise (Failure "Unreachable")
      | Var (C.DummyBinder did, _) ->
          assert (not (C.DummyVarId.Set.mem did old_ids.dids))
      | Abs abs ->
          assert (not (V.AbstractionId.Set.mem abs.abs_id old_ids.aids))
      | Frame -> ()
    in
    List.iter check_valid env0;
    List.iter check_valid env1;
    (* Concatenate the suffixes and append the abstractions introduced while
       joining the prefixes *)
    let absl = List.map (fun abs -> C.Abs abs) !nabs in
    List.concat [ env0; env1; absl ]
  in

  let module S : MatchJoinState = struct
    (* The context is only used to lookup module data: we can pick whichever we want *)
    let ctx = ctx
    let loop_id = loop_id
    let nabs = nabs
  end in
  let module JM = MakeJoinMatcher (S) in
  let module M = Match (JM) in
  (* Rem.: this function raises exceptions *)
  let rec join_prefixes (env0 : C.env) (env1 : C.env) : C.env =
    match (env0, env1) with
    | ( (C.Var (C.DummyBinder b0, v0) as var) :: env0',
        C.Var (C.DummyBinder b1, v1) :: env1' ) ->
        (* Two cases: the dummy value is an old value, in which case the bindings
           must be the same and we must join their values. Otherwise, it means we
           are not in the prefix anymore *)
        if C.DummyVarId.Set.mem b0 old_ids.dids then (
          (* Still in the prefix: the values must match *)
          assert (b0 = b1);
          assert (v0 = v1);
          (* Continue *)
          var :: join_prefixes env0' env1')
        else (* Not in the prefix anymore *)
          join_suffixes env0 env1
    | C.Var (C.VarBinder b0, v0) :: env0', C.Var (C.VarBinder b1, v1) :: env1'
      ->
        (* Variable bindings *must* be in the prefix and consequently their
           ids must be the same *)
        assert (b0 = b1);
        (* Match the values *)
        let b = b0 in
        let v = M.match_typed_values ctx v0 v1 in
        let var = C.Var (C.VarBinder b, v) in
        (* Continue *)
        var :: join_prefixes env0' env1'
    | (C.Abs abs0 as abs) :: env0', C.Abs abs1 :: env1' ->
        (* Same as for the dummy values: there are two cases *)
        if V.AbstractionId.Set.mem abs0.abs_id old_ids.aids then (
          (* Still in the prefix: the abstractions must be the same *)
          assert (abs0 = abs1);
          (* Continue *)
          abs :: join_suffixes env0' env1')
        else (* Not in the prefix anymore *)
          join_suffixes env0 env1
    | _ ->
        (* The elements don't match: we are not in the prefix anymore *)
        join_suffixes env0 env1
  in

  try
    let env = List.rev (join_prefixes env0 env1) in

    (* Construct the joined context - of course, the type, fun, etc. contexts
     * should be the same in the two contexts *)
    let {
      C.type_context;
      fun_context;
      global_context;
      type_vars;
      env = _;
      ended_regions = ended_regions0;
    } =
      ctx0
    in
    let {
      C.type_context = _;
      fun_context = _;
      global_context = _;
      type_vars = _;
      env = _;
      ended_regions = ended_regions1;
    } =
      ctx1
    in
    let ended_regions = T.RegionId.Set.union ended_regions0 ended_regions1 in
    Ok
      {
        C.type_context;
        fun_context;
        global_context;
        type_vars;
        env;
        ended_regions;
      }
  with ValueMatchFailure e -> Error e

(** Join the context at the entry of the loop with the contexts upon reentry
    (upon reaching the [Continue] statement - the goal is to compute a fixed
    point for the loop entry).
 *)
let loop_join_origin_with_continue_ctxs (config : C.config)
    (loop_id : V.LoopId.id) (old_ctx : C.eval_ctx) (ctxl : C.eval_ctx list) :
    C.eval_ctx =
  (* # Look for borrows and abstractions that exist in [old_ctx] and not in [ctxl]:
   * we need to end those *)
  (* Compute the sets of borrows and abstractions *)
  let old_ids = InterpreterBorrowsCore.compute_context_ids old_ctx in
  let new_ids = InterpreterBorrowsCore.compute_contexts_ids ctxl in
  let bids = V.BorrowId.Set.diff old_ids.bids new_ids.bids in
  let aids = V.AbstractionId.Set.diff old_ids.aids new_ids.aids in
  (* End those borrows and abstractions *)
  let old_ctx = InterpreterBorrows.end_borrows_no_synth config bids old_ctx in
  let old_ctx =
    InterpreterBorrows.end_abstractions_no_synth config aids old_ctx
  in

  (* # Join with the new contexts, one by one

     For every context, we repeteadly attempt to join it with the current
     result of the join: if we fail (because we need to end loans for instance),
     we update the context and retry.
     Rem.: we should never have to end loans in the aggregated context, only
     in the one we are trying to add to the join.
  *)
  let joined_ctx = ref old_ctx in
  let rec join_one_aux (ctx : C.eval_ctx) : unit =
    match join_ctxs loop_id old_ids !joined_ctx ctx with
    | Ok nctx -> joined_ctx := nctx
    | Error err ->
        let ctx =
          match err with
          | LoanInRight bid ->
              InterpreterBorrows.end_borrow_no_synth config bid ctx
          | LoansInRight bids ->
              InterpreterBorrows.end_borrows_no_synth config bids ctx
          | AbsInRight _ | AbsInLeft _ | LoanInLeft _ | LoansInLeft _ ->
              raise (Failure "Unexpected")
        in
        join_one_aux ctx
  in
  let join_one (ctx : C.eval_ctx) : unit =
    (* Destructure the abstractions introduced in the new context *)
    let ctx = destructure_new_abs loop_id old_ids.aids ctx in
    (* Collapse the context we want to add to the join *)
    let ctx = collapse_ctx loop_id None old_ids ctx in
    (* Join the two contexts  *)
    join_one_aux ctx;
    (* Collapse again - the join might have introduce abstractions we want
       to merge with the others (note that those abstractions may actually
       lead to borrows/loans duplications) *)
    joined_ctx := collapse_ctx_with_merge loop_id old_ids !joined_ctx;
    (* Sanity check *)
    if !Config.check_invariants then Invariants.check_invariants !joined_ctx
  in

  List.iter join_one ctxl;

  (* # Return *)
  !joined_ctx

let compute_loop_entry_fixed_point (config : C.config) (loop_id : V.LoopId.id)
    (eval_loop_body : st_cm_fun) (ctx0 : C.eval_ctx) : C.eval_ctx =
  (* The continuation for when we exit the loop - we register the
     environments upon loop *reentry*, and synthesize nothing by
     returning [None]
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
  let join_ctxs (ctx0 : C.eval_ctx) : C.eval_ctx =
    let ctx1 = loop_join_origin_with_continue_ctxs config loop_id ctx0 !ctxs in
    ctxs := [];
    ctx1
  in
  (* Check if two contexts are equivalent - modulo alpha conversion on the
     existentially quantified borrows/abstractions/symbolic values *)
  let equiv_ctxs (_ctx1 : C.eval_ctx) (_ctx2 : C.eval_ctx) : bool =
    failwith "Unimplemented"
  in
  let max_num_iter = Config.loop_fixed_point_max_num_iters in
  let rec compute_fixed_point (ctx : C.eval_ctx) (i : int) : C.eval_ctx =
    if i = 0 then
      raise
        (Failure
           ("Could not compute a loop fixed point in "
          ^ string_of_int max_num_iter ^ " iterations"))
    else
      (* Evaluate the loop body to register the different contexts upon reentry *)
      let _ = eval_loop_body cf_exit_loop_body ctx in
      (* Compute the join between the original contexts and the contexts computed
         upon reentry *)
      let ctx1 = join_ctxs ctx0 in
      (* Check if we reached a fixed point: if not, iterate *)
      if equiv_ctxs ctx0 ctx1 then ctx1 else compute_fixed_point ctx1 (i - 1)
  in
  compute_fixed_point ctx0 max_num_iter

let match_ctx_with_target (config : C.config) (tgt_ctx : C.eval_ctx) : cm_fun =
 fun cf src_ctx ->
  (* We first reorganize [src_ctx] so that we can match it with [tgt_ctx] *)
  (* First, collect all the borrows and abstractions which are in [ctx]
     and not in [tgt_ctx]: we need to end them *)
  let src_ids = InterpreterBorrowsCore.compute_context_ids src_ctx in
  let tgt_ids = InterpreterBorrowsCore.compute_context_ids tgt_ctx in
  let bids = V.BorrowId.Set.diff src_ids.bids tgt_ids.bids in
  let aids = V.AbstractionId.Set.diff src_ids.aids tgt_ids.aids in
  (* End those borrows and abstractions *)
  let cc = InterpreterBorrows.end_borrows config bids in
  let cc = comp cc (InterpreterBorrows.end_abstractions config aids) in
  (* TODO *)
  raise (Failure "Unimplemented")

(** Evaluate a loop in concrete mode *)
let eval_loop_concrete (eval_loop_body : st_cm_fun) : st_cm_fun =
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
  (* Compute a fresh loop id *)
  let loop_id = C.fresh_loop_id () in
  (* Compute the fixed point at the loop entrance *)
  let fp_ctx =
    compute_loop_entry_fixed_point config loop_id eval_loop_body ctx
  in
  (* Synthesize the end of the function - we simply match the context at the
     loop entry with the fixed point: in the synthesized code, the function
     will end with a call to the loop translation
  *)
  let end_expr = match_ctx_with_target config fp_ctx (cf EndEnterLoop) ctx in
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
        match_ctx_with_target config fp_ctx (cf EndContinue) ctx
    | Unit | EndEnterLoop | EndContinue ->
        (* For why we can't get [Unit], see the comments inside {!eval_loop_concrete}.
           For [EndEnterLoop] and [EndContinue]: we don't support nested loops for now.
        *)
        raise (Failure "Unreachable")
  in
  let loop_expr = eval_loop_body cf_loop fp_ctx in
  (* Put together *)
  S.synthesize_loop end_expr loop_expr

(** Evaluate a loop *)
let eval_loop (config : C.config) (eval_loop_body : st_cm_fun) : st_cm_fun =
 fun cf ctx ->
  match config.C.mode with
  | ConcreteMode -> eval_loop_concrete eval_loop_body cf ctx
  | SymbolicMode -> eval_loop_symbolic config eval_loop_body cf ctx
