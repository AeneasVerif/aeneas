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

(** Utility exception *)
exception Distinct

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
    (merge_funs : merge_duplicates_funcs option) (old_ids : ids_sets)
    (ctx0 : C.eval_ctx) : C.eval_ctx =
  (* Debug *)
  log#ldebug
    (lazy
      ("collapse_ctx:\n\n- fixed_ids:\n" ^ show_ids_sets old_ids
     ^ "\n\n- ctx0:\n" ^ eval_ctx_to_string ctx0 ^ "\n\n"));

  let abs_kind = V.Loop loop_id in
  let can_end = false in
  let destructure_shared_values = true in
  let is_fresh_abs_id (id : V.AbstractionId.id) : bool =
    not (V.AbstractionId.Set.mem id old_ids.aids)
  in
  let is_fresh_did (id : C.DummyVarId.id) : bool =
    not (C.DummyVarId.Set.mem id old_ids.dids)
  in
  (* Convert the dummy values to abstractions (note that when we convert
     values to abstractions, the resulting abstraction should be destructured) *)
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
  log#ldebug
    (lazy
      ("collapse_ctx: after converting values to abstractions:\n"
     ^ show_ids_sets old_ids ^ "\n\n- ctx:\n"
      ^ eval_ctx_to_string { ctx0 with env }
      ^ "\n\n"));

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

                    (* Update the environment *)
                    let nctx, abs_id =
                      merge_abstractions abs_kind can_end merge_funs !ctx
                        abs_id0 abs_id1
                    in
                    ctx := nctx;

                    (* Update the union find *)
                    let abs_ref_merged = UF.union abs_ref0 abs_ref1 in
                    UF.set abs_ref_merged abs_id)
                abs_ids1)
        bids)
    abs_ids;

  (* Return the new context *)
  !ctx

(** Match two types during a join. This simply performs a sanity check. *)
let rec match_types (match_distinct_types : 'r T.ty -> 'r T.ty -> 'r T.ty)
    (match_regions : 'r -> 'r -> 'r) (ty0 : 'r T.ty) (ty1 : 'r T.ty) : 'r T.ty =
  let match_rec = match_types match_distinct_types match_regions in
  match (ty0, ty1) with
  | Adt (id0, regions0, tys0), Adt (id1, regions1, tys1) ->
      assert (id0 = id1);
      let id = id0 in
      let regions =
        List.map
          (fun (id0, id1) -> match_regions id0 id1)
          (List.combine regions0 regions1)
      in
      let tys =
        List.map (fun (ty0, ty1) -> match_rec ty0 ty1) (List.combine tys0 tys1)
      in
      Adt (id, regions, tys)
  | TypeVar vid0, TypeVar vid1 ->
      assert (vid0 = vid1);
      let vid = vid0 in
      TypeVar vid
  | Bool, Bool | Char, Char | Never, Never | Str, Str -> ty0
  | Integer int_ty0, Integer int_ty1 ->
      assert (int_ty0 = int_ty1);
      ty0
  | Array ty0, Array ty1 | Slice ty0, Slice ty1 -> match_rec ty0 ty1
  | Ref (r0, ty0, k0), Ref (r1, ty1, k1) ->
      let r = match_regions r0 r1 in
      let ty = match_rec ty0 ty1 in
      assert (k0 = k1);
      let k = k0 in
      Ref (r, ty, k)
  | _ -> match_distinct_types ty0 ty1

(** See {!Match} *)
module type Matcher = sig
  val match_etys : T.ety -> T.ety -> T.ety
  val match_rtys : T.rty -> T.rty -> T.rty

  (** The input primitive values are not equal *)
  val match_distinct_primitive_values :
    T.ety -> V.primitive_value -> V.primitive_value -> V.typed_value

  (** The input ADTs don't have the same variant *)
  val match_distinct_adts : T.ety -> V.adt_value -> V.adt_value -> V.typed_value

  (** The meta-value is the result of a match *)
  val match_shared_borrows : T.ety -> V.borrow_id -> V.borrow_id -> V.borrow_id

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
      *left* environment. Otherwise it comes from the right environment (it
      is important when throwing exceptions, for instance when we need to
      end loans in one of the two environments).
   *)
  val match_symbolic_with_other :
    bool -> V.symbolic_value -> V.typed_value -> V.typed_value

  (** Match a bottom value with a value which is not bottom.

      If the boolean is [true], it means the bottom value comes from the
      *left* environment. Otherwise it comes from the right environment (it
      is important when throwing exceptions, for instance when we need to
      end loans in one of the two environments).
   *)
  val match_bottom_with_other : bool -> V.typed_value -> V.typed_value

  (** The input ADTs don't have the same variant *)
  val match_distinct_aadts :
    T.rty -> V.adt_avalue -> T.rty -> V.adt_avalue -> T.rty -> V.typed_avalue

  (** Parameters:
      [ty0]
      [bid0]
      [ty1]
      [bid1]
      [ty]: result of matching ty0 and ty1
   *)
  val match_ashared_borrows :
    T.rty -> V.borrow_id -> T.rty -> V.borrow_id -> T.rty -> V.typed_avalue

  (** Parameters:
      [ty0]
      [mv0]
      [bid0]
      [av0]
      [ty1]
      [mv1]
      [bid1]
      [av1]
      [ty]: result of matching ty0 and ty1
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
    T.rty ->
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
      [ty]: result of matching ty0 and ty1
      [v]:  result of matching v0 and v1
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
    T.rty ->
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
      [ty]: result of matching ty0 and ty1
      [av]: result of matching av0 and av1
   *)
  val match_amut_loans :
    T.rty ->
    V.borrow_id ->
    V.typed_avalue ->
    T.rty ->
    V.borrow_id ->
    V.typed_avalue ->
    T.rty ->
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
    let ty = M.match_etys v0.V.ty v1.V.ty in
    match (v0.V.value, v1.V.value) with
    | V.Primitive pv0, V.Primitive pv1 ->
        if pv0 = pv1 then v1 else M.match_distinct_primitive_values ty pv0 pv1
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
          M.match_distinct_adts ty av0 av1)
    | Bottom, Bottom -> v0
    | Borrow bc0, Borrow bc1 ->
        let bc =
          match (bc0, bc1) with
          | SharedBorrow bid0, SharedBorrow bid1 ->
              let bid = M.match_shared_borrows ty bid0 bid1 in
              V.SharedBorrow bid
          | MutBorrow (bid0, bv0), MutBorrow (bid1, bv1) ->
              let bv = match_rec bv0 bv1 in
              assert (not (value_has_borrows ctx bv.V.value));
              let bid, bv = M.match_mut_borrows ty bid0 bv0 bid1 bv1 bv in
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
        { V.value = V.Borrow bc; ty }
    | Loan lc0, Loan lc1 ->
        (* TODO: maybe we should enforce that the ids are always exactly the same -
           without matching *)
        let lc =
          match (lc0, lc1) with
          | SharedLoan (ids0, sv0), SharedLoan (ids1, sv1) ->
              let sv = match_rec sv0 sv1 in
              assert (not (value_has_borrows ctx sv.V.value));
              let ids, sv = M.match_shared_loans ty ids0 ids1 sv in
              V.SharedLoan (ids, sv)
          | MutLoan id0, MutLoan id1 ->
              let id = M.match_mut_loans ty id0 id1 in
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
    | Bottom, _ -> M.match_bottom_with_other true v1
    | _, Bottom -> M.match_bottom_with_other false v0
    | _ ->
        log#ldebug
          (lazy
            ("Unexpected match case:\n- value0: "
            ^ typed_value_to_string ctx v0
            ^ "\n- value1: "
            ^ typed_value_to_string ctx v1));
        raise (Failure "Unexpected match case")

  (** Match two avalues.

      Rem.: this function raises exceptions of type {!ValueMatchFailure}.
   *)
  and match_typed_avalues (ctx : C.eval_ctx) (v0 : V.typed_avalue)
      (v1 : V.typed_avalue) : V.typed_avalue =
    log#ldebug
      (lazy
        ("match_typed_avalues:\n- value0: "
        ^ typed_avalue_to_string ctx v0
        ^ "\n- value1: "
        ^ typed_avalue_to_string ctx v1));

    let match_rec = match_typed_values ctx in
    let match_arec = match_typed_avalues ctx in
    let ty = M.match_rtys v0.V.ty v1.V.ty in
    match (v0.V.value, v1.V.value) with
    | V.APrimitive _, V.APrimitive _ ->
        (* We simply ignore - those are actually not used *)
        mk_aignored ty
    | V.AAdt av0, V.AAdt av1 ->
        if av0.variant_id = av1.variant_id then
          let fields = List.combine av0.field_values av1.field_values in
          let field_values =
            List.map (fun (f0, f1) -> match_arec f0 f1) fields
          in
          let value : V.avalue =
            V.AAdt { variant_id = av0.variant_id; field_values }
          in
          { V.value; ty }
        else (* Merge *)
          M.match_distinct_aadts v0.V.ty av0 v1.V.ty av1 ty
    | ABottom, ABottom -> mk_abottom ty
    | AIgnored, AIgnored -> mk_aignored ty
    | ABorrow bc0, ABorrow bc1 -> (
        match (bc0, bc1) with
        | ASharedBorrow bid0, ASharedBorrow bid1 ->
            M.match_ashared_borrows v0.V.ty bid0 v1.V.ty bid1 ty
        | AMutBorrow (mv0, bid0, av0), AMutBorrow (mv1, bid1, av1) ->
            (* The meta-value should be the value consumed by the abstracion.
               This only makes sense if the abstraction was introduced because
               of a function call (we use it for the translation).
               TODO: make it optional?
            *)
            let mv = mk_bottom mv0.V.ty in
            let av = match_arec av0 av1 in
            M.match_amut_borrows v0.V.ty mv0 bid0 av0 v1.V.ty mv1 bid1 av1 ty mv
              av
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
            M.match_ashared_loans v0.V.ty ids0 sv0 av0 v1.V.ty ids1 sv1 av1 ty
              sv av
        | AMutLoan (id0, av0), AMutLoan (id1, av1) ->
            let av = match_arec av0 av1 in
            M.match_amut_loans v0.V.ty id0 av0 v1.V.ty id1 av1 ty av
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

  let push_absl (absl : V.abs list) : unit = List.iter push_abs absl

  let match_etys ty0 ty1 =
    assert (ty0 = ty1);
    ty0

  let match_rtys ty0 ty1 =
    (* The types must be equal - in effect, this forbids to match symbolic
       values containing borrows *)
    assert (ty0 = ty1);
    ty0

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

  let match_shared_borrows (ty : T.ety) (bid0 : V.borrow_id)
      (bid1 : V.borrow_id) : V.borrow_id =
    if bid0 = bid1 then bid0
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
      let _, bv_ty, kind = ty_as_ref ty in
      let sv = mk_fresh_symbolic_typed_value_from_ety V.LoopJoin bv_ty in

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
      bid2

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
      let _, bv_ty, kind = ty_as_ref ty in
      let sv = mk_fresh_symbolic_typed_value_from_ety V.LoopJoin bv_ty in

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
    let value_is_left = not left in
    (match InterpreterBorrowsCore.get_first_loan_in_value v with
    | None -> ()
    | Some (SharedLoan (ids, _)) ->
        if value_is_left then raise (ValueMatchFailure (LoansInLeft ids))
        else raise (ValueMatchFailure (LoansInRight ids))
    | Some (MutLoan id) ->
        if value_is_left then raise (ValueMatchFailure (LoanInLeft id))
        else raise (ValueMatchFailure (LoanInRight id)));
    (* Return a fresh symbolic value *)
    mk_fresh_symbolic_typed_value V.LoopJoin sv.sv_ty

  let match_bottom_with_other (left : bool) (v : V.typed_value) : V.typed_value
      =
    (* If there are outer loans in the non-bottom value, raise an exception.
       Otherwise, convert it to an abstraction and return [Bottom].
    *)
    let with_borrows = false in
    let value_is_left = not left in
    match
      InterpreterBorrowsCore.get_first_outer_loan_or_borrow_in_value
        with_borrows v
    with
    | Some (BorrowContent _) -> raise (Failure "Unreachable")
    | Some (LoanContent lc) -> (
        match lc with
        | V.SharedLoan (ids, _) ->
            if value_is_left then raise (ValueMatchFailure (LoansInLeft ids))
            else raise (ValueMatchFailure (LoansInRight ids))
        | V.MutLoan id ->
            if value_is_left then raise (ValueMatchFailure (LoanInLeft id))
            else raise (ValueMatchFailure (LoanInRight id)))
    | None ->
        (* Convert the value to an abstraction *)
        let abs_kind = V.Loop S.loop_id in
        let can_end = false in
        let destructure_shared_values = true in
        let absl =
          convert_value_to_abstractions abs_kind can_end
            destructure_shared_values S.ctx v
        in
        push_absl absl;
        (* Return [Bottom] *)
        mk_bottom v.V.ty

  let match_distinct_aadts _ _ _ _ _ = raise (Failure "Unreachable")
  let match_ashared_borrows _ _ _ _ = raise (Failure "Unreachable")
  let match_amut_borrows _ _ _ _ _ _ _ _ _ _ _ = raise (Failure "Unreachable")
  let match_ashared_loans _ _ _ _ _ _ _ _ _ _ _ = raise (Failure "Unreachable")
  let match_amut_loans _ _ _ _ _ _ _ _ = raise (Failure "Unreachable")
  let match_avalues _ _ = raise (Failure "Unreachable")
end

(** Collapse an environment, merging the duplicated borrows/loans.

    This function simply calls {!collapse_ctx} with the proper merging functions.

    We do this because when we join environments, we may introduce duplicated
    *loans*: we thus don't implement merge functions for the borrows, only for
    the loans. See the explanations for {!join_ctxs}.

 *)
let collapse_ctx_with_merge (loop_id : V.LoopId.id) (old_ids : ids_sets)
    (ctx : C.eval_ctx) : C.eval_ctx =
  (* Rem.: the merge functions raise exceptions (that we catch). *)
  let module S : MatchJoinState = struct
    let ctx = ctx
    let loop_id = loop_id
    let nabs = ref []
  end in
  let module JM = MakeJoinMatcher (S) in
  let module M = Match (JM) in
  (* TODO: why not simply call: M.match_type_avalues? (or move this code to
     MakeJoinMatcher?) *)
  let merge_amut_borrows id ty0 (mv0 : V.typed_value) child0 _ty1
      (mv1 : V.typed_value) child1 =
    (* Sanity checks *)
    assert (is_aignored child0.V.value);
    assert (is_aignored child1.V.value);
    assert (mv0.V.ty = mv1.V.ty);

    (* Same remarks as for [merge_amut_loans] *)
    let ty = ty0 in
    let child = child0 in
    let mv = mk_bottom mv0.ty in
    let value = V.ABorrow (V.AMutBorrow (mv, id, child)) in
    { V.value; ty }
  in

  let merge_ashared_borrows id ty0 ty1 =
    (* Sanity checks *)
    assert (not (ty_has_borrows ctx.type_context.type_infos ty0));
    assert (not (ty_has_borrows ctx.type_context.type_infos ty1));

    (* Same remarks as for [merge_amut_loans] *)
    let ty = ty0 in
    let value = V.ABorrow (V.ASharedBorrow id) in
    { V.value; ty }
  in

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

(** Join two contexts.

    We make the hypothesis (and check it) that the environments have the same
    prefixes (same variable ids, same abstractions, etc.). The prefix of
    variable and abstraction ids is given by the [fixed_ids] identifier sets. We
    check that those prefixes are the same (the dummy variables are the same,
    the abstractions are the same), match the values mapped to by the variables
    which are not dummy, then group the additional dummy variables/abstractions
    together. Note that when joining the values mapped to by the non-dummy
    variables, we may introduce duplicated borrows. Also, we don't match the
    abstractions which are not in the prefix, which can also lead to borrow
    duplications.  For this reason, the environment needs to be collapsed
    afterwards to get rid of those duplicated loans/borrows.

    For instance, if we have:
    {[
      env0 = {
        abs0 { ML l0 }
        l -> MB l0 s0
      }

      env1 = {
        abs0 { ML l0 }
        l -> MB l1 s1
        abs1 { MB l0, ML l1 }
      }
    ]}

    Then:
    {[
      join env0 env1 = {
        abs0 { ML l0 }
        l -> MB l2 s2
        abs1 { MB l0, ML l1 }
        abs2 { MB l0, MB l1, ML l2 } (* Introduced when merging the "l" binding *)
      }
    ]}

    Rem.: in practice, this join works because we take care of pushing new values
    and abstractions *at the end* of the environments, meaning the environment
    prefixes keep the same structure.

    Rem.: assuming that the environment has some structure poses no soundness
    issue. It can only make the join fail if the environments actually don't have
    this structure (this is a completeness issue).
  *)
let join_ctxs (loop_id : V.LoopId.id) (fixed_ids : ids_sets) (ctx0 : C.eval_ctx)
    (ctx1 : C.eval_ctx) : ctx_or_update =
  (* Debug *)
  log#ldebug
    (lazy
      ("join_ctxs:\n\n- fixed_ids:\n" ^ show_ids_sets fixed_ids
     ^ "\n\n- ctx0:\n"
      ^ eval_ctx_to_string_no_filter ctx0
      ^ "\n\n- ctx1:\n"
      ^ eval_ctx_to_string_no_filter ctx1
      ^ "\n\n"));

  let env0 = List.rev ctx0.env in
  let env1 = List.rev ctx1.env in

  (* We need to pick a context for some functions like [match_typed_values]:
     the context is only used to lookup module data, so we can pick whichever
     we want.
     TODO: this is not very clean. Maybe we should just carry this data around.
  *)
  let ctx = ctx0 in

  let nabs = ref [] in

  (* Explore the environments. *)
  let join_suffixes (env0 : C.env) (env1 : C.env) : C.env =
    (* Debug *)
    log#ldebug
      (lazy
        ("join_suffixes:\n\n- fixed_ids:\n" ^ show_ids_sets fixed_ids
       ^ "\n\n- ctx0:\n"
        ^ eval_ctx_to_string_no_filter { ctx0 with env = List.rev env0 }
        ^ "\n\n- ctx1:\n"
        ^ eval_ctx_to_string_no_filter { ctx1 with env = List.rev env1 }
        ^ "\n\n"));

    (* Sanity check: there are no values/abstractions which should be in the prefix *)
    let check_valid (ee : C.env_elem) : unit =
      match ee with
      | C.Var (C.VarBinder _, _) ->
          (* Variables are necessarily in the prefix *)
          raise (Failure "Unreachable")
      | Var (C.DummyBinder did, _) ->
          assert (not (C.DummyVarId.Set.mem did fixed_ids.dids))
      | Abs abs ->
          assert (not (V.AbstractionId.Set.mem abs.abs_id fixed_ids.aids))
      | Frame ->
          (* This should have been eliminated *)
          raise (Failure "Unreachable")
    in
    List.iter check_valid env0;
    List.iter check_valid env1;
    (* Concatenate the suffixes and append the abstractions introduced while
       joining the prefixes *)
    let absl = List.map (fun abs -> C.Abs abs) (List.rev !nabs) in
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
    | ( (C.Var (C.DummyBinder b0, v0) as var0) :: env0',
        (C.Var (C.DummyBinder b1, v1) as var1) :: env1' ) ->
        (* Debug *)
        log#ldebug
          (lazy
            ("join_prefixes: DummyBinders:\n\n- fixed_ids:\n" ^ "\n"
           ^ show_ids_sets fixed_ids ^ "\n\n- value0:\n"
            ^ env_elem_to_string ctx var0
            ^ "\n\n- value1:\n"
            ^ env_elem_to_string ctx var1
            ^ "\n\n"));

        (* Two cases: the dummy value is an old value, in which case the bindings
           must be the same and we must join their values. Otherwise, it means we
           are not in the prefix anymore *)
        if C.DummyVarId.Set.mem b0 fixed_ids.dids then (
          (* Still in the prefix: the values must match *)
          assert (b0 = b1);
          assert (v0 = v1);
          (* Continue *)
          var0 :: join_prefixes env0' env1')
        else (* Not in the prefix anymore *)
          join_suffixes env0 env1
    | ( (C.Var (C.VarBinder b0, v0) as var0) :: env0',
        (C.Var (C.VarBinder b1, v1) as var1) :: env1' ) ->
        (* Debug *)
        log#ldebug
          (lazy
            ("join_prefixes: VarBinders:\n\n- fixed_ids:\n" ^ "\n"
           ^ show_ids_sets fixed_ids ^ "\n\n- value0:\n"
            ^ env_elem_to_string ctx var0
            ^ "\n\n- value1:\n"
            ^ env_elem_to_string ctx var1
            ^ "\n\n"));

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
        (* Debug *)
        log#ldebug
          (lazy
            ("join_prefixes: Abs:\n\n- fixed_ids:\n" ^ "\n"
           ^ show_ids_sets fixed_ids ^ "\n\n- abs0:\n" ^ abs_to_string ctx abs0
           ^ "\n\n- abs1:\n" ^ abs_to_string ctx abs1 ^ "\n\n"));

        (* Same as for the dummy values: there are two cases *)
        if V.AbstractionId.Set.mem abs0.abs_id fixed_ids.aids then (
          (* Still in the prefix: the abstractions must be the same *)
          assert (abs0 = abs1);
          (* Continue *)
          abs :: join_prefixes env0' env1')
        else (* Not in the prefix anymore *)
          join_suffixes env0 env1
    | _ ->
        (* The elements don't match: we are not in the prefix anymore *)
        join_suffixes env0 env1
  in

  try
    (* Remove the frame delimiter (the first element of an environment is a frame delimiter) *)
    let env0, env1 =
      match (env0, env1) with
      | C.Frame :: env0, C.Frame :: env1 -> (env0, env1)
      | _ -> raise (Failure "Unreachable")
    in

    log#ldebug
      (lazy
        ("- env0:\n" ^ C.show_env env0 ^ "\n\n- env1:\n" ^ C.show_env env1
       ^ "\n\n"));

    let env = List.rev (C.Frame :: join_prefixes env0 env1) in

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

(* Very annoying: functors only take modules as inputs... *)
module type MatchCheckEquivState = sig
  val ctx : C.eval_ctx
  val rid_map : T.RegionId.InjSubst.t ref
  val bid_map : V.BorrowId.InjSubst.t ref
  val sid_map : V.SymbolicValueId.InjSubst.t ref
  val aid_map : V.AbstractionId.InjSubst.t ref
end

module MakeCheckEquivMatcher (S : MatchCheckEquivState) = struct
  module MkGetSetM (Id : Identifiers.Id) = struct
    module Inj = Id.InjSubst

    let get (m : Inj.t ref) (k : Id.id) : Id.id =
      match Inj.find_opt k !m with None -> k | Some k -> k

    let add (m : Inj.t ref) (k0 : Id.id) (k1 : Id.id) =
      if Inj.mem k0 !m then raise Distinct
      else if Inj.Set.mem k1 (Inj.elements !m) then raise Distinct
      else (
        m := Inj.add k0 k1 !m;
        k1)

    let match_e (m : Inj.t ref) (k0 : Id.id) (k1 : Id.id) : Id.id =
      let k0 = get m k0 in
      if k0 = k1 then k1 else add m k0 k1

    let match_el (m : Inj.t ref) (kl0 : Id.id list) (kl1 : Id.id list) :
        Id.id list =
      List.map (fun (k0, k1) -> match_e m k0 k1) (List.combine kl0 kl1)

    (** Figuring out mappings between sets of ids is hard in all generality...
        We use the fact that the fresh ids should have been generated
        the same way (i.e., in the same order) and match the ids two by
        two in increasing order.
     *)
    let match_es (m : Inj.t ref) (ks0 : Id.Set.t) (ks1 : Id.Set.t) : Id.Set.t =
      Id.Set.of_list (match_el m (Id.Set.elements ks0) (Id.Set.elements ks1))
  end

  module GetSetRid = MkGetSetM (T.RegionId)

  let match_rid = GetSetRid.match_e S.rid_map
  let match_ridl = GetSetRid.match_el S.rid_map
  let match_rids = GetSetRid.match_es S.rid_map

  module GetSetBid = MkGetSetM (V.BorrowId)

  let get_bid = GetSetBid.get S.bid_map
  let match_bid = GetSetBid.match_e S.bid_map
  let match_bidl = GetSetBid.match_el S.bid_map
  let match_bids = GetSetBid.match_es S.bid_map

  module GetSetSid = MkGetSetM (V.SymbolicValueId)

  let match_sid = GetSetSid.match_e S.sid_map
  let match_sidl = GetSetSid.match_el S.sid_map
  let match_sids = GetSetSid.match_es S.sid_map

  module GetSetAid = MkGetSetM (V.AbstractionId)

  let match_aid = GetSetAid.match_e S.aid_map
  let match_aidl = GetSetAid.match_el S.aid_map
  let match_aids = GetSetAid.match_es S.aid_map

  (** *)
  let match_etys ty0 ty1 = if ty0 <> ty1 then raise Distinct else ty0

  let match_rtys ty0 ty1 =
    let match_distinct_types _ _ = raise Distinct in
    let match_regions r0 r1 =
      match (r0, r1) with
      | T.Static, T.Static -> r1
      | Var rid0, Var rid1 ->
          let rid = match_rid rid0 rid1 in
          Var rid
      | _ -> raise Distinct
    in
    match_types match_distinct_types match_regions ty0 ty1

  let match_distinct_primitive_values (ty : T.ety) (_ : V.primitive_value)
      (_ : V.primitive_value) : V.typed_value =
    mk_fresh_symbolic_typed_value_from_ety V.LoopJoin ty

  let match_distinct_adts (_ty : T.ety) (_adt0 : V.adt_value)
      (_adt1 : V.adt_value) : V.typed_value =
    raise Distinct

  let match_shared_borrows (_ty : T.ety) (bid0 : V.borrow_id)
      (bid1 : V.borrow_id) : V.borrow_id =
    let bid = match_bid bid0 bid1 in
    bid

  let match_mut_borrows (_ty : T.ety) (bid0 : V.borrow_id)
      (_bv0 : V.typed_value) (bid1 : V.borrow_id) (_bv1 : V.typed_value)
      (bv : V.typed_value) : V.borrow_id * V.typed_value =
    let bid = match_bid bid0 bid1 in
    (bid, bv)

  let match_shared_loans (_ : T.ety) (ids0 : V.loan_id_set)
      (ids1 : V.loan_id_set) (sv : V.typed_value) :
      V.loan_id_set * V.typed_value =
    let ids = match_bids ids0 ids1 in
    (ids, sv)

  let match_mut_loans (_ : T.ety) (bid0 : V.loan_id) (bid1 : V.loan_id) :
      V.loan_id =
    match_bid bid0 bid1

  let match_symbolic_values (sv0 : V.symbolic_value) (sv1 : V.symbolic_value) :
      V.symbolic_value =
    let id0 = sv0.sv_id in
    let id1 = sv1.sv_id in
    let sv_id = match_sid id0 id1 in
    let sv_ty = match_rtys sv0.V.sv_ty sv1.V.sv_ty in
    let sv_kind =
      if sv0.V.sv_kind = sv1.V.sv_kind then sv0.V.sv_kind else raise Distinct
    in
    { V.sv_id; sv_ty; sv_kind }

  let match_symbolic_with_other (_left : bool) (_sv : V.symbolic_value)
      (_v : V.typed_value) : V.typed_value =
    raise Distinct

  let match_bottom_with_other (_left : bool) (_v : V.typed_value) :
      V.typed_value =
    raise Distinct

  let match_distinct_aadts _ _ _ _ _ = raise Distinct

  let match_ashared_borrows _ty0 bid0 _ty1 bid1 ty =
    let bid = match_bid bid0 bid1 in
    let value = V.ABorrow (V.ASharedBorrow bid) in
    { V.value; ty }

  let match_amut_borrows _ty0 _mv0 bid0 _av0 _ty1 _mv1 bid1 _av1 ty mv av =
    let bid = match_bid bid0 bid1 in
    let value = V.ABorrow (V.AMutBorrow (mv, bid, av)) in
    { V.value; ty }

  let match_ashared_loans _ty0 ids0 _v0 _av0 _ty1 ids1 _v1 _av1 ty v av =
    let bids = match_bids ids0 ids1 in
    let value = V.ALoan (V.ASharedLoan (bids, v, av)) in
    { V.value; ty }

  let match_amut_loans _ty0 id0 _av0 _ty1 id1 _av1 ty av =
    let id = match_bid id0 id1 in
    let value = V.ALoan (V.AMutLoan (id, av)) in
    { V.value; ty }

  let match_avalues v0 v1 =
    log#ldebug
      (lazy
        ("avalues don't match:\n- v0: "
        ^ typed_avalue_to_string S.ctx v0
        ^ "\n- v1: "
        ^ typed_avalue_to_string S.ctx v1));
    raise Distinct
end

(** Compute whether two contexts are equivalent modulo an identifier substitution.

    [fixed_ids]: ids for which we force the mapping to be the identity.

    We also take advantage of the structure of the environments, which should
    have the same prefixes (we check it). See the explanations for {!join_ctxs}.

    TODO: explanations.
 *)
let ctxs_are_equivalent (fixed_ids : ids_sets) (ctx0 : C.eval_ctx)
    (ctx1 : C.eval_ctx) : bool =
  log#ldebug
    (lazy
      ("ctxs_are_equivalent:\n\n- fixed_ids:\n" ^ show_ids_sets fixed_ids
     ^ "\n\n- ctx0:\n"
      ^ eval_ctx_to_string_no_filter ctx0
      ^ "\n\n- ctx1:\n"
      ^ eval_ctx_to_string_no_filter ctx1
      ^ "\n\n"));

  (* Initialize the maps and instantiate the matcher *)
  let rid_map =
    ref
      (T.RegionId.InjSubst.of_list
         (List.map (fun x -> (x, x)) (T.RegionId.Set.elements fixed_ids.rids)))
  in
  let bid_map =
    ref
      (V.BorrowId.InjSubst.of_list
         (List.map (fun x -> (x, x)) (V.BorrowId.Set.elements fixed_ids.bids)))
  in
  let aid_map =
    ref
      (V.AbstractionId.InjSubst.of_list
         (List.map
            (fun x -> (x, x))
            (V.AbstractionId.Set.elements fixed_ids.aids)))
  in
  let sid_map =
    ref
      (V.SymbolicValueId.InjSubst.of_list
         (List.map
            (fun x -> (x, x))
            (V.SymbolicValueId.Set.elements fixed_ids.sids)))
  in

  let module S : MatchCheckEquivState = struct
    let ctx = ctx0
    let rid_map = rid_map
    let bid_map = bid_map
    let sid_map = sid_map
    let aid_map = aid_map
  end in
  let module CEM = MakeCheckEquivMatcher (S) in
  let module M = Match (CEM) in
  (* Match the environments - we assume that they have the same structure
     (and fail if they don't) *)

  (* Small utility: check that ids are fixed/mapped to themselves *)
  let ids_are_fixed (ids : ids_sets) : bool =
    let { aids; bids; dids; rids; sids } = ids in
    V.AbstractionId.Set.subset aids fixed_ids.aids
    && V.BorrowId.Set.subset bids fixed_ids.bids
    && C.DummyVarId.Set.subset dids fixed_ids.dids
    && T.RegionId.Set.subset rids fixed_ids.rids
    && V.SymbolicValueId.Set.subset sids fixed_ids.sids
  in

  (* We need to pick a context for some functions like [match_typed_values]:
     the context is only used to lookup module data, so we can pick whichever
     we want.
     TODO: this is not very clean. Maybe we should just carry this data around.
  *)
  let ctx = ctx0 in

  (* Rem.: this function raises exceptions of type [Distinct] *)
  let match_abstractions (abs0 : V.abs) (abs1 : V.abs) : unit =
    let {
      V.abs_id = abs_id0;
      kind = kind0;
      can_end = can_end0;
      parents = parents0;
      original_parents = original_parents0;
      regions = regions0;
      ancestors_regions = ancestors_regions0;
      avalues = avalues0;
    } =
      abs0
    in

    let {
      V.abs_id = abs_id1;
      kind = kind1;
      can_end = can_end1;
      parents = parents1;
      original_parents = original_parents1;
      regions = regions1;
      ancestors_regions = ancestors_regions1;
      avalues = avalues1;
    } =
      abs1
    in

    let _ = CEM.match_aid abs_id0 abs_id1 in
    if kind0 <> kind1 || can_end0 <> can_end1 then raise Distinct;
    let _ = CEM.match_aids parents0 parents1 in
    let _ = CEM.match_aidl original_parents0 original_parents1 in
    let _ = CEM.match_rids regions0 regions1 in
    let _ = CEM.match_rids ancestors_regions0 ancestors_regions1 in

    log#ldebug (lazy "match_abstractions: matching values");
    let _ =
      List.map
        (fun (v0, v1) -> M.match_typed_avalues ctx v0 v1)
        (List.combine avalues0 avalues1)
    in
    ()
  in

  (* Rem.: this function raises exceptions of type [Distinct] *)
  let rec match_envs (env0 : C.env) (env1 : C.env) : unit =
    log#ldebug
      (lazy
        ("ctxs_are_equivalent: match_envs:\n\n- fixed_ids:\n"
       ^ show_ids_sets fixed_ids ^ "\n\n- rid_map: "
        ^ T.RegionId.InjSubst.show_t !rid_map
        ^ "\n- bid_map: "
        ^ V.BorrowId.InjSubst.show_t !bid_map
        ^ "\n- sid_map: "
        ^ V.SymbolicValueId.InjSubst.show_t !sid_map
        ^ "\n- aid_map: "
        ^ V.AbstractionId.InjSubst.show_t !aid_map
        ^ "\n\n- ctx0:\n"
        ^ eval_ctx_to_string_no_filter { ctx0 with env = List.rev env0 }
        ^ "\n\n- ctx1:\n"
        ^ eval_ctx_to_string_no_filter { ctx1 with env = List.rev env1 }
        ^ "\n\n"));

    match (env0, env1) with
    | ( C.Var (C.DummyBinder b0, v0) :: env0',
        C.Var (C.DummyBinder b1, v1) :: env1' ) ->
        (* Two cases: the dummy value is an old value, in which case the bindings
           must be the same and their values equal (and the borrows/loans/symbolic
           values they reference must be fixed) *)
        if C.DummyVarId.Set.mem b0 fixed_ids.dids then (
          (* Fixed values: the values must be equal *)
          assert (b0 = b1);
          assert (v0 = v1);
          (* The ids present in the left value must be fixed *)
          let ids = compute_typed_value_ids v0 in
          assert (ids_are_fixed ids);
          (* Continue *)
          match_envs env0' env1')
        else
          let _ = M.match_typed_values ctx v0 v1 in
          match_envs env0' env1'
    | C.Var (C.VarBinder b0, v0) :: env0', C.Var (C.VarBinder b1, v1) :: env1'
      ->
        assert (b0 = b1);
        (* Match the values *)
        let _ = M.match_typed_values ctx v0 v1 in
        (* Continue *)
        match_envs env0' env1'
    | C.Abs abs0 :: env0', C.Abs abs1 :: env1' ->
        (* Same as for the dummy values: there are two cases *)
        if V.AbstractionId.Set.mem abs0.abs_id fixed_ids.aids then (
          (* Still in the prefix: the abstractions must be the same *)
          assert (abs0 = abs1);
          (* Their ids must be fixed *)
          let ids = compute_abs_ids abs0 in
          assert (ids_are_fixed ids);
          (* Continue *)
          match_envs env0' env1')
        else (
          (* Match the values *)
          match_abstractions abs0 abs1;
          (* Continue *)
          match_envs env0' env1')
    | [], [] ->
        (* Done *)
        ()
    | _ ->
        (* The elements don't match *)
        raise Distinct
  in

  (* Match the environments.

     Rem.: we don't match the ended regions (would it make any sense actually?) *)
  try
    (* Remove the frame delimiter (the first element of an environment is a frame delimiter) *)
    let env0 = List.rev ctx0.env in
    let env1 = List.rev ctx1.env in
    let env0, env1 =
      match (env0, env1) with
      | C.Frame :: env0, C.Frame :: env1 -> (env0, env1)
      | _ -> raise (Failure "Unreachable")
    in

    match_envs env0 env1;
    true
  with Distinct -> false

(** Join the context at the entry of the loop with the contexts upon reentry
    (upon reaching the [Continue] statement - the goal is to compute a fixed
    point for the loop entry).

    As we may have to end loans in the environments before doing the join,
    we return those updated environments, and the joined environment.
 *)
let loop_join_origin_with_continue_ctxs (config : C.config)
    (loop_id : V.LoopId.id) (fixed_ids : ids_sets) (old_ctx : C.eval_ctx)
    (ctxl : C.eval_ctx list) : (C.eval_ctx * C.eval_ctx list) * C.eval_ctx =
  (* # Join with the new contexts, one by one

     For every context, we repeteadly attempt to join it with the current
     result of the join: if we fail (because we need to end loans for instance),
     we update the context and retry.
     Rem.: we should never have to end loans in the aggregated context, only
     in the one we are trying to add to the join.
  *)
  let joined_ctx = ref old_ctx in
  let rec join_one_aux (ctx : C.eval_ctx) : C.eval_ctx =
    match join_ctxs loop_id fixed_ids !joined_ctx ctx with
    | Ok nctx ->
        joined_ctx := nctx;
        ctx
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
  let join_one (ctx : C.eval_ctx) : C.eval_ctx =
    log#ldebug
      (lazy
        ("loop_join_origin_with_continue_ctxs:join_one: initial ctx:\n"
       ^ eval_ctx_to_string ctx));

    (* Destructure the abstractions introduced in the new context *)
    let ctx = destructure_new_abs loop_id fixed_ids.aids ctx in
    log#ldebug
      (lazy
        ("loop_join_origin_with_continue_ctxs:join_one: after destructure:\n"
       ^ eval_ctx_to_string ctx));

    (* Collapse the context we want to add to the join *)
    let ctx = collapse_ctx loop_id None fixed_ids ctx in
    log#ldebug
      (lazy
        ("loop_join_origin_with_continue_ctxs:join_one: after collapse:\n"
       ^ eval_ctx_to_string ctx));

    (* Join the two contexts  *)
    let ctx1 = join_one_aux ctx in
    log#ldebug
      (lazy
        ("loop_join_origin_with_continue_ctxs:join_one: after join:\n"
       ^ eval_ctx_to_string ctx1));

    (* Collapse again - the join might have introduce abstractions we want
       to merge with the others (note that those abstractions may actually
       lead to borrows/loans duplications) *)
    joined_ctx := collapse_ctx_with_merge loop_id fixed_ids !joined_ctx;
    log#ldebug
      (lazy
        ("loop_join_origin_with_continue_ctxs:join_one: after join-collapse:\n"
        ^ eval_ctx_to_string !joined_ctx));

    (* Sanity check *)
    if !Config.check_invariants then Invariants.check_invariants !joined_ctx;
    (* Return *)
    ctx1
  in

  let ctxl = List.map join_one ctxl in

  (* # Return *)
  ((old_ctx, ctxl), !joined_ctx)

let compute_loop_entry_fixed_point (config : C.config) (loop_id : V.LoopId.id)
    (eval_loop_body : st_cm_fun) (ctx0 : C.eval_ctx) : C.eval_ctx =
  (* The continuation for when we exit the loop - we register the
     environments upon loop *reentry*, and synthesize nothing by
     returning [None]
  *)
  let ctx_upon_entry = ref None in
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

  (* The fixed ids. They are the ids of the original ctx, after we ended
     the borrows/loans which end during the first loop iteration (we do
     one loop iteration, then set it to [Some].
  *)
  let fixed_ids = ref None in

  (* Join the contexts at the loop entry *)
  let join_ctxs (ctx0 : C.eval_ctx) : C.eval_ctx =
    (* If this is the first iteration, end the borrows/loans/abs which
       appear in ctx0 and not in the other contexts, then compute the
       set of fixed ids. This means those borrows/loans have to end
       in the loop, and we rather end them *before* the loop. *)
    let ctx0 =
      match !fixed_ids with
      | Some _ -> ctx0
      | None ->
          let old_ids = compute_context_ids ctx0 in
          let new_ids = compute_contexts_ids !ctxs in
          let bids = V.BorrowId.Set.diff old_ids.bids new_ids.bids in
          let aids = V.AbstractionId.Set.diff old_ids.aids new_ids.aids in
          (* End those borrows and abstractions *)
          let ctx0 = InterpreterBorrows.end_borrows_no_synth config bids ctx0 in
          let ctx0 =
            InterpreterBorrows.end_abstractions_no_synth config aids ctx0
          in
          fixed_ids := Some (compute_context_ids ctx0);
          ctx0
    in

    let fixed_ids = Option.get !fixed_ids in
    let (ctx0', _), ctx1 =
      loop_join_origin_with_continue_ctxs config loop_id fixed_ids ctx0 !ctxs
    in
    ctxs := [];
    if !ctx_upon_entry = None then ctx_upon_entry := Some ctx0';
    ctx1
  in
  (* Check if two contexts are equivalent - modulo alpha conversion on the
     existentially quantified borrows/abstractions/symbolic values *)
  let equiv_ctxs (ctx1 : C.eval_ctx) (ctx2 : C.eval_ctx) : bool =
    (* Compute the set of fixed ids - for the symbolic ids, we compute the
       intersection of ids between the original environment and [ctx1]
       and [ctx2] *)
    let fixed_ids = compute_context_ids (Option.get !ctx_upon_entry) in
    let { aids; bids; dids; rids; sids } = fixed_ids in
    let fixed_ids1 = compute_context_ids ctx1 in
    let fixed_ids2 = compute_context_ids ctx2 in
    let sids =
      V.SymbolicValueId.Set.inter sids
        (V.SymbolicValueId.Set.inter fixed_ids1.sids fixed_ids2.sids)
    in
    let fixed_ids = { aids; bids; dids; rids; sids } in
    ctxs_are_equivalent fixed_ids ctx1 ctx2
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
      let ctx1 = join_ctxs ctx in

      (* Debug *)
      log#ldebug
        (lazy
          ("compute_fixed_point:" ^ "\n\n- ctx0:\n"
          ^ eval_ctx_to_string_no_filter ctx
          ^ "\n\n- ctx1:\n"
          ^ eval_ctx_to_string_no_filter ctx1
          ^ "\n\n"));

      (* Check if we reached a fixed point: if not, iterate *)
      if equiv_ctxs ctx ctx1 then ctx1 else compute_fixed_point ctx1 (i - 1)
  in
  compute_fixed_point ctx0 max_num_iter

let match_ctx_with_target (config : C.config) (tgt_ctx : C.eval_ctx) : cm_fun =
 fun cf src_ctx ->
  (* We first reorganize [src_ctx] so that we can match it with [tgt_ctx] *)
  (* First, collect all the borrows and abstractions which are in [ctx]
     and not in [tgt_ctx]: we need to end them *)
  let src_ids = compute_context_ids src_ctx in
  let tgt_ids = compute_context_ids tgt_ctx in
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
  (* Debug *)
  log#ldebug
    (lazy ("eval_loop_symbolic:\nContext:\n" ^ eval_ctx_to_string ctx ^ "\n\n"));

  (* Compute a fresh loop id *)
  let loop_id = C.fresh_loop_id () in
  (* Compute the fixed point at the loop entrance *)
  let fp_ctx =
    compute_loop_entry_fixed_point config loop_id eval_loop_body ctx
  in

  (* Debug *)
  log#ldebug
    (lazy
      ("eval_loop_symbolic:\nInitial context:\n" ^ eval_ctx_to_string ctx
     ^ "\n\nFixed point:\n" ^ eval_ctx_to_string fp_ctx));

  failwith "Unimplemented";

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
