(** Core definitions for the [IntepreterLoops*] *)

open Types
open Values
open Contexts
open InterpreterUtils
open InterpreterBorrowsCore

type updt_env_kind =
  | AbsInLeft of AbstractionId.id
  | LoanInLeft of BorrowId.id
  | LoansInLeft of BorrowId.Set.t
  | AbsInRight of AbstractionId.id
  | LoanInRight of BorrowId.id
  | LoansInRight of BorrowId.Set.t
[@@deriving show]

(** Utility exception *)
exception ValueMatchFailure of updt_env_kind

(** Utility exception *)
exception Distinct of string

type ctx_or_update = (eval_ctx, updt_env_kind) result

(** A small utility.

    Remark: we use projection markers, meaning we compute maps from/to pairs of
    (projection marker, borrow/loan id). This allows us to use this utility
    during a reduce phase (when we simplify the environment and all markers
    should be [PNone]) as well as during a collapse (where we actually have
    markers because we performed a join and are progressively transforming the
    environment to get rid of those markers). *)
type abs_borrows_loans_maps = {
  abs_ids : AbstractionId.id list;
  abs_to_borrows : MarkedUniqueBorrowId.Set.t AbstractionId.Map.t;
  abs_to_non_unique_borrows : MarkedBorrowId.Set.t AbstractionId.Map.t;
  abs_to_loans : MarkedLoanId.Set.t AbstractionId.Map.t;
  borrow_to_abs : AbstractionId.Set.t MarkedUniqueBorrowId.Map.t;
  non_unique_borrow_to_abs : AbstractionId.Set.t MarkedBorrowId.Map.t;
      (** A map from a non unique borrow id (in case of shared borrows) to the
          set of region abstractions refering to this borrow *)
  loan_to_abs : AbstractionId.Set.t MarkedLoanId.Map.t;
  abs_to_borrow_projs : MarkedNormSymbProj.Set.t AbstractionId.Map.t;
  abs_to_loan_projs : MarkedNormSymbProj.Set.t AbstractionId.Map.t;
  borrow_proj_to_abs : AbstractionId.Set.t MarkedNormSymbProj.Map.t;
  loan_proj_to_abs : AbstractionId.Set.t MarkedNormSymbProj.Map.t;
}

type tvalue_matcher = tvalue -> tvalue -> tvalue

(** See {!module:Aeneas.InterpreterLoopsMatchCtxs.MakeMatcher} and [Matcher].

    This module contains primitive match functions to instantiate the generic
    {!module:Aeneas.InterpreterLoopsMatchCtxs.MakeMatcher} functor.

    Remark: all the functions receive as input the left context and the right
    context. This is useful for printing, lookups, and also in order to check
    the ended regions. *)
module type PrimMatcher = sig
  val span : Meta.span
  val match_etys : eval_ctx -> eval_ctx -> ety -> ety -> ety
  val match_rtys : eval_ctx -> eval_ctx -> rty -> rty -> rty

  (** The input primitive values are not equal *)
  val match_distinct_literals :
    tvalue_matcher ->
    eval_ctx ->
    eval_ctx ->
    ety ->
    literal ->
    literal ->
    tvalue

  (** The input ADTs don't have the same variant *)
  val match_distinct_adts :
    tvalue_matcher ->
    eval_ctx ->
    eval_ctx ->
    ety ->
    adt_value ->
    adt_value ->
    tvalue

  (** The meta-value is the result of a match. *)
  val match_shared_borrows :
    tvalue_matcher ->
    eval_ctx ->
    eval_ctx ->
    ety ->
    borrow_id ->
    shared_borrow_id ->
    borrow_id ->
    shared_borrow_id ->
    borrow_id * shared_borrow_id

  (** The input parameters are:
      - [match_values]
      - [ty]
      - [bid0]: first borrow id
      - [bv0]: first borrowed value
      - [bid1]
      - [bv1]
      - [bv]: the result of matching [bv0] with [bv1] *)
  val match_mut_borrows :
    tvalue_matcher ->
    eval_ctx ->
    eval_ctx ->
    ety ->
    borrow_id ->
    tvalue ->
    borrow_id ->
    tvalue ->
    tvalue ->
    borrow_id * tvalue

  (** Parameters:
      - [match_values]
      - [ty]
      - [ids0]
      - [ids1]
      - [v]: the result of matching the shared values coming from the two loans
  *)
  val match_shared_loans :
    tvalue_matcher ->
    eval_ctx ->
    eval_ctx ->
    ety ->
    loan_id ->
    loan_id ->
    tvalue ->
    loan_id * tvalue

  val match_mut_loans :
    tvalue_matcher ->
    eval_ctx ->
    eval_ctx ->
    ety ->
    loan_id ->
    loan_id ->
    loan_id

  (** There are no constraints on the input symbolic values *)
  val match_symbolic_values :
    tvalue_matcher ->
    eval_ctx ->
    eval_ctx ->
    symbolic_value ->
    symbolic_value ->
    symbolic_value

  (** Match a symbolic value with a value which is not symbolic.

      If the boolean is [true], it means the symbolic value comes from the
      *left* environment. Otherwise it comes from the right environment (it is
      important when throwing exceptions, for instance when we need to end loans
      in one of the two environments). *)
  val match_symbolic_with_other :
    tvalue_matcher ->
    eval_ctx ->
    eval_ctx ->
    bool ->
    symbolic_value ->
    tvalue ->
    tvalue

  (** Match a bottom value with a value which is not bottom.

      If the boolean is [true], it means the bottom value comes from the *left*
      environment. Otherwise it comes from the right environment (it is
      important when throwing exceptions, for instance when we need to end loans
      in one of the two environments). *)
  val match_bottom_with_other :
    tvalue_matcher -> eval_ctx -> eval_ctx -> bool -> tvalue -> tvalue

  (** The input ADTs don't have the same variant *)
  val match_distinct_aadts :
    tvalue_matcher ->
    eval_ctx ->
    eval_ctx ->
    rty ->
    adt_avalue ->
    rty ->
    adt_avalue ->
    rty ->
    tavalue

  (** Parameters:
      - [match_values]
      - [ctx0]
      - [ctx1]
      - [ty0]
      - [pm0]
      - [bid0]
      - [ty1]
      - [pm1]
      - [bid1]
      - [ty]: result of matching ty0 and ty1 *)
  val match_ashared_borrows :
    tvalue_matcher ->
    eval_ctx ->
    eval_ctx ->
    rty ->
    proj_marker ->
    borrow_id ->
    shared_borrow_id ->
    rty ->
    proj_marker ->
    borrow_id ->
    shared_borrow_id ->
    rty ->
    tavalue

  (** Parameters:
      - [match_values]
      - [ctx0]
      - [ctx1]
      - [ty0]
      - [pm0]
      - [bid0]
      - [av0]
      - [ty1]
      - [pm1]
      - [bid1]
      - [av1]
      - [ty]: result of matching ty0 and ty1
      - [av]: result of matching av0 and av1 *)
  val match_amut_borrows :
    tvalue_matcher ->
    eval_ctx ->
    eval_ctx ->
    rty ->
    proj_marker ->
    borrow_id ->
    tavalue ->
    rty ->
    proj_marker ->
    borrow_id ->
    tavalue ->
    rty ->
    tavalue ->
    tavalue

  (** Parameters:
      - [match_values]
      - [ctx0]
      - [ctx1]
      - [ty0]
      - [pm0]
      - [ids0]
      - [v0]
      - [av0]
      - [ty1]
      - [pm1]
      - [ids1]
      - [v1]
      - [av1]
      - [ty]: result of matching ty0 and ty1
      - [v]: result of matching v0 and v1
      - [av]: result of matching av0 and av1 *)
  val match_ashared_loans :
    tvalue_matcher ->
    eval_ctx ->
    eval_ctx ->
    rty ->
    proj_marker ->
    loan_id ->
    tvalue ->
    tavalue ->
    rty ->
    proj_marker ->
    loan_id ->
    tvalue ->
    tavalue ->
    rty ->
    tvalue ->
    tavalue ->
    tavalue

  (** Parameters:
      - [match_values]
      - [ctx0]
      - [ctx1]
      - [ty0]
      - [pm0]
      - [id0]
      - [av0]
      - [ty1]
      - [pm1]
      - [id1]
      - [av1]
      - [ty]: result of matching ty0 and ty1
      - [av]: result of matching av0 and av1 *)
  val match_amut_loans :
    tvalue_matcher ->
    eval_ctx ->
    eval_ctx ->
    rty ->
    proj_marker ->
    borrow_id ->
    tavalue ->
    rty ->
    proj_marker ->
    borrow_id ->
    tavalue ->
    rty ->
    tavalue ->
    tavalue

  (** Parameters:
      - [match_values]
      - [ctx0]
      - [ctx1]
      - [ty0]
      - [pm0]
      - [proj0]
      - [ty1]
      - [pm1]
      - [proj1]
      - [ty]: result of matching ty0 and ty1
      - [proj_ty]: result of matching proj_ty0 and proj_ty1 *)
  val match_aproj_borrows :
    tvalue_matcher ->
    eval_ctx ->
    eval_ctx ->
    rty ->
    proj_marker ->
    aproj_borrows ->
    rty ->
    proj_marker ->
    aproj_borrows ->
    rty ->
    rty ->
    tavalue

  (** Parameters:
      - [match_values]
      - [ctx0]
      - [ctx1]
      - [ty0]
      - [pm0]
      - [proj0]
      - [ty1]
      - [pm1]
      - [proj1]
      - [ty]: result of matching ty0 and ty1
      - [proj_ty]: result of matching proj_ty0 and proj_ty1 *)
  val match_aproj_loans :
    tvalue_matcher ->
    eval_ctx ->
    eval_ctx ->
    rty ->
    proj_marker ->
    aproj_loans ->
    rty ->
    proj_marker ->
    aproj_loans ->
    rty ->
    rty ->
    tavalue

  (** Match two arbitrary avalues whose constructors don't match (this function
      is typically used to raise the proper exception). *)
  val match_avalues :
    tvalue_matcher -> eval_ctx -> eval_ctx -> tavalue -> tavalue -> tavalue
end

module type Matcher = sig
  val span : Meta.span

  (** Match two values.

      Rem.: this function raises exceptions of type
      {!Aeneas.InterpreterLoopsCore.ValueMatchFailure}. *)
  val match_tvalues : eval_ctx -> eval_ctx -> tvalue -> tvalue -> tvalue

  (** Match two avalues.

      Rem.: this function raises exceptions of type
      {!Aeneas.InterpreterLoopsCore.ValueMatchFailure}. *)
  val match_tavalues : eval_ctx -> eval_ctx -> tavalue -> tavalue -> tavalue
end

(** See {!module:InterpreterLoopsMatchCtxs.MakeCheckEquivMatcher} and
    {!module-type:InterpreterLoopsCore.CheckEquivMatcher}.

    Very annoying: functors only take modules as inputs... *)
module type MatchCheckEquivState = sig
  val span : Meta.span

  (** [true] if we check equivalence between contexts, [false] if we match a
      source context with a target context. *)
  val check_equiv : bool

  val rid_map : RegionId.InjSubst.t ref

  (** Substitution for the loan and borrow ids - used only if [check_equiv] is
      true *)
  val blid_map : BorrowId.InjSubst.t ref

  (** Substitution for the borrow ids - used only if [check_equiv] is false *)
  val borrow_id_map : BorrowId.InjSubst.t ref

  (** Substitution for the loans ids - used only if [check_equiv] is false *)
  val loan_id_map : BorrowId.InjSubst.t ref

  val sid_map : SymbolicValueId.InjSubst.t ref
  val sid_to_value_map : tvalue SymbolicValueId.Map.t ref
  val aid_map : AbstractionId.InjSubst.t ref
  val lookup_shared_value_in_ctx0 : BorrowId.id -> tvalue
  val lookup_shared_value_in_ctx1 : BorrowId.id -> tvalue
end

module type CheckEquivMatcher = sig
  include PrimMatcher

  val match_aid : abstraction_id -> abstraction_id -> abstraction_id

  val match_aidl :
    abstraction_id list -> abstraction_id list -> abstraction_id list

  val match_aids :
    abstraction_id_set -> abstraction_id_set -> abstraction_id_set

  val match_rid : region_id -> region_id -> region_id
  val match_rids : region_id_set -> region_id_set -> region_id_set
  val match_borrow_id : borrow_id -> borrow_id -> borrow_id
  val match_borrow_idl : borrow_id list -> borrow_id list -> borrow_id list
  val match_borrow_ids : borrow_id_set -> borrow_id_set -> borrow_id_set
  val match_loan_id : loan_id -> loan_id -> loan_id
  val match_loan_idl : loan_id list -> loan_id list -> loan_id list
  val match_loan_ids : loan_id_set -> loan_id_set -> loan_id_set
end

(** See {!InterpreterLoopsMatchCtxs.match_ctxs} *)
type ids_maps = {
  aid_map : AbstractionId.InjSubst.t;
  blid_map : BorrowId.InjSubst.t;
      (** Substitution for the loan and borrow ids *)
  borrow_id_map : BorrowId.InjSubst.t;  (** Substitution for the borrow ids *)
  loan_id_map : BorrowId.InjSubst.t;  (** Substitution for the loan ids *)
  rid_map : RegionId.InjSubst.t;
  sid_map : SymbolicValueId.InjSubst.t;
  sid_to_value_map : tvalue SymbolicValueId.Map.t;
}
[@@deriving show]

let ids_maps_to_string (ctx : eval_ctx) (m : ids_maps) : string =
  let {
    aid_map;
    blid_map;
    borrow_id_map;
    loan_id_map;
    rid_map;
    sid_map;
    sid_to_value_map;
  } =
    m
  in
  let indent = Some "    " in
  "{" ^ "\n  aid_map = "
  ^ AbstractionId.InjSubst.to_string indent aid_map
  ^ "\n  blid_map = "
  ^ BorrowId.InjSubst.to_string indent blid_map
  ^ "\n  borrow_id_map = "
  ^ BorrowId.InjSubst.to_string indent borrow_id_map
  ^ "\n  loan_id_map = "
  ^ BorrowId.InjSubst.to_string indent loan_id_map
  ^ "\n  rid_map = "
  ^ RegionId.InjSubst.to_string indent rid_map
  ^ "\n  sid_map = "
  ^ SymbolicValueId.InjSubst.to_string indent sid_map
  ^ "\n  sid_to_value_map = "
  ^ SymbolicValueId.Map.to_string indent (tvalue_to_string ctx) sid_to_value_map
  ^ "\n}"

type borrow_loan_corresp = {
  borrow_to_loan_id_map : BorrowId.InjSubst.t;
  loan_to_borrow_id_map : BorrowId.InjSubst.t;
  borrow_to_loan_proj_map : SymbolicValueId.InjSubst.t;
  loan_to_borrow_proj_map : SymbolicValueId.InjSubst.t;
}
[@@deriving show]

(* Very annoying: functors only take modules as inputs... *)
module type MatchJoinState = sig
  (** The current loop *)
  val loop_id : LoopId.id

  (** The abstractions introduced when performing the matches *)
  val nabs : abs list ref

  val span : Meta.span

  (** Whenever we create fresh abstractions, do we provide an abstraction
      expression or not? We do not need to compute abstraction expressions when
      computing fixed-points (but we need them for the synthesis). *)
  val with_abs_conts : bool
end

(** Split an environment between the fixed abstractions, values, etc. and the
    new abstractions, values, etc.

    Returns: (fixed, new abs, new dummies) *)
let ctx_split_fixed_new (span : Meta.span) (fixed_ids : ids_sets)
    (ctx : eval_ctx) : env * abs list * tvalue list =
  let is_fresh_did (id : DummyVarId.id) : bool =
    not (DummyVarId.Set.mem id fixed_ids.dids)
  in
  let is_fresh_abs_id (id : AbstractionId.id) : bool =
    not (AbstractionId.Set.mem id fixed_ids.aids)
  in
  (* Filter the new abstractions and dummy variables (there shouldn't be any new dummy variable
     though) in the target context *)
  let is_fresh (ee : env_elem) : bool =
    match ee with
    | EBinding (BVar _, _) | EFrame -> false
    | EBinding (BDummy bv, _) -> is_fresh_did bv
    | EAbs abs -> is_fresh_abs_id abs.abs_id
  in
  let new_eel, filt_env = List.partition is_fresh ctx.env in
  let is_abs ee =
    match ee with
    | EAbs _ -> true
    | _ -> false
  in
  let new_absl, new_dummyl = List.partition is_abs new_eel in
  let new_absl =
    List.map
      (fun ee ->
        match ee with
        | EAbs abs -> abs
        | _ -> [%craise] span "Unreachable")
      new_absl
  in
  let new_dummyl =
    List.map
      (fun ee ->
        match ee with
        | EBinding (BDummy _, v) -> v
        | _ -> [%craise] span "Unreachable")
      new_dummyl
  in
  (filt_env, new_absl, new_dummyl)

let ids_sets_empty_borrows_loans (ids : ids_sets) : ids_sets =
  let {
    aids;
    blids = _;
    borrow_ids = _;
    loan_ids = _;
    unique_borrow_ids = _;
    shared_borrow_ids = _;
    dids;
    rids;
    sids;
  } =
    ids
  in
  let empty = BorrowId.Set.empty in
  let ids =
    {
      aids;
      blids = empty;
      borrow_ids = empty;
      unique_borrow_ids = UniqueBorrowIdSet.empty;
      shared_borrow_ids = SharedBorrowId.Set.empty;
      loan_ids = empty;
      dids;
      rids;
      sids;
    }
  in
  ids

(** Small utility: add a projection marker to a typed avalue. This can be used
    in combination with List.map to add markers to an entire abstraction *)
let tavalue_add_marker (span : Meta.span) (ctx : eval_ctx) (pm : proj_marker)
    (av : tavalue) : tavalue =
  let obj =
    object
      inherit [_] map_tavalue as super
      method! visit_borrow_content _ _ = [%craise] span "Unexpected borrow"
      method! visit_loan_content _ _ = [%craise] span "Unexpected loan"

      method! visit_ASymbolic _ pm0 aproj =
        [%sanity_check] span (pm0 = PNone);
        ASymbolic (pm, aproj)

      method! visit_symbolic_value _ sv =
        (* Symbolic values can appear in shared values *)
        [%sanity_check] span
          (not (symbolic_value_has_borrows (Some span) ctx sv));
        sv

      method! visit_aloan_content env lc =
        match lc with
        | AMutLoan (pm0, bid, av) ->
            [%sanity_check] span (pm0 = PNone);
            super#visit_aloan_content env (AMutLoan (pm, bid, av))
        | ASharedLoan (pm0, bids, av, child) ->
            [%sanity_check] span (pm0 = PNone);
            super#visit_aloan_content env (ASharedLoan (pm, bids, av, child))
        | _ -> [%internal_error] span

      method! visit_aborrow_content env bc =
        match bc with
        | AMutBorrow (pm0, bid, av) ->
            [%sanity_check] span (pm0 = PNone);
            super#visit_aborrow_content env (AMutBorrow (pm, bid, av))
        | ASharedBorrow (pm0, bid, sid) ->
            [%sanity_check] span (pm0 = PNone);
            super#visit_aborrow_content env (ASharedBorrow (pm, bid, sid))
        | _ -> [%internal_error] span
    end
  in
  obj#visit_tavalue () av

(** Small utility: add a projection marker to an abstraction. This can be used
    in combination with List.map to add markers to an entire abstraction *)
let abs_add_marker (span : Meta.span) (ctx : eval_ctx) (pm : proj_marker)
    (abs : abs) : abs =
  { abs with avalues = List.map (tavalue_add_marker span ctx pm) abs.avalues }
