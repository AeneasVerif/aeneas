(** Core definitions for the [IntepreterLoops*] *)

module T = Types
module PV = PrimitiveValues
module V = Values
module E = Expressions
module C = Contexts
module Subst = Substitute
module A = LlbcAst
module L = Logging
module Inv = Invariants
module S = SynthesizeSymbolic
module UF = UnionFind
open InterpreterUtils
open InterpreterExpressions

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
exception Distinct of string

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

(** See {!InterpreterLoopsMatchCtxs.MakeMatcher} and {!InterpreterLoopsCore.Matcher}.

    This module contains primitive match functions to instantiate the generic
    {!InterpreterLoopsMatchCtxs.MakeMatcher} functor.
  *)
module type PrimMatcher = sig
  val match_etys : T.ety -> T.ety -> T.ety
  val match_rtys : T.rty -> T.rty -> T.rty

  (** The input primitive values are not equal *)
  val match_distinct_literals : T.ety -> V.literal -> V.literal -> V.typed_value

  (** The input ADTs don't have the same variant *)
  val match_distinct_adts : T.ety -> V.adt_value -> V.adt_value -> V.typed_value

  (** The meta-value is the result of a match.

      We take an additional function as input, which acts as a matcher over
      typed values, to be able to lookup the shared values and match them.
      We do this for shared borrows (and not, e.g., mutable borrows) because
      shared borrows introduce indirections, while mutable borrows carry the
      borrowed values with them: we might want to explore and match those
      borrowed values, in which case we have to manually look them up before
      calling the match function.
   *)
  val match_shared_borrows :
    (V.typed_value -> V.typed_value -> V.typed_value) ->
    T.ety ->
    V.borrow_id ->
    V.borrow_id ->
    V.borrow_id

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
      [bid0]
      [av0]
      [ty1]
      [bid1]
      [av1]
      [ty]: result of matching ty0 and ty1
      [av]: result of matching av0 and av1
   *)
  val match_amut_borrows :
    T.rty ->
    V.borrow_id ->
    V.typed_avalue ->
    T.rty ->
    V.borrow_id ->
    V.typed_avalue ->
    T.rty ->
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

module type Matcher = sig
  (** Match two values.

      Rem.: this function raises exceptions of type {!Aeneas.InterpreterLoopsCore.ValueMatchFailure}.
   *)
  val match_typed_values :
    C.eval_ctx -> V.typed_value -> V.typed_value -> V.typed_value

  (** Match two avalues.

      Rem.: this function raises exceptions of type {!Aeneas.InterpreterLoopsCore.ValueMatchFailure}.
   *)
  val match_typed_avalues :
    C.eval_ctx -> V.typed_avalue -> V.typed_avalue -> V.typed_avalue
end

(** See {!InterpreterLoopsMatchCtxs.MakeCheckEquivMatcher} and
    {!InterpreterLoopsCore.CheckEquivMatcher}.

    Very annoying: functors only take modules as inputs...
 *)
module type MatchCheckEquivState = sig
  (** [true] if we check equivalence between contexts, [false] if we match
      a source context with a target context. *)
  val check_equiv : bool

  val ctx : C.eval_ctx
  val rid_map : T.RegionId.InjSubst.t ref

  (** Substitution for the loan and borrow ids - used only if [check_equiv] is true *)
  val blid_map : V.BorrowId.InjSubst.t ref

  (** Substitution for the borrow ids - used only if [check_equiv] is false *)
  val borrow_id_map : V.BorrowId.InjSubst.t ref

  (** Substitution for the loans ids - used only if [check_equiv] is false *)
  val loan_id_map : V.BorrowId.InjSubst.t ref

  val sid_map : V.SymbolicValueId.InjSubst.t ref
  val sid_to_value_map : V.typed_value V.SymbolicValueId.Map.t ref
  val aid_map : V.AbstractionId.InjSubst.t ref
  val lookup_shared_value_in_ctx0 : V.BorrowId.id -> V.typed_value
  val lookup_shared_value_in_ctx1 : V.BorrowId.id -> V.typed_value
end

module type CheckEquivMatcher = sig
  include PrimMatcher

  val match_aid : V.abstraction_id -> V.abstraction_id -> V.abstraction_id

  val match_aidl :
    V.abstraction_id list -> V.abstraction_id list -> V.abstraction_id list

  val match_aids :
    V.abstraction_id_set -> V.abstraction_id_set -> V.abstraction_id_set

  val match_rid : V.region_id -> V.region_id -> V.region_id
  val match_rids : V.region_id_set -> V.region_id_set -> V.region_id_set
  val match_borrow_id : V.borrow_id -> V.borrow_id -> V.borrow_id

  val match_borrow_idl :
    V.borrow_id list -> V.borrow_id list -> V.borrow_id list

  val match_borrow_ids : V.borrow_id_set -> V.borrow_id_set -> V.borrow_id_set
  val match_loan_id : V.loan_id -> V.loan_id -> V.loan_id
  val match_loan_idl : V.loan_id list -> V.loan_id list -> V.loan_id list
  val match_loan_ids : V.loan_id_set -> V.loan_id_set -> V.loan_id_set
end

(** See {!InterpreterLoopsMatchCtxs.match_ctxs} *)
type ids_maps = {
  aid_map : V.AbstractionId.InjSubst.t;
  blid_map : V.BorrowId.InjSubst.t;
      (** Substitution for the loan and borrow ids *)
  borrow_id_map : V.BorrowId.InjSubst.t;  (** Substitution for the borrow ids *)
  loan_id_map : V.BorrowId.InjSubst.t;  (** Substitution for the loan ids *)
  rid_map : T.RegionId.InjSubst.t;
  sid_map : V.SymbolicValueId.InjSubst.t;
  sid_to_value_map : V.typed_value V.SymbolicValueId.Map.t;
}
[@@deriving show]

type borrow_loan_corresp = {
  borrow_to_loan_id_map : V.BorrowId.InjSubst.t;
  loan_to_borrow_id_map : V.BorrowId.InjSubst.t;
}
[@@deriving show]

(* Very annoying: functors only take modules as inputs... *)
module type MatchJoinState = sig
  (** The current context *)
  val ctx : C.eval_ctx

  (** The current loop *)
  val loop_id : V.LoopId.id

  (** The abstractions introduced when performing the matches *)
  val nabs : V.abs list ref
end

(** Split an environment between the fixed abstractions, values, etc. and
    the new abstractions, values, etc.

    Returns: (fixed, new abs, new dummies)
 *)
let ctx_split_fixed_new (fixed_ids : ids_sets) (ctx : C.eval_ctx) :
    C.env * V.abs list * V.typed_value list =
  let is_fresh_did (id : C.DummyVarId.id) : bool =
    not (C.DummyVarId.Set.mem id fixed_ids.dids)
  in
  let is_fresh_abs_id (id : V.AbstractionId.id) : bool =
    not (V.AbstractionId.Set.mem id fixed_ids.aids)
  in
  (* Filter the new abstractions and dummy variables (there shouldn't be any new dummy variable
     though) in the target context *)
  let is_fresh (ee : C.env_elem) : bool =
    match ee with
    | C.EBinding (BVar _, _) | C.EFrame -> false
    | C.EBinding (BDummy bv, _) -> is_fresh_did bv
    | C.EAbs abs -> is_fresh_abs_id abs.abs_id
  in
  let new_eel, filt_env = List.partition is_fresh ctx.env in
  let is_abs ee = match ee with C.EAbs _ -> true | _ -> false in
  let new_absl, new_dummyl = List.partition is_abs new_eel in
  let new_absl =
    List.map
      (fun ee ->
        match ee with C.EAbs abs -> abs | _ -> raise (Failure "Unreachable"))
      new_absl
  in
  let new_dummyl =
    List.map
      (fun ee ->
        match ee with
        | C.EBinding (BDummy _, v) -> v
        | _ -> raise (Failure "Unreachable"))
      new_dummyl
  in
  (filt_env, new_absl, new_dummyl)

let ids_sets_empty_borrows_loans (ids : ids_sets) : ids_sets =
  let { aids; blids = _; borrow_ids = _; loan_ids = _; dids; rids; sids } =
    ids
  in
  let empty = V.BorrowId.Set.empty in
  let ids =
    {
      aids;
      blids = empty;
      borrow_ids = empty;
      loan_ids = empty;
      dids;
      rids;
      sids;
    }
  in
  ids
