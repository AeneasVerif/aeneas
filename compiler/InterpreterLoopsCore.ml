(** Core definitions for the [IntepreterLoops*] *)

open Types
open Values
open Contexts
open InterpreterUtils
open Errors

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

(** Union Find *)
module UF = UnionFind.Make (UnionFind.StoreMap)

(** A small utility -

    Rem.: some environments may be ill-formed (they may contain several times
    the same loan or borrow - this happens for instance when merging
    environments). This is the reason why we use sets in some places (for
    instance, [borrow_to_abs] maps to a *set* of ids).
*)
type abs_borrows_loans_maps = {
  abs_ids : AbstractionId.id list;
  abs_to_borrows : BorrowId.Set.t AbstractionId.Map.t;
  abs_to_loans : BorrowId.Set.t AbstractionId.Map.t;
  abs_to_borrows_loans : BorrowId.Set.t AbstractionId.Map.t;
  borrow_to_abs : AbstractionId.Set.t BorrowId.Map.t;
  loan_to_abs : AbstractionId.Set.t BorrowId.Map.t;
  borrow_loan_to_abs : AbstractionId.Set.t BorrowId.Map.t;
}

(** See {!module:Aeneas.InterpreterLoopsMatchCtxs.MakeMatcher} and [Matcher].

    This module contains primitive match functions to instantiate the generic
    {!module:Aeneas.InterpreterLoopsMatchCtxs.MakeMatcher} functor.

    Remark: all the functions receive as input the left context and the right context.
    This is useful for printing, lookups, and also in order to check the ended
    regions.
 *)
module type PrimMatcher = sig
  val span : Meta.span
  val match_etys : eval_ctx -> eval_ctx -> ety -> ety -> ety
  val match_rtys : eval_ctx -> eval_ctx -> rty -> rty -> rty

  (** The input primitive values are not equal *)
  val match_distinct_literals :
    eval_ctx -> eval_ctx -> ety -> literal -> literal -> typed_value

  (** The input ADTs don't have the same variant *)
  val match_distinct_adts :
    eval_ctx -> eval_ctx -> ety -> adt_value -> adt_value -> typed_value

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
    eval_ctx ->
    eval_ctx ->
    (typed_value -> typed_value -> typed_value) ->
    ety ->
    borrow_id ->
    borrow_id ->
    borrow_id

  (** The input parameters are:
      - [ty]
      - [bid0]: first borrow id
      - [bv0]: first borrowed value
      - [bid1]
      - [bv1]
      - [bv]: the result of matching [bv0] with [bv1]
  *)
  val match_mut_borrows :
    eval_ctx ->
    eval_ctx ->
    ety ->
    borrow_id ->
    typed_value ->
    borrow_id ->
    typed_value ->
    typed_value ->
    borrow_id * typed_value

  (** Parameters:
      [ty]
      [ids0]
      [ids1]
      [v]: the result of matching the shared values coming from the two loans
   *)
  val match_shared_loans :
    eval_ctx ->
    eval_ctx ->
    ety ->
    loan_id_set ->
    loan_id_set ->
    typed_value ->
    loan_id_set * typed_value

  val match_mut_loans :
    eval_ctx -> eval_ctx -> ety -> loan_id -> loan_id -> loan_id

  (** There are no constraints on the input symbolic values *)
  val match_symbolic_values :
    eval_ctx -> eval_ctx -> symbolic_value -> symbolic_value -> symbolic_value

  (** Match a symbolic value with a value which is not symbolic.

      If the boolean is [true], it means the symbolic value comes from the
      *left* environment. Otherwise it comes from the right environment (it
      is important when throwing exceptions, for instance when we need to
      end loans in one of the two environments).
   *)
  val match_symbolic_with_other :
    eval_ctx -> eval_ctx -> bool -> symbolic_value -> typed_value -> typed_value

  (** Match a bottom value with a value which is not bottom.

      If the boolean is [true], it means the bottom value comes from the
      *left* environment. Otherwise it comes from the right environment (it
      is important when throwing exceptions, for instance when we need to
      end loans in one of the two environments).
   *)
  val match_bottom_with_other :
    eval_ctx -> eval_ctx -> bool -> typed_value -> typed_value

  (** The input ADTs don't have the same variant *)
  val match_distinct_aadts :
    eval_ctx ->
    eval_ctx ->
    rty ->
    adt_avalue ->
    rty ->
    adt_avalue ->
    rty ->
    typed_avalue

  (** Parameters:
      [ty0]
      [pm0]
      [bid0]
      [ty1]
      [pm1]
      [bid1]
      [ty]: result of matching ty0 and ty1
   *)
  val match_ashared_borrows :
    eval_ctx ->
    eval_ctx ->
    rty ->
    proj_marker ->
    borrow_id ->
    rty ->
    proj_marker ->
    borrow_id ->
    rty ->
    typed_avalue

  (** Parameters:
      [ty0]
      [pm0]
      [bid0]
      [av0]
      [ty1]
      [pm1]
      [bid1]
      [av1]
      [ty]: result of matching ty0 and ty1
      [av]: result of matching av0 and av1
   *)
  val match_amut_borrows :
    eval_ctx ->
    eval_ctx ->
    rty ->
    proj_marker ->
    borrow_id ->
    typed_avalue ->
    rty ->
    proj_marker ->
    borrow_id ->
    typed_avalue ->
    rty ->
    typed_avalue ->
    typed_avalue

  (** Parameters:
      [ty0]
      [pm0]
      [ids0]
      [v0]
      [av0]
      [ty1]
      [pm1]
      [ids1]
      [v1]
      [av1]
      [ty]: result of matching ty0 and ty1
      [v]:  result of matching v0 and v1
      [av]: result of matching av0 and av1
   *)
  val match_ashared_loans :
    eval_ctx ->
    eval_ctx ->
    rty ->
    proj_marker ->
    loan_id_set ->
    typed_value ->
    typed_avalue ->
    rty ->
    proj_marker ->
    loan_id_set ->
    typed_value ->
    typed_avalue ->
    rty ->
    typed_value ->
    typed_avalue ->
    typed_avalue

  (** Parameters:
      [ty0]
      [pm0]
      [id0]
      [av0]
      [ty1]
      [pm1]
      [id1]
      [av1]
      [ty]: result of matching ty0 and ty1
      [av]: result of matching av0 and av1
   *)
  val match_amut_loans :
    eval_ctx ->
    eval_ctx ->
    rty ->
    proj_marker ->
    borrow_id ->
    typed_avalue ->
    rty ->
    proj_marker ->
    borrow_id ->
    typed_avalue ->
    rty ->
    typed_avalue ->
    typed_avalue

  (** Match two arbitrary avalues whose constructors don't match (this function
      is typically used to raise the proper exception).
   *)
  val match_avalues :
    eval_ctx -> eval_ctx -> typed_avalue -> typed_avalue -> typed_avalue
end

module type Matcher = sig
  val span : Meta.span

  (** Match two values.

      Rem.: this function raises exceptions of type {!Aeneas.InterpreterLoopsCore.ValueMatchFailure}.
   *)
  val match_typed_values :
    eval_ctx -> eval_ctx -> typed_value -> typed_value -> typed_value

  (** Match two avalues.

      Rem.: this function raises exceptions of type {!Aeneas.InterpreterLoopsCore.ValueMatchFailure}.
   *)
  val match_typed_avalues :
    eval_ctx -> eval_ctx -> typed_avalue -> typed_avalue -> typed_avalue
end

(** See {!module:InterpreterLoopsMatchCtxs.MakeCheckEquivMatcher} and
    {!module-type:InterpreterLoopsCore.CheckEquivMatcher}.

    Very annoying: functors only take modules as inputs...
 *)
module type MatchCheckEquivState = sig
  val span : Meta.span

  (** [true] if we check equivalence between contexts, [false] if we match
      a source context with a target context. *)
  val check_equiv : bool

  val rid_map : RegionId.InjSubst.t ref

  (** Substitution for the loan and borrow ids - used only if [check_equiv] is true *)
  val blid_map : BorrowId.InjSubst.t ref

  (** Substitution for the borrow ids - used only if [check_equiv] is false *)
  val borrow_id_map : BorrowId.InjSubst.t ref

  (** Substitution for the loans ids - used only if [check_equiv] is false *)
  val loan_id_map : BorrowId.InjSubst.t ref

  val sid_map : SymbolicValueId.InjSubst.t ref
  val sid_to_value_map : typed_value SymbolicValueId.Map.t ref
  val aid_map : AbstractionId.InjSubst.t ref
  val lookup_shared_value_in_ctx0 : BorrowId.id -> typed_value
  val lookup_shared_value_in_ctx1 : BorrowId.id -> typed_value
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
  sid_to_value_map : typed_value SymbolicValueId.Map.t;
}
[@@deriving show]

type borrow_loan_corresp = {
  borrow_to_loan_id_map : BorrowId.InjSubst.t;
  loan_to_borrow_id_map : BorrowId.InjSubst.t;
}
[@@deriving show]

(* Very annoying: functors only take modules as inputs... *)
module type MatchJoinState = sig
  (** The current loop *)
  val loop_id : LoopId.id

  (** The abstractions introduced when performing the matches *)
  val nabs : abs list ref

  val span : Meta.span
end

(** Split an environment between the fixed abstractions, values, etc. and
    the new abstractions, values, etc.

    Returns: (fixed, new abs, new dummies)
 *)
let ctx_split_fixed_new (span : Meta.span) (fixed_ids : ids_sets)
    (ctx : eval_ctx) : env * abs list * typed_value list =
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
  let is_abs ee = match ee with EAbs _ -> true | _ -> false in
  let new_absl, new_dummyl = List.partition is_abs new_eel in
  let new_absl =
    List.map
      (fun ee ->
        match ee with
        | EAbs abs -> abs
        | _ -> craise __FILE__ __LINE__ span "Unreachable")
      new_absl
  in
  let new_dummyl =
    List.map
      (fun ee ->
        match ee with
        | EBinding (BDummy _, v) -> v
        | _ -> craise __FILE__ __LINE__ span "Unreachable")
      new_dummyl
  in
  (filt_env, new_absl, new_dummyl)

let ids_sets_empty_borrows_loans (ids : ids_sets) : ids_sets =
  let { aids; blids = _; borrow_ids = _; loan_ids = _; dids; rids; sids } =
    ids
  in
  let empty = BorrowId.Set.empty in
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
