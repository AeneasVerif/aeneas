open Values
open Cps
open Contexts
open InterpUtils

type loop_entry_result =
  | CurrentLoopReentry
  | PropagatedContinueToOuter of int
  | NonReentryExit
  | UnitResult

(** Exposed for focused regression tests and for later exit-propagation code to
    reuse the same fixed-point entry classification. *)
val classify_loop_entry_result : statement_eval_res -> loop_entry_result

type loop_exit_result =
  | CurrentLoopBreak
  | PropagatedLoopBreak of int
  | PropagatedLoopContinue of int
  | PropagatedLoopReturn
  | NotLoopExit
  | UnitLoopResult

(** Exposed for focused regression tests and for later exit-context collection
    code to reuse the same relative-depth classification. *)
val classify_loop_exit_result : statement_eval_res -> loop_exit_result

(** Compute a fixed-point for the context at the entry of the loop. We also
    return:
    - the sets of fixed ids
    - the map from region group id to the corresponding abstraction appearing in
      the fixed point (this is useful to compute the return type of the loop
      backward functions for instance). Note that this is a partial map: the
      loop doesn't necessarily introduce an abstraction for each input region of
      the function.

    Rem.: the list of symbolic values should be computable by simply exploring
    the fixed point environment and listing all the symbolic values we find. In
    the future, we might want to do something more precise, by listing only the
    values which are read or modified (some symbolic values may be ignored). *)
val compute_loop_entry_fixed_point :
  config ->
  Meta.span ->
  loop_id ->
  (* This function is the function to evaluate the loop body (eval_statement applied
     to the proper arguments). We need to take it as input because [compute_loop_entry_fixed_point]
     is mutually recursive with [eval_statement], but doesn't live in the same module. *)
  Cps.stl_cm_fun ->
  eval_ctx ->
  eval_ctx * ids_sets

type break_ctx =
  | NoBreak  (** The loop doesn't contain any break *)
  | Single
      (** There is a single break statement, so we don't join the break contexts
      *)
  | Multiple of (eval_ctx * abs list)  (** We joined multiple break contexts *)

type propagated_exit_kind =
  | PropagatedBreakExit of int
  | PropagatedContinueExit of int
  | PropagatedReturnExit

type propagated_exit_ctx = {
  exit_kind : propagated_exit_kind;
  exit_ctx : eval_ctx;
  exit_abs : abs list;
}

type loop_exit_contexts = {
  normal_break : break_ctx;
  propagated_exits : propagated_exit_ctx list;
}

(** Exposed for focused regression tests and for callers that need the same
    per-kind/per-depth partitioning as [compute_loop_exit_contexts]. *)
val group_by_propagated_exit_kind :
  (propagated_exit_kind * 'a) list -> (propagated_exit_kind * 'a list) list

val compute_loop_exit_contexts :
  config ->
  Meta.span ->
  LoopId.id ->
  stl_cm_fun ->
  eval_ctx ->
  AbsId.Set.t ->
  DummyVarId.Set.t ->
  loop_exit_contexts
