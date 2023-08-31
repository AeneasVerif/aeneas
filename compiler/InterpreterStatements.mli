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
open Cps
open InterpreterExpressions

(** Pop the current frame.

    Drop all the local variables (which has the effect of moving their values to
    dummy variables, after ending the proper borrows of course) but the return
    variable, move the return value out of the return variable, remove all the
    local variables (but preserve the abstractions!), remove the
    {!constructor:C.env_elem.Frame} indicator delimiting the current frame and
    handle the return value to the continuation.

    If the boolean is false, we don't move the return value, and call the
    continuation with [None].
 *)
val pop_frame : C.config -> bool -> (V.typed_value option -> m_fun) -> m_fun

(** Instantiate a function signature, introducing **fresh** abstraction ids and
    region ids. This is mostly used in preparation of function calls, when
    evaluating in symbolic mode of course.

    Note: there are no region parameters, because they should be erased.
 *)
val instantiate_fun_sig :
  C.eval_ctx ->
  T.egeneric_args ->
  T.rtrait_instance_id ->
  LA.fun_sig ->
  LA.inst_fun_sig

(** Helper.

    Create a list of abstractions from a list of regions groups, and insert
    them in the context.

    Parameters:
    - [call_id]
    - [kind]
    - [rgl]: "region group list"
    - [region_can_end]: gives the region groups from which we generate functions
      which can end or not.
    - [compute_abs_avalues]: this function must compute, given an initialized,
      empty (i.e., with no avalues) abstraction, compute the avalues which
      should be inserted in this abstraction before we insert it in the context.
      Note that this function may update the context: it is necessary when
      computing borrow projections, for instance.
    - [ctx]
*)
val create_push_abstractions_from_abs_region_groups :
  (T.RegionGroupId.id -> V.abs_kind) ->
  LA.abs_region_group list ->
  (T.RegionGroupId.id -> bool) ->
  (V.abs -> C.eval_ctx -> C.eval_ctx * V.typed_avalue list) ->
  C.eval_ctx ->
  C.eval_ctx

(** Evaluate a statement *)
val eval_statement : C.config -> LA.statement -> st_cm_fun

(** Evaluate a statement seen as a function body *)
val eval_function_body : C.config -> LA.statement -> st_cm_fun
