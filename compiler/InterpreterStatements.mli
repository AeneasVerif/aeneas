open Types
open Values
open Contexts
open LlbcAst
open Cps

(** Pop the current frame.

    Drop all the local variables (which has the effect of moving their values to
    dummy variables, after ending the proper borrows of course) but the return
    variable, move the return value out of the return variable, remove all the
    local variables (but preserve the abstractions!), remove the
    {!constructor:Contexts.env_elem.EFrame} indicator delimiting the current frame and
    handle the return value to the continuation.

    If the boolean is false, we don't move the return value, and call the
    continuation with [None].
 *)
val pop_frame : Meta.meta -> config -> bool -> (typed_value option -> m_fun) -> m_fun

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
  (RegionGroupId.id -> abs_kind) ->
  abs_region_group list ->
  (RegionGroupId.id -> bool) ->
  (abs -> eval_ctx -> eval_ctx * typed_avalue list) ->
  eval_ctx ->
  eval_ctx

(** Evaluate a statement *)
val eval_statement : config -> statement -> st_cm_fun

(** Evaluate a statement seen as a function body *)
val eval_function_body : Meta.meta -> config -> statement -> st_cm_fun
