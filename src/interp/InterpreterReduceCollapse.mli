open Values
open Contexts
open InterpreterUtils

(** Merge an abstraction into another abstraction in a context.

    This function is similar to {!InterpreterBorrows.merge_into_abstraction}.

    Parameters:
    - [loop_id]
    - [abs_kind]
    - [can_end]
    - [with_abs_conts]
    - [ctx]
    - [aid0]
    - [aid1] *)
val merge_into_first_abstraction :
  Meta.span ->
  loop_id ->
  abs_kind ->
  can_end:bool ->
  with_abs_conts:bool ->
  eval_ctx ->
  abstraction_id ->
  abstraction_id ->
  eval_ctx * abstraction_id

(** Reduce a context to simplify it, by merging abstractions together for
    instance.

    We use this to compute fixed-points: this is equivalent to a widening
    operation. *)
val reduce_ctx :
  config ->
  Meta.span ->
  with_abs_conts:bool ->
  loop_id ->
  ids_sets ->
  eval_ctx ->
  eval_ctx

(** Collapse an environment, merging the duplicated borrows/loans.

    This function simply calls {!collapse_ctx} with the proper merging
    functions.

    We do this because when we join environments, we may introduce duplicated
    loans and borrows. See the explanations for {!join_ctxs}.

    Arguments:
    - config
    - span
    - loop id
    - fixed ids
    - with_abs_conts
    - ctx *)
val collapse_ctx_with_merge :
  config ->
  Meta.span ->
  LoopId.id ->
  ids_sets ->
  with_abs_conts:bool ->
  eval_ctx ->
  eval_ctx
