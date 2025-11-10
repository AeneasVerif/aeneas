open Values
open Contexts

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
  abs_kind ->
  can_end:bool ->
  with_abs_conts:bool ->
  eval_ctx ->
  abs_id ->
  abs_id ->
  eval_ctx * abs_id

(** Reduce a context to simplify it, by merging abstractions together for
    instance.

    We use this to compute fixed-points: this is equivalent to a widening
    operation.

    **IMPORTANT**: the big difference between [reduce] and [collapse] is that
    [collapse] operates on an environment with markers (the goal is to eliminate
    them) while [reduce] operates on an environment without markers.

    Arguments:
    - config
    - span
    - sequence: used to save the sequence of merged abstractions, in reverse
      order (the last merge is pushed to the front of the list).
    - with_abs_conts
    - fresh abs kind
    - fixed abstraction ids
    - ctx *)
val reduce_ctx :
  config ->
  Meta.span ->
  ?sequence:(abs_id * abs_id * abs_id) list ref option ->
  with_abs_conts:bool ->
  abs_kind ->
  AbsId.Set.t ->
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
    - sequence: used to save the sequence of merged abstractions, in reverse
      order (the last merge is pushed to the front of the list).
    - loop id
    - fixed ids
    - with_abs_conts
    - ctx *)
val collapse_ctx :
  config ->
  Meta.span ->
  ?sequence:(abs_id * abs_id * abs_id) list ref option ->
  abs_kind ->
  with_abs_conts:bool ->
  eval_ctx ->
  eval_ctx

(** It can happen that we want to join then collapse two environments, then
    apply the exact same sequence of merges resulting from the collapse
    operation to one of the two original environments (before the join).

    [collapse_ctx] allows saving the sequence of merges which have been
    performed for this reason. [collapse_ctx_no_markers_following_sequence] can
    then use this sequence and apply it on the left or right environment. Note
    that this environment *should not have markers*.

    Also note that the sequence of merges the function expects should have the
    merges ordered from the first to perform to the last. This means that if it
    was computed by, e.g., [collapse_ctx], one should reverse the sequence
    before calling [collapse_ctx_no_markers_following_sequence]. *)
val collapse_ctx_no_markers_following_sequence :
  Meta.span ->
  (abs_id * abs_id * abs_id) list ->
  abs_kind ->
  with_abs_conts:bool ->
  eval_ctx ->
  eval_ctx

val convert_fresh_dummy_values_to_abstractions :
  Meta.span -> abs_kind -> DummyVarId.Set.t -> eval_ctx -> eval_ctx
