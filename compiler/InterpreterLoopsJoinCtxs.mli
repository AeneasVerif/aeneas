open Values
open Contexts
open InterpreterUtils
open InterpreterLoopsCore

(** Merge an abstraction into another abstraction in a context.

    This function is similar to {!InterpreterBorrows.merge_into_abstraction}.
    
    Parameters:
    - [loop_id]
    - [abs_kind]
    - [can_end]
    - [ctx]
    - [aid0]
    - [aid1]
 *)
val merge_into_abstraction :
  Meta.meta ->
  loop_id ->
  abs_kind ->
  bool ->
  eval_ctx ->
  abstraction_id ->
  abstraction_id ->
  eval_ctx * abstraction_id

(** Join two contexts.

    We use this to join the environments at loop (re-)entry to progressively
    compute a fixed point.

    We make the hypothesis (and check it) that the environments have the same
    prefixes (same variable ids, same abstractions, etc.). The prefix of
    variable and abstraction ids is given by the [fixed_ids] identifier sets. We
    check that those prefixes are the same (the dummy variables are the same,
    the abstractions are the same), match the values mapped to by the variables
    which are not dummy, then group the additional dummy variables/abstractions
    together. In a sense, the [fixed_ids] define a frame (in a separation logic
    sense).

    Note that when joining the values mapped to by the non-dummy variables, we
    may introduce duplicated borrows. Also, we don't match the abstractions
    which are not in the prefix, and this can also lead to borrow
    duplications. For this reason, the environment needs to be collapsed
    afterwards to get rid of those duplicated loans/borrows.

    For instance, if we have:
    {[
      fixed = { abs0 }

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

    We get:
    {[
      join env0 env1 = {
        abs0 { ML l0 } (* abs0 is fixed: we simply check it is equal in env0 and env1 *)
        l -> MB l2 s2
        abs1 { MB l0, ML l1 } (* abs1 is new: we keep it unchanged *)
        abs2 { MB l0, MB l1, ML l2 } (* Introduced when joining on the "l" variable *)
      }
    ]}

    Rem.: in practice, this join works because we take care of pushing new values
    and abstractions *at the end* of the environments, meaning the environment
    prefixes keep the same structure.

    Rem.: assuming that the environment has some structure poses *no soundness
    issue*. It can only make the join fail if the environments actually don't have
    this structure: this is a *completeness issue*.
    
    Parameters:
    - [loop_id]
    - [fixed_ids]
    - [ctx0]
    - [ctx1]
  *)
val join_ctxs : Meta.meta -> loop_id -> ids_sets -> eval_ctx -> eval_ctx -> ctx_or_update

(** Join the context at the entry of the loop with the contexts upon reentry
    (upon reaching the [Continue] statement - the goal is to compute a fixed
    point for the loop entry).

    As we may have to end loans in the environments before doing the join,
    we return those updated environments, and the joined environment.
    
    This function is mostly built on top of {!join_ctxs}.
    
    Parameters:
    - [config]
    - [loop_id]
    - [fixed_ids]
    - [old_ctx]
    - [ctxl]
 *)
val loop_join_origin_with_continue_ctxs :
  Meta.meta ->
  config ->
  loop_id ->
  ids_sets ->
  eval_ctx ->
  eval_ctx list ->
  (eval_ctx * eval_ctx list) * eval_ctx
