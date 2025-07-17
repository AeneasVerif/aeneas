open Cps
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
    - [with_abs_conts]
    - [ctx]
    - [aid0]
    - [aid1] *)
val merge_into_first_abstraction :
  Meta.span ->
  loop_id ->
  abs_kind ->
  bool ->
  bool ->
  eval_ctx ->
  abstraction_id ->
  abstraction_id ->
  eval_ctx * abstraction_id

(** Collapse an environment, merging the duplicated borrows/loans.

    This function simply calls {!collapse_ctx} with the proper merging
    functions.

    We do this because when we join environments, we may introduce duplicated
    loans and borrows. See the explanations for {!join_ctxs}.

    Arguments:
    - [span]
    - [with_abs_conts]
    - [loop_id]
    - [old_ids]
    - [ctx] *)
val collapse_ctx_with_merge :
  Meta.span -> bool -> LoopId.id -> ids_sets -> eval_ctx -> eval_ctx

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
    which are not in the prefix, and this can also lead to borrow duplications.
    For this reason, the environment needs to be collapsed afterwards to get rid
    of those duplicated loans/borrows.

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

    Rem.: in practice, this join works because we take care of pushing new
    values and abstractions *at the end* of the environments, meaning the
    environment prefixes keep the same structure.

    Rem.: assuming that the environment has some structure poses *no soundness
    issue*. It can only make the join fail if the environments actually don't
    have this structure: this is a *completeness issue*.

    Parameters:
    - [loop_id]
    - [fixed_ids]
    - [ctx0]
    - [ctx1] *)
val join_ctxs :
  Meta.span -> loop_id -> ids_sets -> eval_ctx -> eval_ctx -> ctx_or_update

(** Match a context with a target context.

    This is used to compute application of loop translations: we use this to
    introduce "identity" abstractions upon (re-)entering the loop.

    For instance, the fixed point for [list_nth_mut] (see the top of the file)
    is:
    {[
      env_fp = {
        abs@0 { ML l0 }
        ls -> MB l1 (s@3 : loops::List<T>)
        i -> s@4 : u32
        abs@fp {
          MB l0
          ML l1
        }
      }
    ]}

    Upon re-entering the loop, starting from the fixed point, we get the
    following environment:
    {[
       env = {
         abs@0 { ML l0 }
         ls -> MB l5 (s@6 : loops::List<T>)
         i -> s@7 : u32
         abs@1 { MB l0, ML l1 }
         _@1 -> MB l1 (loops::List::Cons (ML l2, ML l3))
         _@2 -> MB l3 (@Box (ML l5))                      // tail
         _@3 -> MB l2 (s@3 : T)                           // hd
      }
    ]}

    We want to introduce an abstraction [abs@2], which has the same shape as
    [abs@fp] above (the fixed-point abstraction), and which is actually the
    identity. If we do so, we get an environment which is actually also a fixed
    point (we can reduce the dummy variables and [abs@1] to actually retrieve
    the fixed point we computed, and we use the fact that those values and
    abstractions can't be *directly* manipulated unless we end this newly
    introduced [abs@2], which we forbid).

    We match the *fixed point context* with the context upon entering the loop
    by doing the following.

    1. We filter [env_fp] and [env] to remove the newly introduced dummy
    variables and abstractions. We get:

    {[
      filtered_env_fp = {
        abs@0 { ML l0 }
        ls -> MB l1 (s@3 : loops::List<T>)
        i -> s@4 : u32
        // removed abs@fp
      }

      filtered_env = {
        abs@0 { ML l0 }
        ls -> MB l5 (s@6 : loops::List<T>)
        i -> s@7 : u32
        // removed abs@1, _@1, etc.
      }
    ]}

    2. We match [filtered_env_fp] with [filtered_env] to compute a map from the
    FP borrows/loans to the current borrows/loans (and also from symbolic values
    to values). Note that we take care to *consider loans and borrows
    separately*, and we ignore the "fixed" abstractions (which are unchanged -
    we checked that when computing the fixed point). We get:
    {[
      borrows_map: { l1 -> l5 } // because we matched [MB l1 ...] with [MB l5 ...]
      loans_map: {} // we ignore abs@0, which is "fixed"
    ]}

    3. We want to introduce an instance of [abs@fp] which is actually the
    identity. From [compute_fixed_point_id_correspondance] and looking at
    [abs@fp], we know we should link the instantiation of loan [l1] with the
    instantiation of loan [l0]. We substitute [l0] with [l5] (following step 2.)
    and introduce a fresh borrow [l6] for [l5] that we use to instantiate [l1].
    We get the following environment:

    {[
      env = {
        abs@0 { ML l0 }
        ls -> MB l6 (s@6 : loops::List<T>)
        i -> s@7 : u32
        abs@1 { MB l0, ML l1 }
        _@1 -> MB l1 (loops::List::Cons (ML l2, ML l3))
        _@2 -> MB l3 (@Box (ML l5))                      // tail
        _@3 -> MB l2 (s@3 : T)                           // hd
        abs@2 { MB l5, ML l6 } // this is actually the identity: l6 = l5
      }
    ]}

    4. As we now have a fixed point (see above comments), we can consider than
    [abs@2] links the current iteration to the last one before we exit. What we
    are interested in is that:
    - upon inserting [abs@2] we re-entered the loop, meaning in the translation
      we need to insert a recursive call to the loop forward function
    - upon ending [abs@2] we need to insert a call to the loop backward function

    Because we want to ignore them, we end the loans in the newly introduced
    [abs@2] abstraction (i.e., [l6]). We get:
    {[
      env = {
        abs@0 { ML l0 }
        ls -> ⊥
        i -> s@7 : u32
        abs@1 { MB l0, ML l1 }
        _@1 -> MB l1 (loops::List::Cons (ML l2, ML l3))
        _@2 -> MB l3 (@Box (ML l5))                      // tail
        _@3 -> MB l2 (s@3 : T)                           // hd
        abs@2 { MB l5 }
      }
    ]}

    TODO: we shouldn't need to end the loans, we should actually remove them
    before inserting the new abstractions (we may have issues with the symbolic
    values, if they contain borrows - above [i] points to [s@7], but it should
    be a different symbolic value...).

    Finally, we use the map from symbolic values to values to compute the list
    of input values of the loop: we simply list the values, by order of
    increasing symbolic value id. We *do* use the fixed values (though they are
    in the frame) because they may be *read* inside the loop.

    We can then proceed to finishing the symbolic execution and doing the
    synthesis.

    Rem.: we might reorganize the [tgt_ctx] by ending loans for instance.
    **Parameters**:
    - [config]
    - [span]
    - [loop_id]
    - [is_loop_entry]: [true] if first entry into the loop, [false] if re-entry
      (i.e., continue).
    - [fp_bl_maps]: for the abstractions in the fixed-point (the source
      context), the maps from loans to borrows and borrows to loans, if those
      abstractions are seen as identity abstractions (for every of those
      abstractions, there must be a bijection between the borrows and the loans)
    - [fp_input_svalues]: the list of symbolic values appearing in the fixed
      point (the source context) and which must be instantiated during the match
      (this is the list of input parameters of the loop).
    - [fixed_ids]
    - [src_ctx] *)
val loop_match_ctx_with_target :
  config ->
  Meta.span ->
  loop_id ->
  bool ->
  borrow_loan_corresp ->
  symbolic_value_id list ->
  ids_sets ->
  eval_ctx ->
  st_cm_fun

(** Join the context at the entry of the loop with the contexts upon reentry
    (upon reaching the [Continue] statement - the goal is to compute a fixed
    point for the loop entry).

    As we may have to end loans in the environments before doing the join, we
    return those updated environments, and the joined environment.

    This function is mostly built on top of {!join_ctxs}.

    Warning: this function should only be used to compute loop fixed points as
    it drops the region abstraction continuations.

    Parameters:
    - [config]
    - [loop_id]
    - [fixed_ids]
    - [old_ctx]
    - [ctxl] *)
val loop_join_origin_with_continue_ctxs :
  config ->
  Meta.span ->
  loop_id ->
  ids_sets ->
  eval_ctx ->
  eval_ctx list ->
  (eval_ctx * eval_ctx list) * eval_ctx
