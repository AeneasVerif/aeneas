(** This module implements support to match contexts for loops.

    The matching functions are used for instance to compute joins, or
    to check if two contexts are equivalent (modulo conversion).
 *)

open Values
open Contexts
open Cps
open InterpreterUtils
open InterpreterLoopsCore

(** Compute various maps linking the abstractions and the borrows/loans they contain.

    Parameters:
    - [no_duplicates]: checks that borrows/loans are not referenced more than once
      (see the documentation for {!type:InterpreterLoopsCore.abs_borrows_loans_maps}).
    - [explore]: this function is used to filter abstractions.
    - [env]
 *)
val compute_abs_borrows_loans_maps :
  bool -> (abs -> bool) -> env -> abs_borrows_loans_maps

(** Generic functor to implement matching functions between values, environments,
    etc.

    We use it for joins, to check if two environments are convertible, etc.
    See for instance {!MakeJoinMatcher} and {!MakeCheckEquivMatcher}.

    The functor is parameterized by a {!module-type:InterpreterLoopsCore.PrimMatcher}, which implements the
    non-generic part of the match. More precisely, the role of {!module-type:InterpreterLoopsCore.PrimMatcher} is two
    provide generic functions which recursively match two values (by recursively
    matching the fields of ADT values for instance). When it does need to match
    values in a non-trivial manner (if two ADT values don't have the same
    variant for instance) it calls the corresponding specialized function from
    {!module-type:InterpreterLoopsCore.PrimMatcher}.
 *)
module MakeMatcher : functor (_ : PrimMatcher) -> Matcher

(** A matcher for joins (we use joins to compute loop fixed points).

    See the explanations for {!MakeMatcher}.

    In case of loop joins:
    - we match *concrete* values
    - we check that the "fixed" abstractions (the abstractions to be framed
      - i.e., the abstractions which are the same in the two environments to
      join) are equal
    - we keep the abstractions which are not in the frame, then merge those
      together (if they have borrows/loans in common) later
    The join matcher is used to match the *concrete* values only. For this
    reason, we fail on the functions which match avalues.
 *)
module MakeJoinMatcher : functor (_ : MatchJoinState) -> PrimMatcher

(** An auxiliary matcher that we use for two purposes:
    - to check if two contexts are equivalent modulo id substitution (i.e.,
      alpha equivalent) (see {!ctxs_are_equivalent}).
    - to compute a mapping between the borrows and the symbolic values in a
      target context to the values and borrows in a source context (see
      {!match_ctx_with_target}).
 *)
module MakeCheckEquivMatcher : functor (_ : MatchCheckEquivState) ->
  CheckEquivMatcher

(** Compute whether two contexts are equivalent modulo an identifier substitution.

    [fixed_ids]: ids for which we force the mapping to be the identity.

    We also take advantage of the structure of the environments, which should
    have the same prefixes (we check it). See the explanations for {!InterpreterLoopsJoinCtxs.join_ctxs}.

    TODO: explanations.

    The input parameters are:
    - [check_equiv]: if [true], check if the two contexts are equivalent.
      If [false], compute a mapping from the first context to the second context,
      in the sense of [match_ctx_with_target].

    - [fixed_ids]

    - [lookup_shared_value_in_ctx0], [lookup_shared_value_in_ctx1]:
      The lookup functions are used to match the shared values when [check_equiv]
      is [false] (we sometimes use [match_ctxs] on partial environments, meaning
      we have to lookup the shared values in the complete environment, otherwise
      we miss some mappings).

    - [ctx0]
    - [ctx1]

    We return an optional ids map: [Some] if the match succeeded, [None] otherwise.
 *)
val match_ctxs :
  bool ->
  ids_sets ->
  (loan_id -> typed_value) ->
  (loan_id -> typed_value) ->
  eval_ctx ->
  eval_ctx ->
  ids_maps option

(** Compute whether two contexts are equivalent modulo an identifier substitution.

    We also take advantage of the structure of the environments, which should
    have the same prefixes (we check it). See the explanations for
    {!InterpreterLoopsJoinCtxs.join_ctxs}.

    For instance, the following environments are equivalent:
    {[
      env0 = {
        abs@0 { ML l0 }
        ls -> MB l1 (s2 : loops::List<T>)
        i -> s1 : u32
        abs@1 { MB l0, ML l1 }
      }

      env1 = {
        abs@0 { ML l0 }
        ls -> MB l2 (s4 : loops::List<T>)
        i -> s3 : u32
        abs@2 { MB l0, ML l2 }
      }
    ]}

    We can go from [env0] to [env1] with the substitution:
    {[
      abs_id_subst: { abs@1 -> abs@2 }
      borrow_id_subst: { l1 -> l2 }
      symbolic_id_subst: { s1 -> s3, s2 -> s4 }
    ]}


    Parameters:
    - [fixed_ids]: ids for which we force the mapping to be the identity.
    - [ctx0]
    - [ctx1]
 *)
val ctxs_are_equivalent : ids_sets -> eval_ctx -> eval_ctx -> bool

(** Reorganize a target context so that we can match it with a source context
    (remember that the source context is generally the fixed point context,
    which results from joins during which we ended the loans which
    were introduced during the loop iterations).

   **Parameters**:
   - [config]
   - [loop_id]
   - [fixed_ids]
   - [src_ctx]

 *)
val prepare_match_ctx_with_target :
  config -> LoopId.id -> ids_sets -> eval_ctx -> cm_fun

(** Match a context with a target context.

    This is used to compute application of loop translations: we use this
    to introduce "identity" abstractions upon (re-)entering the loop.

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

   We want to introduce an abstraction [abs@2], which has the same shape as [abs@fp]
   above (the fixed-point abstraction), and which is actually the identity. If we do so,
   we get an environment which is actually also a fixed point (we can collapse
   the dummy variables and [abs@1] to actually retrieve the fixed point we
   computed, and we use the fact that those values and abstractions can't be
   *directly* manipulated unless we end this newly introduced [abs@2], which we
   forbid).

   We match the *fixed point context* with the context upon entering the loop
   by doing the following.

   1. We filter [env_fp] and [env] to remove the newly introduced dummy variables
   and abstractions. We get:

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

   2. We match [filtered_env_fp] with [filtered_env] to compute a map from
   the FP borrows/loans to the current borrows/loans (and also from symbolic values to
   values). Note that we take care to *consider loans and borrows separately*,
   and we ignore the "fixed" abstractions (which are unchanged - we checked that
   when computing the fixed point).
   We get:
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
   values, if they contain borrows - above i points to [s@7], but it should
   be a different symbolic value...).

   Finally, we use the map from symbolic values to values to compute the list of
   input values of the loop: we simply list the values, by order of increasing
   symbolic value id. We *do* use the fixed values (though they are in the frame)
   because they may be *read* inside the loop.

   We can then proceed to finishing the symbolic execution and doing the
   synthesis.

   Rem.: we might reorganize the [tgt_ctx] by ending loans for instance.

   **Parameters**:
   - [config]
   - [loop_id]
   - [is_loop_entry]: [true] if first entry into the loop, [false] if re-entry
     (i.e., continue).
   - [fp_bl_maps]: for the abstractions in the fixed-point (the source context),
     the maps from loans to borrows and borrows to loans, if those abstractions
     are seen as identity abstractions (for every of those abstractions, there
     must be a bijection between the borrows and the loans)
   - [fp_input_svalues]: the list of symbolic values appearing in the fixed
     point (the source context) and which must be instantiated during the match
     (this is the list of input parameters of the loop).
   - [fixed_ids]
   - [src_ctx]
 *)
val match_ctx_with_target :
  config ->
  loop_id ->
  bool ->
  borrow_loan_corresp ->
  symbolic_value_id list ->
  ids_sets ->
  eval_ctx ->
  st_cm_fun
