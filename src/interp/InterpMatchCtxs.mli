(** This module implements support to match contexts for loops.

    The matching functions are used for instance to compute joins, or to check
    if two contexts are equivalent (modulo conversion). *)

open Values
open Contexts
open Cps
open InterpUtils
open InterpJoinCore

(** Compute various maps linking the abstractions and the borrows/loans they
    contain.

    We compute the map for the [env]. The evaluation context is used only for
    printing purposes.

    Parameters:
    - [explore]: this function is used to filter abstractions. *)
val compute_abs_borrows_loans_maps :
  Meta.span -> (abs -> bool) -> eval_ctx -> env -> abs_borrows_loans_maps

(** Generic functor to implement matching functions between values,
    environments, etc.

    We use it for joins, to check if two environments are convertible, etc. See
    for instance {!MakeJoinMatcher} and {!MakeCheckEquivMatcher}.

    The functor is parameterized by a
    {!module-type:InterpLoopsCore.PrimMatcher}, which implements the non-generic
    part of the match. More precisely, the role of
    {!module-type:InterpLoopsCore.PrimMatcher} is two provide generic functions
    which recursively match two values (by recursively matching the fields of
    ADT values for instance). When it does need to match values in a non-trivial
    manner (if two ADT values don't have the same variant for instance) it calls
    the corresponding specialized function from
    {!module-type:InterpLoopsCore.PrimMatcher}. *)
module MakeMatcher : functor (_ : PrimMatcher) -> Matcher

(** A matcher for joins (we use joins to compute loop fixed points).

    See the explanations for {!MakeMatcher}.

    In case of loop joins:
    - we match *concrete* values
    - we check that the "fixed" abstractions (the abstractions to be framed
    - i.e., the abstractions which are the same in the two environments to join)
      are equal
    - we keep the abstractions which are not in the frame, then merge those
      together (if they have borrows/loans in common) later The join matcher is
      used to match the *concrete* values only. For this reason, we fail on the
      functions which match avalues. *)
module MakeJoinMatcher : functor (_ : MatchJoinState) -> PrimMatcher

(** An auxiliary matcher that we use for two purposes:
    - to check if two contexts are equivalent modulo id substitution (i.e.,
      alpha equivalent) (see {!ctxs_are_equivalent}).
    - to compute a mapping between the borrows and the symbolic values in a
      target context to the values and borrows in a source context (see
      {!match_ctx_with_target}). *)
module MakeCheckEquivMatcher : functor (_ : MatchCheckEquivState) ->
  CheckEquivMatcher

(** Compute whether two contexts are equivalent modulo an identifier
    substitution.

    [fixed_ids]: ids for which we force the mapping to be the identity.

    We also take advantage of the structure of the environments, which should
    have the same prefixes (we check it). See the explanations for
    {!InterpLoopsJoinCtxs.join_ctxs}.

    TODO: explanations.

    The input parameters are:
    - [check_equiv]: if [true], check if the two contexts are equivalent. If
      [false], compute a mapping from the first context to the second context,
      in the sense of [match_ctx_with_target].

    - [fixed_ids]

    - [lookup_shared_value_in_ctx0], [lookup_shared_value_in_ctx1]: The lookup
      functions are used to match the shared values when [check_equiv] is
      [false] (we sometimes use [match_ctxs] on partial environments, meaning we
      have to lookup the shared values in the complete environment, otherwise we
      miss some mappings).

    - [ctx0]
    - [ctx1]

    We return an optional ids map: [Some] if the match succeeded, [None]
    otherwise. *)
val match_ctxs :
  Meta.span ->
  check_equiv:bool ->
  ?check_kind:bool ->
  ?check_can_end:bool ->
  ids_sets ->
  (loan_id -> tvalue) ->
  (loan_id -> tvalue) ->
  eval_ctx ->
  eval_ctx ->
  ids_maps option

(** Compute whether two contexts are equivalent modulo an identifier
    substitution.

    We also take advantage of the structure of the environments, which should
    have the same prefixes (we check it). See the explanations for
    {!InterpLoopsJoinCtxs.join_ctxs}.

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
    - [ctx1] *)
val ctxs_are_equivalent : Meta.span -> ids_sets -> eval_ctx -> eval_ctx -> bool

(** Reorganize a target context so that we can match it with a source context
    (remember that the source context is generally the fixed point context of a
    loop, which results from joins during which we ended the loans which were
    introduced during the loop iterations).

    TODO: remove?

    **Parameters**:
    - [config]
    - [span]
    - [fresh_abs_kind]: the abs kind to use for the freshly introduced
      abstractions
    - [fixed_ids]
    - [src_ctx] *)
val prepare_match_ctx_with_target :
  config -> Meta.span -> abs_kind -> eval_ctx -> cm_fun
