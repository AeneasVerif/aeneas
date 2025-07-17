open Values
open Contexts
open InterpreterUtils
open InterpreterLoopsCore

(** Prepare the shared loans in the abstractions by moving them to fresh
    abstractions.

    We use this to prepare an evaluation context before computing a fixed point.

    Because a loop iteration might lead to symbolic value expansions and create
    shared loans in shared values inside the *fixed* abstractions, which we want
    to leave unchanged, we introduce some reborrows in the following way:

    {[
      abs'0 { SL {l0, l1} s0 }
      l0 -> SB l0
      l1 -> SB l1

        ~~>

      abs'0 { SL {l0, l1} s0 }
      l0 -> SB l2
      l1 -> SB l3
      abs'2 { SB l0, SL {l2} s2 }
      abs'3 { SB l1, SL {l3} s3 }
    ]}

    This is sound but leads to information loss. This way, the fixed abstraction
    [abs'0] is never modified because [s0] is never accessed (and thus never
    expanded).

    We do this because it makes it easier to compute joins and fixed points.

    **REMARK**: As a side note, we only reborrow the loan ids whose
    corresponding borrows appear in values (i.e., not in abstractions).

    For instance, if we have:
    {[
      abs'0 {
        SL {l0} s0
        SL {l1} s1
      }
      abs'1 { SB l0 }
      x -> SB l1
    ]}

    we only introduce a fresh abstraction for [l1]. *)
val prepare_ashared_loans : Meta.span -> loop_id option -> Cps.cm_fun

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
  eval_ctx * ids_sets * AbstractionId.id SymbolicAst.region_group_id_map

(** For the abstractions in the fixed point, compute the correspondance between
    the borrows ids and the loans ids, if we want to introduce equivalent
    identity abstractions (i.e., abstractions which do nothing - the input
    borrows are exactly the output loans).

    **Context:**

    When we (re-enter) the loop, we want to introduce identity abstractions
    (i.e., abstractions which actually only introduce fresh identifiers for some
    borrows, to abstract away a bit the borrow graph) which have the same shape
    as the abstractions introduced for the fixed point (see the explanations for
    [match_ctx_with_target]). This allows us to transform the environment into a
    fixed point (again, see the explanations for [match_ctx_with_target]).

    In order to introduce those identity abstractions, we need to figure out,
    for those abstractions, which loans should be linked to which borrows. We do
    this in the following way.

    We match the fixed point environment with the environment upon first entry
    in the loop, and exploit the fact that the fixed point was derived by also
    joining this first entry environment: because of that, the borrows in the
    abstractions introduced for the fixed-point actually exist in this first
    environment (they are not fresh). For [list_nth_mut] (see the explanations
    at the top of the file) we have the following:

    {[
      // Environment upon first entry in the loop
      env0 = {
        abs@0 { ML l0 }
        ls -> MB l0 (s2 : loops::List<T>)
        i -> s1 : u32
      }

      // Fixed-point environment
      env_fp = {
        abs@0 { ML l0 }
        ls -> MB l1 (s3 : loops::List<T>)
        i -> s4 : u32
        abs@fp {
          MB l0 // this borrow appears in [env0]
          ML l1
        }
      }
    ]}

    We filter those environments to remove the non-fixed dummy variables,
    abstractions, etc. in a manner similar to [match_ctx_with_target]. We get:

    {[
      filtered_env0 = {
        abs@0 { ML l0 }
        ls -> MB l0 (s2 : loops::List<T>)
        i -> s1 : u32
      }

      filtered_env_fp = {
        abs@0 { ML l0 }
        ls -> MB l1 (s3 : loops::List<T>)
        i -> s@ : u32
        // removed abs@fp
      }
    ]}

    We then match [filtered_env_fp] with [filtered_env0], taking care to not
    consider loans and borrows in a disjoint manner, and ignoring the fixed
    values, abstractions, loans, etc. We get:
    {[
      borrows_map: { l1 -> l0 } // because we matched [MB l1 ...] with [MB l0 ...] in [ls]
      loans_map: {} // we ignore abs@0, which is "fixed"
    ]}

    From there we deduce that, if we want to introduce an identity abstraction
    with the shape of [abs@fp], we should link [l1] to [l0]. In other words, the
    value retrieved through the loan [l1] is actually the value which has to be
    given back to [l0]. *)
val compute_fixed_point_id_correspondance :
  Meta.span -> ids_sets -> eval_ctx -> eval_ctx -> borrow_loan_corresp

(** Compute the set of "quantified" symbolic value ids in a fixed-point context.

    We compute:
    - the set of symbolic value ids that are freshly introduced
    - the list of input symbolic values *)
val compute_fp_ctx_symbolic_values :
  Meta.span ->
  eval_ctx ->
  eval_ctx ->
  symbolic_value_id_set * symbolic_value list
