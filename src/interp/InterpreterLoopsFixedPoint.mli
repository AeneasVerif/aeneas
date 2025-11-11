open Values
open Cps
open Contexts
open InterpreterUtils

(** Prepare the shared loans in the abstractions by moving them to fresh
    abstractions.

    We use this to prepare an evaluation context before computing a fixed point.

    Because a loop iteration might lead to symbolic value expansions and create
    shared loans in shared values inside the *fixed* abstractions, which we want
    to leave unchanged, we introduce some reborrows in the following way:

    {[
      abs'0 { SL l s0 }
      x0 -> SB l
      x1 -> SB l

        ~~>

      abs'0 { SL l s0 }
      x0 -> SB l1
      x1 -> SB l2
      abs'1 { SB l, SL l1 s1 }
      abs'2 { SB l, SL l2 s2 }
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
        SL l0 s0
        SL l1 s1
      }
      abs'1 { SB l0 }
      x -> SB l1
    ]}

    we only introduce a fresh abstraction for [l1].

    The boolean is [with_abs_conts]: if [true] we synthesize continuations
    expressions for the fresh region abstractions we introduce. *)
val prepare_ashared_loans :
  Meta.span -> loop_id option -> with_abs_conts:bool -> Cps.cm_fun

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

val compute_loop_break_context :
  config ->
  Meta.span ->
  LoopId.id ->
  stl_cm_fun ->
  eval_ctx ->
  AbsId.Set.t ->
  DummyVarId.Set.t ->
  (eval_ctx * abs list) option
