open Values
open Contexts
open Cps
module SA = SymbolicAst

type proj_kind = LoanProj | BorrowProj

(** Apply a symbolic expansion to a context, by replacing the original
    symbolic value with its expanded value. Is valid only if the expansion
    is *not a borrow* (i.e., an adt...).

    This function does *not* update the synthesis.
*)
val apply_symbolic_expansion_non_borrow :
  Meta.meta -> config -> symbolic_value -> symbolic_expansion -> eval_ctx -> eval_ctx

(** Expand a symhbolic value, without branching *)
val expand_symbolic_value_no_branching :
  Meta.meta -> config -> symbolic_value -> SA.mplace option -> cm_fun

(** Expand a symbolic enumeration (leads to branching if the enumeration has
    more than one variant).

    Parameters:
    - [config]
    - [sv]
    - [sv_place]
    - [cf_branches]: the continuation to evaluate the branches. This continuation
      typically evaluates a [match] statement *after* we have performed the symbolic
      expansion (in particular, we can have one continuation for all the branches).
    - [cf_after_join]: the continuation for *after* the match (we perform a join
      then call it).
 *)
val expand_symbolic_adt :
  Meta.meta -> config -> symbolic_value -> SA.mplace option -> st_cm_fun -> st_m_fun -> m_fun

(** Expand a symbolic boolean.

    Parameters: see {!expand_symbolic_adt}.
    The two parameters of type [st_cm_fun] correspond to the [cf_branches]
    parameter (here, there are exactly two branches).
 *)
val expand_symbolic_bool :
  Meta.meta -> 
  config ->
  symbolic_value ->
  SA.mplace option ->
  st_cm_fun ->
  st_cm_fun ->
  st_m_fun ->
  m_fun

(** Symbolic integers are expanded upon evaluating a [SwitchInt].

    When expanding a boolean upon evaluating an [if ... then ... else ...],
    or an enumeration just before matching over it, we can simply expand the
    boolean/enumeration (generating a list of contexts from which to execute)
    then retry evaluating the [if ... then ... else ...] or the [match]: as
    the scrutinee will then have a concrete value, the interpreter will switch
    to the proper branch.
    
    However, when expanding a "regular" integer for a switch, there is always an
    *otherwise* branch that we can take, for which the integer must remain symbolic
    (because in this branch the scrutinee can take a range of values). We thus
    can't simply expand then retry to evaluate the [switch], because then we
    would loop...
    
    For this reason, we take the list of branches to execute as parameters, and
    directly jump to those branches after the expansion, without reevaluating the
    switch. The continuation is thus for the execution *after* the switch.
 *)
val expand_symbolic_int :
  Meta.meta -> 
  config ->
  symbolic_value ->
  SA.mplace option ->
  integer_type ->
  (scalar_value * st_cm_fun) list ->
  st_cm_fun ->
  st_m_fun ->
  m_fun

(** If this mode is activated through the [config], greedily expand the symbolic
    values which need to be expanded. See {!type:Contexts.config} for more information.
 *)
val greedy_expand_symbolic_values : Meta.meta -> config -> cm_fun
