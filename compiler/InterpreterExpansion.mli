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
  config ->
  Meta.meta ->
  symbolic_value ->
  symbolic_expansion ->
  eval_ctx ->
  eval_ctx

(** Expand a symhbolic value, without branching *)
val expand_symbolic_value_no_branching :
  config -> Meta.meta -> symbolic_value -> SA.mplace option -> cm_fun

(** Expand a symbolic enumeration (leads to branching if the enumeration has
    more than one variant).

    Parameters:
    - [config]
    - [sv]
    - [sv_place]
 *)
val expand_symbolic_adt :
  config ->
  Meta.meta ->
  symbolic_value ->
  SA.mplace option ->
  eval_ctx ->
  eval_ctx list * (SymbolicAst.expression list option -> eval_result)

(** Expand a symbolic boolean.

    Parameters: see {!expand_symbolic_adt}.
    The two parameters of type [st_cm_fun] correspond to the [cf_branches]
    parameter (here, there are exactly two branches).
 *)
val expand_symbolic_bool :
  config ->
  Meta.meta ->
  symbolic_value ->
  SA.mplace option ->
  eval_ctx ->
  (eval_ctx * eval_ctx)
  * ((SymbolicAst.expression * SymbolicAst.expression) option -> eval_result)

(** Symbolic integers are expanded upon evaluating a [SwitchInt].

    When expanding a boolean upon evaluating an [if ... then ... else ...],
    or an enumeration just before matching over it, we can simply expand the
    boolean/enumeration (generating a list of contexts from which to execute)
    then retry evaluating the [if ... then ... else ...] or the [match]: as
    the scrutinee will then have a concrete value, the interpreter will switch
    to the proper branch.

    When expanding a "regular" integer for a switch there is always an *otherwise*
    branch. We treat it separatly: for this reason we return a pair of a list
    of evaluation contexts (for the branches which are not the otherwise branch)
    and an additional evaluation context for the otherwise branch.

    TODO: update comment
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
  config ->
  Meta.meta ->
  symbolic_value ->
  SA.mplace option ->
  integer_type ->
  (scalar_value (* * st_cm_fun *)) list ->
  eval_ctx ->
  (eval_ctx list * eval_ctx)
  * ((SymbolicAst.expression list * SymbolicAst.expression) option ->
    eval_result)

(** If this mode is activated through the [config], greedily expand the symbolic
    values which need to be expanded. See {!type:Contexts.config} for more information.
 *)
val greedy_expand_symbolic_values : config -> Meta.meta -> cm_fun
