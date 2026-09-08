open Values
open Contexts
open Cps
module SA = SymbolicAst

type proj_kind = LoanProj | BorrowProj

(** Apply a symbolic expansion to a context, by replacing the original symbolic
    value with its expanded value. Is valid only if the expansion is *not a
    borrow* (i.e., an adt...).

    This function does *not* update the synthesis. *)
val apply_symbolic_expansion_non_borrow :
  Meta.span -> symbolic_value -> eval_ctx -> symbolic_expansion -> eval_ctx

(** Expand a symhbolic value, without branching *)
val expand_symbolic_value_no_branching :
  Meta.span -> symbolic_value -> SA.mplace option -> cm_fun

(** Expand a symbolic enumeration (leads to branching if the enumeration has
    more than one variant).

    Parameters:
    - [config]
    - [span]
    - [sv]
    - [sv_place] *)
val expand_symbolic_adt :
  Meta.span ->
  symbolic_value ->
  SA.mplace option ->
  eval_ctx ->
  eval_ctx list * (SA.expr list -> SA.expr)

(** Expand a symbolic boolean.

    Parameters: see {!expand_symbolic_adt}. *)
val expand_symbolic_bool :
  Meta.span ->
  symbolic_value ->
  SA.mplace option ->
  eval_ctx ->
  (eval_ctx * eval_ctx) * (SA.expr * SA.expr -> SA.expr)

(** Symbolic integers are expanded upon evaluating a switch over a value.

    Boolean and enumeration switches can simply expand their scrutinee
    (generating a list of contexts from which to execute), then retry the
    switch: the scrutinee will have a concrete value, so the interpreter will
    select the proper branch.

    When expanding a "regular" integer for a switch there is always an
    *fallback* branch. We treat it separately: for this reason we return a pair
    of a list of evaluation contexts (for the explicit branches) and an
    additional evaluation context for the fallback branch. *)
val expand_symbolic_int :
  Meta.span ->
  symbolic_value ->
  SA.mplace option ->
  integer_type ->
  scalar_value list ->
  eval_ctx ->
  (eval_ctx list * eval_ctx) * (SA.expr list * SA.expr -> SA.expr)

(** If this mode is activated through the [config], greedily expand the symbolic
    values which need to be expanded. See {!type:Contexts.config} for more
    information. *)
val greedy_expand_symbolic_values : Meta.span -> cm_fun
