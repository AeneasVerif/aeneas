module T = Types
module PV = PrimitiveValues
module V = Values
module E = Expressions
module C = Contexts
module Subst = Substitute
module L = Logging
module Inv = Invariants
module S = SynthesizeSymbolic
module SA = SymbolicAst
open Cps
open InterpreterBorrows

type proj_kind = LoanProj | BorrowProj

(** Expand a symbolic boolean *)
val expand_symbolic_bool :
  C.config -> V.symbolic_value -> SA.mplace option -> m_fun -> m_fun -> m_fun

(** Expand a symbolic value.
    
    Parameters:
    - [config]
    - [allow_branching]: if [true] we can branch (by expanding enumerations with
      stricly more than one variant), otherwise we can't.
    - [sv]
    - [sv_place]
 *)
val expand_symbolic_value :
  C.config -> bool -> V.symbolic_value -> SA.mplace option -> cm_fun

(** Symbolic integers are expanded upon evaluating a [switch], when the integer
    is not an enumeration discriminant.
    Note that a discriminant is never symbolic: we evaluate discriminant values
    upon evaluating [eval_discriminant], which always generates a concrete value
    (because if we call it on a symbolic enumeration, we expand the enumeration
    *then* evaluate the discriminant). This is how we can spot "regular" switches
    over integers.

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
  C.config ->
  V.symbolic_value ->
  SA.mplace option ->
  T.integer_type ->
  (V.scalar_value * m_fun) list ->
  m_fun ->
  m_fun

(** See {!expand_symbolic_value} *)
val expand_symbolic_value_no_branching :
  C.config -> V.symbolic_value -> SA.mplace option -> cm_fun

(** If this mode is activated through the [config], greedily expand the symbolic
    values which need to be expanded. See {!C.config} for more information.
 *)
val greedy_expand_symbolic_values : C.config -> cm_fun
