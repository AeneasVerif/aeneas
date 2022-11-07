module T = Types
module PV = PrimitiveValues
module V = Values
module LA = LlbcAst
module E = Expressions
module C = Contexts
module Subst = Substitute
module L = Logging
module Inv = Invariants
module S = SynthesizeSymbolic
open Cps
open InterpreterPaths

(** Evaluate an operand.

    Reorganize the context, then evaluate the operand.

    **Warning**: this function shouldn't be used to evaluate a list of
    operands (for a function call, for instance): we must do *one* reorganization
    of the environment, before evaluating all the operands at once.
    Use {!eval_operands} instead.
 *)
val eval_operand : C.config -> E.operand -> (V.typed_value -> m_fun) -> m_fun

(** Evaluate several operands at once. *)
val eval_operands :
  C.config -> E.operand list -> (V.typed_value list -> m_fun) -> m_fun

(** Evaluate an rvalue which is not a global.

    Transmits the computed rvalue to the received continuation.
 *)
val eval_rvalue_not_global :
  C.config -> E.rvalue -> ((V.typed_value, eval_error) result -> m_fun) -> m_fun

(** Evaluate a fake read (update the context so that we can read a place) *)
val eval_fake_read : C.config -> E.place -> cm_fun
