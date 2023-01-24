(* Base tactics for the primitives library *)
structure primitivesBaseTacLib =
struct

open HolKernel boolLib bossLib Parse
open boolTheory arithmeticTheory integerTheory intLib listTheory

(* Ignore a theorem.

   To be used in conjunction with {!pop_assum} for instance.
 *)
fun IGNORE_TAC (_ : thm) : tactic = ALL_TAC

val POP_IGNORE_TAC = POP_ASSUM IGNORE_TAC

end
