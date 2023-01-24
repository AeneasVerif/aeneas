(* Base tactics for the primitives library *)
structure primitivesBaseTacLib =
struct

open HolKernel boolLib bossLib Parse
open boolTheory arithmeticTheory integerTheory intLib listTheory

(* Ignore a theorem.

   To be used in conjunction with {!pop_assum} for instance.
 *)
fun ignore_tac (_ : thm) : tactic = ALL_TAC

val pop_ignore_tac = pop_assum ignore_tac

(* TODO: no exfalso tactic?? *)
val ex_falso : tactic =
  SUBGOAL_THEN “F” (fn th => ASSUME_TAC th >> fs[])

fun qspec_assume x th = qspec_then x assume_tac th
fun qspecl_assume xl th = qspecl_then xl assume_tac th
fun first_qspec_assume x = first_assum (qspec_assume x)
fun first_qspecl_assume xl = first_assum (qspecl_assume xl)



val cooper_tac = COOPER_TAC
val pure_once_rewrite_tac = PURE_ONCE_REWRITE_TAC

(* Dependent rewrites *)
val dep_pure_once_rewrite_tac = dep_rewrite.DEP_PURE_ONCE_REWRITE_TAC
val dep_pure_rewrite_tac = dep_rewrite.DEP_PURE_REWRITE_TAC

end
