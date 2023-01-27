open HolKernel boolLib bossLib Parse
open boolTheory arithmeticTheory integerTheory intLib listTheory stringTheory

open primitivesArithTheory primitivesBaseTacLib

(* The following theory contains alternative definitions of functions operating
   on lists like “EL” or “LENGTH”, but this time using integers rather than
   natural numbers.

   By using integers, we make sure we don't have to convert back and forth
   between integers and natural numbers, which is extremely cumbersome in
   the proofs.
 *)

val _ = new_theory "ilist"

val len_def = Define ‘
  len [] : int = 0 /\
  len (x :: ls) : int = 1 + len ls
’

(* Return the ith element of a list.

   Remark: we initially added the following case, so that we wouldn't need the
   premise [i < len ls] is [index_eq_EL]:
   “index (i : int) [] = EL (Num i) []”
 *)
val index_def = Define ‘
  index (i : int) [] = EL (Num i) [] ∧
  index (i : int) (x :: ls) = if i = 0 then x else (if 0 < i then index (i - 1) ls else ARB)
’

val update_def = Define ‘
  update ([] : 'a list) (i : int) (y : 'a) : 'a list = [] ∧

  update (x :: ls) (i : int) y =
    if i = 0 then y :: ls else (if 0 < i then x :: update ls (i - 1) y else x :: ls)
’

Theorem len_eq_LENGTH:
  ∀ls. len ls = &(LENGTH ls)
Proof
  Induct_on ‘ls’ >> fs [len_def] >> cooper_tac
QED

Theorem index_eq_EL:
  ∀(i: int) ls.
    0 ≤ i ⇒
    i < len ls ⇒
    index i ls = EL (Num i) ls
Proof  
  Induct_on ‘ls’ >> rpt strip_tac >> fs [len_def, index_def] >>
  Cases_on ‘i = 0’ >> fs [] >>
  (* TODO: automate *)
  sg ‘0 < i’ >- cooper_tac >> fs [] >>
  Cases_on ‘Num i’ >- (exfalso >> cooper_tac) >> fs [] >>
  last_assum (qspec_assume ‘i - 1’) >>
  pop_assum sg_premise_tac >- cooper_tac >>
  sg ‘n = Num (i - 1)’ >- cooper_tac >> fs [] >>
  last_assum irule >> cooper_tac
QED

Theorem len_append:
  ∀l1 l2. len (l1 ++ l2) = len l1 + len l2
Proof
  rw [len_eq_LENGTH] >> cooper_tac
QED

Theorem append_len_eq:
  (∀l1 l2 l1' l2'.
       len l1 = len l1' ⇒
       (l1 ⧺ l2 = l1' ⧺ l2' ⇔ l1 = l1' ∧ l2 = l2')) ∧
  (∀l1 l2 l1' l2'.
        len l2 = len l2' ⇒
        (l1 ⧺ l2 = l1' ⧺ l2' ⇔ l1 = l1' ∧ l2 = l2'))
Proof
  rw [len_eq_LENGTH] >> fs [APPEND_11_LENGTH]
QED

(* TODO: prove more theorems, and add rewriting theorems *)

val _ = export_theory ()
