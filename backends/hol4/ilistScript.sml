open listTheory
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
val _ = BasicProvers.export_rewrites ["len_def"]

(* Return the ith element of a list.

   Remark: we initially added the following case, so that we wouldn't need the
   premise [i < len ls] is [index_eq_EL]:
   “index (i : int) [] = EL (Num i) []”

   TODO: this can be simplified. See the Lean backend.
 *)
val index_def = Define ‘
  index (i : int) (x :: ls) = if i = 0 then x else (if 0 < i then index (i - 1) ls else ARB)
’

(* We use the following theorem as a rewriting theorem for [index]: it performs
   better with the rewritings.

   TODO: we could even write:
   if (0 < i) ∨ (i > 0) ∨ ((0 ≤ i ∨ i >= 0) ∧ (i ≠ 0 ∨ 0 ≠ i)) then ...
 *)
Theorem index_eq:
  (∀x ls. index 0 (x :: ls) = x) ∧
  (∀i x ls. index i (x :: ls) =
    if (0 < i) ∨ (0 ≤ i ∧ i ≠ 0) then index (i - 1) ls
    else (if i = 0 then x else ARB))
Proof
  rw [index_def] >> fs [] >>
  exfalso >> cooper_tac
QED

(* TODO: this can be simplified. See the Lean backend. *)
val update_def = Define ‘
  update ([] : 'a list) (i : int) (y : 'a) : 'a list = [] ∧

  update (x :: ls) (i : int) y =
    if i = 0 then y :: ls else (if 0 < i then x :: update ls (i - 1) y else x :: ls)
’

Theorem update_eq:
  (∀i y. update ([] : 'a list) (i : int) (y : 'a) : 'a list = []) ∧

  (∀x ls y. update (x :: ls) 0 y = y :: ls) ∧

  (∀x ls i y.
   update (x :: ls) i y =
     if (0 < i) ∨ (0 ≤ i ∧ i ≠ 0) then x :: update ls (i - 1) y
     else if i < 0 then x :: ls else y :: ls)
Proof
  rw [update_def] >> fs [] >>
  exfalso >> cooper_tac
QED

Definition drop_def:
  drop (i : int) ([] : 'a list) = [] ∧
  drop (i : int) (x :: ls) =
    if i < 0 then x :: ls
    else if i = 0 then x :: ls
    else drop (i - 1) ls
End

Theorem drop_eq:
  (∀ i. drop i [] = []) ∧
  (∀ ls. drop 0 ls = ls) ∧
  (∀ i x ls. drop i (x :: ls) =
    if (0 < i) ∨ (0 ≤ i ∧ i ≠ 0) then drop (i - 1) ls
    else x :: ls)
Proof
  rw [drop_def] >> fs [] >> try_tac int_tac >>
  Cases_on ‘ls’ >> fs [drop_def]
QED

Theorem len_eq_LENGTH:
  ∀ls. len ls = &(LENGTH ls)
Proof
  Induct_on ‘ls’ >> fs [len_def] >> cooper_tac
QED

Theorem len_pos:
  ∀ls. 0 ≤ len ls
Proof
  strip_tac >>
  qspec_assume ‘ls’ len_eq_LENGTH >>
  cooper_tac
QED

Theorem index_eq_EL:
  ∀(i: int) ls.
    0 ≤ i ⇒
    i < len ls ⇒
    index i ls = EL (Num i) ls
Proof  
  Induct_on ‘ls’ >> rpt strip_tac >> fs [len_def, index_eq] >- int_tac >>
  Cases_on ‘i = 0’ >> fs [] >>
  Cases_on ‘Num i’ >- (int_tac) >> fs [] >>
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
val _ = BasicProvers.export_rewrites ["len_append"]

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

Theorem drop_more_than_length:
  ∀ ls i.
  len ls ≤ i ⇒
  drop i ls = []
Proof
  Induct_on ‘ls’ >>
  rw [drop_def] >>
  qspec_assume ‘ls’ len_pos >> try_tac int_tac >>
  last_x_assum irule >>
  int_tac
QED

(* TODO: prove more theorems, and add rewriting theorems *)

val _ = export_theory ()
