/- Complementary list functions and lemmas which operate on integers rather
   than natural numbers. -/

import Std.Data.Int.Lemmas
import Mathlib.Tactic.Linarith
import Base.Arith

namespace List

#check List.get
def len (ls : List α) : Int :=
  match ls with
  | [] => 0
  | _ :: tl => 1 + len tl

-- Remark: if i < 0, then the result is none
def optIndex (i : Int) (ls : List α) : Option α :=
  match ls with
  | [] => none
  | hd :: tl => if i = 0 then some hd else optIndex (i - 1) tl

-- Remark: if i < 0, then the result is the defaul element
def index [Inhabited α] (i : Int) (ls : List α) : α :=
  match ls with
  | [] => Inhabited.default
  | x :: tl =>
    if i = 0 then x else index (i - 1) tl

-- Remark: the list is unchanged if the index is not in bounds (in particular
-- if it is < 0)
def update (ls : List α) (i : Int) (y : α) : List α :=
  match ls with
  | [] => []
  | x :: tl => if i = 0 then y :: tl else x :: update tl (i - 1) y

-- Remark: the whole list is dropped if the index is not in bounds (in particular
-- if it is < 0)
def idrop (i : Int) (ls : List α) : List α :=
  match ls with
  | [] => []
  | x :: tl => if i = 0 then x :: tl else idrop (i - 1) tl

@[simp] theorem len_nil : len ([] : List α) = 0 := by simp [len]
@[simp] theorem len_cons : len ((x :: tl) : List α) = 1 + len tl := by simp [len]

@[simp] theorem index_zero_cons [Inhabited α] : index 0 ((x :: tl) : List α) = x := by simp [index]
@[simp] theorem index_nzero_cons [Inhabited α] (hne : i ≠ 0) : index i ((x :: tl) : List α) = index (i - 1) tl := by simp [*, index]

@[simp] theorem update_nil : update ([] : List α) i y = [] := by simp [update]
@[simp] theorem update_zero_cons : update ((x :: tl) : List α) 0 y = y :: tl := by simp [update]
@[simp] theorem update_nzero_cons (hne : i ≠ 0) : update ((x :: tl) : List α) i y = x :: update tl (i - 1) y := by simp [*, update]

@[simp] theorem idrop_nil : idrop i ([] : List α) = [] := by simp [idrop]
@[simp] theorem idrop_zero : idrop 0 (ls : List α) = ls := by cases ls <;> simp [idrop]
@[simp] theorem idrop_nzero_cons (hne : i ≠ 0) : idrop i ((x :: tl) : List α) = idrop (i - 1) tl := by simp [*, idrop]

theorem len_eq_length (ls : List α) : ls.len = ls.length := by
  induction ls
  . rfl
  . simp [*, Int.ofNat_succ, Int.add_comm]

theorem len_pos : 0 ≤ (ls : List α).len := by
  induction ls <;> simp [*]
  linarith

instance (a : Type u) : Arith.HasIntProp (List a) where
  prop_ty := λ ls => 0 ≤ ls.len
  prop := λ ls => ls.len_pos

@[simp] theorem len_append (l1 l2 : List α) : (l1 ++ l2).len = l1.len + l2.len := by
  -- Remark: simp loops here because of the following rewritings:
  -- @Nat.cast_add: ↑(List.length l1 + List.length l2) ==> ↑(List.length l1) + ↑(List.length l2)
  -- Int.ofNat_add_ofNat: ↑(List.length l1) + ↑(List.length l2) ==> ↑(List.length l1 + List.length l2)
  -- TODO: post an issue?
  simp only [len_eq_length]
  simp only [length_append]
  simp only [Int.ofNat_add]

theorem left_length_eq_append_eq (l1 l2 l1' l2' : List α) (heq : l1.length = l1'.length) :
  l1 ++ l2 = l1' ++ l2' ↔ l1 = l1' ∧ l2 = l2' := by
  revert l1'
  induction l1
  . intro l1'; cases l1' <;> simp [*]
  . intro l1'; cases l1' <;> simp_all; tauto

theorem right_length_eq_append_eq (l1 l2 l1' l2' : List α) (heq : l2.length = l2'.length) :
  l1 ++ l2 = l1' ++ l2' ↔ l1 = l1' ∧ l2 = l2' := by
  have := left_length_eq_append_eq l1 l2 l1' l2'
  constructor <;> intro heq2 <;>
  have : l1.length + l2.length = l1'.length + l2'.length := by
    have : (l1 ++ l2).length = (l1' ++ l2').length := by simp [*]
    simp only [length_append] at this
    apply this
  . simp [heq] at this
    tauto
  . tauto

theorem left_len_eq_append_eq (l1 l2 l1' l2' : List α) (heq : l1.len = l1'.len) :
  l1 ++ l2 = l1' ++ l2' ↔ l1 = l1' ∧ l2 = l2' := by
  simp [len_eq_length] at heq
  apply left_length_eq_append_eq
  assumption

theorem right_len_eq_append_eq (l1 l2 l1' l2' : List α) (heq : l2.len = l2'.len) :
  l1 ++ l2 = l1' ++ l2' ↔ l1 = l1' ∧ l2 = l2' := by
  simp [len_eq_length] at heq
  apply right_length_eq_append_eq
  assumption

open Arith in
theorem idrop_eq_nil_of_le (hineq : ls.len ≤ i) : idrop i ls = [] := by
  revert i
  induction ls <;> simp [*]
  rename_i hd tl hi
  intro i hineq
  if heq: i = 0 then
    simp [*] at *
    have := tl.len_pos
    linarith
  else
    simp at hineq
    have : 0 < i := by int_tac
    simp [*]
    apply hi
    linarith

end List
