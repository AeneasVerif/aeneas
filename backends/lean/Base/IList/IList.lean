/- Complementary list functions and lemmas which operate on integers rather
   than natural numbers. -/

import Std.Data.Int.Lemmas
import Base.Arith

namespace List

def len (ls : List α) : Int :=
  match ls with
  | [] => 0
  | _ :: tl => 1 + len tl

@[simp] theorem len_nil : len ([] : List α) = 0 := by simp [len]
@[simp] theorem len_cons : len ((x :: tl) : List α) = 1 + len tl := by simp [len]

theorem len_pos : 0 ≤ (ls : List α).len := by
  induction ls <;> simp [*]
  linarith

instance (a : Type u) : Arith.HasIntProp (List a) where
  prop_ty := λ ls => 0 ≤ ls.len
  prop := λ ls => ls.len_pos

-- Remark: if i < 0, then the result is none
def indexOpt (ls : List α) (i : Int) : Option α :=
  match ls with
  | [] => none
  | hd :: tl => if i = 0 then some hd else indexOpt tl (i - 1)

@[simp] theorem indexOpt_nil : indexOpt ([] : List α) i = none := by simp [indexOpt]
@[simp] theorem indexOpt_zero_cons : indexOpt ((x :: tl) : List α) 0 = some x := by simp [indexOpt]
@[simp] theorem indexOpt_nzero_cons (hne : i ≠ 0) : indexOpt ((x :: tl) : List α) i = indexOpt tl (i - 1) := by simp [*, indexOpt]

-- Remark: if i < 0, then the result is the defaul element
def index [Inhabited α] (ls : List α) (i : Int) : α :=
  match ls with
  | [] => Inhabited.default
  | x :: tl =>
    if i = 0 then x else index tl (i - 1)

@[simp] theorem index_zero_cons [Inhabited α] : index ((x :: tl) : List α) 0 = x := by simp [index]
@[simp] theorem index_nzero_cons [Inhabited α] (hne : i ≠ 0) : index ((x :: tl) : List α) i = index tl (i - 1) := by simp [*, index]

theorem indexOpt_bounds (ls : List α) (i : Int) :
  ls.indexOpt i = none ↔ i < 0 ∨ ls.len ≤ i :=
  match ls with
  | [] =>
    have : ¬ (i < 0) → 0 ≤ i := by intro; linarith -- TODO: simplify (we could boost int_tac)
    by simp; tauto
  | _ :: tl =>
    have := indexOpt_bounds tl (i - 1)
    if h: i = 0 then
      by
        simp [*];
        -- TODO: int_tac/scalar_tac should also explore the goal!
        have := tl.len_pos
        linarith
    else by
      simp [*]
      constructor <;> intros <;>
      -- TODO: tactic to split all disjunctions
      rename_i hor <;> cases hor <;>
      first | left; int_tac | right; int_tac

theorem indexOpt_eq_index [Inhabited α] (ls : List α) (i : Int) :
  0 ≤ i →
  i < ls.len →
  ls.indexOpt i = some (ls.index i) :=
  match ls with
  | [] => by simp; intros; linarith
  | hd :: tl =>
    if h: i = 0 then
      by simp [*]
    else
      have hi := indexOpt_eq_index tl (i - 1)
      by simp [*]; intros;  apply hi <;> int_tac

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

section Lemmas

variable {α : Type u} 

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

@[simp] theorem len_append (l1 l2 : List α) : (l1 ++ l2).len = l1.len + l2.len := by
  -- Remark: simp loops here because of the following rewritings:
  -- @Nat.cast_add: ↑(List.length l1 + List.length l2) ==> ↑(List.length l1) + ↑(List.length l2)
  -- Int.ofNat_add_ofNat: ↑(List.length l1) + ↑(List.length l2) ==> ↑(List.length l1 + List.length l2)
  -- TODO: post an issue?
  simp only [len_eq_length]
  simp only [length_append]
  simp only [Int.ofNat_add]

@[simp]
theorem length_update (ls : List α) (i : Int) (x : α) : (ls.update i x).length = ls.length := by
  revert i
  induction ls <;> simp_all [length, update]
  intro; split <;> simp [*]

@[simp]
theorem len_update (ls : List α) (i : Int) (x : α) : (ls.update i x).len = ls.len := by
  simp [len_eq_length]


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

@[simp]
theorem index_ne
  {α : Type u} [Inhabited α] (l: List α) (i: ℤ) (j: ℤ) (x: α) :
   0 ≤ i → i < l.len → 0 ≤ j → j < l.len → j ≠ i →
    (l.update i x).index j = l.index j
  :=
  λ _ _ _ _ _ => match l with
  | [] => by simp at *
  | hd :: tl =>
    if h: i = 0 then
      have : j ≠ 0 := by scalar_tac
      by simp [*]
    else if h : j = 0 then
      have : i ≠ 0 := by scalar_tac
      by simp [*]
    else
      by
        simp [*]
        simp at *
        apply index_ne <;> scalar_tac

@[simp]
theorem index_eq
  {α : Type u} [Inhabited α] (l: List α) (i: ℤ) (x: α) :
   0 ≤ i → i < l.len →
    (l.update i x).index i = x
  :=
  fun _ _ => match l with
  | [] => by simp at *; exfalso; scalar_tac -- TODO: exfalso needed. Son FIXME
  | hd :: tl =>
    if h: i = 0 then
      by
        simp [*]
    else
      by
        simp [*]
        simp at *
        apply index_eq <;> scalar_tac

def allP {α : Type u} (l : List α) (p: α → Prop) : Prop :=
  foldr (fun a r => p a ∧ r) True l

@[simp]
theorem allP_nil {α : Type u} (p: α → Prop) : allP [] p :=
  by simp [allP, foldr]

@[simp]
theorem allP_cons {α : Type u} (hd: α) (tl : List α) (p: α → Prop) :
  allP (hd :: tl) p ↔ p hd ∧ allP tl p
  := by simp [allP, foldr]

def pairwise_rel
  {α : Type u} (rel : α → α → Prop) (l: List α) : Prop
  := match l with
  | [] => True
  | hd :: tl => allP tl (rel hd) ∧ pairwise_rel rel tl

@[simp]
theorem pairwise_rel_nil {α : Type u} (rel : α → α → Prop) :
  pairwise_rel rel []
  := by simp [pairwise_rel]

@[simp]
theorem pairwise_rel_cons {α : Type u} (rel : α → α → Prop) (hd: α) (tl: List α) :
  pairwise_rel rel (hd :: tl) ↔ allP tl (rel hd) ∧ pairwise_rel rel tl
  := by simp [pairwise_rel]

end Lemmas

end List
