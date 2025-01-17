/- Complementary list functions and lemmas which operate on integers rather
   than natural numbers. -/

import Base.Arith
import Base.Utils
import Base.Core

namespace List

open Arith

def indexOpt (ls : List α) (i : Nat) : Option α :=
  match ls with
  | [] => none
  | hd :: tl => if i = 0 then some hd else indexOpt tl (i - 1)

@[simp] theorem indexOpt_nil : indexOpt ([] : List α) i = none := by simp [indexOpt]
@[simp] theorem indexOpt_zero_cons : indexOpt ((x :: tl) : List α) 0 = some x := by simp [indexOpt]
@[simp] theorem indexOpt_nzero_cons (hne : Nat.not_eq i 0) : indexOpt ((x :: tl) : List α) i = indexOpt tl (i - 1) := by simp [indexOpt]; intro; simp_all

def index [Inhabited α] (ls : List α) (i : Nat) : α :=
  match ls with
  | [] => Inhabited.default
  | x :: tl =>
    if i = 0 then x else index tl (i - 1)

@[simp] theorem index_nil [Inhabited α] : @index α _ [] i = Inhabited.default := by simp [index]
@[simp] theorem index_zero_cons (x : α) (tl : List α) [Inhabited α] : index ((x :: tl) : List α) 0 = x := by simp [index]
@[simp] theorem index_nzero_cons (x : α) (tl : List α) (i : Nat) [Inhabited α] (hne : Nat.not_eq i 0) : index ((x :: tl) : List α) i = index tl (i - 1) := by simp [index]; intro; simp_all

theorem indexOpt_bounds (ls : List α) (i : Nat) :
  ls.indexOpt i = none ↔ i < 0 ∨ ls.length ≤ i := by
  match ls with
  | [] => simp
  | _ :: tl =>
    have := indexOpt_bounds tl (i - 1)
    if h: i = 0 then simp [*]
    else
      simp [*]
      omega

theorem indexOpt_eq_index [Inhabited α] (ls : List α) (i : Nat) :
  i < ls.length →
  ls.indexOpt i = some (ls.index i) :=
  match ls with
  | [] => by simp
  | hd :: tl =>
    if h: i = 0 then
      by simp [*]
    else by
      have hi := indexOpt_eq_index tl (i - 1)
      simp [*]; intros
      -- TODO: there seems to be syntax errors if we don't put the parentheses below??
      apply hi; int_tac

-- Remark: the list is unchanged if the index is not in bounds
def update (ls : List α) (i : Nat) (y : α) : List α :=
  match ls with
  | [] => []
  | x :: tl => if i = 0 then y :: tl else x :: update tl (i - 1) y

def slice (start end_ : Nat) (ls : List α) : List α :=
  (ls.drop start).take (end_ - start)

def replace_slice (start end_ : Nat) (l nl : List α) : List α :=
  let l_beg := l.take start
  let l_end := l.drop end_
  l_beg ++ nl ++ l_end

def allP {α : Type u} (l : List α) (p: α → Prop) : Prop :=
  foldr (fun a r => p a ∧ r) True l

def pairwise_rel
  {α : Type u} (rel : α → α → Prop) (l: List α) : Prop
  := match l with
  | [] => True
  | hd :: tl => allP tl (rel hd) ∧ pairwise_rel rel tl

section

variable {α : Type u}

def resize (l : List α) (new_len : Nat) (x : α) : List α :=
  if new_len ≥ 0 then
    l.take new_len ++ replicate (new_len - l.length) x
  else []

@[simp] theorem update_nil i y : update ([] : List α) i y = [] := by simp [update]
@[simp] theorem update_zero_cons x tl y : update ((x :: tl) : List α) 0 y = y :: tl := by simp [update]
@[simp] theorem update_nzero_cons x tl i y (hne : Nat.not_eq i 0) : update ((x :: tl) : List α) i y = x :: update tl (i - 1) y := by simp [update]; intro; simp_all

@[simp] theorem drop_nzero_cons i x tl (hne : Nat.not_eq i 0) : drop i ((x :: tl) : List α) = drop (i - 1) tl := by cases i <;> simp_all [drop]

@[simp] theorem take_nzero_cons i x tl (hne : Nat.not_eq i 0) : take i ((x :: tl) : List α) = x :: take (i - 1) tl := by cases i <;> simp_all

@[simp] theorem slice_nil i j : slice i j ([] : List α) = [] := by simp [slice]
@[simp] theorem slice_zero ls : slice 0 0 (ls : List α) = [] := by cases ls <;> simp [slice]

@[simp] theorem replicate_nzero_cons i (x : List α) (hne : Nat.not_eq i 0) : replicate i x = x :: replicate (i - 1) x := by
  cases i <;> simp_all [replicate]

@[simp]
theorem slice_nzero_cons (i j : Nat) (x : α) (tl : List α) (hne : Nat.not_eq i 0) :
  slice i j ((x :: tl) : List α) = slice (i - 1) (j - 1) tl := by
  apply Nat.not_eq_imp_not_eq at hne
  induction i <;> cases j <;> simp_all [slice]

@[simp, scalar_tac replicate l x]
theorem replicate_length {α : Type u} (l : Nat) (x : α) :
  (replicate l x).length = l := by
  induction l <;> simp_all

@[simp, scalar_tac ls.update i x]
theorem length_update (ls : List α) (i : Nat) (x : α) : (ls.update i x).length = ls.length := by
  revert i
  induction ls <;> simp_all [length, update]
  intro; split <;> simp [*]

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

@[simp]
theorem index_append_beg [Inhabited α] (i : Nat) (l0 l1 : List α) (_ : i < l0.length) :
  (l0 ++ l1).index i = l0.index i := by
  match l0 with
  | [] => simp_all
  | hd :: tl =>
    if hi : i = 0 then simp_all
    else
      have := index_append_beg (i - 1) tl l1 (by simp_all; int_tac)
      simp_all

@[simp]
theorem index_append_end [Inhabited α] (i : Nat) (l0 l1 : List α)
  (_ : l0.length ≤ i) :
  (l0 ++ l1).index i = l1.index (i - l0.length) :=
  match l0 with
  | [] => by simp_all
  | hd :: tl =>
    have : ¬ i = 0 := by simp_all; int_tac
    have := index_append_end (i - 1) tl l1 (by simp_all; int_tac)
    -- TODO: canonize arith expressions
    have : i - 1 - length tl = i - (1 + length tl) := by int_tac
    by simp_all; ring_nf

@[scalar_tac ls.drop i]
theorem drop_length_is_le (i : Nat) (ls : List α) : (ls.drop i).length ≤ ls.length :=
  match ls with
  | [] => by simp
  | hd :: tl =>
    if h: i = 0 then by simp [*]
    else
      have := drop_length_is_le (i - 1) tl
      by simp [*]; omega

@[simp, scalar_tac ls.drop i]
theorem length_drop_eq (i : Nat) (ls : List α) :
  (ls.drop i).length = ls.length - i := by
  induction ls <;> simp_all

@[scalar_tac ls.take i]
theorem take_length_is_le (i : Nat) (ls : List α) : (ls.take i).length ≤ ls.length := by
  induction ls <;> simp_all

attribute [scalar_tac l.take i] length_take

@[simp, scalar_tac l.resize new_len x]
theorem resize_length (l : List α) (new_len : Nat) (x : α) :
  (l.resize new_len x).length = new_len := by
  induction l <;> simp_all [resize]
  int_tac

@[simp] theorem slice_zero_j (l : List α) : l.slice 0 j = l.take j := by simp [slice]

theorem slice_length_le (i j : Nat) (ls : List α) : (ls.slice i j).length ≤ ls.length := by
  simp [slice]

theorem slice_length (i j : Nat) (ls : List α) : (ls.slice i j).length = min (ls.length - i) (j - i) := by
  simp [slice]; int_tac

@[simp]
theorem index_drop [Inhabited α] (i : Nat) (j : Nat) (ls : List α) :
  (ls.drop i).index j = ls.index (i + j) := by
  revert i
  induction ls
  . intro i; simp_all
  . intro i; cases i <;> simp_all

@[simp]
theorem index_take_same [Inhabited α] (i : Nat) (j : Nat) (ls : List α)
  (_ : j < i) (_ : j < ls.length) :
  (ls.take i).index j = ls.index j := by
  revert i j
  induction ls
  . intro i j; simp_all
  . intro i j h0 h1; cases i <;> simp_all
    cases j <;> simp_all

@[simp]
theorem index_slice [Inhabited α] (i j k : Nat) (ls : List α)
  (_ : j ≤ ls.length) (_ : i + k < j) :
  (ls.slice i j).index k = ls.index (i + k) := by
  revert i j
  induction ls
  . intro i j; simp_all
  . intro i j h0 h1
    simp_all [slice]
    rw [index_take_same] <;> first | simp_all | int_tac
    int_tac

@[simp]
theorem index_take_append_beg [Inhabited α] (i j : Nat) (l0 l1 : List α)
  (_ : j < i) (_ : i ≤ l0.length) :
  ((l0 ++ l1).take i).index j = l0.index j := by
  revert i j l1
  induction l0 <;> simp_all
  intros i j l1
  cases i <;> simp_all
  cases j <;> simp_all

@[simp]
theorem index_update_neq
  {α : Type u} [Inhabited α] (l: List α) (i: Nat) (j: Nat) (x: α) :
   Nat.not_eq i j → (l.update i x).index j = l.index j
  :=
  λ _ => match l with
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
        simp_all
        apply index_update_neq; scalar_tac

@[simp]
theorem index_update_eq
  {α : Type u} [Inhabited α] (l: List α) (i: Nat) (x: α) :
  i < l.length → (l.update i x).index i = x
  := by
  revert i
  induction l <;> simp_all
  intro i h
  cases i <;> simp_all

@[simp]
theorem map_update_eq {α : Type u} {β : Type v} (ls : List α) (i : Nat) (x : α) (f : α → β) :
  (ls.update i x).map f = (ls.map f).update i (f x) :=
  match ls with
  | [] => by simp
  | hd :: tl =>
    if h : i = 0 then by simp [*]
    else
      have hi := map_update_eq tl (i - 1) x f
      by simp [*]

-- TODO: we need "composite" patterns for scalar_tac here
theorem length_index_le_length_flatten (ls : List (List α)) :
  forall (i : Nat), (ls.index i).length ≤ ls.flatten.length := by
  induction ls <;> intro i <;> simp_all [default]
  cases i <;> simp_all
  rename ∀ _, _ => ih
  rename Nat => i
  replace ih := ih i
  int_tac

theorem length_flatten_update_eq {α : Type u} (ls : List (List α)) (i : Nat) (x : List α)
  (h1 : i < ls.length) :
  (ls.update i x).flatten.length + (ls.index i).length = ls.flatten.length + x.length := by
  revert i
  induction ls <;> intro i <;> simp_all [default]
  cases i <;> simp_all
  . int_tac
  . rename Nat => i
    rename ∀ _, _ => ih
    replace ih := ih i
    int_tac

@[scalar_tac (ls.update i x).flatten]
theorem length_flatten_update_eq_disj {α : Type u} (ls : List (List α)) (i : Nat) (x : List α) :
  i < 0 ∨ ls.length ≤ i ∨
  (ls.update i x).flatten.length + (ls.index i).length = ls.flatten.length + x.length := by
  cases h: (i < 0 : Bool) <;> simp_all only [not_lt_zero', decide_false, Bool.false_eq_true, not_false_eq_true, neq_imp]
  cases h: (ls.length ≤ i : Bool) <;> simp_all only [decide_eq_false_iff_not, not_le, false_or, decide_eq_true_eq, true_or]
  rw [length_flatten_update_eq] <;> simp [*]

theorem length_flatten_update_as_int_eq {α : Type u} (ls : List (List α)) (i : Nat) (x : List α)
  (h1 : i < ls.length) :
  ((ls.update i x).flatten.length : Nat) = ls.flatten.length + x.length - (ls.index i).length := by
  int_tac

@[simp]
theorem index_map_eq {α : Type u} {β : Type v} [Inhabited α] [Inhabited β]
  (ls : List α) (i : Nat) (f : α → β)
  (h1 : i < ls.length) :
  (ls.map f).index i = f (ls.index i) := by
  revert i; induction ls <;> simp_all
  intro i h
  cases i <;> simp_all

@[simp]
theorem index_nat_map_eq {α : Type u} {β : Type v} [Inhabited α] [Inhabited β]
  (ls : List α) (i : Nat) (f : α → β)
  (h1 : i < ls.length) :
  (ls.map f).index i = f (ls.index i) := by
  match ls with
  | [] => simp at h1
  | hd :: tl =>
    if h : i = 0 then
      simp [*]
    else
      have hi := index_nat_map_eq tl (i - 1) f (by simp at h1; int_tac)
      have : (i : Nat) - 1 < tl.length := by simp_all; scalar_tac
      simp [*]

theorem replace_slice_index [Inhabited α] (start end_ : Nat) (l nl : List α)
  (_ : start < end_) (_ : end_ ≤ l.length) (_ : nl.length = end_ - start) :
  let l1 := l.replace_slice start end_ nl
  (∀ i, i < start → l1.index i = l.index i) ∧
  (∀ i, start ≤ i → i < end_ → l1.index i = nl.index (i - start)) ∧
  (∀ i, end_ ≤ i → i < l.length → l1.index i = l.index i)
  := by
  -- We need those assumptions everywhere
  have : start ≤ l.length := by int_tac
  simp only [replace_slice]
  split_conjs
  . intro i _
    -- Introducing exactly the assumptions we need to make the rewriting work
    have : i < l.length := by int_tac
    simp_all
  . intro i _ _
    have : (List.take start l).length ≤ i := by simp_all
    have : i < (List.take start l).length + (nl ++ List.drop end_ l).length := by
      simp_all; int_tac
    simp_all
    have : i - start < nl.length := by int_tac
    simp_all
  . intro i _ _
    have : 0 ≤ end_ := by scalar_tac
    have : end_ ≤ l.length := by int_tac
    have : (List.take start l).length ≤ i := by int_tac
    have := index_append_end i (take start l ++ nl) (drop end_ l) (by simp; int_tac)
    simp_all
    congr
    int_tac

@[simp]
theorem allP_nil {α : Type u} (p: α → Prop) : allP [] p :=
  by simp [allP, foldr]

@[simp]
theorem allP_cons {α : Type u} (hd: α) (tl : List α) (p: α → Prop) :
  allP (hd :: tl) p ↔ p hd ∧ allP tl p
  := by simp [allP, foldr]

@[simp]
theorem pairwise_rel_nil {α : Type u} (rel : α → α → Prop) :
  pairwise_rel rel []
  := by simp [pairwise_rel]

@[simp]
theorem pairwise_rel_cons {α : Type u} (rel : α → α → Prop) (hd: α) (tl: List α) :
  pairwise_rel rel (hd :: tl) ↔ allP tl (rel hd) ∧ pairwise_rel rel tl
  := by simp [pairwise_rel]

theorem lookup_not_none_imp_length_pos [BEq α] (l : List (α × β)) (key : α)
  (hLookup : l.lookup key ≠ none) :
  0 < l.length := by
  induction l <;> simp_all

end

@[simp]
theorem list_update_index_eq α [Inhabited α] (x : List α) (i : ℕ) :
  x.update i (x.index i) = x := by
  revert i
  induction x
  . simp
  . intro i
    dcases hi: 0 < i <;> simp_all

end List
