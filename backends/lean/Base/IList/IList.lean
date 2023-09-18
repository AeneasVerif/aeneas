/- Complementary list functions and lemmas which operate on integers rather
   than natural numbers. -/

import Std.Data.Int.Lemmas
import Base.Arith
import Base.Utils

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
    have : ¬ (i < 0) → 0 ≤ i := by int_tac
    by simp; tauto
  | _ :: tl =>
    have := indexOpt_bounds tl (i - 1)
    if h: i = 0 then
      by
        simp [*];
        int_tac
    else by
      simp [*]
      constructor <;> intros <;>
      casesm* _ ∨ _ <;> -- splits all the disjunctions
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

def itake (i : Int) (ls : List α) : List α :=
  match ls with
  | [] => []
  | hd :: tl => if i = 0 then [] else hd :: itake (i - 1) tl

def slice (start end_ : Int) (ls : List α) : List α :=
  (ls.idrop start).itake (end_ - start)

def replace_slice (start end_ : Int) (l nl : List α) : List α :=
  let l_beg := l.itake start
  let l_end := l.idrop end_
  l_beg ++ nl ++ l_end

def allP {α : Type u} (l : List α) (p: α → Prop) : Prop :=
  foldr (fun a r => p a ∧ r) True l

def pairwise_rel
  {α : Type u} (rel : α → α → Prop) (l: List α) : Prop
  := match l with
  | [] => True
  | hd :: tl => allP tl (rel hd) ∧ pairwise_rel rel tl

section Lemmas

variable {α : Type u} 

@[simp] theorem update_nil : update ([] : List α) i y = [] := by simp [update]
@[simp] theorem update_zero_cons : update ((x :: tl) : List α) 0 y = y :: tl := by simp [update]
@[simp] theorem update_nzero_cons (hne : i ≠ 0) : update ((x :: tl) : List α) i y = x :: update tl (i - 1) y := by simp [*, update]

@[simp] theorem idrop_nil : idrop i ([] : List α) = [] := by simp [idrop]
@[simp] theorem idrop_zero : idrop 0 (ls : List α) = ls := by cases ls <;> simp [idrop]
@[simp] theorem idrop_nzero_cons (hne : i ≠ 0) : idrop i ((x :: tl) : List α) = idrop (i - 1) tl := by simp [*, idrop]

@[simp] theorem itake_nil : itake i ([] : List α) = [] := by simp [itake]
@[simp] theorem itake_zero : itake 0 (ls : List α) = [] := by cases ls <;> simp [itake]
@[simp] theorem itake_nzero_cons (hne : i ≠ 0) : itake i ((x :: tl) : List α) = x :: itake (i - 1) tl := by simp [*, itake]

@[simp] theorem slice_nil : slice i j ([] : List α) = [] := by simp [slice]
@[simp] theorem slice_zero : slice 0 0 (ls : List α) = [] := by cases ls <;> simp [slice]

@[simp]
theorem slice_nzero_cons (i j : Int) (x : α) (tl : List α) (hne : i ≠ 0) : slice i j ((x :: tl) : List α) = slice (i - 1) (j - 1) tl :=
  match tl with
  | [] => by simp [slice]; simp [*]
  | hd :: tl =>
    if h: i - 1 = 0 then by
      have : i = 1 := by int_tac
      simp [*, slice]
    else
      have := slice_nzero_cons (i - 1) (j - 1) hd tl h
      by
        conv => lhs; simp [slice, *]
        conv at this => lhs; simp [slice, *]
        simp [*, slice]

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

@[simp]
theorem len_map (ls : List α) (f : α → β) : (ls.map f).len = ls.len := by
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

@[simp]
theorem index_append_beg [Inhabited α] (i : Int) (l0 l1 : List α)
  (_ : 0 ≤ i) (_ : i < l0.len) :
  (l0 ++ l1).index i = l0.index i :=
  match l0 with
  | [] => by simp_all; int_tac
  | hd :: tl =>
    if hi : i = 0 then by simp_all
    else by
      have := index_append_beg (i - 1) tl l1 (by int_tac) (by simp_all; int_tac)
      simp_all

@[simp]
theorem index_append_end [Inhabited α] (i : Int) (l0 l1 : List α)
  (_ : l0.len ≤ i) (_ : i < l0.len + l1.len) :
  (l0 ++ l1).index i = l1.index (i - l0.len) :=
  match l0 with
  | [] => by simp_all
  | hd :: tl =>
    have : ¬ i = 0 := by simp_all; int_tac
    have := index_append_end (i - 1) tl l1 (by simp_all; int_tac) (by simp_all; int_tac)
    -- TODO: canonize arith expressions
    have : i - 1 - len tl = i - (1 + len tl) := by int_tac
    by simp_all

open Arith in
@[simp] theorem idrop_eq_nil_of_le (hineq : ls.len ≤ i) : idrop i ls = [] := by
  revert i
  induction ls <;> simp [*]
  rename_i hd tl hi
  intro i hineq
  if heq: i = 0 then
    simp [*] at *
    have := tl.len_pos
    linarith
  else
    have : 0 < i := by int_tac
    simp [*]
    apply hi
    linarith

theorem idrop_len_le (i : Int) (ls : List α) : (ls.idrop i).len ≤ ls.len :=
  match ls with
  | [] => by simp
  | hd :: tl =>
    if h: i = 0 then by simp [*]
    else
      have := idrop_len_le (i - 1) tl
      by simp [*]; linarith

@[simp]
theorem idrop_len (i : Int) (ls : List α) (_ : 0 ≤ i) (_ : i ≤ ls.len) :
  (ls.idrop i).len = ls.len - i :=
  match ls with
  | [] => by simp_all; linarith
  | hd :: tl =>
    if h: i = 0 then by simp [*]
    else
      have := idrop_len (i - 1) tl (by int_tac) (by simp at *; int_tac)
      by simp [*] at *; int_tac

theorem itake_len_le (i : Int) (ls : List α) : (ls.itake i).len ≤ ls.len :=
  match ls with
  | [] => by simp
  | hd :: tl =>
    if h: i = 0 then by simp [*]; int_tac
    else
      have := itake_len_le (i - 1) tl
      by simp [*]

@[simp]
theorem itake_len (i : Int) (ls : List α) (_ : 0 ≤ i) (_ : i ≤ ls.len) : (ls.itake i).len = i :=
  match ls with
  | [] => by simp_all; int_tac
  | hd :: tl =>
    if h: i = 0 then by simp [*]
    else
      have := itake_len (i - 1) tl (by int_tac) (by simp at *; int_tac)
      by simp [*]

theorem slice_len_le (i j : Int) (ls : List α) : (ls.slice i j).len ≤ ls.len := by
  simp [slice]
  have := ls.idrop_len_le i
  have := (ls.idrop i).itake_len_le (j - i)
  int_tac

@[simp]
theorem index_idrop [Inhabited α] (i : Int) (j : Int) (ls : List α)
  (_ : 0 ≤ i) (_ : 0 ≤ j) (_ : i + j < ls.len) :
  (ls.idrop i).index j = ls.index (i + j) :=
  match ls with
  | [] => by simp at *; int_tac
  | hd :: tl =>
    if h: i = 0 then by simp [*]
    else by
      have : ¬ i + j = 0 := by int_tac
      simp [*]
      -- TODO: rewriting rule: ¬ i = 0 → 0 ≤ i → 0 < i ?
      have := index_idrop (i - 1) j tl (by int_tac) (by simp at *; int_tac) (by simp at *; int_tac)
      -- TODO: canonize add/subs?
      have : i - 1 + j = i + j - 1 := by int_tac
      simp [*]

@[simp]
theorem index_itake [Inhabited α] (i : Int) (j : Int) (ls : List α)
  (_ : 0 ≤ j) (_ : j < i) (_ : j < ls.len) :
  (ls.itake i).index j = ls.index j :=
  match ls with
  | [] => by simp at *
  | hd :: tl =>
    have : ¬ 0 = i := by int_tac -- TODO: this is slightly annoying
    if h: j = 0 then by simp [*] at *
    else by
      simp [*]
      -- TODO: rewriting rule: ¬ i = 0 → 0 ≤ i → 0 < i ?
      have := index_itake (i - 1) (j - 1) tl (by simp at *; int_tac) (by simp at *; int_tac) (by simp at *; int_tac)
      simp [*]

@[simp]
theorem index_slice [Inhabited α] (i j k : Int) (ls : List α)
  (_ : 0 ≤ i) (_ : j ≤ ls.len) (_ : 0 ≤ k) (_ : i + k < j) :
  (ls.slice i j).index k = ls.index (i + k) :=
  match ls with
  | [] => by simp at *; int_tac
  | hd :: tl =>
    if h: i = 0 then by
      simp [*, slice] at *
      apply index_itake <;> simp_all
      int_tac
    else by
      have : ¬ i + k = 0 := by int_tac
      simp [*]
      -- TODO: tactics simp_int_tac/simp_scalar_tac?
      have := index_slice (i - 1) (j - 1) k tl (by simp at *; int_tac) (by simp at *; int_tac)
                (by simp at *; int_tac) (by simp at *; int_tac)
      have : (i - 1 + k) = (i + k - 1) := by int_tac -- TODO: canonize add/sub
      simp [*]

@[simp]
theorem index_itake_append_beg [Inhabited α] (i j : Int) (l0 l1 : List α)
  (_ : 0 ≤ j) (_ : j < i) (_ : i ≤ l0.len) :
  ((l0 ++ l1).itake i).index j = l0.index j :=
  match l0 with
  | [] => by
    simp at *
    int_tac
  | hd :: tl =>
    have : ¬ i = 0 := by simp at *; int_tac
    if hj : j = 0 then by simp [*]
    else by
      have := index_itake_append_beg (i - 1) (j - 1) tl l1 (by simp_all; int_tac) (by simp_all) (by simp_all; int_tac)
      simp [*]

@[simp]
theorem index_itake_append_end [Inhabited α] (i j : Int) (l0 l1 : List α)
  (_ : l0.len ≤ j) (_ : j < i) (_ : i ≤ l0.len + l1.len) :
  ((l0 ++ l1).itake i).index j = l1.index (j - l0.len) :=
  match l0 with
  | [] => by
    simp at *
    have := index_itake i j l1 (by simp_all) (by simp_all) (by int_tac)
    try simp [*]
  | hd :: tl =>
    have : ¬ i = 0 := by simp at *; int_tac
    if hj : j = 0 then by simp_all; int_tac -- Contradiction
    else by
      have := index_itake_append_end (i - 1) (j - 1) tl l1 (by simp_all; int_tac) (by simp_all) (by simp_all; int_tac)
      -- TODO: normalization of add/sub
      have : j - 1 - len tl = j - (1 + len tl) := by int_tac
      simp_all

@[simp]
theorem index_update_ne
  {α : Type u} [Inhabited α] (l: List α) (i: ℤ) (j: ℤ) (x: α) :
   j ≠ i → (l.update i x).index j = l.index j
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
        apply index_update_ne; scalar_tac

@[simp]
theorem index_update_eq
  {α : Type u} [Inhabited α] (l: List α) (i: ℤ) (x: α) :
   0 ≤ i → i < l.len →
    (l.update i x).index i = x
  :=
  fun _ _ => match l with
  | [] => by simp at *; scalar_tac
  | hd :: tl =>
    if h: i = 0 then
      by
        simp [*]
    else
      by
        simp [*]
        simp at *
        apply index_update_eq <;> scalar_tac

theorem update_map_eq {α : Type u} {β : Type v} (ls : List α) (i : Int) (x : α) (f : α → β) :
  (ls.update i x).map f = (ls.map f).update i (f x) :=
  match ls with
  | [] => by simp
  | hd :: tl =>
    if h : i = 0 then by simp [*]
    else
      have hi := update_map_eq tl (i - 1) x f
      by simp [*]

theorem len_flatten_update_eq {α : Type u} (ls : List (List α)) (i : Int) (x : List α)
  (h0 : 0 ≤ i) (h1 : i < ls.len) :
  (ls.update i x).flatten.len = ls.flatten.len + x.len - (ls.index i).len :=
  match ls with
  | [] => by simp at h1; int_tac
  | hd :: tl => by
    simp at h1
    if h : i = 0 then simp [*]; int_tac
    else
      have hi := len_flatten_update_eq tl (i - 1) x (by int_tac) (by int_tac)
      simp [*]
      int_tac

@[simp]
theorem index_map_eq {α : Type u} {β : Type v} [Inhabited α] [Inhabited β] (ls : List α) (i : Int) (f : α → β)
  (h0 : 0 ≤ i) (h1 : i < ls.len) :
  (ls.map f).index i = f (ls.index i) :=
  match ls with
  | [] => by simp at h1; int_tac
  | hd :: tl =>
    if h : i = 0 then by
      simp [*]
    else
      have hi := index_map_eq tl (i - 1) f (by int_tac) (by simp at h1; int_tac)
      by
        simp [*]

theorem replace_slice_index [Inhabited α] (start end_ : Int) (l nl : List α)
  (_ : 0 ≤ start) (_ : start < end_) (_ : end_ ≤ l.len) (_ : nl.len = end_ - start) :
  let l1 := l.replace_slice start end_ nl
  (∀ i, 0 ≤ i → i < start → l1.index i = l.index i) ∧
  (∀ i, start ≤ i → i < end_ → l1.index i = nl.index (i - start)) ∧
  (∀ i, end_ ≤ i → i < l.len → l1.index i = l.index i)
  := by
  -- let s_end := s.val ++ a.val.idrop r.end_.val
  -- We need those assumptions everywhere
  -- have : 0 ≤ start := by scalar_tac
  have : start ≤ l.len := by int_tac
  simp only [replace_slice]
  split_conjs
  . intro i _ _
    -- Introducing exactly the assumptions we need to make the rewriting work
    have : i < l.len := by int_tac
    simp_all
  . intro i _ _
    have : (List.itake start l).len ≤ i := by simp_all
    have : i < (List.itake start l).len + (nl ++ List.idrop end_ l).len := by
      simp_all; int_tac
    simp_all
  . intro i _ _
    have : 0 ≤ end_ := by scalar_tac
    have : end_ ≤ l.len := by int_tac
    have : (List.itake start l).len ≤ i := by simp_all; int_tac
    have : i < (List.itake start l).len + (nl ++ List.idrop end_ l).len := by simp_all
    simp_all

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

end Lemmas

end List
