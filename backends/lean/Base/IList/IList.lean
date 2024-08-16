/- Complementary list functions and lemmas which operate on integers rather
   than natural numbers. -/

import Base.Arith
import Base.Utils
import Base.Core

namespace List

-- Small helper
-- We cover a set of cases which might imply inequality, to make sure that using
-- this as the precondition of a `simp` lemma will allow the lemma to get correctly
-- triggered.
-- TODO: there should be something more systematic to do, with discharged procedures
-- or simprocs I guess.
@[simp]
abbrev Int.not_eq (i j : Int) : Prop :=
  i ≠ j ∨ j ≠ i ∨ i < j ∨ j < i

theorem Int.not_eq_imp_not_eq {i j} : Int.not_eq i j → i ≠ j := by
  intro h g
  simp_all

-- Remark: if i < 0, then the result is none
def indexOpt (ls : List α) (i : Int) : Option α :=
  match ls with
  | [] => none
  | hd :: tl => if i = 0 then some hd else indexOpt tl (i - 1)

@[simp] theorem indexOpt_nil : indexOpt ([] : List α) i = none := by simp [indexOpt]
@[simp] theorem indexOpt_zero_cons : indexOpt ((x :: tl) : List α) 0 = some x := by simp [indexOpt]
@[simp] theorem indexOpt_nzero_cons (hne : Int.not_eq i 0) : indexOpt ((x :: tl) : List α) i = indexOpt tl (i - 1) := by simp [indexOpt]; intro; simp_all

-- Remark: if i < 0, then the result is the default element
def index [Inhabited α] (ls : List α) (i : Int) : α :=
  match ls with
  | [] => Inhabited.default
  | x :: tl =>
    if i = 0 then x else index tl (i - 1)

@[simp] theorem index_zero_cons [Inhabited α] : index ((x :: tl) : List α) 0 = x := by simp [index]
@[simp] theorem index_nzero_cons [Inhabited α] (hne : Int.not_eq i 0) : index ((x :: tl) : List α) i = index tl (i - 1) := by simp [index]; intro; simp_all

theorem indexOpt_bounds (ls : List α) (i : Int) :
  ls.indexOpt i = none ↔ i < 0 ∨ ls.length ≤ i :=
  match ls with
  | [] =>
    have : ¬ (i < 0) → 0 ≤ i := by int_tac
    by simp; tauto
  | _ :: tl =>
    have := indexOpt_bounds tl (i - 1)
    if h: i = 0 then
      by
        simp [*]
    else by
      simp [*]
      constructor <;> intros <;>
      casesm* _ ∨ _ <;> -- splits all the disjunctions
      first | left; int_tac | right; int_tac

theorem indexOpt_eq_index [Inhabited α] (ls : List α) (i : Int) :
  0 ≤ i →
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
      apply hi <;> (int_tac)

-- Remark: the list is unchanged if the index is not in bounds (in particular
-- if it is < 0)
def update (ls : List α) (i : Int) (y : α) : List α :=
  match ls with
  | [] => []
  | x :: tl => if i = 0 then y :: tl else x :: update tl (i - 1) y

-- Remark: the whole list is dropped if the index is not in bounds (in particular
-- if it is < 0)
def idrop {α : Type u} (i : Int) (ls : List α) : List α :=
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

section

variable {α : Type u}

def ireplicate {α : Type u} (i : ℤ) (x : α) : List α :=
  if i ≤ 0 then []
  else x :: ireplicate (i - 1) x
termination_by i.toNat
decreasing_by int_decr_tac

def resize (l : List α) (new_len : Int) (x : α) : List α :=
  if new_len ≥ 0 then
    l.itake new_len ++ ireplicate (new_len - l.length) x
  else []

@[simp] theorem update_nil : update ([] : List α) i y = [] := by simp [update]
@[simp] theorem update_zero_cons : update ((x :: tl) : List α) 0 y = y :: tl := by simp [update]
@[simp] theorem update_nzero_cons (hne : Int.not_eq i 0) : update ((x :: tl) : List α) i y = x :: update tl (i - 1) y := by simp [update]; intro; simp_all

@[simp] theorem idrop_nil : idrop i ([] : List α) = [] := by simp [idrop]
@[simp] theorem idrop_zero : idrop 0 (ls : List α) = ls := by cases ls <;> simp [idrop]
@[simp] theorem idrop_nzero_cons (hne : Int.not_eq i 0) : idrop i ((x :: tl) : List α) = idrop (i - 1) tl := by simp [idrop]; intro; simp_all

@[simp] theorem itake_nil : itake i ([] : List α) = [] := by simp [itake]
@[simp] theorem itake_zero : itake 0 (ls : List α) = [] := by cases ls <;> simp [itake]
@[simp] theorem itake_nzero_cons (hne : Int.not_eq i 0) : itake i ((x :: tl) : List α) = x :: itake (i - 1) tl := by simp [itake]; intro; simp_all

@[simp] theorem slice_nil : slice i j ([] : List α) = [] := by simp [slice]
@[simp] theorem slice_zero : slice 0 0 (ls : List α) = [] := by cases ls <;> simp [slice]

@[simp] theorem ireplicate_le (h : i ≤ 0) : ireplicate i x = [] := by rw [ireplicate]; simp [*]
@[simp] theorem ireplicate_zero : ireplicate 0 x = [] := by rw [ireplicate]; simp
@[simp] theorem ireplicate_nzero_cons (hne : 0 < i) : ireplicate i x = x :: ireplicate (i - 1) x := by
  rw [ireplicate]; simp [*]

@[simp]
theorem slice_nzero_cons (i j : Int) (x : α) (tl : List α) (hne : Int.not_eq i 0) :
  slice i j ((x :: tl) : List α) = slice (i - 1) (j - 1) tl := by
  apply Int.not_eq_imp_not_eq at hne
  match tl with
  | [] => simp [slice]; simp [*]
  | hd :: tl =>
    if h: i - 1 = 0 then
      have : i = 1 := by int_tac
      simp [*, slice]
    else
      have hi := slice_nzero_cons (i - 1) (j - 1) hd tl (by simp_all)
      conv => lhs; simp [slice, *]
      conv at hi => lhs; simp [slice, *]
      simp [slice]
      simp [*]

@[simp]
theorem ireplicate_replicate {α : Type u} (l : ℤ) (x : α) (h : 0 ≤ l) :
  ireplicate l x = replicate l.toNat x :=
  if hz: l = 0 then by
    simp [*]
  else by
    have : 0 < l := by int_tac
    have hr := ireplicate_replicate (l - 1) x (by int_tac)
    simp [*]
    have hl : l.toNat = .succ (l.toNat - 1) := by
      cases hl: l.toNat <;> simp_all
    conv => rhs; rw[hl]
    rfl
termination_by l.toNat
decreasing_by int_decr_tac

@[simp]
theorem ireplicate_length {α : Type u} (l : ℤ) (x : α) (h : 0 ≤ l) :
  (ireplicate l x).length = l :=
  if hz: l = 0 then by
    simp [*]
  else by
    have : 0 < l := by int_tac
    have hr := ireplicate_length (l - 1) x (by int_tac)
    simp [*]
termination_by l.toNat
decreasing_by int_decr_tac

@[scalar_tac ireplicate l x]
theorem ireplicate_length_max {α : Type u} (l : ℤ) (x : α) :
  (ireplicate l x).length = max 0 l := by
  if h: l ≤ 0 then
    simp_all
  else
    have : 0 < l := by int_tac
    have hr := ireplicate_length_max (l - 1) x
    simp_all
    int_tac
termination_by l.toNat
decreasing_by int_decr_tac

@[simp, scalar_tac ls.update i x]
theorem length_update (ls : List α) (i : Int) (x : α) : (ls.update i x).length = ls.length := by
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
theorem index_append_beg [Inhabited α] (i : Int) (l0 l1 : List α)
  (_ : 0 ≤ i) (_ : i < l0.length) :
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
  (_ : l0.length ≤ i) (_ : i < l0.length + l1.length) :
  (l0 ++ l1).index i = l1.index (i - l0.length) :=
  match l0 with
  | [] => by simp_all
  | hd :: tl =>
    have : ¬ i = 0 := by simp_all; int_tac
    have := index_append_end (i - 1) tl l1 (by simp_all; int_tac) (by simp_all; int_tac)
    -- TODO: canonize arith expressions
    have : i - 1 - length tl = i - (1 + length tl) := by int_tac
    by simp_all; ring_nf

open Arith in
@[simp] theorem idrop_eq_nil_of_le (hineq : ls.length ≤ i) : idrop i ls = [] := by
  revert i
  induction ls <;> simp [*]
  rename_i hd tl hi
  intro i hineq
  if heq: i = 0 then
    simp [*] at *
    have := tl.length_pos
    omega
  else
    have : 0 < i := by int_tac
    simp [*]
    apply hi
    omega

theorem idrop_length_le (i : Int) (ls : List α) : (ls.idrop i).length ≤ ls.length :=
  match ls with
  | [] => by simp
  | hd :: tl =>
    if h: i = 0 then by simp [*]
    else
      have := idrop_length_le (i - 1) tl
      by simp [*]; omega

@[simp]
theorem idrop_len (i : Int) (ls : List α) (_ : 0 ≤ i) (_ : i ≤ ls.length) :
  (ls.idrop i).length = ls.length - i :=
  match ls with
  | [] => by simp_all; omega
  | hd :: tl =>
    if h: i = 0 then by simp [*]
    else
      have := idrop_len (i - 1) tl (by int_tac) (by simp at *; int_tac)
      by simp [*] at *; int_tac

theorem itake_length_le (i : Int) (ls : List α) : (ls.itake i).length ≤ ls.length :=
  match ls with
  | [] => by simp
  | hd :: tl =>
    if h: i = 0 then by simp [*]
    else
      have := itake_length_le (i - 1) tl
      by simp [*]

@[scalar_tac ls.itake i]
theorem itake_length_eq (i : Int) (ls : List α) :
  (ls.itake i).length = if 0 ≤ i then min (ls.length : Int) i else ls.length := by
  match ls with
  | [] => simp; scalar_tac
  | hd :: tl =>
    if h: i = 0 then simp [*]; scalar_tac
    else
      have := itake_length_eq (i - 1) tl
      simp [*]
      scalar_tac

@[simp]
theorem itake_length (i : Int) (ls : List α) (_ : 0 ≤ i) (_ : i ≤ ls.length) :
  (ls.itake i).length = i :=
  match ls with
  | [] => by simp_all; int_tac
  | hd :: tl =>
    if h: i = 0 then by simp [*]
    else
      have := itake_length (i - 1) tl (by int_tac) (by simp at *; int_tac)
      by simp [*]

@[simp, scalar_tac (l.resize new_len x).length]
theorem resize_length (l : List α) (new_len : Int) (x : α) :
  (l.resize new_len x).length = max 0 new_len := by
  if h: 0 ≤ new_len then
    simp_all [resize]
    scalar_tac
  else
    simp [resize, *]
    scalar_tac

theorem slice_length_le (i j : Int) (ls : List α) : (ls.slice i j).length ≤ ls.length := by
  simp [slice]
  have := ls.idrop_length_le i
  have := (ls.idrop i).itake_length_le (j - i)
  int_tac

@[simp]
theorem index_idrop [Inhabited α] (i : Int) (j : Int) (ls : List α)
  (_ : 0 ≤ i) (_ : 0 ≤ j) (_ : i + j < ls.length) :
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
  (_ : 0 ≤ j) (_ : j < i) (_ : j < ls.length) :
  (ls.itake i).index j = ls.index j :=
  match ls with
  | [] => by simp at *
  | hd :: tl =>
    have : ¬ 0 = i := by int_tac -- TODO: this is slightly annoying
    if h: j = 0 then by
      simp_all
    else by
      simp [*]
      -- TODO: rewriting rule: ¬ i = 0 → 0 ≤ i → 0 < i ?
      have := index_itake (i - 1) (j - 1) tl (by simp at *; int_tac) (by simp at *; int_tac) (by simp at *; int_tac)
      simp [*]

@[simp]
theorem index_slice [Inhabited α] (i j k : Int) (ls : List α)
  (_ : 0 ≤ i) (_ : j ≤ ls.length) (_ : 0 ≤ k) (_ : i + k < j) :
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
  (_ : 0 ≤ j) (_ : j < i) (_ : i ≤ l0.length) :
  ((l0 ++ l1).itake i).index j = l0.index j :=
  match l0 with
  | [] => by
    simp at *
    int_tac
  | hd :: tl =>
    have : ¬ i = 0 := by simp at *; int_tac
    if hj : j = 0 then by simp [*]
    else by
      have := index_itake_append_beg (i - 1) (j - 1) tl l1 (by simp_all; int_tac) (by simp_all) (by simp_all)
      simp [*]

@[simp]
theorem index_itake_append_end [Inhabited α] (i j : Int) (l0 l1 : List α)
  (_ : l0.length ≤ j) (_ : j < i) (_ : i ≤ l0.length + l1.length) :
  ((l0 ++ l1).itake i).index j = l1.index (j - l0.length) :=
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
      have : j - 1 - length tl = j - (1 + length tl) := by int_tac
      simp_all; ring_nf

@[simp]
theorem index_update_ne
  {α : Type u} [Inhabited α] (l: List α) (i: ℤ) (j: ℤ) (x: α) :
   Int.not_eq i j → (l.update i x).index j = l.index j
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
   0 ≤ i → i < l.length →
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

@[simp]
theorem map_update_eq {α : Type u} {β : Type v} (ls : List α) (i : Int) (x : α) (f : α → β) :
  (ls.update i x).map f = (ls.map f).update i (f x) :=
  match ls with
  | [] => by simp
  | hd :: tl =>
    if h : i = 0 then by simp [*]
    else
      have hi := map_update_eq tl (i - 1) x f
      by simp [*]

example (x tl hd : Nat) : x + tl = hd + tl + x - hd := by omega

@[scalar_tac ls.index i]
theorem length_index_le_length_flatten (ls : List (List α)) :
  forall (i : Int), (ls.index i).length ≤ ls.flatten.length := by
  induction ls <;> intro i <;> simp_all
  . rw [List.index]
    simp [default]
  . rename ∀ _, _ => ih
    if hi: i = 0 then
      simp_all
    else
      replace ih := ih (i - 1)
      simp_all
      int_tac

theorem length_flatten_update_eq {α : Type u} (ls : List (List α)) (i : Int) (x : List α)
  (h0 : 0 ≤ i) (h1 : i < ls.length) :
  (ls.update i x).flatten.length + (ls.index i).length = ls.flatten.length + x.length :=
  match ls with
  | [] => by simp at h1; int_tac
  | hd :: tl => by
    simp at h1
    if h : i = 0 then
      simp [*]; int_tac
    else
      have hi := length_flatten_update_eq tl (i - 1) x (by int_tac) (by int_tac)
      simp [*]
      int_tac

@[scalar_tac (ls.update i x).flatten]
theorem length_flatten_update_eq_disj {α : Type u} (ls : List (List α)) (i : Int) (x : List α) :
  i < 0 ∨ ls.length ≤ i ∨
  (ls.update i x).flatten.length + (ls.index i).length = ls.flatten.length + x.length := by
  cases h: (i < 0 : Bool) <;> simp_all
  cases h: (ls.length ≤ i : Bool) <;> simp_all
  rw [length_flatten_update_eq] <;> simp [*]

@[simp]
theorem length_flatten_update_as_int_eq {α : Type u} (ls : List (List α)) (i : Int) (x : List α)
  (h0 : 0 ≤ i) (h1 : i < ls.length) :
  ((ls.update i x).flatten.length : Int) = ls.flatten.length + x.length - (ls.index i).length :=
  match ls with
  | [] => by simp at h1; int_tac
  | hd :: tl => by
    simp at h1
    if h : i = 0 then
      simp [*]; int_tac
    else
      have hi := length_flatten_update_eq tl (i - 1) x (by int_tac) (by int_tac)
      simp [*]
      int_tac

@[simp]
theorem index_map_eq {α : Type u} {β : Type v} [Inhabited α] [Inhabited β]
  (ls : List α) (i : Int) (f : α → β)
  (h0 : 0 ≤ i) (h1 : i < ls.length) :
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
      have : 0 ≤ (i : Int) - 1 ∧ (i : Int) - 1 < tl.length := by simp_all; scalar_tac
      simp [*]

theorem replace_slice_index [Inhabited α] (start end_ : Int) (l nl : List α)
  (_ : 0 ≤ start) (_ : start < end_) (_ : end_ ≤ l.length) (_ : nl.length = end_ - start) :
  let l1 := l.replace_slice start end_ nl
  (∀ i, 0 ≤ i → i < start → l1.index i = l.index i) ∧
  (∀ i, start ≤ i → i < end_ → l1.index i = nl.index (i - start)) ∧
  (∀ i, end_ ≤ i → i < l.length → l1.index i = l.index i)
  := by
  -- let s_end := s.val ++ a.val.idrop r.end_.val
  -- We need those assumptions everywhere
  -- have : 0 ≤ start := by scalar_tac
  have : start ≤ l.length := by int_tac
  simp only [replace_slice]
  split_conjs
  . intro i _ _
    -- Introducing exactly the assumptions we need to make the rewriting work
    have : i < l.length := by int_tac
    simp_all
  . intro i _ _
    have : (List.itake start l).length ≤ i := by simp_all
    have : i < (List.itake start l).length + (nl ++ List.idrop end_ l).length := by
      simp_all; int_tac
    simp_all
  . intro i _ _
    have : 0 ≤ end_ := by scalar_tac
    have : end_ ≤ l.length := by int_tac
    have : (List.itake start l).length ≤ i := by simp_all; int_tac
    have : i < (List.itake start l).length + (nl ++ List.idrop end_ l).length := by simp_all
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

theorem lookup_not_none_imp_length_pos [BEq α] (l : List (α × β)) (key : α)
  (hLookup : l.lookup key ≠ none) :
  0 < l.length := by
  induction l <;> simp_all

end

end List
