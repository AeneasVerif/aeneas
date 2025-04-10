/- Complementary functions and lemmas for the `List` type -/

import Mathlib.Data.List.GetD
import Aeneas.ScalarTac
import Aeneas.Utils
import Aeneas.SimpLemmas
import Aeneas.Nat
import Aeneas.SimpLists.Init
import Aeneas.Std.Primitives

namespace List -- We do not use the `Aeneas` namespace on purpose

open Aeneas
open Aeneas.ScalarTac
open Aeneas.Simp

attribute [scalar_tac_simps] List.length_nil List.length_cons List.length_append List.length_reverse
                            List.get!_eq_getElem! List.get?_eq_getElem?

def set_opt (l : List α) (i : Nat) (x : Option α) : List α :=
  match l with
  | [] => l
  | hd :: tl => if i = 0 then Option.getD x hd :: tl else hd :: set_opt tl (i-1) x

attribute [simp] getElem?_cons_zero getElem!_cons_zero
@[simp] theorem getElem?_cons_nzero (hne : Nat.not_eq i 0) : getElem? ((x :: tl) : List α) i = getElem? tl (i - 1) := by cases i <;> simp_all
@[simp] theorem getElem!_cons_nzero (x : α) (tl : List α) (i : Nat) [Inhabited α] (hne : Nat.not_eq i 0) : getElem! ((x :: tl) : List α) i = getElem! tl (i - 1) := by cases i <;> simp_all

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

@[simp] theorem set_cons_nzero x tl i (hne : Nat.not_eq i 0) y : set ((x :: tl) : List α) i y = x :: set tl (i - 1) y := by cases i <;> simp_all

@[simp] theorem drop_cons_nzero i x tl (hne : Nat.not_eq i 0) : drop i ((x :: tl) : List α) = drop (i - 1) tl := by cases i <;> simp_all [drop]

@[simp] theorem take_cons_nzero i x tl (hne : Nat.not_eq i 0) : take i ((x :: tl) : List α) = x :: take (i - 1) tl := by cases i <;> simp_all

@[simp] theorem slice_nil i j : slice i j ([] : List α) = [] := by simp [slice]
@[simp] theorem slice_zero ls : slice 0 0 (ls : List α) = [] := by cases ls <;> simp [slice]

@[simp] theorem replicate_cons_nzero i (x : List α) (hne : Nat.not_eq i 0) : replicate i x = x :: replicate (i - 1) x := by
  cases i <;> simp_all [replicate]

@[simp] theorem set_opt_nil i y : set_opt ([] : List α) i y = [] := by simp [set_opt]
@[simp] theorem set_opt_zero_cons x tl y : set_opt ((x :: tl) : List α) 0 y = y.getD x :: tl := by simp [set_opt]
@[simp] theorem set_opt_cons_nzero x tl i y (hne : Nat.not_eq i 0) : set_opt ((x :: tl) : List α) i y = x :: set_opt tl (i - 1) y := by simp [set_opt]; intro; simp_all

@[simp]
theorem slice_cons_nzero (i j : Nat) (x : α) (tl : List α) (hne : Nat.not_eq i 0) :
  slice i j ((x :: tl) : List α) = slice (i - 1) (j - 1) tl := by
  apply Nat.not_eq_imp_not_eq at hne
  induction i <;> cases j <;> simp_all [slice]

@[simp, scalar_tac_simps]
theorem replicate_length {α : Type u} (l : Nat) (x : α) :
  (replicate l x).length = l := by
  induction l <;> simp_all

@[simp]
theorem getElem!_replicate {α : Type u} [Inhabited α] (a : α) {n i : ℕ} (h : i < n) :
  (List.replicate n a)[i]! = a := by
  simp only [getElem!_eq_getElem?_getD, length_replicate, h, getElem?_eq_getElem, getElem_replicate,
    Option.getD_some]

@[simp]
theorem set_getElem! {α} [Inhabited α] (l : List α) (i : Nat) :
  l.set i l[i]! = l := by
  revert i; induction l <;> simp_all
  rename_i hd tail hi
  intro i
  cases i <;> simp_all

attribute [scalar_tac_simps] length_set

@[simp, scalar_tac_simps]
theorem length_set_opt {α} (l : List α) (i : Nat) (x : Option α):
  (l.set_opt i x).length = l.length := by
  revert i
  induction l <;> simp_all
  rename_i hd tl hi
  intro i
  cases i <;> simp_all

theorem left_length_eq_append_eq (l1 l2 l1' l2' : List α) (heq : l1.length = l1'.length) :
  l1 ++ l2 = l1' ++ l2' ↔ l1 = l1' ∧ l2 = l2' := by
  revert l1'
  induction l1
  . intro l1'; cases l1' <;> simp [*]
  . intro l1'; cases l1' <;> simp_all

theorem right_length_eq_append_eq (l1 l2 l1' l2' : List α) (heq : l2.length = l2'.length) :
  l1 ++ l2 = l1' ++ l2' ↔ l1 = l1' ∧ l2 = l2' := by
  have := left_length_eq_append_eq l1 l2 l1' l2'
  constructor <;> intro heq2 <;>
  have : l1.length + l2.length = l1'.length + l2'.length := by
    have : (l1 ++ l2).length = (l1' ++ l2').length := by simp [*]
    simp only [length_append] at this
    apply this
  . simp only [heq, add_left_inj] at this
    tauto
  . tauto

@[simp]
theorem getElem!_append_left [Inhabited α] (l0 l1 : List α) (i : Nat) (h : i < l0.length) :
  (l0 ++ l1)[i]! = l0[i]! := by
  have := @getElem?_append_left _ l0 l1 i h
  simp_all

@[simp]
theorem getElem!_append_right [Inhabited α] (l0 l1 : List α) (i : Nat)
  (h : l0.length ≤ i) :
  (l0 ++ l1)[i]! = l1[i - l0.length]! := by
  have := @getElem?_append_right _ l0 l1 i h
  simp_all

@[scalar_tac_simps]
theorem drop_length_is_le (i : Nat) (ls : List α) : (ls.drop i).length ≤ ls.length :=
  match ls with
  | [] => by simp
  | hd :: tl =>
    if h: i = 0 then by simp [*]
    else
      have := drop_length_is_le (i - 1) tl
      by simp only [Nat.not_eq, ne_eq, not_false_eq_true, neq_imp, not_lt_zero', false_or, true_or,
        or_self, drop_cons_nzero, length_drop, length_cons, tsub_le_iff_right, h]; omega

attribute [simp, simp_lists_simps] drop_of_length_le
attribute [scalar_tac_simps] length_drop

@[scalar_tac_simps]
theorem take_length_is_le (i : Nat) (ls : List α) : (ls.take i).length ≤ ls.length := by
  induction ls <;> simp_all

attribute [scalar_tac_simps] length_take

@[simp, scalar_tac_simps]
theorem resize_length (l : List α) (new_len : Nat) (x : α) :
  (l.resize new_len x).length = new_len := by
  induction l <;> simp_all [resize]
  scalar_tac

@[simp] theorem slice_zero_j (l : List α) : l.slice 0 j = l.take j := by simp [slice]

theorem slice_length_le (i j : Nat) (ls : List α) : (ls.slice i j).length ≤ ls.length := by
  simp [slice]

@[scalar_tac_simps]
theorem slice_length (i j : Nat) (ls : List α) : (ls.slice i j).length = min (ls.length - i) (j - i) := by
  simp [slice]; scalar_tac

@[simp]
theorem getElem?_slice (i j k : Nat) (ls : List α)
  (_ : j ≤ ls.length) (_ : i + k < j) :
  (ls.slice i j)[k]? = ls[i + k]? := by
  revert i j
  induction ls
  . intro i j; simp_all
  . intro i j h0 h1
    simp_all [slice]
    have : k < j - i := by scalar_tac
    simp [*]

@[simp]
theorem getElem!_slice [Inhabited α] (i j k : Nat) (ls : List α)
  (_ : j ≤ ls.length) (_ : i + k < j) :
  (ls.slice i j)[k]! = ls[i + k]! := by
  have := getElem?_slice i j k ls
  simp_all

@[simp]
theorem getElem?_take_append_beg (i j : Nat) (l0 l1 : List α)
  (_ : j < i) (_ : i ≤ l0.length) :
  getElem? ((l0 ++ l1).take i) j = getElem? l0 j := by
  revert i j l1
  induction l0 <;> simp_all
  intros i j l1
  cases i <;> simp_all
  cases j <;> simp_all
  rename_i tail hi n n1
  intros
  have : n1 < tail.length := by scalar_tac
  rw [hi n] <;> simp [*]

@[simp]
theorem getElem!_take_append_beg [Inhabited α] (i j : Nat) (l0 l1 : List α)
  (_ : j < i) (_ : i ≤ l0.length) :
  getElem! ((l0 ++ l1).take i) j = getElem! l0 j := by
  have := getElem?_take_append_beg i j l0 l1
  simp_all

@[simp]
theorem getElem!_drop [Inhabited α] (i : Nat) (j : Nat) (ls : List α) :
  getElem! (ls.drop i) j = getElem! ls (i + j) := by
  have := @getElem?_drop _ ls i j
  simp_all

@[simp]
theorem getElem?_take_same (i : Nat) (j : Nat) (ls : List α)
  (_ : j < i) (_ : j < ls.length) :
  getElem? (ls.take i) j = getElem? ls j := by
  simp [getElem?_take, *]

@[simp]
theorem getElem!_take_same [Inhabited α] (i : Nat) (j : Nat) (ls : List α)
  (_ : j < i) (_ : j < ls.length) :
  getElem! (ls.take i) j = getElem! ls j := by
  simp [getElem?_take_same, *]

@[simp]
theorem getElem?_set_neq
  {α : Type u} (l: List α) (i: Nat) (j: Nat) (x: α)
  (h : Nat.not_eq i j) : getElem? (l.set i x) j = getElem? l j
  := by
  simp [getElem?_set]
  intro
  simp_all

@[simp, simp_lists_simps]
theorem getElem!_set_neq
  {α : Type u} [Inhabited α] (l: List α) (i: Nat) (j: Nat) (x: α)
  (h : Nat.not_eq i j) : getElem! (l.set i x) j = getElem! l j
  := by
  have := getElem?_set_neq l i j x h
  simp_all

@[simp]
theorem getElem!_set_self
  {α : Type u} [Inhabited α] (l: List α) (i: Nat) (x: α)
  (h : i < l.length) : getElem! (l.set i x) i = x
  := by
  simp [*]

@[simp_lists_simps]
theorem getElem!_set_self'
  {α : Type u} [Inhabited α] (l: List α) (i i': Nat) (x: α)
  (h : i' < l.length ∧ i = i') : getElem! (l.set i x) i' = x
  := by
  simp only [getElem!_set_self, *]

-- TODO: we need "composite" patterns for scalar_tac here
theorem length_getElem!_le_length_flatten (ls : List (List α)) :
  forall (i : Nat), (getElem! ls i).length ≤ ls.flatten.length := by
  induction ls <;> intro i <;> simp_all [default]
  cases i <;> simp_all
  rename ∀ _, _ => ih
  rename Nat => i
  replace ih := ih i
  scalar_tac

theorem length_flatten_set_eq {α : Type u} (ls : List (List α)) (i : Nat) (x : List α)
  (h1 : i < ls.length) :
  (ls.set i x).flatten.length + (ls[i]!).length = ls.flatten.length + x.length := by
  revert i
  induction ls <;> intro i <;> simp_all [default]
  cases i <;> simp_all
  . scalar_tac
  . rename Nat => i
    rename ∀ _, _ => ih
    intro hi
    replace ih := ih i hi
    scalar_tac

@[scalar_tac (ls.set i x).flatten]
theorem length_flatten_set_eq_disj {α : Type u} (ls : List (List α)) (i : Nat) (x : List α) :
  ls.length ≤ i ∨
  (ls.set i x).flatten.length + (ls[i]!).length = ls.flatten.length + x.length := by
  cases h: (ls.length ≤ i : Bool) <;> simp_all only [decide_eq_false_iff_not, not_le, false_or, decide_eq_true_eq, true_or]
  rw [length_flatten_set_eq] <;> simp [*]

theorem length_flatten_set_as_int_eq {α : Type u} (ls : List (List α)) (i : Nat) (x : List α)
  (h1 : i < ls.length) :
  ((ls.set i x).flatten.length : Nat) = ls.flatten.length + x.length - (ls[i]!).length := by
  scalar_tac

@[simp, simp_lists_simps]
theorem getElem!_map_eq {α : Type u} {β : Type v} [Inhabited α] [Inhabited β]
  (ls : List α) (i : Nat) (f : α → β)
  (h1 : i < ls.length) : -- We need the bound because otherwise we have to prove that: `(default : β) = f (default : α)`
  (ls.map f)[i]! = f (ls[i]!) := by
  simp only [getElem!_eq_getElem?_getD, length_map, getElem?_eq_getElem, getElem_map,
    Option.getD_some, h1]

@[simp]
theorem getElem!_map_eq' {α : Type u} {β : Type v} [Inhabited α] [Inhabited β]
  (ls : List α) (i : Nat) (f : α → β)
  (hdef : default = f default) :
  (ls.map f)[i]! = f (ls[i]!) := by
  dcases hi : i < ls.length
  . simp only [hi, List.getElem!_map_eq]
  . simp only [not_lt] at hi
    simp only [getElem!_eq_getElem?_getD, getElem?_map, Option.getD_map, hdef]

@[simp, simp_lists_simps]
theorem getElem!_default [Inhabited α] (ls : List α) (i : ℕ)
  (h : ls.length ≤ i) : ls[i]! = default := by
  revert i h
  induction ls
  . intros i h
    simp only [getElem!_eq_getElem?_getD, getElem?_nil, Option.getD_none]
  . intros i h
    cases i <;> simp_all [getElem!_eq_getElem?_getD, length_cons, nonpos_iff_eq_zero,
      AddLeftCancelMonoid.add_eq_zero, List.length_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true,
      neq_imp, add_le_add_iff_right, getElem?_cons_succ]

@[simp, simp_lists_simps]
theorem getElem!_map_default [Inhabited α] [Inhabited β] (ls : List α) (i : ℕ) (f : α → β)
  (h1 : ls.length ≤ i) : (List.map f ls)[i]! = default := by
  simp only [length_map, getElem!_default, h1]

@[simp]
theorem getElem?_length_le {α} [Inhabited α] (l : List α) (i : Nat) (hi : l.length ≤ i) :
  l[i]? = none := by
  simp [*]

@[simp]
theorem getElem!_length_le {α} [Inhabited α] (l : List α) (i : Nat) (hi : l.length ≤ i) :
  l[i]! = default := by
  simp only [List.getElem!_eq_getElem?_getD, getElem?_length_le, Option.getD_none, hi]

theorem replace_slice_getElem? (start end_ : Nat) (l nl : List α)
  (_ : start < end_) (_ : end_ ≤ l.length) (_ : nl.length = end_ - start) :
  let l1 := l.replace_slice start end_ nl
  (∀ i, i < start → getElem? l1 i = getElem? l i) ∧
  (∀ i, start ≤ i → i < end_ → getElem? l1 i = getElem? nl (i - start)) ∧
  (∀ i, end_ ≤ i → i < l.length → getElem? l1 i = getElem? l i)
  := by
  -- We need those assumptions everywhere
  have : start ≤ l.length := by scalar_tac
  simp only [replace_slice]
  split_conjs
  . intro i _
    -- Introducing exactly the assumptions we need to make the rewriting work
    have : i < l.length := by scalar_tac
    simp_all only [append_assoc, length_take, inf_of_le_left, getElem?_append_left]
    simp [*]
  . intro i _ _
    have : (List.take start l).length ≤ i := by simp_all
    have : i < (List.take start l).length + (nl ++ List.drop end_ l).length := by
      simp_all; scalar_tac
    simp_all only [length_take, inf_of_le_left, length_append, length_drop, append_assoc,
      getElem?_append_right]
    have : i - start < nl.length := by scalar_tac
    simp_all only [getElem?_append_left]
  . intro i _ _
    have : 0 ≤ end_ := by scalar_tac
    have : end_ ≤ l.length := by scalar_tac
    have : (List.take start l).length ≤ i := by scalar_tac
    have := @getElem?_append_right _ (take start l ++ nl) (drop end_ l) i (by simp; scalar_tac)
    simp_all only [zero_le, length_take, inf_of_le_left, append_assoc, getElem?_append_right,
      tsub_le_iff_right, Nat.sub_add_cancel, getElem?_drop, length_append]
    congr
    scalar_tac

theorem replace_slice_getElem! [Inhabited α] (start end_ : Nat) (l nl : List α)
  (_ : start < end_) (_ : end_ ≤ l.length) (_ : nl.length = end_ - start) :
  let l1 := l.replace_slice start end_ nl
  (∀ i, i < start → getElem! l1 i = getElem! l i) ∧
  (∀ i, start ≤ i → i < end_ → getElem! l1 i = getElem! nl (i - start)) ∧
  (∀ i, end_ ≤ i → i < l.length → getElem! l1 i = getElem! l i)
  := by
  have := replace_slice_getElem? start end_ l nl (by assumption) (by assumption) (by assumption)
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

@[simp]
theorem getElem?_range'_if (i start n: ℕ) :
  (List.range' start n)[i]? = if i < n then some (start + i) else none := by
  revert start i
  induction n <;> intro i start
  . simp
  . rename_i n hInd
    unfold List.range'
    cases i
    . simp
    . rename_i i
      have := hInd i (start + 1)
      simp [this]
      simp_all
      ring_nf

theorem getElem!_range' (i start n: ℕ) :
  (List.range' start n)[i]! = if i < n then start + i else 0 := by
  have := List.getElem?_range'_if i start n
  simp_all
  split <;> simp

@[simp] theorem getElem!_range'_lt (i start n: ℕ) (h : i < n) :
  (List.range' start n)[i]! = start + i := by
  simp [getElem!_range', *]

@[simp] theorem getElem!_range'_not_lt (i start n: ℕ) (h : n ≤ i) :
  (List.range' start n)[i]! = 0 := by
  simp [getElem!_range', *]

theorem getElem!_range (i n: ℕ) :
  (List.range n)[i]! = if i < n then i else 0 := by
  simp only [List.range_eq_range']
  rw [getElem!_range']
  simp only [zero_add]

@[simp] theorem getElem!_range_lt (i n: ℕ) (h : i < n) :
  (List.range n)[i]! = i := by
  simp [getElem!_range, *]

@[simp] theorem getElem!_range_not_lt (i n: ℕ) (h : n ≤ i) :
  (List.range n)[i]! = 0 := by
  simp [getElem!_range, *]

end

theorem eq_iff_eq_getElem? {α} (l0 l1 : List α) :
  l0 = l1 ↔ ∀ (i : Nat), l0[i]? = l1[i]? := by
  revert l1
  induction l0 <;> intro l1
  . constructor
    . simp +contextual
    . intro hi
      have := hi 0
      simp at this
      rw [this]
  . rename_i hd l0 hind
    constructor
    . simp +contextual
    . intro hi
      cases l1
      . have := hi 0
        simp at this
      . rename_i hd' l1
        replace hind := hind l1
        simp [hind]
        have := hi 0
        simp at this; simp [this]
        intro i
        replace hi := hi (i + 1)
        simp at hi
        apply hi

theorem eq_iff_eq_getElem! {α} [Inhabited α] (l0 l1 : List α) :
  l0 = l1 ↔ (l0.length = l1.length ∧ ∀ i < l0.length, l0[i]! = l1[i]!) := by
  constructor
  . simp +contextual only [getElem!_eq_getElem?_getD, getElem?_eq_getElem, Option.getD_some,
    implies_true, and_self]
  . simp only [getElem!_eq_getElem?_getD, and_imp]
    intro h0 h1
    rw [eq_iff_eq_getElem?]
    intro i
    dcases hi : i < l0.length
    . replace h1 := h1 i hi
      simp_all only [getElem?_eq_getElem, Option.getD_some]
    . simp only [not_lt] at hi
      simp only [hi, getElem?_length_le, none_eq_getElem?_iff]
      simp only [← h0, hi]

theorem mapM_Result_length {α : Type w} {β : Type u} {f : α → Std.Result β} {l : List α} {l' : List β}
  (h : List.mapM f l = .ok l') :
  l'.length = l.length := by
  have hind (l : List α) (l' acc : List β) (h : List.mapM.loop f l acc = .ok l') : l'.length = l.length + acc.length
    := by
    revert l' acc
    induction l <;> intro l' acc h <;> simp_all [pure, mapM.loop]
    . rw [← h]
      simp
    . rename_i hd tl ih
      cases hf : f hd <;> simp_all
      replace ih := ih _ _ h
      simp [ih]
      omega
  have := hind l l' [] h
  simp [this]

theorem splitAt_length {α : Type u}  (n : Nat)  (l : List α) :
  (l.splitAt n).fst.length = min l.length n ∧ (l.splitAt n).snd.length = l.length - n := by
  revert n
  induction l <;> intro n <;> simp_all
  omega

end List
