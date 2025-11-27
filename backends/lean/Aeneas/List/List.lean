/- Complementary functions and lemmas for the `List` type -/

import Mathlib.Data.List.GetD
import Aeneas.ScalarTac
import AeneasMeta.Utils
import Aeneas.SimpLemmas
import Aeneas.Nat
import Aeneas.SimpLists.Init
import Aeneas.Std.Primitives
import Aeneas.SimpLists.SimpLists
import Aeneas.SimpScalar.SimpScalar

namespace List -- We do not use the `Aeneas` namespace on purpose

open Aeneas
open Aeneas.ScalarTac
open Aeneas.Simp

attribute [scalar_tac_simps]
  List.length_nil List.length_cons List.length_append List.length_reverse

attribute [simp_lists_simps]
  List.append_nil List.nil_append List.take_of_length_le
  and_true true_and implies_true

attribute [simp_lists_simps] getElem?_eq_none

def set_opt (l : List α) (i : Nat) (x : Option α) : List α :=
  match l with
  | [] => l
  | hd :: tl => if i = 0 then Option.getD x hd :: tl else hd :: set_opt tl (i-1) x

attribute [simp] getElem?_cons_zero getElem!_cons_zero
@[simp] theorem getElem?_cons_nzero (hne : Nat.not_eq i 0) : getElem? ((x :: tl) : List α) i = getElem? tl (i - 1) := by cases i <;> simp_all
@[simp] theorem getElem!_cons_nzero (x : α) (tl : List α) (i : Nat) [Inhabited α] (hne : Nat.not_eq i 0) : getElem! ((x :: tl) : List α) i = getElem! tl (i - 1) := by cases i <;> simp_all

def slice (start end_ : Nat) (ls : List α) : List α :=
  (ls.drop start).take (end_ - start)

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

@[simp, simp_lists_simps]
theorem getElem!_replicate {α : Type u} [Inhabited α] (a : α) {n i : ℕ} (h : i < n) :
  (List.replicate n a)[i]! = a := by
  simp only [getElem!_eq_getElem?_getD, length_replicate, h, getElem?_eq_getElem, getElem_replicate,
    Option.getD_some]

@[simp, simp_lists_simps]
theorem getElem!_replicate_eq_default {α : Type u} [Inhabited α] (a : α) {n i : ℕ} (h : n ≤ i) :
  (List.replicate n a)[i]! = default := by
  revert i
  induction n
  . simp_all
  . rename_i n hind
    intros i hi
    unfold replicate
    cases i <;> simp_all

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

@[simp, simp_lists_simps]
theorem getElem!_append_left [Inhabited α] (l0 l1 : List α) (i : Nat) (h : i < l0.length) :
  (l0 ++ l1)[i]! = l0[i]! := by
  have := @getElem?_append_left _ l0 l1 i h
  simp_all

@[simp, simp_lists_simps]
theorem getElem!_append_right [Inhabited α] (l0 l1 : List α) (i : Nat)
  (h : l0.length ≤ i) :
  (l0 ++ l1)[i]! = l1[i - l0.length]! := by
  have := @getElem?_append_right _ l0 l1 i h
  simp_all

attribute [simp_lists_simps] getElem?_append_left getElem?_append_right

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

attribute [scalar_tac_simps, simp_lists_simps] length_take

@[simp, scalar_tac_simps]
theorem resize_length (l : List α) (new_len : Nat) (x : α) :
  (l.resize new_len x).length = new_len := by
  induction l <;> simp_all [resize]
  scalar_tac

@[simp] theorem slice_zero_j (l : List α) : l.slice 0 j = l.take j := by simp [slice]

theorem slice_length_le (i j : Nat) (ls : List α) : (ls.slice i j).length ≤ ls.length := by
  simp [slice]

@[simp_lists_simps, scalar_tac_simps]
theorem slice_length (i j : Nat) (ls : List α) : (ls.slice i j).length = min (ls.length - i) (j - i) := by
  simp [slice]; scalar_tac

@[simp, simp_lists_simps]
theorem getElem?_slice (i j k : Nat) (ls : List α)
  (_ : j ≤ ls.length ∧ i + k < j) :
  (ls.slice i j)[k]? = ls[i + k]? := by
  revert i j
  induction ls
  . intro i j; simp_all
  . intro i j h
    simp_all [slice]
    have : k < j - i := by scalar_tac
    simp [*]

@[simp, simp_lists_simps]
theorem getElem!_slice [Inhabited α] (i j k : Nat) (ls : List α)
  (_ : j ≤ ls.length ∧ i + k < j) :
  (ls.slice i j)[k]! = ls[i + k]! := by
  have := getElem?_slice i j k ls
  simp_all

@[simp, simp_lists_simps]
theorem getElem?_take_append_beg (i j : Nat) (l0 l1 : List α)
  (_ : j < i ∧ i ≤ l0.length) :
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

@[simp, simp_lists_simps]
theorem getElem!_take_append_beg [Inhabited α] (i j : Nat) (l0 l1 : List α)
  (_ : j < i) (_ : i ≤ l0.length) :
  getElem! ((l0 ++ l1).take i) j = getElem! l0 j := by
  have := getElem?_take_append_beg i j l0 l1
  simp_all

@[simp, simp_lists_simps]
theorem getElem!_drop [Inhabited α] (i : Nat) (j : Nat) (ls : List α) :
  getElem! (ls.drop i) j = getElem! ls (i + j) := by
  have := @getElem?_drop _ ls i j
  simp_all

attribute [simp_lists_simps] getElem?_take_eq_none getElem?_take_of_lt getElem?_drop

@[simp, simp_lists_simps]
theorem getElem!_take_of_lt [Inhabited α] (i : Nat) (j : Nat) (ls : List α)
  (_ : j < i) :
  getElem! (ls.take i) j = getElem! ls j := by
  simp only [getElem!_eq_getElem?_getD, getElem?_take_of_lt, *]

@[simp, simp_lists_simps]
theorem getElem!_take_eq_default [Inhabited α] (i : Nat) (j : Nat) (ls : List α)
  (_ : i ≤ j) :
  getElem! (ls.take i) j = default := by
  simp only [getElem!_eq_getElem?_getD, getElem?_take_eq_none, Option.getD_none, *]

@[simp]
theorem getElem?_set_neq
  {α : Type u} (l: List α) (i: Nat) (j: Nat) (x: α)
  (h : Nat.not_eq i j) : getElem? (l.set i x) j = getElem? l j
  := by
  simp [getElem?_set]
  intro
  simp_all

@[simp, simp_lists_simps]
theorem getElem!_set_ne
  {α : Type u} [Inhabited α] (l: List α) (i: Nat) (j: Nat) (x: α)
  (h : Nat.not_eq i j) : getElem! (l.set i x) j = getElem! l j
  := by
  have := getElem?_set_neq l i j x h
  simp_all

@[simp]
theorem getElem!_set
  {α : Type u} [Inhabited α] (l: List α) (i: Nat) (x: α)
  (h : i < l.length) : getElem! (l.set i x) i = x
  := by
  simp [*]

@[simp_lists_simps]
theorem getElem!_set'
  {α : Type u} [Inhabited α] (l: List α) (i i': Nat) (x: α)
  (h : i' < l.length ∧ i = i') : getElem! (l.set i x) i' = x
  := by
  simp only [getElem!_set, *]

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
  induction ls <;> intro i <;> simp_all
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
  cases h: (ls.length ≤ i : Bool) <;> simp_all only [decide_eq_false_iff_not, not_le, decide_eq_true_eq, true_or]
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
    cases i <;> simp_all [length_cons, nonpos_iff_eq_zero, List.length_eq_zero_iff,
      one_ne_zero, and_false, not_false_eq_true, neq_imp, add_le_add_iff_right]

@[simp, simp_lists_simps]
theorem getElem!_map_default [Inhabited α] [Inhabited β] (ls : List α) (i : ℕ) (f : α → β)
  (h1 : ls.length ≤ i) : (List.map f ls)[i]! = default := by
  simp only [length_map, getElem!_default, h1]

@[simp]
theorem getElem?_length_le {α} [Inhabited α] (l : List α) (i : Nat) (hi : l.length ≤ i) :
  l[i]? = none := by
  simp [*]

@[simp, simp_lists_simps]
theorem getElem!_length_le {α} [Inhabited α] (l : List α) (i : Nat) (hi : l.length ≤ i) :
  l[i]! = default := by
  simp only [List.getElem!_eq_getElem?_getD, getElem?_length_le, Option.getD_none, hi]

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
  simp [*]

@[simp] theorem getElem!_range'_not_lt (i start n: ℕ) (h : n ≤ i) :
  (List.range' start n)[i]! = 0 := by
  simp [*]

theorem getElem!_range (i n: ℕ) :
  (List.range n)[i]! = if i < n then i else 0 := by
  simp only [List.range_eq_range']
  rw [getElem!_range']
  simp only [zero_add]

@[simp, simp_lists_simps] theorem getElem!_range_of_lt (i n: ℕ) (h : i < n) :
  (List.range n)[i]! = i := by
  simp [*]

@[simp, simp_lists_simps] theorem getElem!_range_zero (i n: ℕ) (h : n ≤ i) :
  (List.range n)[i]! = 0 := by
  simp [*]

end

theorem eq_iff_forall_eq_getElem? {α} (l0 l1 : List α) :
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

theorem eq_iff_forall_eq_getElem! {α} [Inhabited α] (l0 l1 : List α) :
  l0 = l1 ↔ (l0.length = l1.length ∧ ∀ i < l0.length, l0[i]! = l1[i]!) := by
  constructor
  . simp +contextual only [getElem!_eq_getElem?_getD, getElem?_eq_getElem, Option.getD_some,
    implies_true, and_self]
  . simp only [getElem!_eq_getElem?_getD, and_imp]
    intro h0 h1
    rw [eq_iff_forall_eq_getElem?]
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

@[scalar_tac_simps]
theorem splitAt_length {α : Type u}  (n : Nat)  (l : List α) :
  (l.splitAt n).fst.length = min l.length n ∧ (l.splitAt n).snd.length = l.length - n := by
  revert n
  induction l <;> intro n <;> simp_all
  omega

section -- setSlice!
  attribute [-simp] getElem!_eq_getElem?_getD

  def setSlice! {α} (s : List α) (i : ℕ) (s' : List α) : List α :=
    let s0 := List.take i s
    let n := min s'.length (s.length - i)
    let s1 := List.take n s'
    let s2 := List.drop (i + n) s
    s0 ++ s1 ++ s2

  @[simp, simp_lists_simps, scalar_tac_simps]
  theorem length_setSlice! {α} (s : List α) (i : ℕ) (s' : List α) :
    (s.setSlice! i s').length = s.length := by
    simp only [setSlice!, append_assoc, length_append, length_take, inf_le_left, inf_of_le_left,
      length_drop]
    omega

  theorem getElem!_setSlice!_prefix {α} [Inhabited α]
    (s : List α) (s' : List α) (i j : ℕ) (h : j < i) :
    (s.setSlice! i s')[j]! = s[j]! := by
    simp only [setSlice!, append_assoc]
    -- TODO: simp_lists +split
    by_cases hi: i ≤ s.length <;> simp_lists
    by_cases hj: s.length ≤ j <;> simp_lists

  @[simp_lists_simps]
  theorem getElem!_setSlice!_middle {α} [Inhabited α]
    (s : List α) (s' : List α) (i j : ℕ) (h : i ≤ j ∧ j - i < s'.length ∧ j < s.length) :
    (s.setSlice! i s')[j]! = s'[j - i]! := by
    simp only [setSlice!, append_assoc]
    simp_lists
    by_cases h1: s.length ≤ j + s'.length <;> simp (disch := omega) only [inf_of_le_left]

  theorem getElem!_setSlice!_suffix {α} [Inhabited α]
    (s : List α) (s' : List α) (i j : ℕ) (h : i + s'.length ≤ j) :
    (s.setSlice! i s')[j]! = s[j]! := by
    simp only [setSlice!, append_assoc]
    simp_lists
    by_cases h1: j < s.length <;> simp_lists
    simp (disch := omega) only [inf_of_le_left, add_add_tsub_cancel,
      add_tsub_cancel_of_le]

  @[simp_lists_simps]
  theorem getElem!_setSlice!_same {α} [Inhabited α] (s : List α) (s' : List α) (i j : ℕ)
    (h : j < i ∨ i + s'.length ≤ j) :
    (s.setSlice! i s')[j]! = s[j]! := by
    cases h <;> simp_lists [getElem!_setSlice!_prefix, getElem!_setSlice!_suffix]

  @[simp, simp_lists_simps]
  theorem map_setSlice! (s : List α) (i : ℕ) (s' : List α) (f : α → β):
    (s.setSlice! i s').map f = (s.map f).setSlice! i (s'.map f) := by
    simp only [List.setSlice!, List.append_assoc, List.map_append, List.map_take, List.map_drop,
      List.length_map]

  theorem setSlice!_getElem?_prefix {α}
    (s : List α) (s' : List α) (i j : ℕ) (h : j < i) :
    (s.setSlice! i s')[j]? = s[j]? := by
    simp only [setSlice!, append_assoc]
    -- TODO: simp_lists +split
    by_cases hi: i ≤ s.length <;> simp_lists
    by_cases hj: s.length ≤ j <;> simp_lists

  @[simp_lists_simps]
  theorem setSlice!_getElem?_middle {α}
    (s : List α) (s' : List α) (i j : ℕ) (h : i ≤ j ∧ j - i < s'.length ∧ j < s.length) :
    (s.setSlice! i s')[j]? = s'[j - i]? := by
    simp only [setSlice!, append_assoc]
    simp_lists
    by_cases h1: s.length ≤ j + s'.length <;> simp (disch := omega) only [inf_of_le_left,
      getElem?_eq_getElem]

  theorem setSlice!_getElem?_suffix {α}
    (s : List α) (s' : List α) (i j : ℕ) (h : i + s'.length ≤ j) :
    (s.setSlice! i s')[j]? = s[j]? := by
    simp only [setSlice!, append_assoc]
    simp_lists
    by_cases h1: j < s.length <;> simp_lists
    simp (disch := omega) only [inf_of_le_left, add_add_tsub_cancel,
      add_tsub_cancel_of_le, getElem?_eq_getElem]

  @[simp_lists_simps]
  theorem setSlice!_getElem?_same {α} (s : List α) (s' : List α) (i j : ℕ)
    (h : j < i ∨ i + s'.length ≤ j) :
    (s.setSlice! i s')[j]? = s[j]? := by
    cases h <;> simp_lists [setSlice!_getElem?_prefix, setSlice!_getElem?_suffix]

end -- setSlice!

@[simp, simp_lists_simps]
theorem setSlice!_drop {α} (l : List α) (i : ℕ) :
  l.setSlice! i (List.drop i l) = l := by
  simp [List.eq_iff_forall_eq_getElem?]
  intro j
  by_cases h0: j < i <;> simp_lists
  by_cases h1: j < l.length <;> simp_lists
  simp_scalar

@[simp_lists_hyps_simps]
def Inhabited_getElem_eq_getElem! {α} [Inhabited α] (l : List α) (i : ℕ) (hi : i < l.length) :
  l[i] = l[i]! := by
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some, hi]

theorem forall_imp_foldl_eq {α β} (l : List β) (s0 s1 : α) (f1 f2 : α → β → α)
  (h0 : s0 = s1)
  (h1 : ∀ s, ∀ x ∈ l, f1 s x = f2 s x) :
  l.foldl f1 s0 = l.foldl f2 s1 := by
  simp [h0]; clear h0 s0
  revert s1 h1
  induction l
  . simp_all only [not_mem_nil, IsEmpty.forall_iff, implies_true, foldl_nil]
  . simp_all only [mem_cons, forall_eq_or_imp, foldl_cons, implies_true]

/- This one might be expensive -/
@[simp_lists_simps]
theorem set_comm' {α} {i j : Nat} (h : j < i) (a : List α) (x y : α) :
  (a.set i x).set j y = (a.set j y).set i x := by
  rw [set_comm]
  omega

@[simp_lists_simps]
theorem getElem!_ofFn {n : ℕ} {α : Type u} [Inhabited α] (f : Fin n → α) (i : ℕ) (hi : i < n) :
  (List.ofFn f)[i]! = f ⟨ i, hi ⟩ := by
  simp only [getElem!_eq_getElem?_getD, length_ofFn, getElem?_eq_getElem, List.getElem_ofFn,
    Option.getD_some, hi]

end List
