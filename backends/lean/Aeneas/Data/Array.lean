import Aeneas.Data.List
import Aeneas.Tactic.Simp.SimpIfs

namespace Array

local macro_rules
| `(tactic| get_elem_tactic) => `(tactic| grind)

attribute [-simp] List.getElem!_eq_getElem?_getD

attribute [scalar_tac_simps, simp_lists_safe] Array.size

def setSlice! {α} (a : Array α) (i : ℕ) (s : List α) : Array α :=
  ⟨ a.toList.setSlice! i s⟩

@[deprecated "Use `← getElem!_toList` instead." (since := "2026-05-07")]
theorem getElem!_eq_toList_getElem! {α} [Inhabited α] (s : Array α) (i : ℕ) :
  s[i]! = s.toList[i]! := Array.getElem!_toList.symm

@[deprecated "Use `← getElem_toList` instead." (since := "2026-05-07")]
theorem getElem_eq_toList_getElem {α} [Inhabited α] (s : Array α) (i : ℕ) (hi : i < s.size) :
  s[i] = s.toList[i] := (Array.getElem_toList hi).symm

@[simp, simp_lists_safe]
theorem getElem!_default [Inhabited α] (ls : Array α) (i : ℕ)
  (h : ls.size ≤ i) : ls[i]! = default := by
  simp only [← getElem!_toList]; simp_lists

@[simp, simp_lists_safe, scalar_tac_simps, grind =, agrind =]
theorem length_setSlice! {α} (s : Array α) (i : ℕ) (s' : List α) :
  (s.setSlice! i s').size = s.size := by
  simp only [setSlice!, List.size_toArray, List.length_setSlice!, length_toList]

theorem getElem!_setSlice!_prefix {α} [Inhabited α]
  (s : Array α) (s' : List α) (i j : ℕ) (h : j < i) :
  (s.setSlice! i s')[j]! = s[j]! := by
  simp only [setSlice!, ← getElem!_toList]
  simp_lists

@[simp_lists_safe]
theorem getElem!_setSlice!_middle {α} [Inhabited α]
  (s : Array α) (s' : List α) (i j : ℕ) (h : i ≤ j ∧ j - i < s'.length ∧ j < s.size) :
  (s.setSlice! i s')[j]! = s'[j - i]! := by
  simp only [setSlice!, ← getElem!_toList]
  simp_lists

theorem getElem!_setSlice!_suffix {α} [Inhabited α]
  (s : Array α) (s' : List α) (i j : ℕ) (h : i + s'.length ≤ j) :
  (s.setSlice! i s')[j]! = s[j]! := by
  simp only [setSlice!, ← getElem!_toList]
  simp_lists

@[simp_lists_safe]
theorem getElem!_setSlice!_same {α} [Inhabited α] (s : Array α) (s' : List α) (i j : ℕ)
  (h : j < i ∨ i + s'.length ≤ j) :
  (s.setSlice! i s')[j]! = s[j]! := by
  cases h <;> simp_lists [getElem!_setSlice!_prefix, getElem!_setSlice!_suffix]

theorem getElem_setSlice!_prefix {α}
  (s : Array α) (s' : List α) (i j : ℕ) (h : j < i ∧ j < s.size) :
  (s.setSlice! i s')[j] = s[j] := by
  simp only [setSlice!, ← getElem_toList]
  simp_lists

@[simp_lists_safe]
theorem getElem_setSlice!_middle {α}
  (s : Array α) (s' : List α) (i j : ℕ) (h : i ≤ j ∧ j - i < s'.length ∧ j < s.size) :
  (s.setSlice! i s')[j] = s'[j - i] := by
  simp only [setSlice!, ← getElem_toList]
  simp_lists

theorem getElem_setSlice!_suffix {α}
  (s : Array α) (s' : List α) (i j : ℕ) (h : i + s'.length ≤ j ∧ j < s.size) :
  (s.setSlice! i s')[j] = s[j] := by
  simp only [setSlice!, ← getElem_toList]
  simp_lists

@[simp_lists_safe]
theorem getElem_setSlice!_same {α} (s : Array α) (s' : List α) (i j : ℕ)
  (h : (j < i ∨ i + s'.length ≤ j) ∧ j < s.size) :
  (s.setSlice! i s')[j] = s[j] := by
  cases h.1 <;> simp_lists [getElem_setSlice!_prefix, getElem_setSlice!_suffix]

def Inhabited_getElem_eq_getElem! {α} [Inhabited α] (l : Array α) (i : ℕ) (hi : i < l.size) :
  l[i] = l[i]! := by
  have : l.toList[i] = l.toList[i]! :=
    List.Inhabited_getElem_eq_getElem! l.toList i (by simpa using hi)
  simp [← Array.getElem_toList, ← Array.getElem!_toList, this]

@[simp_lists_safe, simp_lists_hyps_simps]
theorem set_eq_set! (a : Array α) (i : ℕ) (x : α) (hi : i < a.size) :
  a.set i x hi = a.set! i x := by
  simp only [Array.set, Array.set!, Array.setIfInBounds, hi, ↓reduceDIte]

@[simp, simp_lists_safe]
theorem getElem!_set! {α : Type u}
  [Inhabited α] {i j : ℕ} {x : α} {xs : Array α}
  (hi : i < xs.size ∧ j = i) :
  (xs.set! i x)[j]! = x := by
  simp only [set!_eq_setIfInBounds, ← getElem!_toList, toList_setIfInBounds]
  simp_lists

@[simp, simp_lists_safe]
theorem getElem_set! {α : Type u}
  {i j : ℕ} {x : α} {xs : Array α}
  (hi : i < xs.size ∧ j = i) :
  (xs.set! i x)[j] = x := by
  simp only [set!_eq_setIfInBounds, ← getElem_toList, toList_setIfInBounds]
  simp_lists

@[simp, simp_lists_safe]
theorem getElem!_set!_ne {α : Type u}
  [Inhabited α] {i j : ℕ} {x : α} {xs : Array α}
  (h : i ≠ j) :
  (xs.set! i x)[j]! = xs[j]! := by
  simp only [set!_eq_setIfInBounds, ← getElem!_toList, toList_setIfInBounds]
  simp_lists

@[simp, simp_lists_safe]
theorem getElem_set!_ne {α : Type u}
  {i j : ℕ} {x : α} {xs : Array α}
  (h : i ≠ j ∧ j < xs.size) :
  (xs.set! i x)[j] = xs[j] := by
  simp only [set!_eq_setIfInBounds, ← getElem_toList, toList_setIfInBounds]
  simp_lists

@[simp, simp_lists_safe]
theorem getElem!_replicate {α : Type u} [Inhabited α] {i n : ℕ} {a : α} (h : i < n) :
  (Array.replicate n a)[i]! = a := by
  unfold getElem! Array.instGetElem?NatLtSize Array.get!Internal
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  simp_ifs
  simp only [Option.getD_some]

attribute [simp_lists_safe] getElem_replicate

theorem eq_iff_forall_eq_getElem! {α} [Inhabited α] (l0 l1 : Array α) :
  l0 = l1 ↔ (l0.size = l1.size ∧ ∀ i < l0.size, l0[i]! = l1[i]!) := by
  cases l0; cases l1; simp [List.eq_iff_forall_eq_getElem!]

@[simp_lists_safe]
theorem getElem!_map_eq {α β} [Inhabited α] [Inhabited β] (f : α → β) (x : Array α) (i : ℕ) (hi : i < x.size) :
  (x.map f)[i]! = f x[i]! := by
  simp only [← getElem!_toList, toList_map]
  simp_lists

attribute [simp_lists_safe] getElem_map

@[simp_lists_safe]
theorem getElem!_map_default {α β} [Inhabited α] [Inhabited β] (f : α → β) (x : Array α) (i : ℕ) (hi : x.size ≤ i) :
  (x.map f)[i]! = default := by
  simp only [← getElem!_toList, toList_map]
  simp_lists

@[simp_lists_safe]
theorem getElem!_range_of_lt {n i : Nat}  (hi : i < n) : (Array.range n)[i]! = i := by
  simp only [← getElem!_toList, toList_range]
  simp_lists

attribute [simp_lists_safe] getElem_range

@[simp_lists_safe]
theorem getElem!_range_zero {n i : Nat}  (hi : n ≤ i) : (Array.range n)[i]! = 0 := by
  simp only [← getElem!_toList, toList_range]
  simp_lists

@[simp_lists_safe]
theorem set!_comm' {α} {i j : Nat} (h : j < i) (a : Array α) (x y : α) :
  (a.set! i x).set! j y = (a.set! j y).set! i x := by
  cases a; simp
  rw [List.set_comm']
  assumption

@[simp_lists_safe]
theorem getElem!_ofFn {n : ℕ} {α : Type u} [Inhabited α] (f : Fin n → α) (i : ℕ) (hi : i < n) :
  (Array.ofFn f)[i]! = f ⟨ i, hi ⟩ := by
  simp only [← getElem!_toList, toList_ofFn, List.getElem!_ofFn, hi]

attribute [simp_lists_safe] getElem_ofFn

attribute [simp_lists_safe] Array.getElem!_toList Array.getElem_toList

end Array
