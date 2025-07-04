import Aeneas.Array

namespace Vector

attribute [-simp] List.getElem!_eq_getElem?_getD getElem!_pos
attribute [local simp] Array.getElem!_eq_toList_getElem! Array.getElem_eq_toList_getElem
attribute [scalar_tac self.toArray] Vector.size_toArray

attribute [-simp] Array.getElem!_toList

@[scalar_tac xs.toList]
theorem toList_length {α : Type u} {n : ℕ} (xs : Vector α n) :
  xs.toList.length = n := by
  simp only [length_toList]

def setSlice! {α} {n} (a : Vector α n) (i : ℕ) (s : List α) : Vector α n :=
  ⟨ a.toArray.setSlice! i s, by simp only [Array.length_setSlice!, size_toArray] ⟩

attribute [local simp] List.Inhabited_getElem_eq_getElem! Array.Inhabited_getElem_eq_getElem!

@[local simp]
theorem getElem!_eq_toArray_getElem! {α} {n} [Inhabited α] (s : Vector α n) (i : ℕ) :
  s[i]! = s.toArray[i]! := by
  cases s; simp
  unfold instGetElem?OfGetElemOfDecidable decidableGetElem?
  simp only [getElem_mk, Array.getElem_eq_toList_getElem, List.Inhabited_getElem_eq_getElem!,
    dite_eq_ite]; split <;> simp_all only [Option.ite_none_right_eq_some, Option.some.injEq, ite_eq_right_iff]
  simp only [reduceCtorEq, imp_false, not_lt] at *
  simp only [outOfBounds, Std.DHashMap.Internal.AssocList.panicWithPosWithDecl_eq,
    Array.length_toList, not_lt, getElem!_neg, *]

@[simp, simp_lists_simps]
theorem getElem!_default [Inhabited α] (ls : Vector α n) (i : ℕ)
  (h : n ≤ i) : ls[i]! = default := by
  have : ls.toArray.size ≤ i := by scalar_tac
  simp only [getElem!_eq_toArray_getElem!, Array.getElem!_eq_toList_getElem!]; simp_lists

@[local simp]
theorem getElem_eq_toArray_getElem {α} {n} [Inhabited α] (s : Vector α n) (i : ℕ) (hi : i < n) :
  s[i] = getElem s.toArray i (by have := s.size_toArray; omega) := by
  cases s; simp

theorem getElem_eq_getElem! {α} {n} [Inhabited α] (s : Vector α n) (i : ℕ) (hi : i < n) :
  s[i] = s[i]! := by
  cases s; simp

attribute [simp_lists_simps, scalar_tac_simps] Vector.size_toArray

theorem getElem!_setSlice!_prefix {α} {n} [Inhabited α]
  (s : Vector α n) (s' : List α) (i j : ℕ) (h : j < i) :
  (s.setSlice! i s')[j]! = s[j]! := by
  simp only [getElem!_eq_toArray_getElem!, setSlice!]
  simp_lists [Array.getElem!_setSlice!_prefix] -- TODO: we shouldn't have to provide the theorem

@[simp_lists_simps]
theorem getElem!_setSlice!_middle {α} {n} [Inhabited α]
  (s : Vector α n) (s' : List α) (i j : ℕ) (h : i ≤ j ∧ j - i < s'.length ∧ j < s.size) :
  (s.setSlice! i s')[j]! = s'[j - i]! := by
  simp only [setSlice!, getElem!_eq_toArray_getElem!]
  simp_lists [Array.getElem!_setSlice!_middle] -- TODO: we shouldn't have to provide the theorem

theorem getElem!_setSlice!_suffix {α} {n} [Inhabited α]
  (s : Vector α n) (s' : List α) (i j : ℕ) (h : i + s'.length ≤ j) :
  (s.setSlice! i s')[j]! = s[j]! := by
  simp only [setSlice!, getElem!_eq_toArray_getElem!]
  simp_lists [Array.getElem!_setSlice!_suffix] -- TODO: we shouldn't have to provide the theorem

@[simp_lists_simps]
theorem getElem!_setSlice!_same {α} {n} [Inhabited α] (s : Vector α n) (s' : List α) (i j : ℕ)
  (h : j < i ∨ i + s'.length ≤ j) :
  (s.setSlice! i s')[j]! = s[j]! := by
  cases h <;> simp_lists [getElem!_setSlice!_prefix, getElem!_setSlice!_suffix]

@[simp_lists_simps]
def Inhabited_getElem_eq_getElem! {α} {n} [Inhabited α] (l : Vector α n) (i : ℕ) (hi : i < n) :
  l[i] = l[i]! := by
  simp only [getElem_eq_toArray_getElem, Array.Inhabited_getElem_eq_getElem!,
    getElem!_eq_toArray_getElem!]

@[simp_lists_simps]
theorem set_eq_set! (v : Vector α n) (i : ℕ) (x : α) (hi : i < n) :
  v.set i x hi = v.set! i x := by
  simp only [Vector.set, Array.set_eq_set!, Vector.set!]

@[simp, simp_lists_simps]
theorem getElem!_set! {α : Type u}
  [Inhabited α] {n i j : ℕ} {x : α} {xs : Vector α n}
  (hi : i < n ∧ j = i) :
  (xs.set! i x)[j]! = x := by
  have : i < xs.toArray.size := by scalar_tac
  simp only [getElem!_eq_toArray_getElem!, toArray_set!, Array.set!_eq_setIfInBounds,
    Array.getElem!_eq_toList_getElem!, Array.toList_setIfInBounds]
  simp_lists

@[simp, simp_lists_simps]
theorem getElem!_set!_ne {α : Type u}
  [Inhabited α] {n i j : ℕ} {x : α} {xs : Vector α n}
  (h : i ≠ j) :
  (xs.set! i x)[j]! = xs[j]! := by
  simp
  simp_lists

@[simp, simp_lists_simps]
theorem getElem!_replicate {α : Type u} [Inhabited α] {i n : ℕ} {a : α} (h : i < n) :
 (Vector.replicate n a)[i]! = a := by
 unfold getElem! instGetElem?OfGetElemOfDecidable Vector.instGetElemNatLt decidableGetElem? Vector.get
 simp; simp_lists
 split_ifs
 simp

@[simp, simp_lists_simps]
theorem getElem!_cast {n m : ℕ} {α : Type u_1} [Inhabited α] (h: n = m) (v : Vector α n) (i : ℕ):
  (Vector.cast h v)[i]! = v[i]! := by
  simp only [getElem!_eq_toArray_getElem!, toArray_cast, Array.getElem!_eq_toList_getElem!]

theorem eq_iff_forall_eq_getElem! {α} {n} [Inhabited α] (l0 l1 : Vector α n) :
  l0 = l1 ↔ (∀ i < n, l0[i]! = l1[i]!) := by
  cases l0; cases l1; simp only [eq_mk, Array.eq_iff_forall_eq_getElem!,
    Array.getElem!_eq_toList_getElem!, true_and, getElem!_eq_toArray_getElem!, *]

@[simp_lists_simps]
theorem getElem!_map_eq {α β} [Inhabited α] [Inhabited β] {n} (f : α → β) (x : Vector α n) (i : ℕ) (hi : i < n) :
  (x.map f)[i]! = f x[i]! := by
  have : i < x.size := by scalar_tac
  simp only [getElem!_eq_toArray_getElem!, toArray_map, Array.getElem!_eq_toList_getElem!,
    Array.toList_map]
  simp_lists

@[simp_lists_simps]
theorem getElem!_map_eq_default {α β} [Inhabited α] [Inhabited β] {n} (f : α → β) (x : Vector α n) (i : ℕ) (hi : n ≤ i) :
  (x.map f)[i]! = default := by
  have : x.size ≤ i := by scalar_tac
  simp only [getElem!_eq_toArray_getElem!, toArray_map, Array.getElem!_eq_toList_getElem!,
    Array.toList_map]
  simp_lists

@[simp_lists_simps]
theorem getElem!_range_of_lt {n i : Nat}  (hi : i < n) : (Vector.range n)[i]! = i := by
  simp only [getElem!_eq_toArray_getElem!, toArray_range, Array.getElem!_eq_toList_getElem!,
    Array.toList_range]
  simp_lists

@[simp_lists_simps]
theorem set!_comm' {α} {i j : Nat} (h : j < i)
  (v : Vector α n) (x y : α) :
  (v.set! i x).set! j y = (v.set! j y).set! i x := by
  cases v; rename_i a h; cases a; simp
  rw [List.set_comm']
  assumption

@[simp_lists_simps]
theorem getElem!_ofFn {n : ℕ} {α : Type u} [Inhabited α] (f : Fin n → α) (i : ℕ) (hi : i < n) :
  (Vector.ofFn f)[i]! = f ⟨ i, hi ⟩ := by
  simp only [ofFn, getElem!_eq_toArray_getElem!, Array.getElem!_eq_toList_getElem!,
    Array.toList_ofFn, List.getElem!_ofFn, hi]

@[simp, simp_lists_simps]
theorem getElem!_toList {α} {n} [Inhabited α] (v : Vector α n) (i : ℕ) :
  v.toList[i]! = v[i]! := by
  simp only [toList, getElem!_eq_toArray_getElem!, Array.getElem!_eq_toList_getElem!]

@[simp, simp_lists_simps]
theorem getElem!_toArray {α} {n} [Inhabited α] (v : Vector α n) (i : ℕ) :
  v.toArray[i]! = v[i]! := by
  simp only [Vector.getElem!_eq_toArray_getElem!, Array.getElem!_eq_toList_getElem!]

end Vector
