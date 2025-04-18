import Aeneas.Array

namespace Vector

attribute [-simp] List.getElem!_eq_getElem?_getD
attribute [local simp] Array.getElem!_eq_toList_getElem! Array.getElem_eq_toList_getElem
attribute [scalar_tac self.toArray] Vector.size_toArray

@[scalar_tac xs.toList]
theorem toList_length {α : Type u} {n : ℕ} (xs : Vector α n) :
  xs.toList.length = n := by
  simp only [Array.length_toList, size_toArray]

def setSlice! {α} {n} (a : Vector α n) (i : ℕ) (s : List α) : Vector α n :=
  ⟨ a.toArray.setSlice! i s, by simp only [Array.setSlice!_length, size_toArray] ⟩

attribute [local simp] List.Inhabited_getElem_eq_getElem! Array.Inhabited_getElem_eq_getElem!

@[local simp]
theorem getElem!_eq_toArray_getElem! {α} {n} [Inhabited α] (s : Vector α n) (i : ℕ) :
  s[i]! = s.toArray[i]! := by
  cases s; simp
  unfold instGetElem?OfGetElemOfDecidable decidableGetElem?
  simp; split <;> simp_all only [Option.ite_none_right_eq_some, Option.some.injEq, ite_eq_right_iff]
  simp_all
  rfl

@[simp, simp_lists_simps]
theorem getElem!_default [Inhabited α] (ls : Vector α n) (i : ℕ)
  (h : n ≤ i) : ls[i]! = default := by
  have : ls.toArray.size ≤ i := by scalar_tac
  simp only [getElem!_eq_toArray_getElem!]; simp_lists

@[local simp]
theorem getElem_eq_toArray_getElem {α} {n} [Inhabited α] (s : Vector α n) (i : ℕ) (hi : i < n) :
  s[i] = getElem s.toArray i (by have := s.size_toArray; omega) := by
  cases s; simp

@[simp, simp_lists_simps, scalar_tac_simps]
theorem setSlice!_length {α} {n} (s : Vector α n) (i : ℕ) (s' : List α) :
  (s.setSlice! i s').size = n := by
  simp only [size_toArray]

theorem setSlice!_getElem!_prefix {α} {n} [Inhabited α]
  (s : Vector α n) (s' : List α) (i j : ℕ) (h : j < i) :
  (s.setSlice! i s')[j]! = s[j]! := by
  simp only [getElem!_eq_toArray_getElem!, setSlice!]
  simp_lists

@[simp_lists_simps]
theorem setSlice!_getElem!_middle {α} {n} [Inhabited α]
  (s : Vector α n) (s' : List α) (i j : ℕ) (h : i ≤ j ∧ j - i < s'.length ∧ j < s.size) :
  (s.setSlice! i s')[j]! = s'[j - i]! := by
  simp only [setSlice!, getElem!_eq_toArray_getElem!]
  simp_lists

theorem setSlice!_getElem!_suffix {α} {n} [Inhabited α]
  (s : Vector α n) (s' : List α) (i j : ℕ) (h : i + s'.length ≤ j) :
  (s.setSlice! i s')[j]! = s[j]! := by
  simp only [setSlice!, getElem!_eq_toArray_getElem!]
  simp_lists

@[simp_lists_simps]
theorem setSlice!_getElem!_same {α} {n} [Inhabited α] (s : Vector α n) (s' : List α) (i j : ℕ)
  (h : j < i ∨ i + s'.length ≤ j) :
  (s.setSlice! i s')[j]! = s[j]! := by
  cases h <;> simp_lists [setSlice!_getElem!_prefix, setSlice!_getElem!_suffix]

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


end Vector
