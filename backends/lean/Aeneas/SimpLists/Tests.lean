import Aeneas.SimpLists.SimpLists
import Aeneas.List.List
import Aeneas.Std.Slice

example [Inhabited α] (l : List α) (x : α) (i j : Nat) (hj : i ≠ j) : (l.set j x)[i]! = l[i]! := by
  simp_lists

example [Inhabited α] (l : List α) (x : α) (i : Nat) (hi : i < l.length) : (l.set i x)[i]! = x := by
  simp_lists

/-- We use this lemma to "normalize" successive calls to `List.set` -/
@[simp_lists_simps]
theorem List.set_comm_lt (a b : α) (n m : Nat) (l : List α) (h : n < m) :
  (l.set m a).set n b = (l.set n b).set m a := by
  rw [List.set_comm]
  omega

example [Inhabited α] (l : List α) (x y : α) (i j : Nat) (hj : i < j) : (l.set i x).set j y = (l.set j y).set i x := by
  simp_lists

example (CList : Type) (l : CList) (get : CList → Nat → Bool) (set : CList → Nat → Bool → CList)
  (h : ∀ i j l x, i ≠ j → get (set l i x) j = get l j) (i j : Nat) (hi : i < j) : get (set l i x) j = get l j := by
  simp_lists [h]

example (CList : Type) (l : CList) (get : CList → Nat → Bool) (set : CList → Nat → Bool → CList)
  (h : ∀ i j l x, i ≠ j → get (set l i x) j = get l j) (i j : Nat) (hi : i < j) : get (set l i x) j = get l j := by
  simp_lists [*]

example
  (T : Type)
  [Inhabited T]
  (i : ℕ)
  (tl : List T)
  (h : i < tl.length + 1)
  (hi : ¬i = 0)
  (i1 : ℕ)
  (_ : i1 = i - 1)
  (_ : 1 ≤ i)
  (x : T)
  (_ : x = tl[i1]!) :
  x = tl[i - 1]!
  := by
  simp_lists [*]

abbrev Zq := ZMod 3329

example
  (x y : ℕ)
  (l : List ℕ)
  (h : ∀ (j : ℕ), (↑l[j]! : Zq) = (↑x : Zq) - (↑y : Zq))
  (j : ℕ) :
  (↑l[j]! : Zq) = (↑x : Zq) - (↑y : Zq)
  := by
  simp_lists [h]
