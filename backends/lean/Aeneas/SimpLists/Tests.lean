import Aeneas.SimpLists.SimpLists
import Aeneas.List.List
import Aeneas.Std.Slice

example {α} [Inhabited α] (l : List α) (x : α) (i j : Nat) (hj : i ≠ j) : (l.set j x)[i]! = l[i]! := by
  simp_lists

example {α} [Inhabited α] (l : List α) (x : α) (i : Nat) (hi : i < l.length) : (l.set i x)[i]! = x := by
  simp_lists

example {α} [Inhabited α] (l : List α) (x y : α) (i j : Nat) (hj : i < j) : (l.set i x).set j y = (l.set j y).set i x := by
  simp_lists

example (CList : Type) (l : CList) (x : Bool) (get : CList → Nat → Bool) (set : CList → Nat → Bool → CList)
  (h : ∀ i j l x, i ≠ j → get (set l i x) j = get l j) (i j : Nat) (hi : i < j) : get (set l i x) j = get l j := by
  simp_lists [h]

example (CList : Type) (l : CList) (x : Bool) (get : CList → Nat → Bool) (set : CList → Nat → Bool → CList)
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

example
  (x y : ℕ)
  (l : List ℕ)
  (h : ∀ (j : ℕ), (↑l[j]! : ZMod 3329) = (↑x : ZMod 3329) - (↑y : ZMod 3329))
  (j : ℕ) :
  (↑l[j]! : ZMod 3329) = (↑x : ZMod 3329) - (↑y : ZMod 3329)
  := by
  simp_lists [h]
