import Aeneas.SimpLists.SimpLists
import Aeneas.List.List
import Aeneas.Std.Slice

open Aeneas Std

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

/- This test comes from SymCrypt -/
example
    (f : Std.Array U16 256#usize)
    (g : Std.Array U16 256#usize)
    (B0 : ℕ)
    (B1 : ℕ)
    (i0 : ℕ)
    (i : Usize)
    (c0 : U32)
    (c1 : U32)
    (paDst0 : Std.Array U32 256#usize)
    (paDst : Std.Array U32 256#usize)
    (hi0 : i0 < 128)
    (hc0bound : (↑c0 : ℕ) ≤ B0 + B1)
    (hc1bound : (↑c1 : ℕ) ≤ B0 + B1)
    (hc1 : (↑c1 : ℕ) =
    (↑paDst0[(↑i : ℕ) + 1]! : ℕ) + (↑f[(↑i : ℕ)]! : ℕ) * (↑g[(↑i : ℕ) + 1]! : ℕ) +
      (↑f[(↑i : ℕ) + 1]! : ℕ) * (↑g[(↑i : ℕ)]! : ℕ))
    (hi : (↑i : ℕ) = 2 * i0)
    (paDst1 : Std.Array U32 256#usize)
    (paDst1_post : paDst1 = paDst.set i c0)
    (i' : Usize)
    (i'_post : (↑i' : ℕ) = (↑i : ℕ) + 1)
    (paDst2 : Std.Array U32 256#usize)
    (paDst2_post : paDst2 = paDst1.set i' c1)
    (h0 : ∀ j < i0, (↑paDst[2 * j]! : ℕ) ≤ B0 + B1 ∧ (↑paDst[2 * j + 1]! : ℕ) ≤ B0 + B1)
    (h1 : ∀ (j : ℕ), i0 ≤ j → j < 128 → (↑paDst0[2 * j]! : ℕ) ≤ B0 ∧ (↑paDst0[2 * j + 1]! : ℕ) ≤ B0)
    (h3 : ∀ (j : ℕ), i0 ≤ j → j < 128 → paDst[2 * j]! = paDst0[2 * j]! ∧ paDst[2 * j + 1]! = paDst0[2 * j + 1]!)
    (j : ℕ)
    (hj : j < i0 + 1)
    (hjeq : j = i0) :
    (↑paDst2[2 * j]! : ℕ) ≤ B0 + B1 ∧ (↑paDst2[2 * j + 1]! : ℕ) ≤ B0 + B1
    := by
    simp_lists [*]
