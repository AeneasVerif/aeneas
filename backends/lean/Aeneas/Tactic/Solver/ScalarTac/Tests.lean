import Aeneas.ScalarTac.Lemmas

namespace Aeneas.Std.ScalarTac.Tests

/-!
# Tests
-/

-- Checking that things happen correctly when there are several conjunctions
example (x y : Int) (h0: 0 ≤ x) (h1: x ≠ 0) (h2 : 0 ≤ y) (h3 : y ≠ 0) : 0 < x ∧ 0 < y := by
  scalar_tac

-- Checking that things happen correctly when there are several conjunctions
example (x y : Int) (h0: 0 ≤ x) (h1: x ≠ 0) (h2 : 0 ≤ y) (h3 : y ≠ 0) : 0 < x ∧ 0 < y ∧ x + y ≥ 2 := by
  scalar_tac

-- Checking that we can prove exfalso
example (a : Prop) (x : Int) (h0: 0 < x) (h1: x < 0) : a := by
  scalar_tac

-- Intermediate cast through natural numbers
example (a : Prop) (x : Int) (h0: (0 : Nat) < x) (h1: x < 0) : a := by
  scalar_tac

example (x : Int) (h : x ≤ -3) : x ≤ -2 := by
  scalar_tac

example (x y : Int) (h : x + y = 3) :
  let z := x + y
  z = 3 := by
  intro z
  omega

example (P : Nat → Prop) (z : Nat) (h : ∀ x, P x → x ≤ z) (y : Nat) (hy : P y) :
  y + 2 ≤ z + 2 := by
  have := h y hy
  scalar_tac

-- Checking that we manage to split the cases/if then else
example (x : Int) (b : Bool) (h : if b then x ≤ 0 else x ≤ 0) : x ≤ 0 := by
  scalar_tac +split

/-!
Checking some non-linear problems
-/

example (x y : Nat) (h0 : x ≤ 4) (h1 : y ≤ 5): x * y ≤ 4 * 5 := by
  scalar_tac +nonLin

example (x y : Nat) (h0 : x ≤ 4) (h1 : y < 5): x * y < 4 * 5 := by
  scalar_tac +nonLin

example (x y : Nat) (h0 : x < 4) (h1 : y < 5): x * y < 4 * 5 := by
  scalar_tac +nonLin

example (x y : Nat) (h0 : x < 4) (h1 : y ≤ 5): x * y < 4 * 5 := by
  scalar_tac +nonLin


example (x _y : U32) : x.val ≤ UScalar.max .U32 := by
  scalar_tac_preprocess

example (x _y : U32) : x.val ≤ UScalar.max .U32 := by
  scalar_tac

-- Checking that we explore the goal *and* projectors correctly
example (x : U32 × U32) : 0 ≤ x.fst.val := by
  scalar_tac

-- Checking that we properly handle [ofInt]
example : (U32.ofNat 1).val ≤ U32.max := by
  scalar_tac

example (x : Nat) (h1 : x ≤ U32.max) :
  (U32.ofNat x (by scalar_tac)).val ≤ U32.max := by
  scalar_tac

-- Not equal
example (x : U32) (h0 : ¬ x = U32.ofNat 0) : 0 < x.val := by
  scalar_tac

/- See this: https://aeneas-verif.zulipchat.com/#narrow/stream/349819-general/topic/U64.20trouble/near/444049757

   We solved it by removing the instance `OfNat` for `Scalar`.
   Note however that we could also solve it with a simplification lemma.
   However, after testing, we noticed we could only apply such a lemma with
   the rewriting tactic (not the simplifier), probably because of the use
   of typeclasses. -/
example {u: U64} (h1: (u : Nat) < 2): (u : Nat) = 0 ∨ (u : Nat) = 1 := by
  scalar_tac

example (x : I32) : -100000000000 < x.val := by
  scalar_tac

example : (Usize.ofNat 2).val ≠ 0 := by
  scalar_tac

example (x : U32) : x.val ≤ Usize.max := by scalar_tac
example (x : I32) : x.val ≤ Isize.max := by scalar_tac
example (x : I32) : Isize.min ≤ x.val := by scalar_tac

example (x y : Nat) (z : Int) (h : Int.subNatNat x y + z = 0) : (x : Int) - (y : Int) + z = 0 := by
  scalar_tac_preprocess

example (x : U32) (h : 16 * x.val ≤ U32.max) :
  4 * (U32.ofNat (4 * x.val) (by scalar_tac)).val ≤ U32.max := by
  scalar_tac

example (b : Bool) (x y : Int) (h : if b then P ∧ x + y < 3 else x + y < 4) : x + y < 5 := by
  scalar_tac +split

open Utils

/- Some tests which introduce big constants (those sometimes cause issues when reducing expressions).

   See for instance: https://github.com/leanprover/lean4/issues/6955
 -/
example (x y : Nat) (h : x = y + 2^32) : 0 ≤ x := by
  scalar_tac

example (x y : Nat) (h : x = y - 2^32) : 0 ≤ x := by
  scalar_tac

set_option maxHeartbeats 500000 in
example
  (xi yi : U32)
  (c0 : U8)
  (hCarryLe : c0.val ≤ 1)
  (c0u : U32)
  (_ : c0u.val = c0.val)
  (s1 : U32)
  (c1 : Bool)
  (hConv1 : if xi.val + c0u.val > U32.max then s1.val = ↑xi + ↑c0u - U32.max - 1 ∧ c1 = true else s1 = xi.val + c0u ∧ c1 = false)
  (s2 : U32)
  (c2 : Bool)
  (hConv2 : if s1.val + yi.val > U32.max then s2.val = ↑s1 + ↑yi - U32.max - 1 ∧ c2 = true else s2 = s1.val + yi ∧ c2 = false)
  (c1u : U8)
  (_ : c1u.val = if c1 = true then 1 else 0)
  (c2u : U8)
  (_ : c2u.val = if c2 = true then 1 else 0)
  (c3 : U8)
  (_ : c3.val = c1u.val + c2u.val):
  c3.val ≤ 1 := by
  scalar_tac +split

example (x y : Nat) (h : x = y - 2^32) : 0 ≤ x := by
  scalar_tac

example (v : { l : List α // l.length ≤ Usize.max }) :
  v.val.length < 2 ^ UScalarTy.Usize.numBits := by
  scalar_tac

example (i : I8) : - 2^(Isize.numBits - 1) ≤ i.val ∧ i.val ≤ 2^(Isize.numBits - 1) := by scalar_tac

example (x : I8) : -2 ^ (System.Platform.numBits - 1) ≤ x.val := by scalar_tac

example
  (α : Type u)
  (v : { l : List α // l.length ≤ Usize.max })
  (nlen : ℕ)
  (h : nlen ≤ U32.max ∨ nlen ≤ 2 ^ Usize.numBits - 1) :
  nlen ≤ 2 ^ Usize.numBits - 1
  := by
  scalar_tac

example
  (α : Type u)
  (v : { l : List α // l.length ≤ Usize.max })
  (nlen : ℕ)
  (h : (decide (nlen ≤ U32.max) || decide (nlen ≤ Usize.max)) = true) :
  nlen ≤ Usize.max
  := by
  scalar_tac

example (x : I8) : x.toNat = x.val.toNat := by scalar_tac

/- `assumption` triggers a "max recursion depth" error if `U32.max` is reducible -/
example (x y : U32)
    (h : 2 * x.val + 1 + y.val ≤ (U32.max : Int)) :
  2 * x.val + 1 ≤ (U32.max : Int) := by
  try assumption
  scalar_tac

example (d k : ℕ) (hdn : d < k) :
  let nBits := d ⊓ k;
  2 < 2 ^ k → 2 ^ nBits < 2 ^ k := by
  intros nBits h
  scalar_tac +nonLin

-- TODO: improve this one
example (d i : ℕ) (h : i ≤ 256) : d * i / 8 ≤ d * 256 / 8 := by
  apply Nat.div_le_div_right
  scalar_tac +nonLin

/- This example exhibited an "unknown free variable" bug because expressions
   containing free variables were not properly ignored. -/
example
  (layer : ℕ)
  (_ : layer < 7)
  (_ : ∀ (a b : Nat), b = a * (a + 1) → True) :
  True
  := by
  scalar_tac


def inv (x : Nat) : Prop := 0 < x ∧ x % 2 = 0
@[scalar_tac inv x]
theorem inv_imp (x : Nat) (h : inv x) : 0 < x ∧ x % 2 = 0 := by simp [inv] at h; assumption

--example (x y : Nat) (h : inv x) : y % x < x := by
--  scalar_tac


end Aeneas.Std.ScalarTac.Tests
