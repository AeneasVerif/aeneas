import Aeneas.SLPoC.MutableData.Ptr

/-!
# Curry, introduction, and `qimp` elimination interaction

This file checks that currying exposes result components before the
introduction and `qimp`-elimination passes extract pure facts embedded anywhere
in a spatial assertion.
-/

namespace CurryIntroQimpTests

open Aeneas.Std (Result)
open Aeneas.SepLogic
open Aeneas.SepLogic.WP

def pairResult (_p : Ptr Nat) : Result (Nat × Nat) :=
  Result.ok (1, 2)

@[step]
theorem pairResult.spec (p : Ptr Nat) (n : Nat) :
    ⦃ p ↦ n ⦄ pairResult p ⦃⇓ x y =>
      p ↦ n ∗ ⌜x = 1⌝ ∗ ⌜y = 2⌝
    ⦄ := by
  unfold pairResult
  step
  iframe

def consumePair (p : Ptr Nat) : Result Nat := do
  let (x, y) ← pairResult p
  pure (x + y)

/-- Pure facts to the right of a spatial resource are introduced after the
curried result components. -/
example (p : Ptr Nat) (n : Nat) :
    ⦃ p ↦ n ⦄ consumePair p ⦃⇓ result =>
      p ↦ n ∗ ⌜result = 3⌝
    ⦄ := by
  unfold consumePair
  step as ⟨ x, y, hx, hy ⟩
  guard_hyp hx : x = 1
  guard_hyp hy : y = 2
  step*

/-- Facts in the inferred frame remain spatial and are not included among the
names introduced from the callee postcondition. -/
example (p : Ptr Nat) (n : Nat) (F : Prop) :
    ⦃ p ↦ n ∗ ⌜F⌝ ⦄ consumePair p ⦃⇓ result =>
      p ↦ n ∗ ⌜F⌝ ∗ ⌜result = 3⌝
    ⦄ := by
  unfold consumePair
  step as ⟨ x, y, hx, hy ⟩
  guard_hyp hx : x = 1
  guard_hyp hy : y = 2
  fail_if_success have : F := by assumption
  step*

end CurryIntroQimpTests
