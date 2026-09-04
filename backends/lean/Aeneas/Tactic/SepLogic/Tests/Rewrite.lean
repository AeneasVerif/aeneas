import Aeneas.Tactic.SepLogic.Rewrite

/-!
# Regression tests for `irewrite`
-/

namespace Aeneas.Tactic.SepLogic.Tests.Rewrite

open Aeneas.SepLogic

example (P Q R : IProp) (h : P ⊢ Q) : P ∗ R ⊢ Q ∗ R := by
  irewrite h
  iframe

/-- The rule accepts an equality as well as an entailment. -/
example (P Q R : IProp) (h : P = Q) : P ∗ R ⊢ Q ∗ R := by
  irewrite h
  iframe

/-- The rewritten atom need not occur first: `irewrite` reorders up to
associativity and commutativity. -/
example (P Q R : IProp) (h : P ⊢ Q) : R ∗ P ⊢ Q ∗ R := by
  irewrite h
  iframe

/-- Packaging a wand: the cancellation happens under `wand_intro`. -/
example (P Q : IProp) : emp ⊢ (P ∗ (P -∗ Q)) -∗ Q := by
  apply wand_intro
  irewrite (wand_cancel P Q)
  iframe

end Aeneas.Tactic.SepLogic.Tests.Rewrite
