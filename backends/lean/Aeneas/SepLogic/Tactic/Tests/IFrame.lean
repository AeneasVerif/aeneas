module
public import Aeneas.SepLogic.Tactic.IFrame
public section

/-!
# Regression tests for `iframe`
-/

namespace Aeneas.SepLogic.Tactic.Tests.IFrame

open Aeneas.SepLogic
open Aeneas.Std (Ref)

example (P Q : IProp) : P ∗ Q ⊢ Q ∗ P := by
  iframe

example (P Q F : IProp) : iprop(P ∧ Q) ∗ F ⊢ F ∗ iprop(P ∧ Q) := by
  iframe

private def combined (P Q : IProp) : IProp := iprop(P ∧ Q)

example (P Q F : IProp) : combined P Q ∗ F ⊢ F ∗ iprop(P ∧ Q) := by
  iframe

example {α : Type} (P : α → IProp) :
    iprop(∃ x, P x) ⊢ iprop(∃ x, P x) := by
  iframe

example {α : Type} (P : α → IProp) :
    iprop(∀ x, P x) ⊢ iprop(∀ x, P x) := by
  iframe

example {α : Type} (r : Ref α) (value : α) :
    r ↦ value ⊢ r ↦ value := by
  iframe

/-- An unmatched pure assertion of the left-hand side may be discarded: the
logic is affine. -/
example (P : IProp) : P ⊢ ⌜8 = 8⌝ := by
  iframe

example {α : Type} (r s : Ref α) (x y : α) :
    r ↦ x ∗ s ↦ y ⊢ s ↦ y ∗ r ↦ x := by
  iframe

/-- Unmatched spatial assertions of the left-hand side are discarded too. -/
example {α : Type} (r s : Ref α) (x y : α) : r ↦ x ∗ s ↦ y ⊢ s ↦ y := by
  iframe

/-- Equalities extracted from ownership must be available during cancellation. -/
example (cell : Nat → Nat → IProp) (p q value : Nat) :
    ⌜p = q⌝ ∗ cell p value ⊢ cell q value := by
  iframe

example (cell : Nat → Nat → IProp) (p q value : Nat) :
    ⌜p = q⌝ ∗ cell p value ⊢
      iprop(∃ value', ⌜value' = value⌝ ∗ cell q value') := by
  iframe

/-- Terminal calls introduce their pure equalities inside a postcondition wand. -/
example (cell : Nat → Nat → IProp) (p value : Nat) :
    cell p value ⊢ cell p value ∗
      ((fun r : Nat × Nat => iprop(⌜r.1 = p⌝ ∗ cell p r.2)) -∗+
        fun r => iprop(∃ value', ⌜value' = r.2⌝ ∗ cell r.1 value')) := by
  iframe

/-- A failed candidate must not commit part of an existential instantiation. -/
example (cell : Nat → Nat → IProp) :
    cell 1 3 ∗ cell 2 4 ⊢
      iprop(∃ p : Nat, ∃ q : Nat, ⌜p = 2 ∧ q = 1⌝ ∗ cell p 4 ∗ cell q 3) := by
  iframe

/-- Cancellation cannot duplicate an arbitrary owned resource. -/
example (cell : IProp) : cell ⊢ cell := by
  fail_if_success
    have : cell ⊢ cell ∗ cell := by iframe
  iframe

end Aeneas.SepLogic.Tactic.Tests.IFrame
