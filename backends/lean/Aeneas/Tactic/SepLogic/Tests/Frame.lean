import Aeneas.Tactic.SepLogic.Frame

/-!
# Regression tests for `iframe` and `isimp`
-/

namespace Aeneas.Tactic.SepLogic.Tests.Frame

open Aeneas.SepLogic
open Aeneas.Std (Ref)

example (P Q : IProp) : P ∗ Q ⊢ Q ∗ P := by
  iframe

example (P : IProp) : emp ∗ P ⊢ P := by
  isimp
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

end Aeneas.Tactic.SepLogic.Tests.Frame
