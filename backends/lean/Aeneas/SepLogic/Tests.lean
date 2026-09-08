import Aeneas.SepLogic.PredicateTransformer

/-!
# Regression tests for the separation logic itself

The lemmas of the assertion language and of the predicate transformers, proved
without the proof mode.  The tactic tests are in `Aeneas.Tactic.SepLogic.Tests`.
-/

namespace Aeneas.SepLogic.Tests

example (P Q : IProp) : (P ∗ Q) ⊣⊢ (Q ∗ P) :=
  sep_comm P Q

example (P : IProp) : (emp ∗ P) = P := by
  simp

example (P : IProp) : (⌜True⌝ ∗ P) = P := by
  simp

example (P Q : IProp) : P ∗ (P -∗ Q) ⊢ Q :=
  wand_cancel P Q

example (Q₁ Q₂ : IPost Nat) : Q₁ ∗+ (Q₁ -∗+ Q₂) ⊢+ Q₂ :=
  postWand_cancel Q₁ Q₂

example {α : Type} (w : Wp α) : w.wp = Wp.wp w :=
  rfl

/-- A slot cannot be owned twice: separation is still separation. -/
example {α : Type} (r : Aeneas.Std.Ref α) (x y : α) : r ↦ x ∗ r ↦ y ⊢ ⌜False⌝ :=
  Ref.pointsTo_exclusive r x y

end Aeneas.SepLogic.Tests
