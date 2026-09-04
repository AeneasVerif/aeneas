import Aeneas.Tactic.SepLogic.Intro

/-!
# Regression tests for `iintro_entail` and `isimpl`

`iintro`, `iintro_shallow` and `iintro_keep` act on a triple, so their tests
live with the module that defines triples.
-/

namespace Aeneas.Tactic.SepLogic.Tests.Intro

open Aeneas.SepLogic
open Aeneas.Std (Ref)

/-- `isimpl` is `iframe` under the name used for entailment simplification. -/
example (P Q : IProp) : P ∗ Q ⊢ Q ∗ P := by
  isimpl

example {α : Type} (r : Ref α) (x : α) : (r ↦ x ⊢ r ↦ x) ∧ 1 = 1 := by
  refine ⟨by isimpl, rfl⟩

/-- `iintro_entail` moves the pure facts of the left-hand side into the local
context, leaving the right-hand side alone. -/
example (P : Prop) (H : IProp) (hEmp : P → H ⊢ emp) : iprop(⌜P⌝ ∗ H) ⊢ emp := by
  iintro_entail
  exact hEmp ‹P›

/-- The existentials of the left-hand side are introduced too, which is what
lets the right-hand side mention the variable they bind. -/
example {α : Type} (P : α → IProp) : iprop(∃ x, P x) ⊢ iprop(∃ x, P x) := by
  iintro_entail
  iframe

end Aeneas.Tactic.SepLogic.Tests.Intro
