import Aeneas.Tactic.SepLogic.Intro

/-!
# Regression tests for `iintro_entail` and `isimpl`

Specification-wrapper coverage lives with the module that defines those
wrappers.
-/

namespace Aeneas.Tactic.SepLogic.Tests.Intro

open Aeneas.SepLogic
open Aeneas.Std (Ref)

private def wrappedEntails (P Q : IProp) : Prop := P ⊢ Q
private def hiddenPure (P : Prop) : IProp := ⌜P⌝

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

/-- Introduction works through arbitrary reducible wrappers around entailments. -/
example (P : Prop) (H : IProp) : wrappedEntails iprop(⌜P⌝ ∗ H) H := by
  iintro hP
  guard_hyp hP : P
  guard_target = wrappedEntails H H
  unfold wrappedEntails
  iframe

/-- A pure assertion hidden behind a reducible definition is still exposed. -/
example (H : IProp) : wrappedEntails (hiddenPure False ∗ H) H := by
  iintro hFalse
  contradiction

/-- Keeping a pure assertion introduces its fact without changing the wrapper. -/
example (P : Prop) (H : IProp) :
    wrappedEntails iprop(⌜P⌝ ∗ H) iprop(⌜P⌝ ∗ H) := by
  iintro_keep
  rename_i hP
  guard_hyp hP : P
  guard_target = wrappedEntails iprop(⌜P⌝ ∗ H) iprop(⌜P⌝ ∗ H)
  unfold wrappedEntails
  iframe

end Aeneas.Tactic.SepLogic.Tests.Intro
