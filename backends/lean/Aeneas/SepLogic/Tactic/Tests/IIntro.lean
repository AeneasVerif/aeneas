module
public import Aeneas.SepLogic.Tactic.IIntro
public section

namespace Aeneas.SepLogic.Tactic.Tests.IIntro

open Aeneas.SepLogic
open Aeneas.Std (Heap Loc)

private def wrappedEntails (P Q : IProp) : Prop := P ⊢ Q
private def hiddenPure (P : Prop) : IProp := ⌜P⌝

example (P Q : IProp) : P ∗ Q ⊢ Q ∗ P := by
  isimpl

example {α : Type} (r : Loc) (x : α) :
    (owns (Heap.singleton r x) ⊢ owns (Heap.singleton r x)) ∧ 1 = 1 := by
  refine ⟨by isimpl, rfl⟩

example (P : Prop) (H : IProp) (hEmp : P → H ⊢ emp) : iprop(⌜P⌝ ∗ H) ⊢ emp := by
  iintro_entail
  exact hEmp ‹P›

example {α : Type} (P : α → IProp) : iprop(∃ x, P x) ⊢ iprop(∃ x, P x) := by
  iintro_entail
  iframe

example (P : Prop) (H : IProp) : wrappedEntails iprop(⌜P⌝ ∗ H) H := by
  iintro hP
  guard_hyp hP : P
  guard_target = wrappedEntails H H
  unfold wrappedEntails
  iframe

example (H : IProp) : wrappedEntails (hiddenPure False ∗ H) H := by
  iintro hFalse
  contradiction

example (P : Prop) (H : IProp) :
    wrappedEntails iprop(⌜P⌝ ∗ H) iprop(⌜P⌝ ∗ H) := by
  iintro_keep
  rename_i hP
  guard_hyp hP : P
  guard_target = wrappedEntails iprop(⌜P⌝ ∗ H) iprop(⌜P⌝ ∗ H)
  unfold wrappedEntails
  iframe

end Aeneas.SepLogic.Tactic.Tests.IIntro
