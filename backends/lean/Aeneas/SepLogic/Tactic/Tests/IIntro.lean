module
public import Aeneas.SepLogic.Tactic.IIntro
public import Aeneas.Std.RawPtr
public section

namespace Aeneas.SepLogic.Tactic.Tests.IIntro

open Aeneas.SepLogic
open Aeneas.Std (MutRawPtr)

private def wrappedEntails (P Q : IProp) : Prop := P ⊢ Q
private def hiddenPure (P : Prop) : IProp := ⌜P⌝

example (P Q : IProp) : P ∗ Q ⊢ Q ∗ P := by
  iframe

example {α : Type} (r : MutRawPtr α) (x : α) : (r ↦ x ⊢ r ↦ x) ∧ 1 = 1 := by
  refine ⟨by iframe, rfl⟩

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

-- `iintro_shallow` pulls the real `⌜P⌝`, not the pure fact hidden in `hiddenPure`.
example (P Q : Prop) (H : IProp) : wrappedEntails (hiddenPure Q ∗ ⌜P⌝ ∗ H) H := by
  iintro_shallow
  guard_hyp h : P
  guard_target = wrappedEntails (hiddenPure Q ∗ H) H
  unfold wrappedEntails hiddenPure
  iframe

example (P : Prop) (H : IProp) :
    wrappedEntails iprop(⌜P⌝ ∗ H) iprop(⌜P⌝ ∗ H) := by
  iintro_keep
  rename_i hP
  guard_hyp hP : P
  guard_target = wrappedEntails iprop(⌜P⌝ ∗ H) iprop(⌜P⌝ ∗ H)
  unfold wrappedEntails
  iframe

example (P Q : Prop) (H : IProp) :
    wrappedEntails iprop(⌜P⌝ ∗ H ∗ ⌜Q⌝) H := by
  iintro_keep
  rename_i hP hQ
  guard_hyp hP : P
  guard_hyp hQ : Q
  guard_target = wrappedEntails iprop(⌜P⌝ ∗ H ∗ ⌜Q⌝) H
  unfold wrappedEntails
  iframe

example (P Q : Prop) (H : IProp) (_ : P) :
    wrappedEntails iprop(⌜P⌝ ∗ H ∗ ⌜Q⌝) H := by
  iintro_keep
  rename_i hQ
  guard_hyp hQ : Q
  unfold wrappedEntails
  iframe

end Aeneas.SepLogic.Tactic.Tests.IIntro
