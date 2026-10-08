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

-- a fact occurring twice is copied once
example (P : Prop) (H : IProp) : wrappedEntails iprop(⌜P⌝ ∗ H ∗ ⌜P⌝) H := by
  iintro_keep
  rename_i hP
  fail_if_success have : P := by clear hP; assumption
  unfold wrappedEntails
  iframe

-- `iintro x` opens the `∃` in place, and nothing else
example {α : Type} (P : α → IProp) (H G Q : IProp) (R : Prop)
    (h : ∀ x, (H ∗ P x) ∗ ⌜R⌝ ∗ G ⊢ Q) : (H ∗ iprop(∃ x, P x)) ∗ ⌜R⌝ ∗ G ⊢ Q := by
  iintro y
  guard_target = ((H ∗ P y) ∗ ⌜R⌝ ∗ G ⊢ Q)
  exact h y

-- one fact per pattern, removed in place
example (P Q : Prop) (H G : IProp) : (⌜P⌝ ∗ H) ∗ ⌜Q⌝ ∗ G ⊢ G := by
  iintro hP
  guard_hyp hP : P
  guard_target = (H ∗ ⌜Q⌝ ∗ G ⊢ G)
  iframe

example {α : Type} (P : α → IProp) (Q : IProp) (h : ∀ x, P x ⊢ Q) : iprop(∃ x, P x) ⊢ Q := by
  iintro y
  guard_target = (P y ⊢ Q)
  exact h y

-- the frame, the right operand of the precondition, is left untouched
example (P F : Prop) (H : IProp) (hFrame : P → H ∗ ⌜F⌝ ⊢ H ∗ ⌜F⌝) :
    (H ∗ ⌜P⌝) ∗ ⌜F⌝ ⊢ H ∗ ⌜F⌝ := by
  iintro_shallow_post
  guard_hyp h : P
  fail_if_success have : F := by assumption
  exact hFrame h

end Aeneas.SepLogic.Tactic.Tests.IIntro
