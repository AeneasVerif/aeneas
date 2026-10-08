module
public import Aeneas.SepLogic.Tactic.IFrame
public import Aeneas.Std.RawPtr
public section

namespace Aeneas.SepLogic.Tactic.Tests.IFrame

open Aeneas.SepLogic
open Aeneas.Std (MutRawPtr)

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

example {α : Type} (r : MutRawPtr α) (value : α) :
    r ↦ value ⊢ r ↦ value := by
  iframe

example (P : IProp) : P ⊢ ⌜8 = 8⌝ := by
  iframe

example {α : Type} (r s : MutRawPtr α) (x y : α) :
    r ↦ x ∗ s ↦ y ⊢ s ↦ y ∗ r ↦ x := by
  iframe

example {α : Type} (r s : MutRawPtr α) (x y : α) : r ↦ x ∗ s ↦ y ⊢ s ↦ y := by
  iframe

example (cell : Nat → Nat → IProp) (p q value : Nat) :
    ⌜p = q⌝ ∗ cell p value ⊢ cell q value := by
  iframe

example (cell : Nat → Nat → IProp) (p q value : Nat) :
    ⌜p = q⌝ ∗ cell p value ⊢
      iprop(∃ value', ⌜value' = value⌝ ∗ cell q value') := by
  iframe

example (cell : Nat → Nat → IProp) (p value : Nat) :
    cell p value ⊢ cell p value ∗
      ((fun r : Nat × Nat => iprop(⌜r.1 = p⌝ ∗ cell p r.2)) -∗+
        fun r => iprop(∃ value', ⌜value' = r.2⌝ ∗ cell r.1 value')) := by
  iframe

example (cell : Nat → Nat → IProp) :
    cell 1 3 ∗ cell 2 4 ⊢
      iprop(∃ p : Nat, ∃ q : Nat, ⌜p = 2 ∧ q = 1⌝ ∗ cell p 4 ∗ cell q 3) := by
  iframe

example (cell : IProp) : cell ⊢ cell := by
  fail_if_success
    have : cell ⊢ cell ∗ cell := by iframe
  iframe

example (cell : Nat → IProp) (a b : Nat) :
    cell a ∗ cell b ⊢ iprop(∃ m : Nat, ⌜m = b⌝ ∗ cell m) := by
  iframe

example : (emp : IProp) ⊢ iexists fun _ : Nat => (emp : IProp) := by
  fail_if_success iframe
  exact entails_exists_r 0 (entails_refl _)

example (P R : IProp) : R ⊢ iprop(P -∗ (P ∗ R)) := by
  iframe

example (P R S : IProp) : R ∗ S ⊢ iprop(S ∗ (P -∗ (R ∗ P))) := by
  iframe

private def wrap (P : IProp) : IProp := P

-- `P` matches `wrap P` only by unfolding, and the atoms must be reordered
example (P R : IProp) : wrap P ∗ R ⊢ R ∗ P := by
  iframe

private def wrap' (P : IProp) : IProp := P

-- `P` is matched with `wrap P` and with `wrap' P`: all three are one atom of the reordering
example (P : IProp) : P ∗ wrap' P ⊢ wrap P ∗ P := by
  iframe

end Aeneas.SepLogic.Tactic.Tests.IFrame
