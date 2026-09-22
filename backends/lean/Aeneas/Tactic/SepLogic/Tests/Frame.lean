import Aeneas.Tactic.SepLogic.Frame

/-!
# Regression tests for `iframe` and `isimp`
-/

namespace Aeneas.Tactic.SepLogic.Tests.Frame

open Aeneas.SepLogic
open Aeneas.Std (Ref)

example (P Q : IProp) : P ∗ Q ⊢ Q ∗ P := by
  iframe

example (P Q F : IProp) : iprop(P ∧ Q) ∗ F ⊢ F ∗ iprop(P ∧ Q) := by
  iframe

private def combined (P Q : IProp) : IProp := iprop(P ∧ Q)

example (P Q F : IProp) : combined P Q ∗ F ⊢ F ∗ iprop(P ∧ Q) := by
  iframe

example (P : IProp) : emp ∗ P ⊢ P := by
  isimp

/-- Framing leaves a pure obligation instead of trying to prove it. -/
example (R : IProp) (P : Prop) (hP : ∀ _ : Unit, P) :
    R ⊢ ⌜P⌝ ∗ R := by
  isimp
  guard_target = P
  exact hP ()

/-- Structural-only framing keeps equalities available without rewriting the goal. -/
example (R : IProp) (n : Nat) (hn : n = 0) :
    R ⊢ ⌜n + 1 = 1⌝ ∗ R := by
  isimp only
  guard_target = n + 1 = 1
  rw [hn]

/-- Facts inside resources must survive cancellation. -/
example (R : IProp) (P Q : Prop) (h : Nat → P → Q) :
    ⌜P⌝ ∗ R ⊢ ⌜Q⌝ ∗ ⌜True⌝ ∗ R := by
  isimp
  guard_target = Q
  exact h 0 ‹P›

/-- Unmatched spatial assertions remain visible on both sides. -/
example (P Q R : IProp) (h : Unit → Q ⊢ R) :
    P ∗ Q ⊢ R ∗ P := by
  isimp
  guard_target = Q ⊢ R
  exact h ()

example (R : IProp) (P Q : Prop) (h : ∀ _ : Unit, P ∧ Q) :
    R ⊢ ⌜P⌝ ∗ R ∗ ⌜Q⌝ := by
  isimp
  guard_target = P ∧ Q
  exact h ()

private def wrappedPure (P : Prop) (R : IProp) : IProp := ⌜P⌝ ∗ R

example (R : IProp) (P : Prop) :
    wrappedPure P R ⊢ ⌜P⌝ ∗ R := by
  isimp [wrappedPure]

example (R : IProp) (P Q : Prop) (h : P → Q) :
    wrappedPure P R ⊢ ⌜Q⌝ ∗ R := by
  isimp only [wrappedPure]
  guard_target = Q
  exact h ‹P›

/-- Existential witnesses inferred from spatial resources need no manual names. -/
example (cell : Nat → IProp) (n : Nat) :
    cell n ⊢ iprop(∃ m : Nat, ⌜m = n⌝ ∗ cell m) := by
  isimp

/-- An uninferred witness is a real goal, not a hidden metavariable. -/
example : emp ⊢ iprop(∃ n : Nat, ⌜n = n⌝) := by
  isimp
  guard_target = Nat
  exact 0

/-- Partial cancellation cannot silently prove a duplicated resource. -/
example (R : IProp) : R ⊢ R := by
  fail_if_success
    have : R ⊢ R ∗ R := by isimp
  isimp

/-- Simplifying one goal must not discard its siblings. -/
example (R : IProp) : (R ⊢ R) ∧ True := by
  constructor
  · isimp
  · trivial

set_option linter.unusedTactic false in
/-- A deliberate no-op: facts must stay in an inferred frame. -/
example (H : IProp) (P : Prop) :
    ∃ F : IProp, ⌜P⌝ ∗ H ⊢ H ∗ F := by
  refine ⟨?_, ?_⟩
  swap
  isimp
  fail_if_success
    have : P := by assumption
  iframe

set_option linter.unusedTactic false in
/-- A deliberate no-op: keep existential witnesses inside an inferred frame. -/
example (cell : Nat → IProp) (H : IProp) :
    ∃ F : IProp, (iexists cell) ∗ H ⊢ H ∗ F := by
  refine ⟨?_, ?_⟩
  swap
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

/-- Introduce a postcondition wand while retaining the resources of its source. -/
example (cell : Nat → IProp) (frame : IProp) (P : Nat → Prop)
    (h : ∀ n, P n) :
    frame ⊢
      ((fun n => cell n) -∗+ fun n => iprop(⌜P n⌝ ∗ frame ∗ cell n)) := by
  isimp only
  guard_target = P value
  exact h value

/-- Cancel the callee precondition, introduce its spatial post, and infer the
    output view from ownership before leaving the mathematical obligation. -/
example (cell : Nat → IProp) (pre frame : IProp) (P : Nat → Prop)
    (h : ∀ n, P n) :
    pre ∗ frame ⊢ pre ∗
      ((fun n => cell n) -∗+ fun _ =>
        iprop(∃ view : Nat, ⌜P view⌝ ∗ cell view ∗ frame)) := by
  isimp only
  guard_target = P value
  exact h value

example (cell : Nat → Nat → IProp) (p value : Nat) :
    cell p value ⊢ cell p value ∗
      ((fun r : Nat × Nat => iprop(⌜r.1 = p⌝ ∗ cell p r.2)) -∗+
        fun r => iprop(∃ value', ⌜value' = r.2⌝ ∗ cell r.1 value')) := by
  isimp

/-- Opening a wand must not make an unmatched resource disappear. -/
example (H : IProp) : emp ⊢ ((fun _ : Nat => H) -∗+ fun _ => H) := by
  fail_if_success
    have : emp ⊢ ((fun _ : Nat => H) -∗+ fun _ => H ∗ H) := by
      isimp only
  isimp only

/-- A witness chosen under the wand may depend on the introduced result. -/
example : emp ⊢
    ((fun _ : Nat => emp) -∗+ fun n => iprop(∃ m : Nat, ⌜m = n⌝)) := by
  isimp only
  guard_target = Nat
  · exact value
  · rfl

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

end Aeneas.Tactic.SepLogic.Tests.Frame
