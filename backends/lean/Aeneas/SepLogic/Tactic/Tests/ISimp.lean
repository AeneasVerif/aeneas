module
public import Aeneas.SepLogic.Tactic.ISimp
public section

/-!
# Regression tests for `isimp`
-/

namespace Aeneas.SepLogic.Tactic.Tests.ISimp

open Aeneas.SepLogic

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

end Aeneas.SepLogic.Tactic.Tests.ISimp
