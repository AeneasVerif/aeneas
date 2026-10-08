module
public import Aeneas.SepLogic.Tactic.ISimp
public section

namespace Aeneas.SepLogic.Tactic.Tests.ISimp

open Aeneas.SepLogic

example (P : IProp) : emp ∗ P ⊢ P := by
  isimp

example (R : IProp) (P : Prop) (hP : ∀ _ : Unit, P) :
    R ⊢ ⌜P⌝ ∗ R := by
  isimp
  guard_target = P
  exact hP ()

example (R : IProp) (n : Nat) (hn : n = 0) :
    R ⊢ ⌜n + 1 = 1⌝ ∗ R := by
  isimp only
  guard_target = n + 1 = 1
  rw [hn]

example (R : IProp) (P Q : Prop) (h : Nat → P → Q) :
    ⌜P⌝ ∗ R ⊢ ⌜Q⌝ ∗ ⌜True⌝ ∗ R := by
  isimp
  guard_target = Q
  exact h 0 ‹P›

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

example (cell : Nat → IProp) (n : Nat) :
    cell n ⊢ iprop(∃ m : Nat, ⌜m = n⌝ ∗ cell m) := by
  isimp

example : emp ⊢ iprop(∃ n : Nat, ⌜n = n⌝) := by
  isimp
  guard_target = Nat
  exact 0

example (R : IProp) : R ⊢ R := by
  fail_if_success
    have : R ⊢ R ∗ R := by isimp
  isimp

example (R : IProp) : (R ⊢ R) ∧ True := by
  constructor
  · isimp
  · trivial

set_option linter.unusedTactic false in
example (H : IProp) (P : Prop) :
    ∃ F : IProp, ⌜P⌝ ∗ H ⊢ H ∗ F := by
  refine ⟨?_, ?_⟩
  swap
  isimp
  fail_if_success
    have : P := by assumption
  iframe

set_option linter.unusedTactic false in
example (cell : Nat → IProp) (H : IProp) :
    ∃ F : IProp, (iexists cell) ∗ H ⊢ H ∗ F := by
  refine ⟨?_, ?_⟩
  swap
  isimp
  iframe

example (cell : Nat → IProp) (frame : IProp) (P : Nat → Prop)
    (h : ∀ n, P n) :
    frame ⊢
      ((fun n => cell n) -∗+ fun n => iprop(⌜P n⌝ ∗ frame ∗ cell n)) := by
  isimp only
  guard_target = P value
  exact h value

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

example (H : IProp) : emp ⊢ ((fun _ : Nat => H) -∗+ fun _ => H) := by
  fail_if_success
    have : emp ⊢ ((fun _ : Nat => H) -∗+ fun _ => H ∗ H) := by
      isimp only
  isimp only

example : emp ⊢
    ((fun _ : Nat => emp) -∗+ fun n => iprop(∃ m : Nat, ⌜m = n⌝)) := by
  isimp only

example (cell : Nat → IProp) (a b : Nat) :
    cell a ∗ cell b ⊢ iprop(∃ m : Nat, ⌜m = b⌝ ∗ cell m) := by
  isimp
  iframe

example (cell : Nat → IProp) (a b : Nat) :
    cell a ∗ cell b ⊢ iprop(∃ m : Nat, cell m ∗ cell a) := by
  isimp

end Aeneas.SepLogic.Tactic.Tests.ISimp
