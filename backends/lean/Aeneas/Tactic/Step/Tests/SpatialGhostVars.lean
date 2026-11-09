module
public import Aeneas.Tactic.Step
public section

/-! # `step` on separation-logic specifications: frame inference and output destructuring

`step` infers the frame of a callee's precondition (`iframe` in frame-inference mode), proves the
pure parts of that precondition, and introduces the callee's outputs and postconditions. -/

namespace Aeneas.Tactic.Step.Tests.SpatialGhostVars

open Aeneas.Std Aeneas.SepLogic

example (cell : Nat → Nat → IProp) (read : Nat → Result Nat)
    (hread : ∀ p value, 0 < value →
      ⦃ cell p value ⦄ read p
      ⦃ result => ⌜result = value⌝ ∗ cell p value ⦄)
    (p current : Nat) (hcurrent : 0 < current) :
    ⦃ cell p current ⦄ read p
    ⦃ result => cell p current ∗ ⌜result = current⌝ ⦄ := by
  step*

-- The spec above with the pure condition in the precondition instead of as a premise: frame
-- inference matches `cell p ?value` and proves `0 < current` from the context.
example (cell : Nat → Nat → IProp) (read : Nat → Result Nat)
    (hread : ∀ p value,
      ⦃ ⌜0 < value⌝ ∗ cell p value ⦄ read p
      ⦃ result => ⌜result = value⌝ ∗ cell p value ⦄)
    (p current : Nat) (hcurrent : 0 < current) :
    ⦃ cell p current ⦄ read p
    ⦃ result => cell p current ∗ ⌜result = current⌝ ⦄ := by
  step*

example (cell : Nat → Nat → IProp) (read : Nat → Result Nat)
    (hread : ∀ p value, 0 < value →
      ⦃ cell p value ⦄ read p
      ⦃ result => ⌜result = value⌝ ∗ cell p value ⦄)
    (p current : Nat) (frame : IProp) (hcurrent : 0 < current) :
    WP.ispec (frame ∗ cell p current)
    (do let value ← read p; pure (value + 1))
    (fun result => iprop(⌜result = current + 1⌝ ∗ cell p current ∗ frame)) := by
  step*

example (cell : Nat → Nat → IProp) (read : Nat → Result Nat)
    (hread : ∀ p value, 0 < value →
      ⦃ cell p value ⦄ read p
      ⦃ result => ⌜result = value⌝ ∗ cell p value ⦄)
    (p current : Nat) (hcurrent : 0 < current) :
    WP.dispec (cell p current) (read p)
      (fun result => iprop(⌜result = current⌝ ∗ cell p current)) := by
  step*

example (cell : Nat → Nat → IProp) (read : Nat → Result Nat)
    (hread : ∀ p value, 0 < value →
      ⦃ cell p value ⦄ read p
      ⦃ result => ⌜result = value⌝ ∗ cell p value ⦄)
    (p q current : Nat) (hp : q = p) (hcurrent : 0 < current) :
    WP.ispec (cell p current)
      (do let value ← read q; pure (value + 1))
      (fun result => iprop(⌜result = current + 1⌝ ∗ cell p current)) := by
  subst hp
  step*

example (pre frame : IProp) (cell : Nat → IProp) (P Q : Nat → Prop)
    (run : Result (Nat × Nat))
    (hrun : ⦃ pre ⦄ run
      ⦃ x y => ∃ view : Nat, ⌜view = x + y ∧ P view⌝ ∗ cell view ⦄)
    (hQ : ∀ n, P n → Q n) :
    ⦃ frame ∗ pre ⦄ run
    ⦃ x y => ∃ view : Nat, ⌜view = x + y ∧ Q view⌝ ∗ cell view ∗ frame ⦄ := by
  step with hrun as ⟨x, y, view, hView, hP⟩
  exact ⟨hView, hQ view hP⟩

example (pre frame : IProp) (cell : Nat → IProp) (P Q : Nat → Prop)
    (run : Result (Nat × Nat))
    (hrun : WP.dispec pre run
      (fun (x, y) => iprop(∃ view : Nat, ⌜view = x + y ∧ P view⌝ ∗ cell view)))
    (hQ : ∀ n, P n → Q n) :
    WP.dispec (frame ∗ pre) run
      (fun (x, y) => iprop(∃ view : Nat, ⌜view = x + y ∧ Q view⌝ ∗ cell view ∗ frame)) := by
  step with hrun as ⟨result, view, hView, hP⟩
  exact ⟨hView, hQ view hP⟩

example (H : IProp) (run : Result Nat)
    (hrun : ⦃ H ⦄ run ⦃ _ => H ⦄) :
    ⦃ H ⦄ run ⦃ result => ∃ witness : Nat, ⌜witness = result⌝ ∗ H ⦄ := by
  step with hrun

example (cell : Nat → IProp) (n : Nat) (P : Nat → Prop) (hP : Unit → P n) :
    ⦃ cell n ⦄
    Result.ok (n, n, n, n, n, n, n, n, n, n, n, n, n, n, n, n, n, n, n, n)
    ⦃ first _a2 _a3 _a4 _a5 _a6 _a7 _a8 _a9 _a10
        _a11 _a12 _a13 _a14 _a15 _a16 _a17 _a18 _a19 last =>
      ∃ view : Nat, ⌜view = first ∧ P last⌝ ∗ cell view ⦄ := by
  step
  guard_target = P n
  exact hP ()

example (cell : Nat → IProp) (n : Nat) (P : Nat → Prop) (hP : Unit → P n) :
    ⦃ cell n ⦄
    Result.ok (n, n, n, n, n, n, n, n, n, n, n, n,
      n, n, n, n, n, n, n, n, n, n, n, n)
    ⦃ first _a2 _a3 _a4 _a5 _a6 _a7 _a8 _a9 _a10 _a11 _a12
        _a13 _a14 _a15 _a16 _a17 _a18 _a19 _a20 _a21 _a22 _a23 last =>
      ∃ view : Nat, ⌜view = first ∧ P last⌝ ∗ cell view ⦄ := by
  step
  guard_target = P n
  exact hP ()

example (cell : Nat → IProp) (n : Nat) (P : Nat → Prop) (hP : Unit → P n) :
    ⦃ cell n ⦄
    Result.ok (n, n, n, n, n, n, n, n, n, n, n, n,
      n, n, n, n, n, n, n, n, n, n, n, n)
    ⦃ first _a2 _a3 _a4 _a5 _a6 _a7 _a8 _a9 _a10 _a11 _a12
        _a13 _a14 _a15 _a16 _a17 _a18 _a19 _a20 _a21 _a22 _a23 last =>
      ∃ view : Nat, ⌜view = first ∧ P last⌝ ∗ cell view ⦄div := by
  step
  guard_target = P n
  exact hP ()

end Aeneas.Tactic.Step.Tests.SpatialGhostVars
