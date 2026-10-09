import Aeneas.Std.RawPtr
import Aeneas.SepLogic.Tactic
import Aeneas.Tactic.Step.StepStar

open Aeneas Aeneas.SepLogic Aeneas.Std.WP
open Aeneas.Std (MutRawPtr RawPtr Result)

namespace SepLogic.Fixtures

def add1 (x : Nat) : Result Nat :=
  pure (x + 1)

@[step]
theorem add1.spec (x : Nat) : add1 x ⦃ y => y = x + 1⦄ := by
  unfold add1
  step*

def incr_ptr (p : MutRawPtr Nat) : Result Unit := do
  let value ← p.read
  p.write (value + 1)

@[step]
theorem incr_ptr.spec (p : MutRawPtr Nat) (value : Nat) :
    ⦃ p ↦ value ⦄ incr_ptr p ⦃ p ↦ value + 1⦄ := by
  unfold incr_ptr
  step*

/-- The pointer points to a copy of `value` (see `core.ptr.from_mut`): the increment is read back
through it. -/
def incr_borrow (value : Nat) : Result Nat := do
  let (p, _) ← Aeneas.Std.core.ptr.from_mut value
  incr_ptr p
  p.read

@[step]
theorem incr_borrow.spec (value : Nat) :
    ⦃ emp ⦄ incr_borrow value ⦃ result => ⌜result = value + 1⌝⦄ := by
  unfold incr_borrow
  step*

end SepLogic.Fixtures
