import Aeneas.Std.RawPtrSpecs
import Aeneas.SepLogic.Tactic
import Aeneas.Tactic.Step.StepStar

open Aeneas Aeneas.SepLogic Aeneas.Std.WP
open Aeneas.Std

namespace SepLogic.Fixtures

def add1 (x : Nat) : Result Nat :=
  pure (x + 1)

@[step]
theorem add1.spec (x : Nat) : add1 x ⦃ y => y = x + 1⦄ := by
  unfold add1
  step*

def incr_ptr (p : MutRawPtr U32) : Result Unit := do
  let value ← p.read
  let value' ← value + 1#u32
  p.write value'

@[step]
theorem incr_ptr.spec (p : MutRawPtr U32) (value : U32) (h : value.val + 1 ≤ U32.max) :
    ⦃ p ↦ value ⦄ incr_ptr p ⦃ ∃ v, ⌜v.val = value.val + 1⌝ ∗ p ↦ v ⦄ := by
  unfold incr_ptr
  step*

/-- The pointer exposes the place of `value` (see `core.ptr.from_mut`): the increment is read back
through it. As in the extracted code, the address of the exposure comes from a placement. -/
def incr_borrow (placement : Placement) (value : U32) : Result U32 := do
  let (p, back) ← core.ptr.from_mut (placement.addr 0) ⟨value⟩
  incr_ptr p
  back

@[step]
theorem incr_borrow.spec (placement : Placement) (value : U32) (h : value.val + 1 ≤ U32.max) :
    ⦃ emp ⦄ incr_borrow placement value ⦃ result => ⌜result.val = value.val + 1⌝⦄ := by
  unfold incr_borrow
  step*
  subst_vars
  step*

end SepLogic.Fixtures
