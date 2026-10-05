import Aeneas.Std.RawPtr
import Aeneas.Std.Scalar.WrappingOps
import Aeneas.Tactic.SepLogic
import Aeneas.Tactic.Step.StepStar

/-! Small verified programs shared by the separation-logic regression tests. -/

open Aeneas Aeneas.SepLogic Aeneas.Std.WP
open Aeneas.Std (MutRawPtr RawPtr Result U32)

namespace SepLogic.Fixtures

def add1 (x : Nat) : Result Nat :=
  pure (x + 1)

@[step]
theorem add1.spec (x : Nat) : add1 x ⦃ y => y = x + 1⦄ := by
  unfold add1
  step*

def incr_ptr (p : MutRawPtr U32) : Result Unit := do
  let value ← p.read
  p.write (value.wrapping_add 1#u32)

@[step]
theorem incr_ptr.spec (p : MutRawPtr U32) (value : U32) :
    ⦃ p ↦ value ⦄ incr_ptr p ⦃⇓ p ↦ value.wrapping_add 1#u32⦄ := by
  unfold incr_ptr
  step*

def incr_borrow (value : U32) : Result U32 := do
  let p ← MutRawPtr.mut_to_raw value
  incr_ptr p
  MutRawPtr.end_mut_to_raw p

@[step]
theorem incr_borrow.spec (value : U32) :
    ⦃ emp ⦄ incr_borrow value ⦃⇓ result => ⌜result = value.wrapping_add 1#u32⌝⦄ := by
  unfold incr_borrow
  step*

end SepLogic.Fixtures
