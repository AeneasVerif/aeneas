module
public import Aeneas
public import Borrow.Borrow
public section

open Aeneas Aeneas.Std Result

/-! Proofs about the extracted `tests/src/borrow.rs`, using the specification theorem of the model
of the blanket `impl<T> Borrow<T> for T` through `step`. -/

namespace borrow

/-- The example of the documentation of `Borrow::borrow`, through the blanket instance: generic code
calls the `borrow` field of the instance, which `step` unfolds to the blanket implementation. -/
theorem check_spec (x : Std.U32) : check (core.borrow.Borrow.Blanket Std.U32) x ⦃ y => y = x ⦄ := by
  unfold check
  step*

/-- A direct call of the blanket implementation. -/
theorem direct_spec (x : Std.U32) : direct x ⦃ y => y = x ⦄ := by
  unfold direct
  step*

end borrow
