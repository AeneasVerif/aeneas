module
public import Aeneas
public import Borrow.Borrow
public section

open Aeneas Aeneas.Std Result

/-! Proofs for the `impl<T> Borrow<T> for T` examples. -/

namespace borrow

/-- The example of the documentation of `Borrow::borrow`, through the blanket instance. -/
theorem check_spec (x : Std.U32) : check (core.borrow.Borrow.Blanket Std.U32) x ⦃ y => y = x ⦄ := by
  unfold check
  step*

/-- A direct call of the blanket implementation. -/
theorem direct_spec (x : Std.U32) : direct x ⦃ y => y = x ⦄ := by
  unfold direct
  step*

end borrow
