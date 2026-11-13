import CrossCrateLib.Funs

/-! # Specifications of the library crate `cross_crate_lib`

The theorems hold for every implementation of `Shape`: they only assume specifications of the
implementation's methods, as hypotheses. `CrossCrateUser/Properties.lean` uses them with the
implementations of the user crate, whose translation calls this crate's translation: `step` proves
those hypotheses itself, by stepping through the user's methods (see
`Aeneas.Tactic.Step.SpecDischarge`), so the user's proofs are just `step*`.
-/

open Aeneas Std Result

namespace cross_crate_lib

/-- The default `double_area` doubles the area: if the implementation's `area` computes `f`, the
default `double_area` computes `2 * f`. -/
@[step]
theorem Shape.double_area.default_spec {Self : Type} (ShapeInst : Shape Self) (f : Self → Nat)
    (harea : ∀ x, f x ≤ U32.max → ShapeInst.area x ⦃ a => a.val = f x ⦄)
    (x : Self) (h : 2 * f x ≤ U32.max) :
    Shape.double_area.default ShapeInst x ⦃ r => r.val = 2 * f x ⦄ := by
  unfold Shape.double_area.default
  step*

/-- `sum_double a b` adds the double area of `a` and the area of `b`. -/
@[step]
theorem sum_double_spec {T : Type} (ShapeInst : Shape T) (f g : T → Nat)
    (harea : ∀ x, f x ≤ U32.max → ShapeInst.area x ⦃ a => a.val = f x ⦄)
    (hdouble : ∀ x, g x ≤ U32.max → ShapeInst.double_area x ⦃ d => d.val = g x ⦄)
    (a b : T) (h : g a + f b ≤ U32.max) :
    sum_double ShapeInst a b ⦃ r => r.val = g a + f b ⦄ := by
  unfold sum_double
  step*

end cross_crate_lib
