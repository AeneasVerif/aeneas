import CrossCrateUser.Funs
import CrossCrateLib.Properties

/-! # Specifications of the user crate `cross_crate_user`

The functions of the user crate call the translation of the library crate (`cross_crate_lib`):
its default methods, applied to this crate's instances, and its generic functions. Their
specifications are proved with the library's specification theorems
(`CrossCrateLib/Properties.lean`) by `step*` alone: it applies them, and proves their hypotheses
about this crate's instance by stepping through this crate's methods.
-/

open Aeneas Std Result cross_crate_lib

namespace cross_crate_user

/-- The `area` of a square, as implemented in this crate. -/
@[step]
theorem Square.area_spec (s : Square) (h : s.side.val * s.side.val ≤ U32.max) :
    Square.Insts.Cross_crate_libShape.area s ⦃ a => a.val = s.side.val * s.side.val ⦄ := by
  unfold Square.Insts.Cross_crate_libShape.area
  step*

/-- The library's default `double_area`, applied to this crate's `Shape` instance (case E1). -/
theorem square_double_spec (s : Square) (h : 2 * (s.side.val * s.side.val) ≤ U32.max) :
    square_double s ⦃ r => r.val = 2 * (s.side.val * s.side.val) ⦄ := by
  unfold square_double
  step*

/-- The library's generic `sum_double`, called with this crate's `Shape` instance, whose
`double_area` is the library's default (case E5). -/
theorem two_squares_spec (a b : Square)
    (h : 2 * (a.side.val * a.side.val) + b.side.val * b.side.val ≤ U32.max) :
    two_squares a b ⦃ r => r.val = 2 * (a.side.val * a.side.val) + b.side.val * b.side.val ⦄
    := by
  unfold two_squares
  step*

/-! The proofs rely only on Lean's standard axioms: none of the library's items was axiomatized. -/

/--
info: 'cross_crate_user.square_double_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms square_double_spec

/--
info: 'cross_crate_user.two_squares_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms two_squares_spec

end cross_crate_user
