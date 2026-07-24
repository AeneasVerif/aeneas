/- Arrays/slices -/
module
public import Lean
public import Lean.Meta.Tactic.Simp
public import Init.Data.List.Basic
public import Mathlib.Tactic.Linarith
public import Aeneas.Std.Scalar.Core
public import Aeneas.Tactic.Solver.ScalarTac
public import Aeneas.Tactic.Step.Init
public section

namespace Aeneas

namespace Std

@[rust_type "core::ops::range::Range"]
structure core.ops.range.Range (Idx : Type u) where
  mk ::
  start: Idx
  «end»: Idx

@[rust_type "core::ops::range::RangeTo"]
structure core.ops.range.RangeTo (Idx : Type u) where
  mk ::
  «end»: Idx

/-- `core::ops::range::RangeInclusive` (`a..=b`).

    Modelled with the three logical fields of the Rust struct: `start`, `«end»`,
    and the `exhausted` flag (set once `a..=a` yields its single element).
    `is_empty` is `exhausted || start > «end»`. -/
@[rust_type "core::ops::range::RangeInclusive"]
structure core.ops.range.RangeInclusive (Idx : Type u) where
  mk ::
  start : Idx
  «end» : Idx
  exhausted : Bool

end Std

end Aeneas
