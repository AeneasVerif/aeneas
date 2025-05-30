/- Arrays/slices -/
import Lean
import Lean.Meta.Tactic.Simp
import Init.Data.List.Basic
import Mathlib.Tactic.Linarith
import Aeneas.Std.Scalar
import Aeneas.ScalarTac
import Aeneas.Progress.Init

namespace Aeneas

namespace Std

/-- [core::ops::range::Range] -/
structure core.ops.range.Range (Idx : Type u) where
  mk ::
  start: Idx
  end_: Idx

/-- [core::ops::range::RangeTo] -/
structure core.ops.range.RangeTo (Idx : Type u) where
  mk ::
  end_: Idx

end Std

end Aeneas
