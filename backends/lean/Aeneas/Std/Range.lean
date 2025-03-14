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

structure core.ops.range.Range (α : Type u) where
  mk ::
  start: α
  end_: α

end Std

end Aeneas
