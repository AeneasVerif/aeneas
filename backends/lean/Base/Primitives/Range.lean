/- Arrays/slices -/
import Lean
import Lean.Meta.Tactic.Simp
import Init.Data.List.Basic
import Mathlib.Tactic.Linarith
import Base.Primitives.Scalar
import Base.Arith
import Base.Progress.Base

namespace Primitives

structure core.ops.range.Range (α : Type u) where
  mk ::
  start: α
  end_: α

end Primitives
