/- Arrays/slices -/
import Lean
import Lean.Meta.Tactic.Simp
import Init.Data.List.Basic
import Mathlib.Tactic.Linarith
import Aeneas.Std.Scalar.Core
import Aeneas.ScalarTac
import Aeneas.Progress.Init

namespace Aeneas

namespace Std

@[rust_type "core::ops::range::Range" (body := .struct [⟨ "end", "end_" ⟩])]
structure core.ops.range.Range (Idx : Type u) where
  mk ::
  start: Idx
  end_: Idx

@[rust_type "core::ops::range::RangeTo" (body := .struct [⟨ "end", "end_" ⟩])]
structure core.ops.range.RangeTo (Idx : Type u) where
  mk ::
  end_: Idx

end Std

end Aeneas
