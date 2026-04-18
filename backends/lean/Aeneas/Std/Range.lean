/- Arrays/slices -/
import Lean
import Lean.Meta.Tactic.Simp
import Init.Data.List.Basic
import Mathlib.Tactic.Linarith
import Aeneas.Std.Scalar.Core
import Aeneas.Tactic.Solver.ScalarTac
import Aeneas.Tactic.Step.Init

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

/-- `core::ops::range::RangeFull` — unit marker for the `..` syntax.
Modeled as `Unit` to match Aeneas's default encoding for unit structs. -/
@[reducible, rust_type "core::ops::range::RangeFull"]
def core.ops.range.RangeFull := Unit

/-- `core::ops::range::Bound<T>`: the three kinds of endpoint used by
`RangeBounds` — inclusive, exclusive, or unbounded.

- Docs: https://doc.rust-lang.org/core/ops/enum.Bound.html
- Source: https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/ops/range.rs
-/
@[rust_type "core::ops::range::Bound"]
inductive core.ops.range.Bound (T : Type u) where
| Included : T → core.ops.range.Bound T
| Excluded : T → core.ops.range.Bound T
| Unbounded : core.ops.range.Bound T

end Std

end Aeneas
