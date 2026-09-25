module
import Aeneas.Do
import Aeneas.Tactic.Step

/-! # Tests for the `grind` option of `step` -/

open Aeneas Aeneas.Std Result

namespace Aeneas.Tactic.Step.Tests.GrindConfig

/- With `-grind`, `step` must not use `grind` (threaded or not) to discharge the preconditions. -/
example (x : U32) (h : x.val < 10) : (x + 1#u32) ⦃ y => y.val = x.val + 1 ⦄ := by
  step -grind
  case hmax => scalar_tac
  case a => assumption

/- By default, the precondition is discharged by `grind`. -/
example (x : U32) (h : x.val < 10) : (x + 1#u32) ⦃ y => y.val = x.val + 1 ⦄ := by
  step
  assumption

end Aeneas.Tactic.Step.Tests.GrindConfig
