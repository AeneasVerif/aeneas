module
import Aeneas.Tactic.Step

open Aeneas Aeneas.Std Result

namespace Aeneas.Tactic.Step.Tests.SplitNegation

/- `step*` simplifies the negated condition when splitting an `if` -/
example (b : Bool) : (if ¬ b then ok 0 else ok 1 : Result Nat) ⦃ r => r ≤ 1 ⦄ := by
  step*

end Aeneas.Tactic.Step.Tests.SplitNegation
