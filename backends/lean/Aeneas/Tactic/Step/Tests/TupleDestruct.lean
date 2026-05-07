import Aeneas.Std.Slice
import Aeneas.Tactic.Step

open Aeneas Aeneas.Std Result

namespace step_tuple_destruct

/- A function that returns a pair, then destructures it -/
def getPairAndUse (x : U32) : Result U32 := do
  let pair ← do
    let a ← x + 1#u32
    ok (a, x)
  let (a, _b) := pair
  a + 1#u32

@[step]
theorem getPairAndUse_step (x : U32) (h : x.val + 2 ≤ U32.max) :
    getPairAndUse x ⦃ r => r.val = x.val + 2 ⦄ := by
  unfold getPairAndUse
  step*

end step_tuple_destruct
