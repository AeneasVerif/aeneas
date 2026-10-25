module
import Aeneas.Std.Core.CoreResult
import Aeneas.Tactic.Step

open Aeneas Aeneas.Std Result

namespace higher_order_result

/-! The closures below have the shape Aeneas generates: a type, a `call_once` function and an
`FnOnce` instance. Marking `call_once` with `step_simps` lets `step` go through it. -/

/- `r.map(|x| x + 1)` -/
@[reducible] def incr.closure := Unit

@[step_simps]
def incr.closure.call_once (_ : incr.closure) (x : U32) : Result U32 := x + 1#u32

@[reducible] def incr.closure.FnOnceInst :
  core.ops.function.FnOnce incr.closure U32 U32 := { call_once := incr.closure.call_once }

def result_map (r : core.result.Result U32 Bool) : Result (core.result.Result U32 Bool) :=
  core.result.Result.map incr.closure.FnOnceInst r ()

example (x : U32) (hx : x.val < U32.max) :
    result_map (.Ok x) ⦃ r => ∃ y, r = .Ok y ∧ y.val = x.val + 1 ⦄ := by
  unfold result_map
  step* +inferPost

example (e : Bool) : result_map (.Err e) ⦃ r => r = .Err e ⦄ := by
  unfold result_map
  simp

end higher_order_result
