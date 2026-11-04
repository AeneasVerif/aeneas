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

/- On a constructor, `step` picks `map.spec_Ok` / `map.spec_Err`; `+inferPost` infers the
postcondition of the closure from its body. -/
example (x : U32) (hx : x.val < U32.max) :
    result_map (.Ok x) ⦃ r => ∃ y, r = .Ok y ∧ y.val = x.val + 1 ⦄ := by
  unfold result_map
  step* +inferPost

example (e : Bool) : result_map (.Err e) ⦃ r => r = .Err e ⦄ := by
  unfold result_map
  step*

/- On a variable, the general `map.spec`, through `step with`. -/
example (r : core.result.Result U32 Bool) (hr : ∀ x, r = .Ok x → x.val < U32.max) :
    result_map r ⦃ r' => (∀ x, r = .Ok x → ∃ y, r' = .Ok y ∧ y.val = x.val + 1) ∧
      (∀ e, r = .Err e → r' = .Err e) ⦄ := by
  unfold result_map
  step with core.result.Result.map.spec _ _ _ (post := fun (x y : U32) => y.val = x.val + 1)
    by (intro x hx; have := hr x hx; step*)
  solve_by_elim

end higher_order_result
