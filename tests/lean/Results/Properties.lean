import Aeneas
import Results.Results
open Aeneas Aeneas.Std Result

/-! Proofs about the extracted `tests/src/results.rs`, using the specification theorems of the model
of `Result::map` through `step`: on `Ok`, `step* +inferPost` infers the postcondition of the
closure from its body; on `Err`, the closure isn't called. -/

namespace results

attribute [local step_simps]
  doubled.closure.Insts.CoreOpsFunctionFnOnceTupleI32I32.call_once
  scale.closure.Insts.CoreOpsFunctionFnOnceTupleU32U32.call_once

/-- The example of the documentation of `Result::map`, on a line which parses. -/
theorem doubled_ok (i : I32) (h : I32.min ≤ i.val * 2 ∧ i.val * 2 ≤ I32.max) :
    doubled (.Ok i) ⦃ o => ∃ n, o = some n ∧ n.val = i.val * 2 ⦄ := by
  unfold doubled
  step* +inferPost

/-- …and on a line which doesn't parse: nothing is printed. -/
theorem doubled_err : doubled (.Err ()) ⦃ o => o = none ⦄ := by
  unfold doubled
  step*

theorem scale_ok (x y : U32) (h : x.val * y.val ≤ U32.max) :
    scale (.Ok x) y ⦃ r => ∃ z, r = .Ok z ∧ z.val = x.val * y.val ⦄ := by
  unfold scale
  step* +inferPost

theorem scale_err (e : Bool) (y : U32) : scale (.Err e) y ⦃ r => r = .Err e ⦄ := by
  unfold scale
  step*

end results
