-- Correctness proofs for docs-example tests in `ResultMethods.lean`.
--
-- Structural proofs via `simp` over library lemmas (is_ok/is_err have
-- `@[simp]`; unwrap_or has `@[simp]` equations; `massert_True` reduces
-- the trailing asserts). `lift` is included in the simp set because
-- `unwrap_or` is `@[step_pure_def]` and emits a lift in the monad.

import ResultMethods

open Aeneas Aeneas.Std Aeneas.Std.WP Result ControlFlow Error

namespace result_methods

/-- `Ok(1).is_ok()` returns `true`. -/
theorem test_result_is_ok_ok_correct :
    test_result_is_ok_ok ⦃ _ => True ⦄ := by
  simp [test_result_is_ok_ok, make_ok_u32]

/-- `Err(e).is_ok()` returns `false`. -/
theorem test_result_is_ok_err_correct :
    test_result_is_ok_err ⦃ _ => True ⦄ := by
  simp [test_result_is_ok_err, make_err_u32]

/-- `Ok(v).unwrap_or(default)` returns `v`. -/
theorem test_result_unwrap_or_ok_correct :
    test_result_unwrap_or_ok ⦃ _ => True ⦄ := by
  simp [test_result_unwrap_or_ok, make_ok_u32, lift]

/-- `Err(e).unwrap_or(default)` returns `default`. -/
theorem test_result_unwrap_or_err_correct :
    test_result_unwrap_or_err ⦃ _ => True ⦄ := by
  simp [test_result_unwrap_or_err, make_err_u32, lift]

/-- `Ok(3).map(|x| x * 2)` returns `Ok(6)`. -/
theorem test_result_map_ok_correct :
    test_result_map_ok ⦃ _ => True ⦄ := by
  simp [test_result_map_ok, make_ok_u32, core.result.Result.map,
    test_result_map_ok.closure.Insts.CoreOpsFunctionFnOnceTupleU32U32,
    test_result_map_ok.closure.Insts.CoreOpsFunctionFnOnceTupleU32U32.call_once]
  step*

/-- `Err(e).map(f)` passes the `Err` through unchanged. The name is
misleading — the test uses `map`, not `map_err`, to verify Err-passthrough
on `map`. -/
theorem test_result_map_err_passthrough_correct :
    test_result_map_err_passthrough ⦃ _ => True ⦄ := by
  simp [test_result_map_err_passthrough, make_err_u32, core.result.Result.map]

/-- `Ok(v).map_err(f)` leaves the Ok branch untouched. -/
theorem test_result_map_err_ok_passthrough_correct :
    test_result_map_err_ok_passthrough ⦃ _ => True ⦄ := by
  simp [test_result_map_err_ok_passthrough, make_ok_u32,
    core.result.Result.map_err]

/-- `Err(e).map_err(|x| x + 1)` transforms the error. -/
theorem test_result_map_err_err_correct :
    test_result_map_err_err ⦃ _ => True ⦄ := by
  simp [test_result_map_err_err, make_err_u32, core.result.Result.map_err,
    test_result_map_err_err.closure.Insts.CoreOpsFunctionFnOnceTupleU32U32,
    test_result_map_err_err.closure.Insts.CoreOpsFunctionFnOnceTupleU32U32.call_once]
  step*

/-- `Try::branch` on `Ok(v)` yields `ControlFlow::Continue(v)`, then
`try_branch_helper` increments by 1 to return `Ok(v+1)`. -/
theorem test_result_try_branch_ok_correct :
    test_result_try_branch_ok ⦃ _ => True ⦄ := by
  simp [test_result_try_branch_ok, try_branch_helper,
    core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch]
  step*

/-- `Try::branch` on `Err(e)` yields `ControlFlow::Break(Err(e))`, then
`from_residual` returns `Err(e)` unchanged via `FromSame`. -/
theorem test_result_try_branch_err_correct :
    test_result_try_branch_err ⦃ _ => True ⦄ := by
  simp [test_result_try_branch_err, try_branch_helper, make_err_u32,
    core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
    core.convert.FromSame, core.convert.FromSame.from_]

end result_methods
