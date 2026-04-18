-- Correctness proofs for docs-example tests in `ResultMethods.lean`.

import ResultMethods
import ProofHelpers

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace result_methods

/-- `Ok(1).is_ok()` returns `true`. -/
theorem test_result_is_ok_ok_correct :
    test_result_is_ok_ok ⦃ _ => True ⦄ :=
  test_correct_of_native (by native_decide)

/-- `Err(e).is_ok()` returns `false`. -/
theorem test_result_is_ok_err_correct :
    test_result_is_ok_err ⦃ _ => True ⦄ :=
  test_correct_of_native (by native_decide)

/-- `Ok(v).unwrap_or(default)` returns `v`. -/
theorem test_result_unwrap_or_ok_correct :
    test_result_unwrap_or_ok ⦃ _ => True ⦄ :=
  test_correct_of_native (by native_decide)

/-- `Err(e).unwrap_or(default)` returns `default`. -/
theorem test_result_unwrap_or_err_correct :
    test_result_unwrap_or_err ⦃ _ => True ⦄ :=
  test_correct_of_native (by native_decide)

/-- `Ok(3).map(|x| x * 2)` returns `Ok(6)`. -/
theorem test_result_map_ok_correct :
    test_result_map_ok ⦃ _ => True ⦄ :=
  test_correct_of_native (by native_decide)

/-- `Ok(v).map_err(f)` leaves `Ok(v)` unchanged. -/
theorem test_result_map_err_passthrough_correct :
    test_result_map_err_passthrough ⦃ _ => True ⦄ :=
  test_correct_of_native (by native_decide)

/-- `Ok(v).map_err(f)` leaves the Ok branch untouched even when the closure
type differs. -/
theorem test_result_map_err_ok_passthrough_correct :
    test_result_map_err_ok_passthrough ⦃ _ => True ⦄ :=
  test_correct_of_native (by native_decide)

/-- `Err(e).map_err(|x| x + 1)` transforms the error. -/
theorem test_result_map_err_err_correct :
    test_result_map_err_err ⦃ _ => True ⦄ :=
  test_correct_of_native (by native_decide)

/-- `Try::branch` on `Ok(v)` yields `ControlFlow::Continue(v)`. -/
theorem test_result_try_branch_ok_correct :
    test_result_try_branch_ok ⦃ _ => True ⦄ :=
  test_correct_of_native (by native_decide)

/-- `Try::branch` on `Err(e)` yields `ControlFlow::Break(Err(e))`. -/
theorem test_result_try_branch_err_correct :
    test_result_try_branch_err ⦃ _ => True ⦄ :=
  test_correct_of_native (by native_decide)

end result_methods
