-- Correctness proofs for docs-example tests in `StepI32.lean`.

import StepI32
import ProofHelpers

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace step_i32

/-- `for i in -2..3 { total += i }` yields `total = 0`. -/
theorem test_i32_range_sum_correct :
    test_i32_range_sum ⦃ _ => True ⦄ :=
  test_correct_of_native (by native_decide)

/-- `for _ in -2..3 { n += 1 }` yields `n = 5`. -/
theorem test_i32_range_count_correct :
    test_i32_range_count ⦃ _ => True ⦄ :=
  test_correct_of_native (by native_decide)

end step_i32
