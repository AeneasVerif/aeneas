-- Correctness proofs for docs-example tests in `ConvertTryfrom.lean`.

import ConvertTryfrom
import ProofHelpers

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace convert_tryfrom

/-- `u32::try_from(1_000_000_000_000u64)` returns `Err` (overflow). -/
theorem test_u32_try_from_u64_overflow_correct :
    test_u32_try_from_u64_overflow ⦃ _ => True ⦄ :=
  test_correct_of_native (by native_decide)

/-- `u32::try_from(42u64)` returns `Ok(42)`. -/
theorem test_u32_try_from_u64_fits_correct :
    test_u32_try_from_u64_fits ⦃ _ => True ⦄ :=
  test_correct_of_native (by native_decide)

/-- `u32::try_from(u32::MAX as u64)` returns `Ok(u32::MAX)`. -/
theorem test_u32_try_from_u64_max_correct :
    test_u32_try_from_u64_max ⦃ _ => True ⦄ :=
  test_correct_of_native (by native_decide)

end convert_tryfrom
