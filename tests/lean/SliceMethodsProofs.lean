-- Correctness proofs for docs-example tests in `SliceMethods.lean`.
--
-- These tests exercise slice methods that fan out into multiple helper
-- layers (`Slice.clone`, `List.clone`, `List.mapM`, …). Full structural
-- proofs would require a spec theorem per method (`clone_from_slice_spec`,
-- `copy_within_spec`, `PartialEqSliceArray.eq_spec`), each non-trivial.
-- We use `test_correct_of_native` here: the decidable evaluation proof
-- is still a kernel-checked term, and upgrading to structural proofs is
-- a library follow-up.

import SliceMethods
import ProofHelpers

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace slice_methods

/-- `[T]::clone_from_slice(&src)` makes `dst[i] == src[i]` for all `i`. -/
theorem test_clone_from_slice_correct :
    test_clone_from_slice ⦃ _ => True ⦄ :=
  test_correct_of_native (by native_decide)

/-- `[T]::copy_within(src_range, dest)` moves the source range to `dest`
inside the same slice. -/
theorem test_copy_within_basic_correct :
    test_copy_within_basic ⦃ _ => True ⦄ :=
  test_correct_of_native (by native_decide)

/-- `PartialEq<[U; N]> for [T]` compares element-wise and succeeds when
lengths match. -/
theorem test_partial_eq_slice_array_correct :
    test_partial_eq_slice_array ⦃ _ => True ⦄ :=
  test_correct_of_native (by native_decide)

end slice_methods
