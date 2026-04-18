-- Correctness proofs for docs-example tests in `SliceMethods.lean`.

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
