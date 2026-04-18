-- Correctness proofs for docs-example tests in `VecMethods.lean`.

import VecMethods
import ProofHelpers

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace vec_methods

/-- `Vec::new().is_empty()` yields `true`. -/
theorem test_vec_is_empty_new_correct :
    test_vec_is_empty_new ⦃ _ => True ⦄ :=
  test_correct_of_native (by native_decide)

/-- After `push`, `is_empty` yields `false`. -/
theorem test_vec_is_empty_after_push_correct :
    test_vec_is_empty_after_push ⦃ _ => True ⦄ :=
  test_correct_of_native (by native_decide)

/-- `Vec::clear` makes the vector empty. -/
theorem test_vec_clear_correct :
    test_vec_clear ⦃ _ => True ⦄ :=
  test_correct_of_native (by native_decide)

/-- `Vec::truncate(n)` shortens the vector to `n` elements when `n < len`. -/
theorem test_vec_truncate_shortens_correct :
    test_vec_truncate_shortens ⦃ _ => True ⦄ :=
  test_correct_of_native (by native_decide)

/-- `Vec::truncate(n)` is a no-op when `n >= len`. -/
theorem test_vec_truncate_noop_if_longer_correct :
    test_vec_truncate_noop_if_longer ⦃ _ => True ⦄ :=
  test_correct_of_native (by native_decide)

/-- `Vec::as_slice` returns a slice with the same contents. -/
theorem test_vec_as_slice_correct :
    test_vec_as_slice ⦃ _ => True ⦄ :=
  test_correct_of_native (by native_decide)

/-- `Vec::remove(i)` pulls out element `i` and shifts the rest. -/
theorem test_vec_remove_middle_correct :
    test_vec_remove_middle ⦃ _ => True ⦄ :=
  test_correct_of_native (by native_decide)

/-- `Vec::append(&mut other)` moves all elements from `other` into `self`. -/
theorem test_vec_append_correct :
    test_vec_append ⦃ _ => True ⦄ :=
  test_correct_of_native (by native_decide)

/-- `Vec::split_off(i)` returns a new vec with elements `[i..]`, leaving
`[0..i)` in `self`. -/
theorem test_vec_split_off_correct :
    test_vec_split_off ⦃ _ => True ⦄ :=
  test_correct_of_native (by native_decide)

/-- `Vec::default()` returns an empty vector. -/
theorem test_vec_default_correct :
    test_vec_default ⦃ _ => True ⦄ :=
  test_correct_of_native (by native_decide)

end vec_methods
