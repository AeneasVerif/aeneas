-- Correctness proofs for docs-example tests in `OptionMethods.lean`.

import OptionMethods
import ProofHelpers

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace option_methods

/-- `Some(97).as_ref()` returns `Some(&97)`. -/
theorem test_option_as_ref_some_correct :
    test_option_as_ref_some ⦃ _ => True ⦄ :=
  test_correct_of_native (by native_decide)

/-- `None.as_ref()` returns `None`. -/
theorem test_option_as_ref_none_correct :
    test_option_as_ref_none ⦃ _ => True ⦄ :=
  test_correct_of_native (by native_decide)

/-- `Some(42).ok_or(0)` returns `Ok(42)`. -/
theorem test_option_ok_or_some_correct :
    test_option_ok_or_some ⦃ _ => True ⦄ :=
  test_correct_of_native (by native_decide)

/-- `None.ok_or(7)` returns `Err(7)`. -/
theorem test_option_ok_or_none_correct :
    test_option_ok_or_none ⦃ _ => True ⦄ :=
  test_correct_of_native (by native_decide)

/-- `Option::default()` for `Option<T>` yields `None`. -/
theorem test_option_default_correct :
    test_option_default ⦃ _ => True ⦄ :=
  test_correct_of_native (by native_decide)

/-- `Some(2) == Some(2)` yields `true`. -/
theorem test_option_partial_eq_some_some_eq_correct :
    test_option_partial_eq_some_some_eq ⦃ _ => True ⦄ :=
  test_correct_of_native (by native_decide)

/-- `Some(2) == Some(3)` yields `false`. -/
theorem test_option_partial_eq_some_some_neq_correct :
    test_option_partial_eq_some_some_neq ⦃ _ => True ⦄ :=
  test_correct_of_native (by native_decide)

/-- `None == Some(2)` yields `false`. -/
theorem test_option_partial_eq_none_some_correct :
    test_option_partial_eq_none_some ⦃ _ => True ⦄ :=
  test_correct_of_native (by native_decide)

/-- `Some(5).clone()` yields `Some(5)`. -/
theorem test_option_clone_some_correct :
    test_option_clone_some ⦃ _ => True ⦄ :=
  test_correct_of_native (by native_decide)

/-- `None.clone()` yields `None`. -/
theorem test_option_clone_none_correct :
    test_option_clone_none ⦃ _ => True ⦄ :=
  test_correct_of_native (by native_decide)

end option_methods
