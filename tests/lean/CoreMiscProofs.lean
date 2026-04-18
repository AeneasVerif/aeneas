-- Correctness proofs for docs-example tests in `CoreMisc.lean`.
--
-- Each test is a ground Unit-valued program; we lift its decidable evaluation
-- to a WP correctness statement via `test_correct_of_native`.

import CoreMisc
import ProofHelpers

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace core_misc

/-- `core::hint::black_box(x)` returns `x` unchanged. -/
theorem test_black_box_identity_correct :
    test_black_box_identity ⦃ _ => True ⦄ :=
  test_correct_of_native (by native_decide)

/-- `T: Borrow<T>` blanket: `borrow` is the identity. -/
theorem test_borrow_ref_correct :
    test_borrow_ref ⦃ _ => True ⦄ :=
  test_correct_of_native (by native_decide)

/-- Derived `Eq` for a `u8`-wrapping struct reflects element equality. -/
theorem test_eq_u8_via_derive_correct :
    test_eq_u8_via_derive ⦃ _ => True ⦄ :=
  test_correct_of_native (by native_decide)

/-- Derived `Eq` for a `usize`-wrapping struct reflects element equality. -/
theorem test_eq_usize_via_derive_correct :
    test_eq_usize_via_derive ⦃ _ => True ⦄ :=
  test_correct_of_native (by native_decide)

end core_misc
