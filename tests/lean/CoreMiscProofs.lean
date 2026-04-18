-- Correctness proofs for docs-example tests in `CoreMisc.lean`.
--
-- Structural proofs via `step*` over library spec theorems:
-- - `black_box` is `@[simp, step_simps]` — it reduces to identity.
-- - `Borrow.Blanket.borrow` is `@[simp, step_simps]` — ditto.
-- - Derived `PartialEq::eq` unfolds to a boolean equality check.

import CoreMisc

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace core_misc

/-- `core::hint::black_box(97)` returns `97` — `massert (y = 97)` succeeds. -/
theorem test_black_box_identity_correct :
    test_black_box_identity ⦃ _ => True ⦄ := by
  unfold test_black_box_identity
  step*

/-- `T: Borrow<T>` blanket: `borrow 42 = 42` — `massert (b = 42)` succeeds. -/
theorem test_borrow_ref_correct :
    test_borrow_ref ⦃ _ => True ⦄ := by
  unfold test_borrow_ref
  step*

/-- Derived `Eq` on `ByteHolder { b: u8 }` makes
`ByteHolder { b: 5 } == ByteHolder { b: 5 }` evaluate to `true`. -/
theorem test_eq_u8_via_derive_correct :
    test_eq_u8_via_derive ⦃ _ => True ⦄ := by
  unfold test_eq_u8_via_derive ByteHolder.Insts.CoreCmpPartialEqByteHolder.eq
  step*

/-- Derived `Eq` on `SizeHolder { s: usize }` makes
`SizeHolder { s: 5 } == SizeHolder { s: 5 }` evaluate to `true`. -/
theorem test_eq_usize_via_derive_correct :
    test_eq_usize_via_derive ⦃ _ => True ⦄ := by
  unfold test_eq_usize_via_derive SizeHolder.Insts.CoreCmpPartialEqSizeHolder.eq
  step*

end core_misc
