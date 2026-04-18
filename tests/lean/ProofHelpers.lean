-- Shared helpers for the `*Proofs.lean` files.
--
-- Most docs-example tests have the form `test_X : Result Unit` that is
-- decidably equal to `ok ()` (that's what the generated `#assert` line
-- checks). `test_correct_of_native` turns that decidable equality into an
-- explicit proof term for the WP postcondition `⦃ _ => True ⦄`.

import Aeneas

open Aeneas Aeneas.Std Aeneas.Std.WP Result

/-- For a concrete `Result Unit` program that reduces (via `native_decide`)
to `ok ()`, lift to the weak-postcondition correctness statement. -/
theorem test_correct_of_native {f : Result Unit}
    (h : (f == ok ()) = true) : f ⦃ _ => True ⦄ := by
  cases hf : f with
  | ok x =>
    cases x
    simp [WP.spec, WP.theta, wp_return]
  | fail e =>
    exfalso
    rw [hf] at h
    contradiction
  | div =>
    exfalso
    rw [hf] at h
    contradiction
