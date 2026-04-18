-- Correctness proof for the docs-example test in `ArrayFromFn.lean`.

import ArrayFromFn
import ProofHelpers

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace array_from_fn

/-- The Rust docs example `core::array::from_fn(|i| i)` with `N = 5`
yields `[0, 1, 2, 3, 4]`, so indexing each position matches and every
`massert` passes. -/
theorem test_from_fn_identity_correct :
    test_from_fn_identity ⦃ _ => True ⦄ :=
  test_correct_of_native (by native_decide)

end array_from_fn
