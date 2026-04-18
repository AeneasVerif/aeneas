-- Correctness proof for the docs-example test in `IteratorCollect.lean`.

import IteratorCollect
import ProofHelpers

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace iterator_collect

/-- `(0..3).collect::<Vec<_>>()` yields a vector of length 3. -/
theorem test_range_collect_vec_correct :
    test_range_collect_vec ⦃ _ => True ⦄ :=
  test_correct_of_native (by native_decide)

end iterator_collect
