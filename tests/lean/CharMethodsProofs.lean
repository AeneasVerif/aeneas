-- Correctness proofs for docs-example tests in `CharMethods.lean`.

import CharMethods
import ProofHelpers

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace char_methods

/-- Comparing `'a' != 'b'` and `'a' == 'a'` via `massert` both succeed. -/
theorem test_char_eq_correct : test_char_eq ⦃ _ => True ⦄ :=
  test_correct_of_native (by native_decide)

end char_methods
