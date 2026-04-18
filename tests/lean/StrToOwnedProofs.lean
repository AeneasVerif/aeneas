-- Correctness proof for the docs-example test in `StrToOwned.lean`.

import StrToOwned
import ProofHelpers

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace str_to_owned

/-- `let _owned: String = s.to_owned();` translates to a successful program:
`to_owned` always returns `ok String`. -/
theorem test_str_to_owned_correct : test_str_to_owned ⦃ _ => True ⦄ :=
  test_correct_of_native (by native_decide)

end str_to_owned
