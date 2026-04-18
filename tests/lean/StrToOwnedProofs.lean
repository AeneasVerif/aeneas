-- Correctness proof for the docs-example test in `StrToOwned.lean`.

import StrToOwned

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace str_to_owned

/-- `let _owned: String = s.to_owned();` always returns `ok String`. -/
theorem test_str_to_owned_correct : test_str_to_owned ⦃ _ => True ⦄ := by
  simp [test_str_to_owned, Str.Insts.AllocBorrowToOwnedString.to_owned]

end str_to_owned
