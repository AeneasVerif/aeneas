-- Correctness proofs for docs-example tests in `CharMethods.lean`.
--
-- Structural proof style: unfold definitions and let `step*` auto-apply
-- library spec theorems (e.g. `massert_spec`). No `native_decide`.

import CharMethods

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace char_methods

/-- Comparing `'a' != 'b'` and `'a' == 'a'` via `massert` both succeed.

Structural reasoning: `make_a = ok 'a'`, `make_b = ok 'b'`; then
`'a' != 'b'` is true and `'a' = 'a'` is reflexive — both `massert`s
discharge via `massert_spec`. -/
theorem test_char_eq_correct : test_char_eq ⦃ _ => True ⦄ := by
  unfold test_char_eq make_a make_b
  step*

end char_methods
