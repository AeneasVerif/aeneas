import Aeneas.Std.Scalar
import Aeneas.Tactic.Step

/-!
# Tests: `@[step]` accepts `spec_partial` lemmas

For a theorem using `spec_partial`, marking it with `@[step]` should register it for `step*` and
for `mvcgen`.
-/

namespace Aeneas.Step.SpecPartialTests

open Aeneas Aeneas.Std Result Std.Do WP

set_option mvcgen.warning false

opaque myDiv (x y : U32) : Result U32

@[step]
axiom myDiv_spec_partial (x y : U32) :
  spec_partial (myDiv x y)
    (fun z => z.val = x.val / y.val)
    (fun _ => y.val = 0)
    False

/-- step* -/
example (x y : U32) (h : y.val ≠ 0) :
    spec (myDiv x y) (fun z => z.val = x.val / y.val) := by
  step*

/-- mvcgen: total correctness -/
example (x y : U32) (h : y.val ≠ 0) :
    ⦃ ⌜ True ⌝ ⦄ (myDiv x y) ⦃ ⇓ z => ⌜ z.val = x.val / y.val ⌝ ⦄ := by
  mvcgen

/-- mvcgen: partial correctness -/
example (x y : U32) :
    ⦃ ⌜ True ⌝ ⦄ (myDiv x y) ⦃ ⇓? z => ⌜ z.val = x.val / y.val ⌝ ⦄ := by
  mvcgen

end Aeneas.Step.SpecPartialTests
