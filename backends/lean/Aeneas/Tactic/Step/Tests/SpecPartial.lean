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


opaque myAdd (x y : U32) : Result U32

@[step]
axiom myAdd_spec_partial (x y : U32) :
  spec_partial (myAdd x y)
    (fun z => z.val = x.val + y.val)
    (fun e => e = .integerOverflow ∧ x.val + y.val > U32.max)
    False

/--
info: Aeneas.Step.SpecPartialTests.myAdd_spec_partial.step_spec (x y : U32) (h : ¬↑x + ↑y > U32.max) :
  myAdd x y ⦃ z => ↑z = ↑x + ↑y ⦄
-/
#guard_msgs in
#check myAdd_spec_partial.step_spec

/--
info: Aeneas.Step.SpecPartialTests.myAdd_spec_partial.mvcgen_spec (x y : U32)
  (Q : PostCond U32 (PostShape.except (ULift.{0, 0} Error) (PostShape.except PUnit.{1} PostShape.pure)))
  (h_ok : ∀ (r : U32), ↑r = ↑x + ↑y → willYield r Q) (h : ↑x + ↑y > U32.max → willFail Error.integerOverflow Q) :
  ⦃⌜True⌝⦄ myAdd x y ⦃Q⦄
-/
#guard_msgs in
#check myAdd_spec_partial.mvcgen_spec

end Aeneas.Step.SpecPartialTests
