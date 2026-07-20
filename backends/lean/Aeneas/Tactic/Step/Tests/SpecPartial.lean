import Aeneas.Std.Scalar
import Aeneas.Tactic.Step

/-!
# Tests: `@[step]` accepts `partialSpec` lemmas

For a theorem using `partialSpec`, marking it with `@[step]` should register it for `step*` and
for `mvcgen`.
-/

namespace Aeneas.Step.SpecPartialTests

open Aeneas Aeneas.Std Result Std.Do WP

set_option mvcgen.warning false

/- ## Mock division: panics when dividing by zero, but does not specify `Error`. -/

opaque myDiv (x y : U32) : Result U32

@[step]
axiom myDiv_partialSpec (x y : U32) :
  partialSpec (myDiv x y)
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

/--
info: Aeneas.Step.SpecPartialTests.myDiv_partialSpec.step_spec (x y : U32) (h_fail : ¬↑y = 0) :
  myDiv x y ⦃ z => ↑z = ↑x / ↑y ⦄
-/
#guard_msgs in
#check myDiv_partialSpec.step_spec

/--
info: Aeneas.Step.SpecPartialTests.myDiv_partialSpec.mvcgen_spec (x y : U32) (Q : PostCond U32 Result.postShape)
  (h_ok : ∀ (r : U32), ↑r = ↑x / ↑y → willYield r Q) (h_fail : ∀ (e : Error), ↑y = 0 → willFail e Q) :
  ⦃⌜True⌝⦄ myDiv x y ⦃Q⦄
-/
#guard_msgs in
#check myDiv_partialSpec.mvcgen_spec

/- ## Mock addition: panics on overflow, specifies `Error.integerOverflow` -/

opaque myAdd (x y : U32) : Result U32

@[step]
axiom myAdd_partialSpec (x y : U32) :
  partialSpec (myAdd x y)
    (fun z => z.val = x.val + y.val)
    (fun | .integerOverflow => x.val + y.val > U32.max | _ => False)
    False

-- Pushing `¬` through `>` should produce `≤`.
/--
info: Aeneas.Step.SpecPartialTests.myAdd_partialSpec.step_spec (x y : U32) (h_fail : ↑x + ↑y ≤ U32.max) :
  myAdd x y ⦃ z => ↑z = ↑x + ↑y ⦄
-/
#guard_msgs in
#check myAdd_partialSpec.step_spec

/--
info: Aeneas.Step.SpecPartialTests.myAdd_partialSpec.mvcgen_spec (x y : U32) (Q : PostCond U32 Result.postShape)
  (h_ok : ∀ (r : U32), ↑r = ↑x + ↑y → willYield r Q) (h_fail : U32.max < ↑x + ↑y → willFail Error.integerOverflow Q) :
  ⦃⌜True⌝⦄ myAdd x y ⦃Q⦄
-/
#guard_msgs in
#check myAdd_partialSpec.mvcgen_spec


/- ## Mock signed add: panics on over- and underflow -/

opaque myAddSigned (x y : I32) : Result I32

@[step]
axiom myAddSigned_partialSpec (x y : I32) :
  partialSpec (myAddSigned x y)
    (fun z => z.val = x.val + y.val)
    (fun | .integerOverflow => (x.val + y.val > I32.max ∨ x.val + y.val < I32.min) | _ => False)
    False

/--
info: Aeneas.Step.SpecPartialTests.myAddSigned_partialSpec.step_spec (x y : I32) (h_fail_1 : ↑x + ↑y ≤ I32.max)
  (h_fail_2 : I32.min ≤ ↑x + ↑y) : myAddSigned x y ⦃ z => ↑z = ↑x + ↑y ⦄
-/
#guard_msgs in
#check myAddSigned_partialSpec.step_spec

/--
info: Aeneas.Step.SpecPartialTests.myAddSigned_partialSpec.mvcgen_spec (x y : I32) (Q : PostCond I32 Result.postShape)
  (h_ok : ∀ (r : I32), ↑r = ↑x + ↑y → willYield r Q) (h_fail_1 : I32.max < ↑x + ↑y → willFail Error.integerOverflow Q)
  (h_fail_2 : ↑x + ↑y < I32.min → willFail Error.integerOverflow Q) : ⦃⌜True⌝⦄ myAddSigned x y ⦃Q⦄
-/
#guard_msgs in
#check myAddSigned_partialSpec.mvcgen_spec


/- ## Mock infinte loop: always diverges -/

opaque infiniteLoop : Result Unit

@[step]
axiom infiniteLoop_partialSpec :
  partialSpec infiniteLoop
    (fun _ => False)
    (fun _ => False)
    True

/--
info: Aeneas.Step.SpecPartialTests.infiniteLoop_partialSpec.step_spec (h_div : False) : infiniteLoop ⦃ x✝ => False ⦄
-/
#guard_msgs in
#check infiniteLoop_partialSpec.step_spec

/--
info: Aeneas.Step.SpecPartialTests.infiniteLoop_partialSpec.mvcgen_spec (Q : PostCond Unit Result.postShape)
  (h_div : willDiverge Q) : ⦃⌜True⌝⦄ infiniteLoop ⦃Q⦄
-/
#guard_msgs in
#check infiniteLoop_partialSpec.mvcgen_spec

end Aeneas.Step.SpecPartialTests
