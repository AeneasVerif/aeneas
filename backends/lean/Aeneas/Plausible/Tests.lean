import Aeneas.Plausible.Basic
import Aeneas.Std.Scalar.Notations

/-! # Tests for the `Plausible` instances

Self-checking demonstrations that `plausible` works on Aeneas `Std` types and prints readable
counter-examples. -/

open Plausible

namespace Aeneas.Std

/-! ## Readable counter-examples

Scalars print as decimal numbers and slices/arrays as lists, not the raw bitvector `Repr` that
`UScalar`/`IScalar` derive. -/

-- `U8` → a plain `Nat` (`x := 1`), with the full failure report pinned.
/--
error:
===================
Found a counter-example!
x := 1
issue: 1 = 0 does not hold
(1 shrinks)
-------------------
-/
#guard_msgs in
#eval Testable.check (∀ x : U8, x.val = 0) { randomSeed := some 0 }

-- `I8` → a signed `Int` (`x := -1`), not the two's-complement `255`. `substring` keeps
-- the check robust to the internal shrink count.
/-- x := -1 -/
#guard_msgs (substring := true) in
#eval Testable.check (∀ x : I8, x.val ≥ 0) { randomSeed := some 0 }

-- `Slice U8` → a list of numbers (`s := [0]`).
/-- s := [0] -/
#guard_msgs (substring := true) in
#eval Testable.check (∀ s : Slice U8, s.val.length = 0) { randomSeed := some 0 }

-- `Array U8 0` has the unique value `[]`, so the counter-example is deterministic with
-- no seed.
/--
error:
===================
Found a counter-example!
a := []
issue: 0 ≠ 0 does not hold
(0 shrinks)
-------------------
-/
#guard_msgs in
#test ∀ a : Array U8 0#usize, a.val.length ≠ 0

/-! ## Verdicts

True props report no counter-example; the generators cover `Slice`/`Vec`/`Array`. -/

/-- info: Unable to find a counter-example -/
#guard_msgs in
#test ∀ x : U8, x.val < 256

/-- info: Unable to find a counter-example -/
#guard_msgs in
#test ∀ s : Slice U8, s.length ≤ Usize.max

/-- info: Unable to find a counter-example -/
#guard_msgs in
#test ∀ v : alloc.vec.Vec U8, v.val.length ≤ Usize.max

/-! ## Spec theorems via `plausible` -/

open Result

/-- Double a `U8` in the `Result` monad — like extracted code, it fails on overflow. -/
private def dbl (x : U8) : Result U8 := do
  let y ← x + x
  ok y

-- The naive spec is wrong: `dbl` overflows for `x ≥ 128`, so a counter-example is found.
-- `randomSeed` fixes the RNG: unseeded, the run draws from an OS-seeded generator and could
-- (with probability ~2⁻¹⁰⁰) miss the failure region; seeding makes the result reproducible.
/-- Found a counter-example! -/
#guard_msgs (substring := true) in
example (x : U8) : dbl x ⦃ y => y.val = 2 * x.val ⦄ := by
  plausible (config := { randomSeed := some 0 })

-- A precondition ruling out overflow makes it hold, so `plausible` admits it.
/--
info: Unable to find a counter-example
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (x : U8) (h : x.val < 128) : dbl x ⦃ y => y.val = 2 * x.val ⦄ := by
  plausible

-- A bounded-∀ precondition, decided as a guard via the `NamedBinder` bridges.
/--
info: Unable to find a counter-example
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (n : U8) (h : ∀ i < n.val, i < 100) : Result.ok n ⦃ _y => True ⦄ := by
  plausible

/-! ## Postconditions quantifying over a scalar type -/

-- Wrong: claims the result dominates every byte — true only at `255`.
/-- Found a counter-example! -/
#guard_msgs (substring := true) in
example (x : U8) : Result.ok x ⦃ y => ∀ i : U8, i.val ≤ y.val ⦄ := by
  plausible (config := { randomSeed := some 0 })

-- Correct at the maximum byte: `255` really does dominate every byte.
/--
info: Unable to find a counter-example
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : Result.ok 255#u8 ⦃ y => ∀ i : U8, i.val ≤ y.val ⦄ := by plausible

end Aeneas.Std
