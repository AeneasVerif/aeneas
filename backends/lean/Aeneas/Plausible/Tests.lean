import Aeneas.Plausible.Basic
import Aeneas.Std.Scalar.Notations

/-! # Tests / usage examples for the `Plausible` instances

Each test is a spec theorem in the usual Aeneas shape — a `Result`-monad function defined with
`do`, and a `WP.spec` postcondition written with `⦃ ⦄` — probed by `plausible`. They double as
usage examples.

`plausible` *tests*, it does not prove: a true spec is *admitted* (hence the `sorry` warning),
a false one yields a readable counter-example. `randomSeed` is fixed so the results are
reproducible; the counter-example checks use `substring` so they don't pin the shrink count. -/

open Plausible

namespace Aeneas.Std

open Result

/-! ## Element-wise addition on a 2-limb array (a `FieldElement51`-style limb op)

Exercises: sampling `Array U8 _` (with `U8` elements shown as decimal lists), bounded-∀
pre/postconditions decided as guards, and `WP.spec`. -/

/-- Add two 2-limb arrays element-wise, in the `Result` monad (fails on limb overflow). -/
def add (a b : Array U8 2#usize) : Result (Array U8 2#usize) := do
  let a0 ← a.index_usize 0#usize
  let a1 ← a.index_usize 1#usize
  let b0 ← b.index_usize 0#usize
  let b1 ← b.index_usize 1#usize
  let c0 ← a0 + b0
  let c1 ← a1 + b1
  ok (Array.make 2#usize [c0, c1])

-- Correct: the `< 128` limb bounds rule out overflow, so `add` succeeds and adds element-wise.
/--
info: Unable to find a counter-example
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (a b : Array U8 2#usize) (ha : ∀ i < 2, a[i]!.val < 128) (hb : ∀ i < 2, b[i]!.val < 128) :
    add a b ⦃ (r : Array U8 2#usize) =>
      (∀ i < 2, r[i]!.val = a[i]!.val + b[i]!.val) ∧ (∀ i < 2, r[i]!.val < 256) ⦄ := by
  plausible (config := { randomSeed := some 0 })

-- Wrong: the naive spec overflows, and `plausible` reports a readable counter-example.
/-- Found a counter-example!
a := [0, 221]
b := [0, 64] -/
#guard_msgs (substring := true) in
example (a b : Array U8 2#usize) :
    add a b ⦃ (r : Array U8 2#usize) => ∀ i < 2, r[i]!.val = a[i]!.val + b[i]!.val ⦄ := by
  plausible (config := { randomSeed := some 0 })

-- Pitfall: if the bound is too tight for uniform sampling to hit (here `< 16`, met by only
-- `(1/16)⁴ ≈ 1/65536` of draws), `plausible` never generates a valid input and *gives up*,
-- admitting the goal — even though this spec is blatantly false. "Gave up" means *not tested*,
-- not proved. (Bound-aware sampling — drawing limbs directly in range — would fix this.)
/--
warning: Gave up after failing to generate values that fulfill the preconditions 100 times.
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (a b : Array U8 2#usize) (ha : ∀ i < 2, a[i]!.val < 16) (hb : ∀ i < 2, b[i]!.val < 16) :
    add a b ⦃ _ => false ⦄ := by
  plausible (config := { randomSeed := some 0 })

/-! ## Realistic tight bound: `U64` limbs `< 2^54`, tested via a bounded subtype

Field-element limbs are `U64` bounded well below the type max (e.g. `< 2^54`). Uniform `U64`
sampling meets that only ~`2⁻¹⁰` of the time, so — as in the pitfall above — a filtered
precondition would make `plausible` give up. Instead we quantify over the bounded subtype
`{x : U64 // x.val < 2^54}`, which `UScalar.boundedSampleableExt` samples *in range* (no
per-bound boilerplate), and lift to the `U64` array; every sample is then valid. -/

/-- Add two 2-limb `U64` arrays element-wise (fails on limb overflow). -/
def add64 (a b : Array U64 2#usize) : Result (Array U64 2#usize) := do
  let a0 ← a.index_usize 0#usize
  let a1 ← a.index_usize 1#usize
  let b0 ← b.index_usize 0#usize
  let b1 ← b.index_usize 1#usize
  let c0 ← a0 + b0
  let c1 ← a1 + b1
  ok (Array.make 2#usize [c0, c1])

-- TODO: `Array.map` belongs in `Aeneas.Std` (PR #1237, "add api for slice/vec/array").
/-- Map a function over an `Array`, preserving the length. -/
def Array.map {α : Type u} {β : Type v} {n : Usize} (f : α → β) (a : Array α n) : Array β n :=
  ⟨a.val.map f, by simp [a.property]⟩

-- With limbs `< 2^54`, `add64` adds without overflow and every result limb is `< 2^55`.
/--
info: Unable to find a counter-example
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (a b : Array {x : U64 // x.val < 2^54} 2#usize) :
    let a' := a.map (·.val); let b' := b.map (·.val)
    add64 a' b' ⦃ (r : Array U64 2#usize) =>
      (∀ i < 2, r[i]!.val = a'[i]!.val + b'[i]!.val) ∧ (∀ i < 2, r[i]!.val < 2^55) ⦄ := by
  plausible (config := { randomSeed := some 0 })

/-! ## A signed limb

Exercises: sampling `I8` (shown as a signed `Int`, not a bitvector). -/

/-- Double a signed limb (fails on overflow). -/
def dbl (x : I8) : Result I8 := do
  let y ← x + x
  ok y

-- Wrong: the naive doubling spec overflows for large `|x|`; the counter-example is a signed
-- value (e.g. `x := -125`, since `-125 + -125 = -250 < -128`).
/-- Found a counter-example! -/
#guard_msgs (substring := true) in
example (x : I8) : dbl x ⦃ y => y.val = 2 * x.val ⦄ := by
  plausible (config := { randomSeed := some 0 })

/-! ## Variable-length collections

Exercises: sampling `Slice` and `Vec` (as lists), with a length precondition decided as a
guard. -/

/-- Double the head element of a slice (fails if empty or on overflow). -/
def sliceHead (s : Slice U8) : Result U8 := do
  let x ← s.index_usize 0#usize
  let y ← x + x
  ok y

/-- Double the head element of a vector. -/
def vecHead (v : alloc.vec.Vec U8) : Result U8 := do
  let x ← v.index_usize 0#usize
  let y ← x + x
  ok y

-- Correct: a non-empty slice whose head is `< 128` has its head doubled without overflow.
/--
info: Unable to find a counter-example
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (s : Slice U8) (hlen : 1 ≤ s.length) (hd : s[0]!.val < 128) :
    sliceHead s ⦃ y => y.val = 2 * s[0]!.val ⦄ := by
  plausible (config := { randomSeed := some 0 })

-- The same for `Vec` (an independent instance with the same behaviour).
/--
info: Unable to find a counter-example
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (v : alloc.vec.Vec U8) (hlen : 1 ≤ v.val.length) (hd : v.val[0]!.val < 128) :
    vecHead v ⦃ y => y.val = 2 * v.val[0]!.val ⦄ := by
  plausible (config := { randomSeed := some 0 })

/-! ## A postcondition quantifying over a whole scalar type

Exercises: a `∀ i : U8, …` postcondition, decided by enumeration via the scalar `Fintype`
instance (rather than the bounded-∀ bridge, which handles `∀ i < n`). -/

/-- Return the maximal byte. -/
def maxByte (x : U8) : Result U8 := do
  let _ ← x + 0#u8
  ok 255#u8

-- Correct: `255` dominates every byte, a `∀ i : U8` postcondition over all 256 values.
/--
info: Unable to find a counter-example
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (x : U8) : maxByte x ⦃ y => ∀ i : U8, i.val ≤ y.val ⦄ := by
  plausible (config := { randomSeed := some 0 })

end Aeneas.Std
