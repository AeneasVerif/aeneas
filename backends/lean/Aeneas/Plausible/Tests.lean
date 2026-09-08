import Aeneas.Plausible.Basic
import Aeneas.Std.Scalar.Notations

/-! # Tests / usage examples for `Plausible`

Each test is a spec theorem in the usual Aeneas shape: a `Result`-monad function defined with `do`, \and a `WP.spec` postcondition.

Note that `plausible` tests, it does not prove. This means that a true spec is admitted (a `sorry`),
a false one yields a counter-example. Here `randomSeed` is often fixed so the results are
reproducible. In typical use this isn't desired.

TODO: This test file is kept separate so it could be moved to an `AeneasTest` lean lib. -/

open Plausible

namespace Aeneas.Std

open Result

/-! ## Element-wise addition on a 2-limb `U64` array (a `FieldElement51`-style limb op)

Sampling arrays and `U64` limbs, bounded-∀ pre/postconditions decided as guards, `WP.spec`, and, for
a tight limb bound, sampling in range rather than filtering. -/

/-- Add two 2-limb arrays element-wise, fails on limb overflow. -/
def add (a b : Array U64 2#usize) : Result (Array U64 2#usize) := do
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

-- Wrong: the naive spec overflows, so `plausible` finds a counter-example.
/-- Found a counter-example!
a := [127, 3441359099766425339]
b := [0, 17677279364608779445] -/
#guard_msgs (substring := true) in
example (a b : Array U64 2#usize) :
    add a b ⦃ (r : Array U64 2#usize) => ∀ i < 2, r[i]!.val = a[i]!.val + b[i]!.val ⦄ := by
  plausible (config := { randomSeed := some 0 })

-- Here `plausible` has a hard time finding valid test data and so admits a blatantly false spec.
/-- warning: Gave up after failing to generate values that fulfill the preconditions 100 times. -/
#guard_msgs  (substring := true) in
example (a b : Array U64 2#usize) (ha : ∀ i < 2, a[i]!.val < 2^54) (hb : ∀ i < 2, b[i]!.val < 2^54) :
    add a b ⦃ _ => false ⦄ := by
  plausible (config := { randomSeed := some 0 })

-- Sample in range via the bounded subtype `{x : U64 // x.val < 2^54}` to more reliably test.
/-- info: Unable to find a counter-example -/
#guard_msgs (substring := true)  in
example (a b : Array {x : U64 // x.val < 2^54} 2#usize) :
    let a' := a.map (·.val); let b' := b.map (·.val)
    add a' b' ⦃ (r : Array U64 2#usize) =>
      (∀ i < 2, r[i]!.val = a'[i]!.val + b'[i]!.val) ∧ (∀ i < 2, r[i]!.val < 2^55) ⦄ := by
  plausible

-- Sample in range, similar to the above, but using `Array (Fin n)`.
/-- info: Unable to find a counter-example -/
#guard_msgs (substring := true)  in
example (a b : Array (Fin (2^54)) 2#usize) :
    let a' := a.map (⟨BitVec.ofNat _ ·.val⟩); let b' := b.map (⟨BitVec.ofNat _ ·.val⟩)
    add a' b' ⦃ (r : Array U64 2#usize) =>
      (∀ i < 2, r[i]!.val = a'[i]!.val + b'[i]!.val) ∧ (∀ i < 2, r[i]!.val < 2^55) ⦄ := by
  plausible

/-! ## A signed limb

Sampling `I8` (shown as a signed `Int`, not a bitvector). -/

/-- Double a signed limb (fails on overflow). -/
def dbl (x : I8) : Result I8 := do
  let y ← x + x
  ok y

-- The naive doubling spec overflows for large `|x|`.
/-- Found a counter-example!
x := -125 -/
#guard_msgs (substring := true) in
example (x : I8) : dbl x ⦃ y => y.val = 2 * x.val ⦄ := by
  plausible (config := { randomSeed := some 0 })

/-! ## Variable-length collections

Sampling `Slice` and `Vec` (as lists), with a length precondition decided as a guard. -/

/-- Double the head element of a slice (fails if empty or overflows). -/
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
/-- info: Unable to find a counter-example -/
#guard_msgs (substring := true) in
example (s : Slice U8) (hlen : 1 ≤ s.length) (hd : s[0]!.val < 128) :
    sliceHead s ⦃ y => y.val = 2 * s[0]!.val ⦄ := by
  plausible (config := { randomSeed := some 0 })

-- The same for `Vec` (an independent instance with the same behaviour).
/-- info: Unable to find a counter-example -/
#guard_msgs (substring := true) in
example (v : alloc.vec.Vec U8) (hlen : 1 ≤ v.val.length) (hd : v.val[0]!.val < 128) :
    vecHead v ⦃ y => y.val = 2 * v.val[0]!.val ⦄ := by
  plausible (config := { randomSeed := some 0 })

/-! ## A postcondition quantifying over a scalar type

A `∀ i : U8, …` postcondition, decided by enumeration via the scalar `Fintype` instance. -/

/-- Saturate a byte to the maximum by OR-ing with `0xFF`. -/
def saturate (x : U8) : Result U8 := do
  let y := x ||| 255#u8
  ok y

/-- info: Unable to find a counter-example -/
#guard_msgs (substring := true) in
example (x : U8) : saturate x ⦃ y => ∀ i : U8, i.val ≤ y.val ⦄ := by
  plausible

end Aeneas.Std
