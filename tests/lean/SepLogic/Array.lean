import Aeneas.SepLogic.Semantics
import SepLogic.MutableData.Array
import SepLogic.MutableData.Buffer
import SepLogic.MutableData.Ptr

/-!
# The array interface

Regression tests for `SepLogic.MutableData.Array`: every operation of the
interface, run end to end by the certified interpreter, and the ownership
lemmas that relate an array to the slice and the range underneath it.
-/

open Aeneas
open SepLogic
open Aeneas.SepLogic

namespace SepLogic

open Aeneas.Std.WP

open Aeneas.Std (Heap Result)

-- These clients own whole arrays rather than individual slots.
attribute [local step] Array.read.spec_array Array.write.spec_array Array.swap.spec
  Buffer.write.spec_array

/-! ## Allocation, indexed access and release -/

def arrayRoundTrip : Result Nat := do
  let a ← Array.alloc Nat 3 (0 : Nat)
  a.write 0 1
  a.write 2 41
  let x ← a.read 0
  let y ← a.read 2
  a.free
  pure (x + y)

theorem arrayRoundTrip.spec :
    ⦃ emp ⦄ arrayRoundTrip ⦃⇓ result => ⌜result = 42⌝⦄ := by
  unfold arrayRoundTrip
  step*
  simp [*]

#guard (execClosed arrayRoundTrip arrayRoundTrip.spec).1 = 42

/-- The interpreter frees every slot, so nothing is left behind. -/
example : (execClosed arrayRoundTrip arrayRoundTrip.spec).2.size = 0 := by
  native_decide

/-! ## `ofList`, `swap` and `fill` -/

def arraySwap : Result (Nat × Nat) := do
  let a ← Array.ofList [7, 8]
  a.swap 0 1
  let x ← a.read 0
  let y ← a.read 1
  a.free
  pure (x, y)

theorem arraySwap.spec : ⦃ emp ⦄ arraySwap ⦃⇓ result => ⌜result = (8, 7)⌝⦄ := by
  unfold arraySwap
  step*
  simp [*]

#guard (execClosed arraySwap arraySwap.spec).1 = (8, 7)

def arrayFill : Result Nat := do
  let a ← Array.alloc Nat 3 (0 : Nat)
  a.fill 5
  let value ← a.read 1
  a.free
  pure value

theorem arrayFill.spec : ⦃ emp ⦄ arrayFill ⦃⇓ result => ⌜result = 5⌝⦄ := by
  unfold arrayFill
  step*
  simp [*]

#guard (execClosed arrayFill arrayFill.spec).1 = 5

/-! ## `copy` and `compare`

Both take two arrays, and the separating conjunction is what says they are two
allocations: nothing has to assume it. -/

def arrayCopyCompare : Result Bool := do
  let src ← Array.ofList [1, 2, 3]
  let dst ← Array.alloc Nat 3 (0 : Nat)
  dst.copy src
  let same ← Array.compare dst src
  dst.free
  src.free
  pure same

theorem arrayCopyCompare.spec :
    ⦃ emp ⦄ arrayCopyCompare ⦃⇓ result => ⌜result = true⌝⦄ := by
  unfold arrayCopyCompare
  step*

#guard (execClosed arrayCopyCompare arrayCopyCompare.spec).1 = true

/-! ## An array is a slice, and a slice is a range

The three layers own the same slots; crossing between them transfers ownership
and nothing else. -/

/-- Owning an array is owning the slice that spans it. -/
example (a : Array Nat 3) (values : List Nat) :
    (a ↦ values) = (a.toBuffer ↦ values) :=
  Array.pointsTo_eq_buffer a values

/-- And owning the slice is owning the range its pointer owns. -/
example (a : Array Nat 3) (values : List Nat) :
    a ↦ values ⊢ a.ptr ↦* values :=
  Array.pointsTo_entails_range a values

/-- An array holds exactly as many values as its type says. -/
example (a : Array Nat 3) (values : List Nat) (h : Heap)
    (hPointsTo : (a ↦ values) h) : values.length = 3 :=
  Array.length_of_pointsTo hPointsTo

/-- A slice of known length is an array. -/
example (b : Buffer Nat) (values : List Nat) (hLength : values.length = 3) :
    b ↦ values ⊢ (b.toArray 3) ↦ values :=
  Aeneas.Std.Buffer.pointsTo_toArray hLength

/-- Ownership of an array still splits along its indices, since the range
underneath it does. -/
example (a : Array Nat 3) (xs ys : List Nat) :
    a.ptr ↦* (xs ++ ys) ⊣⊢ a.ptr ↦* xs ∗ (a.ptr.add xs.length) ↦* ys :=
  Ptr.pointsToRange_append a.ptr xs ys

/-! ## Functional/memory interoperability -/

private def functionalArray :
    Aeneas.Std.Array Nat (Aeneas.Std.Usize.ofNat 3) :=
  Aeneas.Std.Array.from [1, 2, 3] (by simp)

def arrayMutToRawRoundTrip :
    Result (Aeneas.Std.Array Nat (Aeneas.Std.Usize.ofNat 3)) := do
  let a ← Array.mut_to_raw functionalArray
  a.write 1 9
  Array.end_mut_to_raw functionalArray a

theorem arrayMutToRawRoundTrip.spec :
    (arrayMutToRawRoundTrip)
      ⦃⇓ result => result.val = [1, 9, 3]⦄ := by
  unfold arrayMutToRawRoundTrip
  apply ispec_bind (Array.mut_to_raw.spec functionalArray)
  intro a
  step with Array.write.spec_array a [1, 2, 3] 1 9 (by simp)
  step with Array.end_mut_to_raw.spec functionalArray a [1, 9, 3]
  iframe

#guard (execClosed arrayMutToRawRoundTrip arrayMutToRawRoundTrip.spec).1.val =
  [1, 9, 3]

/-- Ending the raw array borrow releases every materialized slot. -/
example :
    (execClosed arrayMutToRawRoundTrip arrayMutToRawRoundTrip.spec).2.size = 0 := by
  native_decide

private def functionalSlice : Aeneas.Std.Slice Nat :=
  Aeneas.Std.Slice.from [4, 5, 6] (by scalar_tac)

def bufferMutToRawRoundTrip : Result (Aeneas.Std.Slice Nat) := do
  let b ← Buffer.mut_to_raw functionalSlice
  b.write 2 7
  Buffer.end_mut_to_raw functionalSlice b

theorem bufferMutToRawRoundTrip.spec :
    (bufferMutToRawRoundTrip)
      ⦃⇓ result => result.val = [4, 5, 7]⦄ := by
  unfold bufferMutToRawRoundTrip
  apply ispec_spec
  step as ⟨b⟩
  step with Buffer.write.spec_array b [4, 5, 6] 2 7 (by simp)
  step with Aeneas.Std.Buffer.end_mut_to_raw.spec functionalSlice b [4, 5, 7]
  simp [functionalSlice, List.setSlice!]
  iframe

#guard (execClosed bufferMutToRawRoundTrip bufferMutToRawRoundTrip.spec).1.val =
  [4, 5, 7]

/-- Ending the raw slice borrow releases every materialized slot. -/
example :
    (execClosed bufferMutToRawRoundTrip bufferMutToRawRoundTrip.spec).2.size = 0 := by
  native_decide

end SepLogic
