import Aeneas.Std.Buffer
import Aeneas.Std.Array.ArraySlice
import Aeneas.Tactic.SepLogic
import Aeneas.Tactic.Step.StepStar

/-!
# Buffer operations and functional/memory interoperability

These tests use the standard-library buffer directly. The fixed-length mutable
array prototype lives on `cezar/fosl-examples`; interpreter checks live on
`cezar/sm-semantics`.
-/

open Aeneas Aeneas.SepLogic Aeneas.Std.WP
open Aeneas.Std (Buffer ByteRepr Heap RawPtr Result U32)

namespace SepLogic.BufferTests

attribute [local step] Buffer.read.spec_buffer Buffer.write.spec_buffer Buffer.swap.spec

private theorem buffer_length {T : Type} [ByteRepr T] (b : Buffer T) (values : List T) :
    b ↦ values ⊢ ⌜b.length = values.length⌝ ∗ b ↦ values :=
  fun heap h => (sep_pure_l _ _ heap).mpr ⟨(Buffer.length_of_pointsTo h).symm, h⟩

/-! ## Allocation, indexed access and release -/

def bufferRoundTrip : Result Nat := do
  let b ← Buffer.alloc 3 0#u32
  b.write 0 1#u32
  b.write 2 41#u32
  let x ← b.read 0
  let y ← b.read 2
  b.free
  pure (x.val + y.val)

theorem bufferRoundTrip.spec :
    ⦃ emp ⦄ bufferRoundTrip ⦃⇓ result => ⌜result = 42⌝⦄ := by
  unfold bufferRoundTrip
  step*
  simp [*]

/-! ## `ofList`, `swap` and `fill` -/

def bufferSwap : Result (U32 × U32) := do
  let b ← Buffer.ofList [7#u32, 8#u32]
  b.swap 0 1
  let x ← b.read 0
  let y ← b.read 1
  b.free
  pure (x, y)

theorem bufferSwap.spec : ⦃ emp ⦄ bufferSwap ⦃⇓ result => ⌜result = (8#u32, 7#u32)⌝⦄ := by
  unfold bufferSwap
  step*
  simp [*]

def bufferFill : Result U32 := do
  let b ← Buffer.alloc 3 0#u32
  b.fill 5#u32
  let value ← b.read 1
  b.free
  pure value

theorem bufferFill.spec : ⦃ emp ⦄ bufferFill ⦃⇓ result => ⌜result = 5#u32⌝⦄ := by
  unfold bufferFill
  step as ⟨b⟩
  irewrite (buffer_length b _)
  iintro hLength
  step*
  simp [*]

/-! ## `copy` and `compare` on separate allocations -/

def bufferCopyCompare : Result Bool := do
  let src ← Buffer.ofList [1#u32, 2#u32, 3#u32]
  let dst ← Buffer.alloc 3 0#u32
  dst.copy src
  let same ← dst.compare src
  dst.free
  src.free
  pure same

theorem bufferCopyCompare.spec :
    ⦃ emp ⦄ bufferCopyCompare ⦃⇓ result => ⌜result = true⌝⦄ := by
  unfold bufferCopyCompare
  step as ⟨src⟩
  step as ⟨dst⟩
  irewrite (buffer_length src _)
  irewrite (buffer_length dst _)
  iintro
  step*

/-! ## Buffer ownership and its underlying range -/

example (b : Buffer U32) (values : List U32) :
    (b ↦ values) = iprop(⌜values.length = b.length⌝ ∗ b.ptr ↦* values) :=
  Buffer.pointsTo_def b values

example (b : Buffer U32) (values : List U32) :
    b ↦ values ⊢ b.ptr ↦* values :=
  Buffer.pointsTo_entails_range b values

example (b : Buffer U32) (values : List U32) (h : Heap)
    (hPointsTo : (b ↦ values) h) : values.length = b.length :=
  Buffer.length_of_pointsTo hPointsTo

example (b : Buffer U32) (values : List U32) (hLength : values.length = b.length) :
    b.ptr ↦* values ⊢ b ↦ values :=
  Buffer.range_entails_pointsTo hLength

example (b : Buffer U32) (xs ys : List U32) :
    b.ptr ↦* (xs ++ ys) ⊣⊢ b.ptr ↦* xs ∗ (b.ptr.add xs.length) ↦* ys :=
  RawPtr.pointsToRange_append b.ptr xs ys

/-! ## Functional/memory interoperability -/

private def functionalArray :
    Aeneas.Std.Array U32 (Aeneas.Std.Usize.ofNat 3) :=
  Aeneas.Std.Array.from [1#u32, 2#u32, 3#u32] (by simp)

def arrayMutToRawRoundTrip :
    Result (Aeneas.Std.Array U32 (Aeneas.Std.Usize.ofNat 3)) := do
  let b ← Buffer.mut_to_raw functionalArray.to_slice
  b.write 1 9#u32
  let updated ← Buffer.end_mut_to_raw functionalArray.to_slice b
  pure (functionalArray.from_slice updated)

theorem arrayMutToRawRoundTrip.spec :
    ⦃ emp ⦄ arrayMutToRawRoundTrip ⦃⇓ result => ⌜result.val = [1#u32, 9#u32, 3#u32]⌝⦄ := by
  unfold arrayMutToRawRoundTrip
  step as ⟨b⟩
  step with Buffer.write.spec_buffer b [1#u32, 2#u32, 3#u32] 1 9#u32 (by simp)
  step with Buffer.end_mut_to_raw.spec functionalArray.to_slice b [1#u32, 9#u32, 3#u32]
    as ⟨updated, hUpdated⟩
  have hValues : updated.val = [1#u32, 9#u32, 3#u32] := by
    simpa [functionalArray, Aeneas.Std.Array.to_slice, List.setSlice!] using hUpdated
  step
  simp [Aeneas.Std.Array.from_slice, hValues]

private def functionalSlice : Aeneas.Std.Slice U32 :=
  Aeneas.Std.Slice.from [4#u32, 5#u32, 6#u32] (by scalar_tac)

def bufferMutToRawRoundTrip : Result (Aeneas.Std.Slice U32) := do
  let b ← Buffer.mut_to_raw functionalSlice
  b.write 2 7#u32
  Buffer.end_mut_to_raw functionalSlice b

theorem bufferMutToRawRoundTrip.spec :
    ⦃ emp ⦄ bufferMutToRawRoundTrip ⦃⇓ result => ⌜result.val = [4#u32, 5#u32, 7#u32]⌝⦄ := by
  unfold bufferMutToRawRoundTrip
  step as ⟨b⟩
  step with Buffer.write.spec_buffer b [4#u32, 5#u32, 6#u32] 2 7#u32 (by simp)
  step with Buffer.end_mut_to_raw.spec functionalSlice b [4#u32, 5#u32, 7#u32]

end SepLogic.BufferTests
