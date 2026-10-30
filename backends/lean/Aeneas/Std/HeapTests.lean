module

import Aeneas.Std.Heap.Model
import Aeneas.Std.Heap.Effects
import all Aeneas.Std.Core.Ptr
import all Aeneas.Std.Primitives
import Aeneas.Std.Scalar.Notations
public meta import Aeneas.Std.Scalar.Core

open Aeneas.Std

namespace Aeneas.Std.HeapTests

unseal Result

def byteRepr : Repr U8 where
  size := 1
  align := ⟨1, 0, rfl⟩
  decode bytes := some bytes[0]
  aligned := by decide
  complete value := ⟨#v[value], rfl⟩

def alignedByteRepr : Repr U8 where
  size := 2
  align := ⟨2, 1, rfl⟩
  decode bytes := some bytes[0]
  aligned := by decide
  complete value := ⟨#v[value, 0#u8], rfl⟩

/- Both encodings are permitted. Choice must not silently fix the ignored byte
to the particular witness used in `complete`. -/
example (value : U8) (s : Heap) :
    HeapWP.Spec (alignedByteRepr.choose value)
      (fun data s' => data.val[0] = value ∧ s' = s) s := by
  apply HeapWP.Spec.mono (HeapWP.choose.spec alignedByteRepr value s)
  rintro data s' ⟨decoded, hs⟩
  exact ⟨Option.some.inj decoded, hs⟩

example (value : U8) (s : Heap) :
    ¬ HeapWP.Spec (alignedByteRepr.choose value) (fun data _ => data.val[1] = 0#u8) s := by
  intro h
  have hx := (HeapWP.Spec.choose alignedByteRepr value _ s).mp h #v[value, 1#u8] rfl
  change (1#u8) = 0#u8 at hx
  exact (by decide : (1#u8) ≠ 0#u8) hx

def roundTrip : Option U8 := do
  let (p, s₀) ← Heap.alloc byteRepr 1 Heap.empty
  if (Heap.read byteRepr p s₀).isSome then none else do
    let s₁ ← Heap.write byteRepr p 7#u8 #v[7#u8] rfl s₀
    let value ← Heap.read byteRepr p s₁
    let s₂ ← Heap.freeBlock byteRepr p 1 true s₁
    if (s₂.allocations p.base).isNone then some value else none

example : roundTrip = some 7#u8 := by native_decide

def borrowUninitialized : Option (List U8) := do
  let (p, s₀) ← Heap.alloc byteRepr 2 Heap.empty
  let s₁ ← Heap.borrowRange byteRepr p 2 s₀
  if (Heap.read byteRepr p s₁).isSome ||
      (Heap.write byteRepr p 7#u8 #v[7#u8] rfl s₁).isSome ||
      (Heap.freeBlock byteRepr p 2 true s₁).isSome then none else do
    let s₂ ← Heap.endBorrowRange byteRepr p [#v[7#u8], #v[8#u8]] s₁
    Heap.readRange byteRepr p 2 s₂

example : borrowUninitialized = some [7#u8, 8#u8] := by native_decide

def mixedSharing : Option (List U8) := do
  let (p, s₀) ← Heap.newBlock byteRepr [#v[7#u8], #v[8#u8]] true Heap.empty
  let s₁ ← Heap.share byteRepr p s₀
  let s₂ ← Heap.shareRange byteRepr p 2 s₁
  let values ← Heap.readRange byteRepr p 2 s₂
  if (Heap.borrowRange byteRepr p 2 s₂).isSome ||
      (Heap.freeBlock byteRepr p 2 true s₂).isSome then none else do
    let s₃ ← Heap.endShareRange byteRepr p 2 s₂
    let s₄ ← Heap.endShare byteRepr p s₃
    let _ ← Heap.freeBlock byteRepr p 2 true s₄
    some values

example : mixedSharing = some [7#u8, 8#u8] := by native_decide

def rangeFailure : Option (List U8) := do
  let (p, s₀) ← Heap.newBlock byteRepr [#v[7#u8], #v[8#u8]] true Heap.empty
  let s₁ ← Heap.share byteRepr ⟨p.base, 1#usize⟩ s₀
  if (Heap.borrowRange byteRepr p 2 s₁).isSome then none
  else Heap.readRange byteRepr p 2 s₁

example : rangeFailure = some [7#u8, 8#u8] := by native_decide

def alignmentFailure : Option Bool := do
  let (p, s) ← Heap.newBlock byteRepr [#v[7#u8], #v[8#u8]] true Heap.empty
  some ((Heap.read alignedByteRepr p s).isNone &&
    (Heap.borrow alignedByteRepr p s).isNone &&
    (Heap.write alignedByteRepr p 9#u8 #v[9#u8, 0#u8] rfl s).isNone &&
    (Heap.freeBlock alignedByteRepr p 1 true s).isNone)

example : alignmentFailure = some true := by native_decide

def movement : Option Bool := do
  let (p, s) ← Heap.alloc byteRepr 2 Heap.empty
  let finish ← Heap.offset byteRepr p 2 s
  let back ← Heap.offset byteRepr finish (-2) s
  some (back.byteOffset == p.byteOffset && finish.byteOffset == 2#usize &&
    (Heap.read byteRepr finish s).isNone &&
    (Heap.offset byteRepr p (-1) s).isNone &&
    (Heap.offset byteRepr finish 1 s).isNone)

example : movement = some true := by native_decide

def cleanupAuthority : Option Bool := do
  let (p, s₀) ← Heap.newBlock byteRepr [#v[7#u8], #v[8#u8]] false Heap.empty
  if (Heap.freeBlock byteRepr p 2 true s₀).isSome ||
      (Heap.freeBlock byteRepr p 1 false s₀).isSome then none else do
    let s₁ ← Heap.freeBlock byteRepr p 2 false s₀
    some ((Heap.read byteRepr p s₁).isNone)

example : cleanupAuthority = some true := by native_decide

def sharedExposure : Option Bool := do
  let (p, s₀) ← Heap.newSharedExposure byteRepr [#v[7#u8]] Heap.empty
  let s₁ ← Heap.share byteRepr p s₀
  if (Heap.endSharedExposure byteRepr p 1 s₁).isSome ||
      (Heap.write byteRepr p 7#u8 #v[7#u8] rfl s₁).isSome then none else do
    let s₂ ← Heap.endShare byteRepr p s₁
    let s₃ ← Heap.endSharedExposure byteRepr p 1 s₂
    some ((s₃.allocations p.base).isNone)

example : sharedExposure = some true := by native_decide

example :
    (Heap.alloc byteRepr 1
      { Heap.empty with next := ⟨BitVec.allOnes _⟩ }).isNone = true := by native_decide

example :
    (Heap.alloc byteRepr (2 ^ UScalarTy.numBits .Usize) Heap.empty).isNone = true := by
  native_decide

def separateAllocations : Option (List U8) := do
  let (p, s₀) ← Heap.newBlock byteRepr [#v[7#u8], #v[8#u8]] true Heap.empty
  let (q, s₁) ← Heap.newBlock byteRepr [#v[9#u8]] true s₀
  let s₂ ← Heap.borrow byteRepr p s₁
  let s₃ ← Heap.freeBlock byteRepr q 1 true s₂
  Heap.readRange byteRepr ⟨p.base, 1#usize⟩ 1 s₃

example : separateAllocations = some [8#u8] := by native_decide

def crossTypePermissions : Option Bool := do
  let (p, s₀) ← Heap.newBlock alignedByteRepr [#v[7#u8, 8#u8]] true Heap.empty
  let byte : RawPtr U8 := ⟨p.base, 1#usize⟩
  let s₁ ← Heap.share byteRepr byte s₀
  let value ← Heap.read alignedByteRepr p s₁
  if value != 7#u8 ||
      (Heap.write alignedByteRepr p 9#u8 #v[9#u8, 0#u8] rfl s₁).isSome then none else do
    let s₂ ← Heap.endShare byteRepr byte s₁
    let s₃ ← Heap.borrow byteRepr byte s₂
    if (Heap.read alignedByteRepr p s₃).isSome ||
        (Heap.write alignedByteRepr p 9#u8 #v[9#u8, 0#u8] rfl s₃).isSome ||
        (Heap.freeBlock alignedByteRepr p 1 true s₃).isSome then none else do
      let s₄ ← Heap.endBorrow byteRepr byte 9#u8 #v[9#u8] rfl s₃
      let first ← Heap.read alignedByteRepr p s₄
      let second ← Heap.read byteRepr byte s₄
      let _ ← Heap.freeBlock alignedByteRepr p 1 true s₄
      some (first == 7#u8 && second == 9#u8)

example : crossTypePermissions = some true := by native_decide

example (p : RawPtr U32) : RawPtr.cast U32 (RawPtr.cast U8 p) = p := rfl

/- The base is sufficiently aligned, but offset one is not. Every typed access
and permission operation must reject it; casting itself preserves it. -/
def misalignedAccess : Option Bool := do
  let (p, s) ← Heap.newBlock alignedByteRepr [#v[7#u8, 8#u8], #v[9#u8, 0#u8]] true Heap.empty
  let q : RawPtr U8 := ⟨p.base, 1#usize⟩
  some ((Heap.read alignedByteRepr q s).isNone &&
    (Heap.readRange alignedByteRepr q 1 s).isNone &&
    (Heap.write alignedByteRepr q 9#u8 #v[9#u8, 0#u8] rfl s).isNone &&
    (Heap.borrow alignedByteRepr q s).isNone &&
    (Heap.share alignedByteRepr q s).isNone &&
    (Heap.endShare alignedByteRepr q s).isNone &&
    (Heap.endBorrow alignedByteRepr q 9#u8 #v[9#u8, 0#u8] rfl s).isNone &&
    (Heap.borrowRange alignedByteRepr q 1 s).isNone &&
    (Heap.shareRange alignedByteRepr q 1 s).isNone &&
    (Heap.endShareRange alignedByteRepr q 1 s).isNone &&
    (Heap.endBorrowRange alignedByteRepr q [#v[9#u8, 0#u8]] s).isNone &&
    (Heap.read byteRepr (RawPtr.cast U8 q) s == some 8#u8))

example : misalignedAccess = some true := by native_decide

/- Observe the actual request and its continuation, not just the executable
heap operation returning `none`. Every permitted response must lead to `undef`. -/
def ObservesUndefined (s : State) (computation : Result T) : Prop :=
  ∃ (Answer : Type) (request : State → Answer → State → Prop)
    (resume : ULift Answer → Result T),
    computation = Result.vis (.guardedModify Answer request) resume ∧
    (∃ answer next, request s answer next) ∧
    ∀ answer next, request s answer next →
      next = s ∧ resume ⟨answer⟩ = Result.fail .undef

theorem read_observes_undef (repr : Repr T) (p : RawPtr T) (s : State)
    (failed : Heap.read repr p s = none) :
    ObservesUndefined s (RawPtr.read repr p) := by
  have disabled : ¬ ∃ value next, State.read repr p s value next := by
    rintro ⟨value, next, he, _⟩
    rw [failed] at he
    cases he
  refine ⟨Option T, State.checked (State.read repr p),
    (fun answer => Result.ofOption answer.down .undef), rfl,
    HeapWP.checked.enabled _ s, ?_⟩
  intro answer next ht
  obtain ⟨rfl, hs⟩ := (HeapWP.checked.failure disabled).mp ht
  exact ⟨hs, rfl⟩

def singleCellHeap (cell : Cell U8) : Heap :=
  { allocations := fun base =>
      if base = 0#usize then some ⟨[cell], ⟨1, 0, rfl⟩, true⟩ else none
    next := 1#usize }

def boolRepr : Repr Bool where
  size := 1
  align := ⟨1, 0, rfl⟩
  decode bytes := if bytes[0] = 0#u8 then some false
    else if bytes[0] = 1#u8 then some true else none
  aligned := by decide
  complete value := by
    cases value
    · exact ⟨#v[0#u8], by decide⟩
    · exact ⟨#v[1#u8], by decide⟩

/- Permission denial and invalid typed contents both reach the explicit
failure continuation without changing the failed operation's input heap. -/
example : ObservesUndefined (singleCellHeap .borrowed)
    (RawPtr.read byteRepr ⟨0#usize, 0#usize⟩) := by
  apply read_observes_undef
  native_decide

example : ObservesUndefined (singleCellHeap (.shared 0 (some 2#u8)))
    (RawPtr.read boolRepr ⟨0#usize, 0#usize⟩) := by
  apply read_observes_undef
  native_decide

def zeroRepr : Repr Unit where
  size := 0
  align := ⟨1, 0, rfl⟩
  decode _ := some ()
  aligned := by decide
  complete value := ⟨#v[], by cases value; rfl⟩

def zeroSize : Option Bool := do
  let (p, s₀) ← Heap.alloc zeroRepr 1 Heap.empty
  if (Heap.read zeroRepr p s₀).isSome ||
      (Heap.borrowRange zeroRepr p 1 s₀).isSome then none else do
    let s₁ ← Heap.borrowRange zeroRepr p 0 s₀
    let _ ← Heap.offset zeroRepr p 0 s₁
    let s₂ ← Heap.freeBlock zeroRepr p 1 true s₁
    some ((s₂.allocations p.base).isNone)

example : zeroSize = some true := by native_decide

/- Direct restoration calls are privileged; the byte store cannot authenticate
the matching Rust backward continuation. -/
def restoration_is_privileged : Option U8 := do
  let (p, s₀) ← Heap.newSharedExposure byteRepr [#v[7#u8]] Heap.empty
  let s₁ ← Heap.endShareRange byteRepr p 1 s₀
  let s₂ ← Heap.write byteRepr p 9#u8 #v[9#u8] rfl s₁
  Heap.read byteRepr p s₂

example : restoration_is_privileged = some 9#u8 := by native_decide

end Aeneas.Std.HeapTests
