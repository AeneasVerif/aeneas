module

import Aeneas.Std.Heap.Model
import Aeneas.Std.Scalar.Notations
public meta import Aeneas.Std.Scalar.Core

open Aeneas.Std

namespace Aeneas.Std.HeapTests

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
  some (back.index == p.index && finish.index == 2#usize &&
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

end Aeneas.Std.HeapTests
