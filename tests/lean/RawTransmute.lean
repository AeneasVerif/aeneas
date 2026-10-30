module

public import RawBoxProofs
public meta import RawBoxProofs
import all Aeneas.Std.Core.Ptr
import all Aeneas.Std.Heap.Model

/- Manually adapted raw-pointer bodies from raw_transmute.rs. The native caller uses
the second element of a two-word array; these contracts start at the raw-pointer boundary,
not at an extracted array exposure. Descriptors are independent unless explicitly calibrated. -/

public section

open Aeneas.Std Aeneas.Std.SepLogic

namespace raw_transmute

def u32_round_trip (repr : Aeneas.Std.Repr U32) (words : RawPtr U32) (value : U32) : Result U32 := do
  let bytes := RawPtr.cast U8 words
  let words_again := RawPtr.cast U32 bytes
  MutRawPtr.write repr words_again value
  RawPtr.read repr words_again

def u8_round_trip (repr : Aeneas.Std.Repr U8) (words : RawPtr U32) (value : U8) : Result U8 := do
  let bytes := RawPtr.cast U8 words
  MutRawPtr.write repr bytes value
  RawPtr.read repr bytes

def word_to_byte (wordRepr : Aeneas.Std.Repr U32) (byteRepr : Aeneas.Std.Repr U8)
    (words : RawPtr U32) (value : U32) : Result U8 := do
  MutRawPtr.write wordRepr words value
  RawPtr.read byteRepr (RawPtr.cast U8 words)

def byte_to_word (wordRepr : Aeneas.Std.Repr U32) (byteRepr : Aeneas.Std.Repr U8)
    (words : RawPtr U32) (value : U8) : Result U32 := do
  MutRawPtr.write byteRepr (RawPtr.cast U8 words) value
  RawPtr.read wordRepr words

theorem write_read.spec (repr : Aeneas.Std.Repr T) (p : RawPtr T) (old value : T)
    (hsize : 0 < repr.size) :
    HeapWP.Triple (pointsTo repr p old)
      (do MutRawPtr.write repr p value; RawPtr.read repr p)
      (fun result h => result = value ∧ pointsTo repr p value 0 h) := by
  apply HeapWP.Triple.bind (HeapWP.write.spec repr p old value hsize)
  intro _
  exact HeapWP.read.spec repr p value 0 hsize

/-- Casting away and back preserves the pointer and same-type write/read correctness. -/
theorem u32_round_trip.spec (repr : Aeneas.Std.Repr U32) (words : RawPtr U32) (old value : U32)
    (hsize : 0 < repr.size) :
    HeapWP.Triple (pointsTo repr words old) (u32_round_trip repr words value)
      (fun result h => result = value ∧ pointsTo repr words value 0 h) :=
  write_read.spec repr words old value hsize

/-- The byte view has its own round-trip law, without an equation relating it to word values. -/
theorem u8_round_trip.spec (repr : Aeneas.Std.Repr U8) (words : RawPtr U32) (old value : U8)
    (hsize : 0 < repr.size) :
    HeapWP.Triple (pointsTo repr (RawPtr.cast U8 words) old) (u8_round_trip repr words value)
      (fun result h => result = value ∧ pointsTo repr (RawPtr.cast U8 words) value 0 h) :=
  write_read.spec repr (RawPtr.cast U8 words) old value hsize

@[expose] def byteRepr : Aeneas.Std.Repr U8 where
  size := 1
  align := ⟨1, 0, rfl⟩
  decode bytes := some bytes[0]
  aligned := by decide
  complete value := ⟨#v[value], rfl⟩

/-- A second admissible word descriptor, with the opposite byte order. -/
@[expose] def bigEndianRepr : Aeneas.Std.Repr U32 where
  size := 4
  align := ⟨4, 2, rfl⟩
  decode bytes := some ⟨bytes[0].bv ++ bytes[1].bv ++ bytes[2].bv ++ bytes[3].bv⟩
  aligned := by decide
  complete value := by
    rcases value with ⟨bits⟩
    refine ⟨#v[⟨bits.extractLsb' 24 8⟩, ⟨bits.extractLsb' 16 8⟩,
      ⟨bits.extractLsb' 8 8⟩, ⟨bits.extractLsb' 0 8⟩], ?_⟩
    apply congrArg some
    apply congrArg UScalar.mk
    exact raw_box.u32Bytes_roundtrip bits

/- Concrete executions witness the lack of a descriptor-independent cross-type prediction.
They use two-element allocations and access only the second word, at byte offset four.
These are alternative descriptor models, not fresh endian choices within one execution. -/
def wordByteRun (repr : Aeneas.Std.Repr U32) (data : Vector U8 repr.size)
    (decoded : repr.decode data = some 0x01020304#u32) : Option U8 := do
  let (base, s₀) ← Heap.alloc repr 2 Heap.empty
  let p ← Heap.offset repr base 1 s₀
  let s₁ ← Heap.write repr p 0x01020304#u32 data decoded s₀
  Heap.read byteRepr (RawPtr.cast U8 p) s₁

def byteWordRun (repr : Aeneas.Std.Repr U32) : Option U32 := do
  let (base, s₀) ← Heap.newBlock repr
    [Vector.replicate repr.size 0#u8, Vector.replicate repr.size 0#u8] true Heap.empty
  let p ← Heap.offset repr base 1 s₀
  let s₁ ← Heap.write byteRepr (RawPtr.cast U8 p) 1#u8 #v[1#u8] rfl s₀
  Heap.read repr p s₁

theorem littleDecoded :
    raw_box.u32Repr.decode #v[4#u8, 3#u8, 2#u8, 1#u8] = some 0x01020304#u32 := by
  native_decide

theorem bigDecoded :
    bigEndianRepr.decode #v[1#u8, 2#u8, 3#u8, 4#u8] = some 0x01020304#u32 := by
  native_decide

theorem cross_word_byte_counterexample :
    wordByteRun raw_box.u32Repr #v[4#u8, 3#u8, 2#u8, 1#u8] littleDecoded = some 4#u8 ∧
    wordByteRun bigEndianRepr #v[1#u8, 2#u8, 3#u8, 4#u8] bigDecoded = some 1#u8 := by
  native_decide

theorem cross_byte_word_counterexample :
    byteWordRun raw_box.u32Repr = some 1#u32 ∧
    byteWordRun bigEndianRepr = some 0x01000000#u32 := by
  native_decide

theorem no_uniform_word_byte_prediction :
    ¬ ∃ prediction : U8, ∀ (repr : Aeneas.Std.Repr U32) (data : Vector U8 repr.size)
      (decoded : repr.decode data = some 0x01020304#u32),
      wordByteRun repr data decoded = some prediction := by
  rintro ⟨prediction, h⟩
  have little := h raw_box.u32Repr #v[4#u8, 3#u8, 2#u8, 1#u8] littleDecoded
  have big := h bigEndianRepr #v[1#u8, 2#u8, 3#u8, 4#u8] bigDecoded
  rw [cross_word_byte_counterexample.1] at little
  rw [cross_word_byte_counterexample.2] at big
  have bad : (4#u8) = 1#u8 := (Option.some.inj little).trans (Option.some.inj big).symm
  exact (by decide : (4#u8) ≠ 1#u8) bad

theorem no_uniform_byte_word_prediction :
    ¬ ∃ prediction : U32, ∀ repr : Aeneas.Std.Repr U32, byteWordRun repr = some prediction := by
  rintro ⟨prediction, h⟩
  have little := h raw_box.u32Repr
  have big := h bigEndianRepr
  rw [cross_byte_word_counterexample.1] at little
  rw [cross_byte_word_counterexample.2] at big
  have bad : (1#u32) = 0x01000000#u32 :=
    (Option.some.inj little).trans (Option.some.inj big).symm
  exact (by decide : (1#u32) ≠ 0x01000000#u32) bad

/-- info: 'raw_transmute.u32_round_trip.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms u32_round_trip.spec

/-- info: 'raw_transmute.u8_round_trip.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms u8_round_trip.spec

end raw_transmute
