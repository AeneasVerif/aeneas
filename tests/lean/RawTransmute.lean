module

public import RawBoxProofs
public meta import RawBoxProofs
import all RawBoxProofs
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

theorem write_read.spec (repr : Aeneas.Std.Repr T) (p : RawPtr T) (bptr : BasePtr) (old value : T)
    (noPointers : ∀ q, ¬ repr.Carries value q)
    (hsize : 0 < repr.size) :
    HeapWP.Triple (pointsTo repr p bptr old)
      (do MutRawPtr.write repr p value; RawPtr.read repr p)
      (fun result h => result = value ∧ pointsTo repr p bptr value 0 h) := by
  apply HeapWP.Triple.bind (HeapWP.write.spec repr p bptr old value noPointers hsize)
  intro _
  exact HeapWP.read.spec repr p bptr value 0 hsize

/-- Casting away and back preserves the pointer and same-type write/read correctness. -/
theorem u32_round_trip.spec (repr : Aeneas.Std.Repr U32) (words : RawPtr U32) (bptr : BasePtr)
    (old value : U32) (noPointers : ∀ q, ¬ repr.Carries value q)
    (hsize : 0 < repr.size) :
    HeapWP.Triple (pointsTo repr words bptr old) (u32_round_trip repr words value)
      (fun result h => result = value ∧ pointsTo repr words bptr value 0 h) :=
  write_read.spec repr words bptr old value noPointers hsize

/-- The byte view has its own round-trip law, without an equation relating it to word values. -/
theorem u8_round_trip.spec (repr : Aeneas.Std.Repr U8) (words : RawPtr U32) (bptr : BasePtr)
    (old value : U8) (noPointers : ∀ q, ¬ repr.Carries value q)
    (hsize : 0 < repr.size) :
    HeapWP.Triple (pointsTo repr (RawPtr.cast U8 words) bptr old) (u8_round_trip repr words value)
      (fun result h => result = value ∧ pointsTo repr (RawPtr.cast U8 words) bptr value 0 h) :=
  write_read.spec repr (RawPtr.cast U8 words) bptr old value noPointers hsize

@[expose] def byteRepr : Aeneas.Std.Repr U8 := Aeneas.Std.Repr.u8

/-- A second admissible word descriptor, with the opposite byte order. -/
@[expose] def bigEndianRepr : Aeneas.Std.Repr U32 where
  size := 4
  align := ⟨4, 2, rfl⟩
  decode bytes := do
    let bytes ← bytes.mapM Aeneas.Std.Byte.numeric
    pure ⟨bytes[0].bv ++ bytes[1].bv ++ bytes[2].bv ++ bytes[3].bv⟩
  encode value bytes := bytes =
    (#v[⟨value.bv.extractLsb' 24 8⟩, ⟨value.bv.extractLsb' 16 8⟩,
      ⟨value.bv.extractLsb' 8 8⟩, ⟨value.bv.extractLsb' 0 8⟩] : Vector U8 4).map Aeneas.Std.Byte.data
  aligned := by decide
  encode_complete value := ⟨_, rfl⟩
  encode_decode value bytes encoded := by
    subst bytes
    rw [raw_box.dataBytes_numeric]
    change some ⟨value.bv.extractLsb' 24 8 ++ value.bv.extractLsb' 16 8 ++
      value.bv.extractLsb' 8 8 ++ value.bv.extractLsb' 0 8⟩ = some value
    apply congrArg some
    cases value
    rename_i bits
    apply congrArg UScalar.mk
    exact raw_box.u32Bytes_roundtrip bits
  decode_mono bytes bytes' value decoded agree := by
    cases hn : bytes.mapM Aeneas.Std.Byte.numeric
    · simp [hn] at decoded
    · rename_i values
      have same := raw_box.numericBytes_eq bytes bytes' values hn agree
      simpa only [same] using decoded
  encode_valid value bytes i encoded := by
    subst bytes
    simp only [Vector.getElem_map]

/- Concrete executions witness the lack of a descriptor-independent cross-type prediction.
They use two-element allocations and access only the second word, at byte offset four.
These are alternative descriptor models, not fresh endian choices within one execution. -/
def wordByteRun (repr : Aeneas.Std.Repr U32) (data : Vector Aeneas.Std.Byte repr.size)
    (encoded : repr.encode 0x01020304#u32 data) : Option U8 := do
  let (base, s₀) ← Heap.alloc repr 2 4#usize Heap.empty
  let p ← Heap.offset repr base 1 s₀
  let s₁ ← Heap.write repr p 0x01020304#u32 data encoded s₀
  Heap.read byteRepr (RawPtr.cast U8 p) s₁

def byteWordRun (repr : Aeneas.Std.Repr U32) : Option U32 := do
  let (base, s₀) ← Heap.newBlock repr
    [Vector.replicate repr.size (.data 0#u8), Vector.replicate repr.size (.data 0#u8)]
    true 4#usize none Heap.empty
  let p ← Heap.offset repr base 1 s₀
  let s₁ ← Heap.write byteRepr (RawPtr.cast U8 p) 1#u8 #v[.data 1#u8] rfl s₀
  Heap.read repr p s₁

theorem littleDecoded :
    raw_box.u32Repr.encode 0x01020304#u32 #v[.data 4#u8, .data 3#u8, .data 2#u8, .data 1#u8] := by
  change #v[.data 4#u8, .data 3#u8, .data 2#u8, .data 1#u8] =
    (raw_box.u32Bytes 0x01020304#u32).map Aeneas.Std.Byte.data
  unfold raw_box.u32Bytes
  native_decide

theorem bigDecoded :
    bigEndianRepr.encode 0x01020304#u32 #v[.data 1#u8, .data 2#u8, .data 3#u8, .data 4#u8] := by
  unfold bigEndianRepr
  dsimp
  native_decide

theorem cross_word_byte_counterexample :
    wordByteRun raw_box.u32Repr #v[.data 4#u8, .data 3#u8, .data 2#u8, .data 1#u8] littleDecoded = some 4#u8 ∧
    wordByteRun bigEndianRepr #v[.data 1#u8, .data 2#u8, .data 3#u8, .data 4#u8] bigDecoded = some 1#u8 := by
  native_decide

theorem cross_byte_word_counterexample :
    byteWordRun raw_box.u32Repr = some 1#u32 ∧
    byteWordRun bigEndianRepr = some 0x01000000#u32 := by
  native_decide

theorem no_uniform_word_byte_prediction :
    ¬ ∃ prediction : U8, ∀ (repr : Aeneas.Std.Repr U32) (data : Vector Aeneas.Std.Byte repr.size)
      (encoded : repr.encode 0x01020304#u32 data),
      wordByteRun repr data encoded = some prediction := by
  rintro ⟨prediction, h⟩
  have little := h raw_box.u32Repr #v[.data 4#u8, .data 3#u8, .data 2#u8, .data 1#u8] littleDecoded
  have big := h bigEndianRepr #v[.data 1#u8, .data 2#u8, .data 3#u8, .data 4#u8] bigDecoded
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
