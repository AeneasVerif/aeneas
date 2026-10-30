module

public import RawTransmuteExternals.Funs
import all Aeneas.Std.Core.Ptr
import all RawTransmute

public section

open Aeneas Aeneas.Std Aeneas.Std.SepLogic

namespace raw_transmute_externals

/-- Thin mutable-pointer transmute is pure and preserves the byte offset and base. -/
@[step]
theorem ext.transmute_mut.spec {T : Type} (U : Type) (p : MutRawPtr T) :
    ext.transmute_mut U p ⦃ (result : MutRawPtr U) => result = RawPtr.cast U p ⦄ := by
  simp [ext.transmute_mut]

/-- Constness changes neither the cast's representation nor its purity. -/
@[step]
theorem ext.transmute_const.spec {T : Type} (U : Type) (p : ConstRawPtr T) :
    ext.transmute_const U p ⦃ (result : ConstRawPtr U) => result = RawPtr.cast U p ⦄ := by
  simp [ext.transmute_const]

/-- The extracted mutable-pointer round trip preserves the original pointer exactly. -/
@[step]
theorem mut_pointer_round_trip.spec (words : MutRawPtr U32) :
    mut_pointer_round_trip words ⦃ (result : MutRawPtr U32) => result = words ⦄ := by
  simp [mut_pointer_round_trip, ext.transmute_mut, RawPtr.cast]

/-- The extracted const-pointer round trip uses ordinary, effect-free WP. -/
@[step]
theorem const_pointer_round_trip.spec (words : ConstRawPtr U32) :
    const_pointer_round_trip words ⦃ (result : ConstRawPtr U32) => result = words ⦄ := by
  simp [const_pointer_round_trip, ext.transmute_const, RawPtr.cast]

theorem u32_round_trip_eq (words : MutRawPtr U32) (value : U32) :
    u32_round_trip words value = raw_transmute.u32_round_trip raw_box.u32Repr words value := by
  simp [u32_round_trip, ext.transmute_mut, ext.write_word, ext.read_word,
    raw_transmute.u32_round_trip]

theorem u8_round_trip_eq (words : MutRawPtr U32) (value : U8) :
    u8_round_trip words value =
      raw_transmute.u8_round_trip raw_transmute.byteRepr words value := by
  simp [u8_round_trip, ext.transmute_mut, ext.write_byte, ext.read_byte,
    raw_transmute.u8_round_trip]

/-- The unedited extracted word caller writes and reads back the replacement. -/
theorem u32_round_trip.spec (words : MutRawPtr U32) (old value : U32) :
    HeapWP.Triple (pointsTo raw_box.u32Repr words old) (u32_round_trip words value)
      (fun result h => result = value ∧ pointsTo raw_box.u32Repr words value 0 h) := by
  rw [u32_round_trip_eq]
  exact raw_transmute.u32_round_trip.spec raw_box.u32Repr words old value (by decide)

/-- The unedited extracted byte caller has the same-type round-trip law. -/
theorem u8_round_trip.spec (words : MutRawPtr U32) (old value : U8) :
    HeapWP.Triple (pointsTo raw_transmute.byteRepr (RawPtr.cast U8 words) old)
      (u8_round_trip words value)
      (fun result h => result = value ∧
        pointsTo raw_transmute.byteRepr (RawPtr.cast U8 words) value 0 h) := by
  rw [u8_round_trip_eq]
  exact raw_transmute.u8_round_trip.spec raw_transmute.byteRepr words old value (by decide)

/- These bridges identify the extracted cross-type callers with the previous
manual models. They do not assert a decoder-independent numeric postcondition. -/
theorem word_to_byte_eq (words : MutRawPtr U32) (value : U32) :
    word_to_byte words value =
      raw_transmute.word_to_byte raw_box.u32Repr raw_transmute.byteRepr words value := by
  simp [word_to_byte, ext.transmute_mut, ext.write_word, ext.read_byte,
    raw_transmute.word_to_byte]

theorem byte_to_word_eq (words : MutRawPtr U32) (value : U8) :
    byte_to_word words value =
      raw_transmute.byte_to_word raw_box.u32Repr raw_transmute.byteRepr words value := by
  simp [byte_to_word, ext.transmute_mut, ext.write_byte, ext.read_word,
    raw_transmute.byte_to_word]

/-- info: 'raw_transmute_externals.mut_pointer_round_trip.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mut_pointer_round_trip.spec

/-- info: 'raw_transmute_externals.const_pointer_round_trip.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms const_pointer_round_trip.spec

/-- info: 'raw_transmute_externals.u32_round_trip.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms u32_round_trip.spec

/-- info: 'raw_transmute_externals.u8_round_trip.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms u8_round_trip.spec

end raw_transmute_externals
