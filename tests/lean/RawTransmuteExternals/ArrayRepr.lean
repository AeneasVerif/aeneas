module

public import RawTransmute
import all Aeneas.Std.Array.Array

@[expose] public section

open Aeneas.Std

namespace raw_transmute_externals

abbrev FourBytes := Aeneas.Std.Array U8 4#usize

def fourBytes (bytes : Vector U8 4) : FourBytes :=
  .from bytes.toList (by simp)

def fourVector (bytes : FourBytes) : Vector U8 4 :=
  ⟨bytes.val.toArray, by simp⟩

@[simp] theorem fourBytes_fourVector (bytes : FourBytes) :
    fourBytes (fourVector bytes) = bytes := by
  simp [fourBytes, fourVector]

@[simp] theorem fourVector_fourBytes (bytes : Vector U8 4) :
    fourVector (fourBytes bytes) = bytes := by
  apply Vector.toList_inj.mp
  simp [fourBytes, fourVector]

/-- Actual byte-array size and alignment: four bytes, aligned to one byte. -/
def arrayRepr : Aeneas.Std.Repr FourBytes where
  size := 4
  align := ⟨1, 0, rfl⟩
  decode bytes := some (fourBytes bytes)
  aligned := by decide
  complete value := ⟨fourVector value, by simp⟩

def wordEncoding (value : U32) : Vector U8 4 :=
  #v[⟨value.bv.extractLsb' 0 8⟩, ⟨value.bv.extractLsb' 8 8⟩,
    ⟨value.bv.extractLsb' 16 8⟩, ⟨value.bv.extractLsb' 24 8⟩]

/-- The fixture's explicit little-endian conversion, not a global layout rule. -/
def toLittleBytes (value : U32) : FourBytes :=
  fourBytes (wordEncoding value)

def fromLittleBytes (bytes : FourBytes) : U32 :=
  let data := fourVector bytes
  ⟨data[3].bv ++ data[2].bv ++ data[1].bv ++ data[0].bv⟩

theorem extract_join (a b c d : BitVec 8) :
    (d ++ c ++ b ++ a).extractLsb' 0 8 = a ∧
    (d ++ c ++ b ++ a).extractLsb' 8 8 = b ∧
    (d ++ c ++ b ++ a).extractLsb' 16 8 = c ∧
    (d ++ c ++ b ++ a).extractLsb' 24 8 = d := by
  bv_decide

theorem wordEncoding_decode (bytes : Vector U8 4) :
    wordEncoding (fromLittleBytes (fourBytes bytes)) = bytes := by
  simp only [fromLittleBytes, fourVector_fourBytes]
  apply Vector.ext
  intro i hi
  have cases_i : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by agrind
  rcases cases_i with rfl | rfl | rfl | rfl
  · change (⟨(bytes[3].bv ++ bytes[2].bv ++ bytes[1].bv ++ bytes[0].bv).extractLsb' 0 8⟩ : U8) = bytes[0]
    exact congrArg UScalar.mk (extract_join _ _ _ _).1
  · change (⟨(bytes[3].bv ++ bytes[2].bv ++ bytes[1].bv ++ bytes[0].bv).extractLsb' 8 8⟩ : U8) = bytes[1]
    exact congrArg UScalar.mk (extract_join _ _ _ _).2.1
  · change (⟨(bytes[3].bv ++ bytes[2].bv ++ bytes[1].bv ++ bytes[0].bv).extractLsb' 16 8⟩ : U8) = bytes[2]
    exact congrArg UScalar.mk (extract_join _ _ _ _).2.2.1
  · change (⟨(bytes[3].bv ++ bytes[2].bv ++ bytes[1].bv ++ bytes[0].bv).extractLsb' 24 8⟩ : U8) = bytes[3]
    exact congrArg UScalar.mk (extract_join _ _ _ _).2.2.2

theorem word_decode_encoding (value : U32) :
    raw_box.u32Repr.decode (wordEncoding value) = some value := by
  cases value
  rename_i bits
  apply congrArg some
  apply congrArg UScalar.mk
  exact raw_box.u32Bytes_roundtrip bits

theorem word_decode_bytes (bytes : Vector U8 4) :
    raw_box.u32Repr.decode bytes = some (fromLittleBytes (fourBytes bytes)) := by
  simp [raw_box.u32Repr, fromLittleBytes]

theorem bytes_of_word_decode (bytes : Vector U8 4) (value : U32)
    (decoded : raw_box.u32Repr.decode bytes = some value) :
    fourBytes bytes = toLittleBytes value := by
  have he : fromLittleBytes (fourBytes bytes) = value :=
    Option.some.inj ((word_decode_bytes bytes).symm.trans decoded)
  rw [← he, toLittleBytes, wordEncoding_decode]

end raw_transmute_externals
