module

public import RawTransmute
import all Aeneas.Std.Array.Array
import all RawBoxProofs

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
  decode bytes := (bytes.mapM Aeneas.Std.Byte.numeric).map fourBytes
  encode value bytes := bytes = (fourVector value).map Aeneas.Std.Byte.data
  aligned := by decide
  encode_complete value := ⟨_, rfl⟩
  encode_decode value bytes encoded := by
    subst bytes
    rw [raw_box.dataBytes_numeric]
    simp
  decode_mono bytes bytes' value decoded agree := by
    cases hn : bytes.mapM Aeneas.Std.Byte.numeric
    · simp [hn] at decoded
    · rename_i values
      have same := raw_box.numericBytes_eq bytes bytes' values hn agree
      simpa only [same] using decoded
  encode_valid value bytes i encoded := by
    subst bytes
    simp

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
    raw_box.u32Repr.decode ((wordEncoding value).map Aeneas.Std.Byte.data) = some value := by
  exact raw_box.u32Repr.encode_decode value _ rfl

theorem word_decode_bytes (bytes : Vector U8 4) :
    raw_box.u32Repr.decode (bytes.map Aeneas.Std.Byte.data) =
      some (fromLittleBytes (fourBytes bytes)) := by
  change ((bytes.map Aeneas.Std.Byte.data).mapM Aeneas.Std.Byte.numeric).bind
    (fun data => some (⟨data[3].bv ++ data[2].bv ++ data[1].bv ++ data[0].bv⟩ : U32)) = _
  rw [raw_box.dataBytes_numeric]
  simp only [Option.bind_some, fromLittleBytes, fourVector_fourBytes]

theorem bytes_of_word_decode (bytes : Vector U8 4) (value : U32)
    (decoded : raw_box.u32Repr.decode (bytes.map Aeneas.Std.Byte.data) = some value) :
    fourBytes bytes = toLittleBytes value := by
  have he : fromLittleBytes (fourBytes bytes) = value :=
    Option.some.inj ((word_decode_bytes bytes).symm.trans decoded)
  rw [← he, toLittleBytes, wordEncoding_decode]

@[simp] theorem from_toLittleBytes (value : U32) :
    fromLittleBytes (toLittleBytes value) = value :=
  Option.some.inj ((word_decode_bytes (wordEncoding value)).symm.trans (word_decode_encoding value))

theorem arrayRepr_noPointers (value : FourBytes) (q : RawPtr Unit) :
    ¬ arrayRepr.Carries value q := by
  rintro ⟨bytes, encoded, i, lane, byte⟩
  change bytes = (fourVector value).map Aeneas.Std.Byte.data at encoded
  subst bytes
  have impossible := (Vector.getElem_map Aeneas.Std.Byte.data
    (xs := fourVector value) i.isLt).symm.trans byte
  cases impossible

/-- Numerical decoding plus the library's exclusive-exposure guarantee recovers
the fixture's canonical word encoding; integer reads alone do not imply this. -/
theorem word_exposure_encoding (value : U32) (bytes : Vector Aeneas.Std.Byte 4)
    (decoded : raw_box.u32Repr.decode bytes = some value)
    (carried : ∀ i : Fin 4, ∀ q lane, bytes[i.val] = .pointer q lane →
      raw_box.u32Repr.Carries value q) :
    raw_box.u32Repr.encode value bytes := by
  have numeric : ∃ values, bytes.mapM Aeneas.Std.Byte.numeric = some values := by
    change (bytes.mapM Aeneas.Std.Byte.numeric).bind _ = some value at decoded
    cases hn : bytes.mapM Aeneas.Std.Byte.numeric
    · simp [hn] at decoded
    · exact ⟨_, rfl⟩
  let values := bytes.map (fun byte => match byte with
    | .data value => value
    | _ => 0#u8)
  have representation : bytes = values.map Aeneas.Std.Byte.data := by
    apply Vector.ext
    intro i hi
    obtain ⟨_, hv⟩ := vector_mapM_enabled numeric.choose_spec i hi
    simp only [values, Vector.getElem_map]
    cases hb : bytes[i]
    · simp [hb, Aeneas.Std.Byte.numeric] at hv
    · rfl
    · rename_i q lane
      exact (raw_box.u32Repr_noPointers value q (carried ⟨i, hi⟩ q lane hb)).elim
  rw [representation] at decoded ⊢
  have he := congrArg fourVector (bytes_of_word_decode values value decoded)
  simp only [toLittleBytes, fourVector_fourBytes] at he
  exact congrArg (Vector.map Aeneas.Std.Byte.data) he

end raw_transmute_externals
