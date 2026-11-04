module

public import RawTransmute
import all Aeneas.Std.Heap.Effects
import all Aeneas.Std.Primitives

@[expose] public section

open Aeneas.Std

namespace raw_value_casts

/- A by-value model for these opaque wrappers, not a compiler rule for arbitrary
Rust transmute or its lifetime and ownership obligations. -/
def reinterpret (source : Aeneas.Std.Repr S) (target : Aeneas.Std.Repr T) (sizeEq : source.size = target.size)
    (value : S) : Result T := do
  let data ← source.choose value
  Result.ofOption (target.decode (data.val.cast sizeEq)) .undef

theorem reinterpret.spec (source : Aeneas.Std.Repr S) (target : Aeneas.Std.Repr T)
    (sizeEq : source.size = target.size) (value : S) (expected : T)
    (compatible : ∀ data, source.decode data = some value →
      target.decode (data.cast sizeEq) = some expected) (s : Heap) :
    HeapWP.Spec (reinterpret source target sizeEq value)
      (fun result s' => result = expected ∧ s' = s) s := by
  unfold reinterpret
  apply HeapWP.Spec.bind (HeapWP.choose.spec source value s)
  rintro ⟨data, decoded⟩ s' ⟨_, rfl⟩
  rw [compatible data (source.encode_decode value data decoded)]
  exact HeapWP.Spec.pure _ _ _ |>.mpr ⟨rfl, rfl⟩

def boolByte (value : Bool) : U8 :=
  if value then 1#u8 else 0#u8

def decodeBool (byte : U8) : Option Bool :=
  if byte = 0#u8 then some false else if byte = 1#u8 then some true else none

def boolRepr : Aeneas.Std.Repr Bool where
  size := 1
  align := ⟨1, 0, rfl⟩
  decode data := (Aeneas.Std.Repr.u8.decode data).bind decodeBool
  encode value data := Aeneas.Std.Repr.u8.encode (boolByte value) data
  aligned := by decide
  encode_complete value := Aeneas.Std.Repr.u8.encode_complete (boolByte value)
  encode_decode value data encoded := by
    rw [Aeneas.Std.Repr.u8.encode_decode _ _ encoded]
    cases value
    · rfl
    · rfl
  decode_mono data data' value decoded agree := by
    cases hd : Aeneas.Std.Repr.u8.decode data
    · simp [hd] at decoded
    · rename_i byte
      rw [Aeneas.Std.Repr.u8.decode_mono _ _ byte hd agree]
      simpa only [hd, Option.bind_some] using decoded
  encode_valid value data i encoded :=
    Aeneas.Std.Repr.u8.encode_valid (boolByte value) data i encoded

@[simp] theorem boolRepr_noPointers (value : Bool) (p : RawPtr Unit) :
    ¬ boolRepr.Carries value p := by
  intro carried
  exact Aeneas.Std.Repr.u8_noPointers (boolByte value) p carried

def asSigned (value : U32) : I32 := ⟨value.bv⟩

def asUnsigned (value : I32) : U32 := ⟨value.bv⟩

def signedRepr : Aeneas.Std.Repr I32 where
  size := raw_box.u32Repr.size
  align := raw_box.u32Repr.align
  decode data := (raw_box.u32Repr.decode data).map asSigned
  encode value data := raw_box.u32Repr.encode (asUnsigned value) data
  aligned := raw_box.u32Repr.aligned
  encode_complete value := raw_box.u32Repr.encode_complete (asUnsigned value)
  encode_decode value data encoded := by
    rw [raw_box.u32Repr.encode_decode _ _ encoded]
    rfl
  decode_mono data data' value decoded agree := by
    cases hd : raw_box.u32Repr.decode data
    · simp [hd] at decoded
    · rename_i word
      rw [raw_box.u32Repr.decode_mono _ _ word hd agree]
      simpa only [hd, Option.map_some] using decoded
  encode_valid value data i encoded :=
    raw_box.u32Repr.encode_valid (asUnsigned value) data i encoded

theorem decodeBool_some (byte : U8) (value : Bool) :
    decodeBool byte = some value ↔ byte = boolByte value := by
  cases value
  · by_cases hz : byte = 0#u8
    · simp [decodeBool, boolByte, hz]
    · simp [decodeBool, boolByte, hz]
  · by_cases hz : byte = 0#u8
    · simp [decodeBool, boolByte, hz]
    · simp [decodeBool, boolByte, hz]
      scalar_tac

/-- Forward bool-to-byte compatibility does not imply mutable write-back closure. -/
theorem bool_writeback_rejected :
    raw_transmute.byteRepr.decode #v[.data 2#u8] = some 2#u8 ∧
      boolRepr.decode #v[.data 2#u8] = none := by
  decide

/-- info: 'raw_value_casts.reinterpret.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reinterpret.spec

end raw_value_casts
