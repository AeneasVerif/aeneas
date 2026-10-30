module

public import RawValueCasts.Funs
import all Aeneas.Std.Heap.Effects
import all Aeneas.Std.Primitives

public section

open Aeneas Aeneas.Std

namespace raw_value_casts

theorem ext.bool_to_byte.spec (value : Bool) (s : Heap) :
    HeapWP.Spec (ext.bool_to_byte value)
      (fun result s' => result = boolByte value ∧ s' = s) s := by
  apply reinterpret.spec
  intro data decoded
  change some data[0] = some (boolByte value)
  exact congrArg some ((decodeBool_some data[0] value).mp decoded)

theorem ext.byte_to_bool.spec (value : U8) (valid : value.val ≤ 1) (s : Heap) :
    HeapWP.Spec (ext.byte_to_bool value)
      (fun result s' => result = (value == 1#u8) ∧ s' = s) s := by
  apply reinterpret.spec
  intro data decoded
  have hd : data[0] = value := Option.some.inj decoded
  change decodeBool data[0] = some (value == 1#u8)
  rw [hd]
  have hv : value = 0#u8 ∨ value = 1#u8 := by scalar_tac
  rcases hv with rfl | rfl
  · rfl
  · rfl

theorem ext.unsigned_to_signed.spec (value : U32) (s : Heap) :
    HeapWP.Spec (ext.unsigned_to_signed value)
      (fun result s' => result = asSigned value ∧ s' = s) s := by
  apply reinterpret.spec
  intro data decoded
  change (raw_box.u32Repr.decode data).map asSigned = some (asSigned value)
  rw [decoded]
  rfl

theorem ext.signed_to_unsigned.spec (value : I32) (s : Heap) :
    HeapWP.Spec (ext.signed_to_unsigned value)
      (fun result s' => result = asUnsigned value ∧ s' = s) s := by
  apply reinterpret.spec
  intro data decoded
  change raw_box.u32Repr.decode data = some (asUnsigned value)
  have hd := congrArg (Option.map asUnsigned) decoded
  change ((raw_box.u32Repr.decode data).map asSigned).map asUnsigned =
    some (asUnsigned value) at hd
  rw [Option.map_map] at hd
  change (raw_box.u32Repr.decode data).map id = some (asUnsigned value) at hd
  simpa only [Option.map_id, id] using hd

theorem bool_byte_round_trip.spec (value : Bool) (s : Heap) :
    HeapWP.Spec (bool_byte_round_trip value)
      (fun result s' => result = value ∧ s' = s) s := by
  unfold bool_byte_round_trip
  apply HeapWP.Spec.bind (ext.bool_to_byte.spec value s)
  rintro byte s' ⟨rfl, rfl⟩
  have hv : (boolByte value).val ≤ 1 := by
    cases value
    · decide
    · decide
  apply HeapWP.Spec.mono (ext.byte_to_bool.spec (boolByte value) hv _)
  rintro result s' ⟨rfl, rfl⟩
  cases value
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

theorem checked_byte_to_bool.spec (value : U8) (s : Heap) :
    HeapWP.Spec (checked_byte_to_bool value)
      (fun result s' => result = decodeBool value ∧ s' = s) s := by
  unfold checked_byte_to_bool
  split
  · rename_i valid
    apply HeapWP.Spec.bind (ext.byte_to_bool.spec value (by simpa using valid) s)
    rintro result s' ⟨rfl, rfl⟩
    apply HeapWP.Spec.pure _ _ _ |>.mpr
    have hv : value = 0#u8 ∨ value = 1#u8 := by scalar_tac
    rcases hv with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
  · rename_i invalid
    apply HeapWP.Spec.pure _ _ _ |>.mpr
    have hz : value ≠ 0#u8 := by intro h; subst value; exact invalid (by decide)
    have ho : value ≠ 1#u8 := by intro h; subst value; exact invalid (by decide)
    simp [decodeBool, hz, ho]

theorem signed_round_trip.spec (value : U32) (s : Heap) :
    HeapWP.Spec (signed_round_trip value)
      (fun result s' => result = value ∧ s' = s) s := by
  unfold signed_round_trip
  apply HeapWP.Spec.bind (ext.unsigned_to_signed.spec value s)
  rintro signed s' ⟨rfl, rfl⟩
  exact ext.signed_to_unsigned.spec (asSigned value) _

theorem bool_byte_copy.spec (value : Bool) (s : Heap) :
    HeapWP.Spec (bool_byte_copy value)
      (fun (byte, value') s' => byte = boolByte value ∧ value' = value ∧ s' = s) s := by
  unfold bool_byte_copy
  apply HeapWP.Spec.bind (ext.bool_to_byte.spec value s)
  rintro byte s' ⟨rfl, rfl⟩
  exact HeapWP.Spec.pure _ _ _ |>.mpr ⟨rfl, rfl, rfl⟩

/-- info: 'raw_value_casts.ext.bool_to_byte.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ext.bool_to_byte.spec

/-- info: 'raw_value_casts.ext.byte_to_bool.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ext.byte_to_bool.spec

/-- info: 'raw_value_casts.ext.unsigned_to_signed.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ext.unsigned_to_signed.spec

/-- info: 'raw_value_casts.ext.signed_to_unsigned.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ext.signed_to_unsigned.spec

/-- info: 'raw_value_casts.bool_byte_round_trip.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bool_byte_round_trip.spec

/-- info: 'raw_value_casts.checked_byte_to_bool.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms checked_byte_to_bool.spec

/-- info: 'raw_value_casts.signed_round_trip.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms signed_round_trip.spec

/-- info: 'raw_value_casts.bool_byte_copy.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bool_byte_copy.spec

end raw_value_casts
