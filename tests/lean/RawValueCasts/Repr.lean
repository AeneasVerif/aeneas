module

public import RawTransmute
import all Aeneas.Std.Heap.Effects
import all Aeneas.Std.Primitives

@[expose] public section

open Aeneas.Std

namespace raw_value_casts

/- A by-value model for these opaque wrappers, not a compiler rule for arbitrary
Rust transmute. Repr describes initialized bytes only; it does not account for
Rust padding, lifetimes, or the ownership obligations of pointer-bearing values. -/
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
  rw [compatible data decoded]
  exact HeapWP.Spec.pure _ _ _ |>.mpr ⟨rfl, rfl⟩

def boolByte (value : Bool) : U8 :=
  if value then 1#u8 else 0#u8

def decodeBool (byte : U8) : Option Bool :=
  if byte = 0#u8 then some false else if byte = 1#u8 then some true else none

def boolRepr : Aeneas.Std.Repr Bool where
  size := 1
  align := ⟨1, 0, rfl⟩
  decode data := decodeBool data[0]
  aligned := by decide
  complete value := by
    cases value
    · exact ⟨#v[0#u8], rfl⟩
    · exact ⟨#v[1#u8], rfl⟩

def asSigned (value : U32) : I32 := ⟨value.bv⟩

def asUnsigned (value : I32) : U32 := ⟨value.bv⟩

def signedRepr : Aeneas.Std.Repr I32 where
  size := raw_box.u32Repr.size
  align := raw_box.u32Repr.align
  decode data := (raw_box.u32Repr.decode data).map asSigned
  aligned := raw_box.u32Repr.aligned
  complete value := by
    obtain ⟨data, hd⟩ := raw_box.u32Repr.complete (asUnsigned value)
    refine ⟨data, ?_⟩
    rw [hd]
    rfl

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
    raw_transmute.byteRepr.decode #v[2#u8] = some 2#u8 ∧
      boolRepr.decode #v[2#u8] = none := by
  decide

/-- info: 'raw_value_casts.reinterpret.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reinterpret.spec

end raw_value_casts
