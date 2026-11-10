module
public import Aeneas.Std.Core
public import Aeneas.Std.Scalar.Core
public import Aeneas.Std.Scalar.Notations
public import Aeneas.Std.Core.Pointee
public meta import Aeneas.Extract.Extract
@[expose] public section

/-! Rust's `f32` and `f64` are Lean's IEEE-754 `Float32` and `Float`. -/

namespace Aeneas.Std

open Result

abbrev F32 := Float32

abbrev F64 := Float

@[rust_fun "core::clone::impls::{core::clone::Clone<f32>}::clone"]
def core.clone.impls.CloneF32.clone (x : SharedBorrow F32) : Result F32 := ok x.val

@[rust_fun "core::clone::impls::{core::clone::Clone<f64>}::clone"]
def core.clone.impls.CloneF64.clone (x : SharedBorrow F64) : Result F64 := ok x.val

@[reducible, rust_trait_impl "core::clone::Clone<f32>"]
def core.clone.CloneF32 : core.clone.Clone F32 := BuiltinClone F32

@[reducible, rust_trait_impl "core::clone::Clone<f64>"]
def core.clone.CloneF64 : core.clone.Clone F64 := BuiltinClone F64

@[reducible, rust_trait_impl "core::marker::Copy<f32>"]
def core.marker.CopyF32 : core.marker.Copy F32 := BuiltinCopy F32

@[reducible, rust_trait_impl "core::marker::Copy<f64>"]
def core.marker.CopyF64 : core.marker.Copy F64 := BuiltinCopy F64

@[rust_fun "core::f32::{f32}::to_bits" -canFail]
def core.f32.F32.to_bits (x : F32) : U32 := UScalar.mk x.toBits.toBitVec

@[rust_fun "core::f64::{f64}::to_bits" -canFail]
def core.f64.F64.to_bits (x : F64) : U64 := UScalar.mk x.toBits.toBitVec

@[rust_const "core::f32::{f32}::MANTISSA_DIGITS" -canFail]
def core.f32.F32.MANTISSA_DIGITS : U32 := 24#u32
@[rust_const "core::f32::{f32}::MIN_10_EXP" -canFail]
def core.f32.F32.MIN_10_EXP : I32 := (-37)#i32
@[rust_const "core::f32::{f32}::MAX_10_EXP" -canFail]
def core.f32.F32.MAX_10_EXP : I32 := 38#i32
@[rust_const "core::f64::{f64}::MANTISSA_DIGITS" -canFail]
def core.f64.F64.MANTISSA_DIGITS : U32 := 53#u32
@[rust_const "core::f64::{f64}::MIN_10_EXP" -canFail]
def core.f64.F64.MIN_10_EXP : I32 := (-307)#i32
@[rust_const "core::f64::{f64}::MAX_10_EXP" -canFail]
def core.f64.F64.MAX_10_EXP : I32 := 308#i32

/-! ### Representation in memory

A float is stored as its IEEE-754 bit pattern, in the representation of the unsigned integers of
the same width. The patterns which are not valid in Lean's model of the floats (the NaNs with a
non-canonical payload, which Lean identifies with the canonical NaN) can't be read as floats: Rust
preserves the payload, which the model can't represent, so the read fails (instead of returning the
canonical NaN, whose `to_bits` differs from the bytes). -/

instance (spec : Float.Model.Format) (b : BitVec spec.numBits) :
    Decidable (Float.Model.Format.Valid spec b) :=
  decidable_of_iff (Float.Model.UnpackedFloat.unpackExponent b = (-1#_) →
      Float.Model.UnpackedFloat.unpackMantissa b ≠ 0#_ →
      b = Float.Model.UnpackedFloat.packedNaN spec)
    ⟨fun h => ⟨h⟩, fun h => h.1⟩

/-- The representation of a type `B` which embeds into the represented type `A` (by `f`): the
values of `A` outside of the image of `f` can't be decoded (`g` gives `none`). -/
def Repr.partialIso {A B : Type} (r : Repr A) (f : B → A) (g : A → Option B)
    (gf : ∀ b, g (f b) = some b) : Repr B where
  size := r.size
  align := r.align
  decode bytes := r.decode bytes >>= g
  encode b bytes := r.encode (f b) bytes
  aligned := r.aligned
  encode_complete b := r.encode_complete (f b)
  encode_decode := by
    intro b bytes h
    simp [r.encode_decode _ _ h, gf]
  decode_mono := by
    intro bytes bytes' b decoded agree
    cases hd : r.decode bytes with
    | none => simp [hd] at decoded
    | some a => simp [r.decode_mono bytes bytes' a hd agree, ← decoded, hd]
  encode_valid := by
    intro b bytes i h
    exact r.encode_valid _ _ i h

/-- The float of a bit pattern, if it is valid (see above). -/
def F32.ofU32? (u : U32) : Option F32 :=
  if h : Float.Model.Format.binary32.Valid u.bv then some ⟨⟨UInt32.ofBitVec u.bv, h⟩⟩ else none

/-- The float of a bit pattern, if it is valid (see above). -/
def F64.ofU64? (u : U64) : Option F64 :=
  if h : Float.Model.Format.binary64.Valid u.bv then some ⟨⟨UInt64.ofBitVec u.bv, h⟩⟩ else none

theorem F32.ofU32?_to_bits (x : F32) : F32.ofU32? (core.f32.F32.to_bits x) = some x := by
  obtain ⟨⟨bits, valid⟩⟩ := x
  unfold F32.ofU32?
  split
  · rfl
  · rename_i h; exact absurd valid h

theorem F64.ofU64?_to_bits (x : F64) : F64.ofU64? (core.f64.F64.to_bits x) = some x := by
  obtain ⟨⟨bits, valid⟩⟩ := x
  unfold F64.ofU64?
  split
  · rfl
  · rename_i h; exact absurd valid h

/-- The invalid patterns (the NaNs with a non-canonical payload) are not floats. -/
theorem F32.ofU32?_eq_none (u : U32) (h : ¬ Float.Model.Format.binary32.Valid u.bv) :
    F32.ofU32? u = none := by
  simp [F32.ofU32?, h]

theorem F64.ofU64?_eq_none (u : U64) (h : ¬ Float.Model.Format.binary64.Valid u.bv) :
    F64.ofU64? u = none := by
  simp [F64.ofU64?, h]

instance : Pointee F32 :=
  ⟨Repr.partialIso (Pointee.repr (T := U32)) core.f32.F32.to_bits F32.ofU32? F32.ofU32?_to_bits⟩

instance : Pointee F64 :=
  ⟨Repr.partialIso (Pointee.repr (T := U64)) core.f64.F64.to_bits F64.ofU64? F64.ofU64?_to_bits⟩

/-- Reading a float whose bytes hold an invalid pattern (a NaN with a non-canonical payload) fails. -/
theorem F32.decode_invalid (bytes : Vector Byte (Pointee.repr (T := U32)).size) (u : U32)
    (hu : (Pointee.repr (T := U32)).decode bytes = some u)
    (h : ¬ Float.Model.Format.binary32.Valid u.bv) :
    (Pointee.repr (T := F32)).decode bytes = none := by
  show (Pointee.repr (T := U32)).decode bytes >>= F32.ofU32? = none
  simp [hu, F32.ofU32?_eq_none u h]

theorem F64.decode_invalid (bytes : Vector Byte (Pointee.repr (T := U64)).size) (u : U64)
    (hu : (Pointee.repr (T := U64)).decode bytes = some u)
    (h : ¬ Float.Model.Format.binary64.Valid u.bv) :
    (Pointee.repr (T := F64)).decode bytes = none := by
  show (Pointee.repr (T := U64)).decode bytes >>= F64.ofU64? = none
  simp [hu, F64.ofU64?_eq_none u h]

/-- For instance, the NaN `0x7fc00001` (whose payload isn't canonical) isn't a float of the model. -/
example : ¬ Float.Model.Format.binary32.Valid (0x7fc00001#u32).bv := by decide

instance : Pointee.Sized F32 := ⟨Pointee.Sized.pos (T := U32)⟩
instance : Pointee.Sized F64 := ⟨Pointee.Sized.pos (T := U64)⟩

end Aeneas.Std
