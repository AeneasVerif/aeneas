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
non-canonical payload, which Lean identifies) are read as the canonical NaN (`ofBits`). -/

instance (spec : Float.Model.Format) (b : BitVec spec.numBits) :
    Decidable (Float.Model.Format.Valid spec b) :=
  decidable_of_iff (Float.Model.UnpackedFloat.unpackExponent b = (-1#_) →
      Float.Model.UnpackedFloat.unpackMantissa b ≠ 0#_ →
      b = Float.Model.UnpackedFloat.packedNaN spec)
    ⟨fun h => ⟨h⟩, fun h => h.1⟩

/-- The float of a bit pattern, which is exact on the valid patterns. -/
def F32.ofU32 (u : U32) : F32 :=
  if h : Float.Model.Format.binary32.Valid u.bv then ⟨⟨UInt32.ofBitVec u.bv, h⟩⟩
  else Float32.ofBits (UInt32.ofBitVec u.bv)

/-- The float of a bit pattern, which is exact on the valid patterns. -/
def F64.ofU64 (u : U64) : F64 :=
  if h : Float.Model.Format.binary64.Valid u.bv then ⟨⟨UInt64.ofBitVec u.bv, h⟩⟩
  else Float.ofBits (UInt64.ofBitVec u.bv)

theorem F32.ofU32_to_bits (x : F32) : F32.ofU32 (core.f32.F32.to_bits x) = x := by
  obtain ⟨⟨bits, valid⟩⟩ := x
  unfold F32.ofU32
  split
  · rfl
  · rename_i h; exact absurd valid h

theorem F64.ofU64_to_bits (x : F64) : F64.ofU64 (core.f64.F64.to_bits x) = x := by
  obtain ⟨⟨bits, valid⟩⟩ := x
  unfold F64.ofU64
  split
  · rfl
  · rename_i h; exact absurd valid h

instance : Pointee F32 :=
  ⟨Repr.iso (Pointee.repr (T := U32)) core.f32.F32.to_bits F32.ofU32 F32.ofU32_to_bits⟩

instance : Pointee F64 :=
  ⟨Repr.iso (Pointee.repr (T := U64)) core.f64.F64.to_bits F64.ofU64 F64.ofU64_to_bits⟩

end Aeneas.Std
