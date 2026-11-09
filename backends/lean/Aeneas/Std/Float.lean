module
public import Aeneas.Std.Core
public import Aeneas.Std.Scalar.Core
public import Aeneas.Std.Scalar.Notations
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

end Aeneas.Std
