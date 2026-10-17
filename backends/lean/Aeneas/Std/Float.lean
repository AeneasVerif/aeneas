module
public import Aeneas.Std.Core
public import Aeneas.Std.Scalar.Core
public meta import Aeneas.Extract.Extract
@[expose] public section

/-! Rust's `f32` and `f64` are Lean's IEEE-754 `Float32` and `Float`. -/

namespace Aeneas.Std

open Result

@[rust_type "f32"]
abbrev F32 := Float32

@[rust_type "f64"]
abbrev F64 := Float

@[rust_fun "core::clone::impls::{core::clone::Clone<f32>}::clone"]
def core.clone.impls.CloneF32.clone (x : F32) : Result F32 := ok x

@[rust_fun "core::clone::impls::{core::clone::Clone<f64>}::clone"]
def core.clone.impls.CloneF64.clone (x : F64) : Result F64 := ok x

@[reducible, rust_trait_impl "core::marker::Copy<f32>"]
def core.marker.CopyF32 : core.marker.Copy F32 := BuiltinCopy F32

@[reducible, rust_trait_impl "core::marker::Copy<f64>"]
def core.marker.CopyF64 : core.marker.Copy F64 := BuiltinCopy F64

@[rust_fun "core::f32::{f32}::to_bits"]
def core.f32.F32.to_bits (x : F32) : Result U32 := ok (UScalar.mk x.toBits.toBitVec)

@[rust_fun "core::f64::{f64}::to_bits"]
def core.f64.F64.to_bits (x : F64) : Result U64 := ok (UScalar.mk x.toBits.toBitVec)

end Aeneas.Std
