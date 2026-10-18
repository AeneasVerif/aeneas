module
public import Aeneas.Std.Scalar.Core
public import Aeneas.Std.Core.Convert
public import Aeneas.Data.BitVec
public import Mathlib.Data.Nat.Log
public meta import Aeneas.Extract.Extract
@[expose] public section

/-! Integer conversions and byte orders. The target is little-endian (as the encoding of the
values in memory, see `ByteRepr`): `to_le` is the identity and `to_be` swaps the bytes. -/

namespace Aeneas.Std

@[expose, rust_fun "core::convert::num::{core::convert::From<i32, u8>}::from" -canFail]
def core.convert.num.FromI32U8.from (x : U8) : I32 := ⟨ x.bv.zeroExtend _ ⟩

@[expose, rust_fun "core::convert::num::{core::convert::From<i64, u8>}::from" -canFail]
def core.convert.num.FromI64U8.from (x : U8) : I64 := ⟨ x.bv.zeroExtend _ ⟩

@[expose, rust_fun "core::num::{i8}::unsigned_abs" -canFail]
def core.num.I8.unsigned_abs (x : I8) : U8 := ⟨ BitVec.ofNat _ x.val.natAbs ⟩

@[expose, rust_fun "core::num::{i16}::unsigned_abs" -canFail]
def core.num.I16.unsigned_abs (x : I16) : U16 := ⟨ BitVec.ofNat _ x.val.natAbs ⟩

@[expose, rust_fun "core::num::{i32}::unsigned_abs" -canFail]
def core.num.I32.unsigned_abs (x : I32) : U32 := ⟨ BitVec.ofNat _ x.val.natAbs ⟩

@[expose, rust_fun "core::num::{i64}::unsigned_abs" -canFail]
def core.num.I64.unsigned_abs (x : I64) : U64 := ⟨ BitVec.ofNat _ x.val.natAbs ⟩

@[expose, rust_fun "core::num::{i128}::unsigned_abs" -canFail]
def core.num.I128.unsigned_abs (x : I128) : U128 := ⟨ BitVec.ofNat _ x.val.natAbs ⟩

@[expose, rust_fun "core::num::{u16}::to_le" -canFail]
def core.num.U16.to_le (x : U16) : U16 := x

@[expose, rust_fun "core::num::{u64}::to_le" -canFail]
def core.num.U64.to_le (x : U64) : U64 := x

@[expose, rust_fun "core::num::{u64}::to_be" -canFail]
def core.num.U64.to_be (x : U64) : U64 := ⟨ BitVec.setWidth _ (BitVec.fromLEBytes x.bv.toBEBytes) ⟩

/-- `ilog10`: panics if the integer is not positive. -/
def UScalar.ilog10 {ty : UScalarTy} (x : UScalar ty) : Result U32 :=
  if h : 0 < x.val ∧ Nat.log 10 x.val < 2 ^ UScalarTy.U32.numBits then
    .ok (UScalar.ofNatCore _ h.2)
  else .fail .panic

def IScalar.ilog10 {ty : IScalarTy} (x : IScalar ty) : Result U32 :=
  if h : 0 < x.val ∧ Nat.log 10 x.val.toNat < 2 ^ UScalarTy.U32.numBits then
    .ok (UScalar.ofNatCore _ h.2)
  else .fail .panic

attribute [rust_fun "core::num::{u8}::ilog10"] UScalar.ilog10
attribute [rust_fun "core::num::{u16}::ilog10"] UScalar.ilog10
attribute [rust_fun "core::num::{u32}::ilog10"] UScalar.ilog10
attribute [rust_fun "core::num::{u64}::ilog10"] UScalar.ilog10
attribute [rust_fun "core::num::{u128}::ilog10"] UScalar.ilog10
attribute [rust_fun "core::num::{i8}::ilog10"] IScalar.ilog10
attribute [rust_fun "core::num::{i16}::ilog10"] IScalar.ilog10
attribute [rust_fun "core::num::{i32}::ilog10"] IScalar.ilog10
attribute [rust_fun "core::num::{i64}::ilog10"] IScalar.ilog10
attribute [rust_fun "core::num::{i128}::ilog10"] IScalar.ilog10

end Aeneas.Std
