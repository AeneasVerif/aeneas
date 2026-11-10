module
public import Aeneas.Std.Scalar.Core
public import Aeneas.Std.Core.Convert
public import Aeneas.Data.BitVec
public import Aeneas.Tactic.Step.Init
public import Aeneas.Std.Scalar.Casts
public import Aeneas.Tactic.Solver.ScalarTac
public meta import Aeneas.Extract.Extract
@[expose] public section

/-! Integer conversions and byte orders. The target is little-endian (as the encoding of the
values in memory, see `ByteRepr`): `to_le` is the identity and `to_be` swaps the bytes. -/

namespace Aeneas.Std

@[rust_fun "core::convert::num::{core::convert::From<i32, u8>}::from" -canFail]
def core.convert.num.FromI32U8.from (x : U8) : I32 := ⟨ x.bv.zeroExtend _ ⟩

@[rust_fun "core::convert::num::{core::convert::From<i64, u8>}::from" -canFail]
def core.convert.num.FromI64U8.from (x : U8) : I64 := ⟨ x.bv.zeroExtend _ ⟩

@[rust_fun "core::num::{i8}::unsigned_abs" -canFail]
def core.num.I8.unsigned_abs (x : I8) : U8 := ⟨ BitVec.ofNat _ x.val.natAbs ⟩

@[rust_fun "core::num::{i16}::unsigned_abs" -canFail]
def core.num.I16.unsigned_abs (x : I16) : U16 := ⟨ BitVec.ofNat _ x.val.natAbs ⟩

@[rust_fun "core::num::{i32}::unsigned_abs" -canFail]
def core.num.I32.unsigned_abs (x : I32) : U32 := ⟨ BitVec.ofNat _ x.val.natAbs ⟩

@[rust_fun "core::num::{i64}::unsigned_abs" -canFail]
def core.num.I64.unsigned_abs (x : I64) : U64 := ⟨ BitVec.ofNat _ x.val.natAbs ⟩

@[rust_fun "core::num::{i128}::unsigned_abs" -canFail]
def core.num.I128.unsigned_abs (x : I128) : U128 := ⟨ BitVec.ofNat _ x.val.natAbs ⟩

@[rust_fun "core::num::{u16}::to_le" -canFail]
def core.num.U16.to_le (x : U16) : U16 := x

@[rust_fun "core::num::{u32}::to_le" -canFail]
def core.num.U32.to_le (x : U32) : U32 := x

@[rust_fun "core::num::{u32}::to_be" -canFail]
def core.num.U32.to_be (x : U32) : U32 := ⟨ BitVec.setWidth _ (BitVec.fromLEBytes x.bv.toBEBytes) ⟩

@[rust_fun "core::num::{u64}::to_le" -canFail]
def core.num.U64.to_le (x : U64) : U64 := x

@[rust_fun "core::num::{u64}::to_be" -canFail]
def core.num.U64.to_be (x : U64) : U64 := ⟨ BitVec.setWidth _ (BitVec.fromLEBytes x.bv.toBEBytes) ⟩

/-! `step` gives the value of `to_le` (the identity), and of the widening conversions. -/

@[simp, step_pure core.num.U16.to_le x]
theorem core.num.U16.to_le_eq (x : U16) : core.num.U16.to_le x = x := rfl
@[simp, step_pure core.num.U32.to_le x]
theorem core.num.U32.to_le_eq (x : U32) : core.num.U32.to_le x = x := rfl
@[simp, step_pure core.num.U64.to_le x]
theorem core.num.U64.to_le_eq (x : U64) : core.num.U64.to_le x = x := rfl

@[simp, scalar_tac_simps, step_pure core.convert.num.FromI32U8.from x]
theorem core.convert.num.FromI32U8.from_val_eq (x : U8) :
    (core.convert.num.FromI32U8.from x).val = x.val := by
  have h : core.convert.num.FromI32U8.from x = UScalar.hcast .I32 x := rfl
  have hx := x.hmax
  rw [h, UScalar.hcast_val_eq]
  simp only [IScalarTy.numBits]
  rw [Int.bmod_eq_of_le] <;> simp at hx ⊢ <;> omega

@[simp, scalar_tac_simps, step_pure core.convert.num.FromI64U8.from x]
theorem core.convert.num.FromI64U8.from_val_eq (x : U8) :
    (core.convert.num.FromI64U8.from x).val = x.val := by
  have h : core.convert.num.FromI64U8.from x = UScalar.hcast .I64 x := rfl
  have hx := x.hmax
  rw [h, UScalar.hcast_val_eq]
  simp only [IScalarTy.numBits]
  rw [Int.bmod_eq_of_le] <;> simp at hx ⊢ <;> omega

end Aeneas.Std
