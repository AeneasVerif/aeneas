import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Elab

namespace Aeneas.Std

open Result Error ScalarElab

/-!
# Wrapping Shl

Wrapping (modular) shift left. Computes `x << (s % BITS)`, wrapping the shift amount.
-/

def UScalar.wrapping_shl {ty} (x : UScalar ty) (s : U32) : UScalar ty :=
  ⟨ x.bv.shiftLeft (s.val % ty.numBits) ⟩

def IScalar.wrapping_shl {ty} (x : IScalar ty) (s : U32) : IScalar ty :=
  ⟨ x.bv.shiftLeft (s.val % ty.numBits) ⟩

uscalar @[step_pure_def]
def «%S».wrapping_shl (x : «%S») (s : U32) : «%S» := @UScalar.wrapping_shl UScalarTy.«%S» x s

iscalar @[step_pure_def]
def «%S».wrapping_shl (x : «%S») (s : U32) : «%S» := @IScalar.wrapping_shl IScalarTy.«%S» x s

/- [core::num::{_}::wrapping_shl] -/
uscalar @[step_pure_def]
def core.num.«%S».wrapping_shl : «%S» → U32 → «%S» := @UScalar.wrapping_shl UScalarTy.«%S»

/- [core::num::{_}::wrapping_shl] -/
iscalar @[step_pure_def]
def core.num.«%S».wrapping_shl : «%S» → U32 → «%S» := @IScalar.wrapping_shl IScalarTy.«%S»

attribute [rust_fun "core::num::{u8}::wrapping_shl" -canFail] core.num.U8.wrapping_shl
attribute [rust_fun "core::num::{u16}::wrapping_shl" -canFail] core.num.U16.wrapping_shl
attribute [rust_fun "core::num::{u32}::wrapping_shl" -canFail] core.num.U32.wrapping_shl
attribute [rust_fun "core::num::{u64}::wrapping_shl" -canFail] core.num.U64.wrapping_shl
attribute [rust_fun "core::num::{u128}::wrapping_shl" -canFail] core.num.U128.wrapping_shl
attribute [rust_fun "core::num::{usize}::wrapping_shl" -canFail] core.num.Usize.wrapping_shl
attribute [rust_fun "core::num::{i8}::wrapping_shl" -canFail] core.num.I8.wrapping_shl
attribute [rust_fun "core::num::{i16}::wrapping_shl" -canFail] core.num.I16.wrapping_shl
attribute [rust_fun "core::num::{i32}::wrapping_shl" -canFail] core.num.I32.wrapping_shl
attribute [rust_fun "core::num::{i64}::wrapping_shl" -canFail] core.num.I64.wrapping_shl
attribute [rust_fun "core::num::{i128}::wrapping_shl" -canFail] core.num.I128.wrapping_shl
attribute [rust_fun "core::num::{isize}::wrapping_shl" -canFail] core.num.Isize.wrapping_shl

@[simp, bvify, grind =, agrind =] theorem UScalar.wrapping_shl_bv_eq {ty} (x : UScalar ty) (s : U32) :
  (wrapping_shl x s).bv = x.bv.shiftLeft (s.val % ty.numBits) := by
  simp only [wrapping_shl]

uscalar @[simp, bvify, grind =, agrind =] theorem «%S».wrapping_shl_bv_eq (x : «%S») (s : U32) :
  («%S».wrapping_shl x s).bv = x.bv.shiftLeft (s.val % %BitWidth) := by
  simp [«%S».wrapping_shl]

uscalar @[simp, bvify, grind =, agrind =] theorem core.num.«%S».wrapping_shl_bv_eq (x : «%S») (s : U32) :
  (core.num.«%S».wrapping_shl x s).bv = x.bv.shiftLeft (s.val % %BitWidth) := by
  simp [core.num.«%S».wrapping_shl]

@[simp, bvify] theorem IScalar.wrapping_shl_bv_eq {ty} (x : IScalar ty) (s : U32) :
  (wrapping_shl x s).bv = x.bv.shiftLeft (s.val % ty.numBits) := by
  simp only [wrapping_shl]

iscalar @[simp, bvify, grind =, agrind =] theorem «%S».wrapping_shl_bv_eq (x : «%S») (s : U32) :
  («%S».wrapping_shl x s).bv = x.bv.shiftLeft (s.val % %BitWidth) := by
  simp [«%S».wrapping_shl]

iscalar @[simp, bvify, grind =, agrind =] theorem core.num.«%S».wrapping_shl_bv_eq (x : «%S») (s : U32) :
  (core.num.«%S».wrapping_shl x s).bv = x.bv.shiftLeft (s.val % %BitWidth) := by
  simp [core.num.«%S».wrapping_shl]

end Aeneas.Std
