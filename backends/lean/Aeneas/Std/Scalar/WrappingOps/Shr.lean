module
public import Aeneas.Std.Scalar.Core
public import Aeneas.Std.Scalar.Elab
public section

namespace Aeneas.Std

open Result Error ScalarElab

/-!
# Wrapping Shr

Wrapping (modular) shift right. Computes `x >> (s % BITS)`, wrapping the shift amount.
For unsigned types this is a logical shift; for signed types an arithmetic shift.
-/

def UScalar.wrapping_shr {ty} (x : UScalar ty) (s : U32) : UScalar ty :=
  ⟨ x.bv.ushiftRight (s.val % ty.numBits) ⟩

def IScalar.wrapping_shr {ty} (x : IScalar ty) (s : U32) : IScalar ty :=
  ⟨ x.bv.sshiftRight (s.val % ty.numBits) ⟩

uscalar @[step_pure_def]
def «%S».wrapping_shr (x : «%S») (s : U32) : «%S» := @UScalar.wrapping_shr UScalarTy.«%S» x s

iscalar @[step_pure_def]
def «%S».wrapping_shr (x : «%S») (s : U32) : «%S» := @IScalar.wrapping_shr IScalarTy.«%S» x s

/- [core::num::{_}::wrapping_shr] -/
uscalar @[step_pure_def]
def core.num.«%S».wrapping_shr : «%S» → U32 → «%S» := @UScalar.wrapping_shr UScalarTy.«%S»

/- [core::num::{_}::wrapping_shr] -/
iscalar @[step_pure_def]
def core.num.«%S».wrapping_shr : «%S» → U32 → «%S» := @IScalar.wrapping_shr IScalarTy.«%S»

attribute [rust_fun "core::num::{u8}::wrapping_shr" -canFail] core.num.U8.wrapping_shr
attribute [rust_fun "core::num::{u16}::wrapping_shr" -canFail] core.num.U16.wrapping_shr
attribute [rust_fun "core::num::{u32}::wrapping_shr" -canFail] core.num.U32.wrapping_shr
attribute [rust_fun "core::num::{u64}::wrapping_shr" -canFail] core.num.U64.wrapping_shr
attribute [rust_fun "core::num::{u128}::wrapping_shr" -canFail] core.num.U128.wrapping_shr
attribute [rust_fun "core::num::{usize}::wrapping_shr" -canFail] core.num.Usize.wrapping_shr
attribute [rust_fun "core::num::{i8}::wrapping_shr" -canFail] core.num.I8.wrapping_shr
attribute [rust_fun "core::num::{i16}::wrapping_shr" -canFail] core.num.I16.wrapping_shr
attribute [rust_fun "core::num::{i32}::wrapping_shr" -canFail] core.num.I32.wrapping_shr
attribute [rust_fun "core::num::{i64}::wrapping_shr" -canFail] core.num.I64.wrapping_shr
attribute [rust_fun "core::num::{i128}::wrapping_shr" -canFail] core.num.I128.wrapping_shr
attribute [rust_fun "core::num::{isize}::wrapping_shr" -canFail] core.num.Isize.wrapping_shr

@[simp, bvify, grind =, agrind =] theorem UScalar.wrapping_shr_bv_eq {ty} (x : UScalar ty) (s : U32) :
  (wrapping_shr x s).bv = x.bv.ushiftRight (s.val % ty.numBits) := by
  simp only [wrapping_shr]

uscalar @[simp, bvify, grind =, agrind =] theorem «%S».wrapping_shr_bv_eq (x : «%S») (s : U32) :
  («%S».wrapping_shr x s).bv = x.bv.ushiftRight (s.val % %BitWidth) := by
  simp [«%S».wrapping_shr]

uscalar @[simp, bvify, grind =, agrind =] theorem core.num.«%S».wrapping_shr_bv_eq (x : «%S») (s : U32) :
  (core.num.«%S».wrapping_shr x s).bv = x.bv.ushiftRight (s.val % %BitWidth) := by
  simp [core.num.«%S».wrapping_shr]

@[simp, bvify, grind =, agrind =] theorem IScalar.wrapping_shr_bv_eq {ty} (x : IScalar ty) (s : U32) :
  (wrapping_shr x s).bv = x.bv.sshiftRight (s.val % ty.numBits) := by
  simp only [wrapping_shr]

iscalar @[simp, bvify, grind =, agrind =] theorem «%S».wrapping_shr_bv_eq (x : «%S») (s : U32) :
  («%S».wrapping_shr x s).bv = x.bv.sshiftRight (s.val % %BitWidth) := by
  simp [«%S».wrapping_shr]

iscalar @[simp, bvify, grind =, agrind =] theorem core.num.«%S».wrapping_shr_bv_eq (x : «%S») (s : U32) :
  (core.num.«%S».wrapping_shr x s).bv = x.bv.sshiftRight (s.val % %BitWidth) := by
  simp [core.num.«%S».wrapping_shr]

end Aeneas.Std
