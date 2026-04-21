import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Elab

namespace Aeneas.Std

open Result Error ScalarElab

/-!
# Wrapping Mul
-/

def UScalar.wrapping_mul {ty} (x y : UScalar ty) : UScalar ty := ⟨ x.toBitVec * y.toBitVec ⟩

def IScalar.wrapping_mul {ty} (x y : IScalar ty) : IScalar ty := ⟨ x.toBitVec * y.toBitVec ⟩

uscalar @[step_pure_def]
def «%S».wrapping_mul (x y : «%S») : «%S» := @UScalar.wrapping_mul UScalarTy.«%S» x y

iscalar @[step_pure_def]
def «%S».wrapping_mul (x y : «%S») : «%S» := @IScalar.wrapping_mul IScalarTy.«%S» x y

/- [core::num::{_}::wrapping_mul] -/
uscalar @[step_pure_def]
def core.num.«%S».wrapping_mul : «%S» → «%S» → «%S» := @UScalar.wrapping_mul UScalarTy.«%S»

/- [core::num::{_}::wrapping_mul] -/
iscalar @[step_pure_def]
def core.num.«%S».wrapping_mul : «%S» → «%S» → «%S»  := @IScalar.wrapping_mul IScalarTy.«%S»

@[simp, bvify, grind =, agrind =] theorem UScalar.wrapping_mul_toBitVec_eq {ty} (x y : UScalar ty) :
  (wrapping_mul x y).toBitVec = x.toBitVec * y.toBitVec := by
  simp only [wrapping_mul]

uscalar @[simp, bvify, grind =, agrind =] theorem «%S».wrapping_mul_bv_eq (x y : «%S») :
  («%S».wrapping_mul x y).toBitVec = x.toBitVec * y.toBitVec := by
  simp [«%S».wrapping_mul]

uscalar @[simp, bvify, grind =, agrind =] theorem core.num.«%S».wrapping_mul_bv_eq (x y : «%S») :
  (core.num.«%S».wrapping_mul x y).toBitVec = x.toBitVec * y.toBitVec := by
  simp [core.num.«%S».wrapping_mul]

@[simp, bvify, grind =, agrind =] theorem IScalar.wrapping_mul_toBitVec_eq {ty} (x y : IScalar ty) :
  (wrapping_mul x y).toBitVec = x.toBitVec * y.toBitVec := by
  simp only [wrapping_mul]

iscalar @[simp, bvify, grind =, agrind =] theorem «%S».wrapping_mul_bv_eq (x y : «%S») :
  («%S».wrapping_mul x y).toBitVec = x.toBitVec * y.toBitVec := by
  simp [«%S».wrapping_mul]

iscalar @[simp, bvify, grind =, agrind =] theorem core.num.«%S».wrapping_mul_bv_eq (x y : «%S») :
  (core.num.«%S».wrapping_mul x y).toBitVec = x.toBitVec * y.toBitVec := by
  simp [core.num.«%S».wrapping_mul]

@[simp] theorem UScalar.wrapping_mul_toNat_eq {ty} (x y : UScalar ty) :
  (wrapping_mul x y).toNat = (x.toNat * y.toNat) % (UScalar.size ty) := by
  simp only [wrapping_mul, toNat, size]
  have : 0 < 2^ty.numBits := by simp
  have : 2 ^ ty.numBits - 1 + 1 = 2^ty.numBits := by omega
  simp only [BitVec.toNat_mul, toBitVec_toNat]

uscalar @[simp, grind =, agrind =] theorem «%S».wrapping_mul_val_eq (x y : «%S») :
  («%S».wrapping_mul x y).toNat = (x.toNat * y.toNat) % (UScalar.size .«%S») :=
  UScalar.wrapping_mul_toNat_eq x y

uscalar @[simp, grind =, agrind =] theorem core.num.«%S».wrapping_mul_val_eq (x y : «%S») :
  (core.num.«%S».wrapping_mul x y).toNat = (x.toNat * y.toNat) % (UScalar.size .«%S») :=
  UScalar.wrapping_mul_toNat_eq x y

@[simp] theorem IScalar.wrapping_mul_toInt_eq {ty} (x y : IScalar ty) :
  (wrapping_mul x y).toInt = Int.bmod (x.toInt * y.toInt) (2^ty.numBits) := by
  simp only [wrapping_mul, toInt]
  simp only [BitVec.toInt_mul, toBitVec_toInt_eq]

iscalar @[simp, grind =, agrind =] theorem «%S».wrapping_mul_val_eq (x y : «%S») :
  («%S».wrapping_mul x y).toInt = Int.bmod (x.toInt * y.toInt) (2^ %BitWidth) :=
  IScalar.wrapping_mul_toInt_eq x y

iscalar @[simp, grind =, agrind =] theorem core.num.«%S».wrapping_mul_val_eq (x y : «%S») :
  (core.num.«%S».wrapping_mul x y).toInt = Int.bmod (x.toInt * y.toInt) (2^ %BitWidth) :=
  IScalar.wrapping_mul_toInt_eq x y

end Aeneas.Std
