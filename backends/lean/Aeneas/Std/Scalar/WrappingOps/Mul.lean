import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Elab

namespace Aeneas.Std

open Result Error ScalarElab

/-!
# Wrapping Mul
-/

def UScalar.wrapping_mul {ty} (x y : UScalar ty) : UScalar ty := ⟨ x.bv * y.bv ⟩

/- [core::num::{u8}::wrapping_mul] -/
uscalar @[progress_pure_def]
def core.num.«%S».wrapping_mul : «%S» → «%S» → «%S» := @UScalar.wrapping_mul UScalarTy.«%S»

def IScalar.wrapping_mul {ty} (x y : IScalar ty) : IScalar ty := ⟨ x.bv * y.bv ⟩

/- [core::num::{i8}::wrapping_mul] -/
iscalar @[progress_pure_def]
def core.num.«%S».wrapping_mul : «%S» → «%S» → «%S»  := @IScalar.wrapping_mul IScalarTy.«%S»

@[simp, bvify_simps] theorem UScalar.wrapping_mul_bv_eq {ty} (x y : UScalar ty) :
  (wrapping_mul x y).bv = x.bv * y.bv := by
  simp only [wrapping_mul]

uscalar @[simp, bvify_simps] theorem «%S».wrapping_mul_bv_eq (x y : «%S») :
  (core.num.«%S».wrapping_mul x y).bv = x.bv * y.bv := by
  simp [core.num.«%S».wrapping_mul, bv]

@[simp, bvify_simps] theorem IScalar.wrapping_mul_bv_eq {ty} (x y : IScalar ty) :
  (wrapping_mul x y).bv = x.bv * y.bv := by
  simp only [wrapping_mul]

iscalar @[simp, bvify_simps] theorem «%S».wrapping_mul_bv_eq (x y : «%S») :
  (core.num.«%S».wrapping_mul x y).bv = x.bv * y.bv := by
  simp [core.num.«%S».wrapping_mul, bv]

@[simp] theorem UScalar.wrapping_mul_val_eq {ty} (x y : UScalar ty) :
  (wrapping_mul x y).val = (x.val * y.val) % (UScalar.size ty) := by
  simp only [wrapping_mul, val, size]
  have : 0 < 2^ty.numBits := by simp
  have : 2 ^ ty.numBits - 1 + 1 = 2^ty.numBits := by omega
  simp only [BitVec.toNat_mul, bv_toNat]

uscalar @[simp] theorem «%S».wrapping_mul_val_eq (x y : «%S») :
  (core.num.«%S».wrapping_mul x y).val = (x.val * y.val) % (UScalar.size .«%S») :=
  UScalar.wrapping_mul_val_eq x y

@[simp] theorem IScalar.wrapping_mul_val_eq {ty} (x y : IScalar ty) :
  (wrapping_mul x y).val = Int.bmod (x.val * y.val) (2^ty.numBits) := by
  simp only [wrapping_mul, val]
  simp only [BitVec.toInt_mul, bv_toInt_eq]

iscalar @[simp] theorem «%S».wrapping_mul_val_eq (x y : «%S») :
  (core.num.«%S».wrapping_mul x y).val = Int.bmod (x.val * y.val) (2^ %BitWidth) :=
  IScalar.wrapping_mul_val_eq x y

end Aeneas.Std
