import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Elab

namespace Aeneas.Std

open Result Error ScalarElab

/-!
# Wrapping Add
-/

def UScalar.wrapping_add {ty} (x y : UScalar ty) : UScalar ty := ⟨ x.toBitVec + y.toBitVec ⟩

def IScalar.wrapping_add {ty} (x y : IScalar ty) : IScalar ty := ⟨ x.toBitVec + y.toBitVec ⟩

uscalar @[step_pure_def]
def «%S».wrapping_add (x y : «%S») : «%S» := @UScalar.wrapping_add UScalarTy.«%S» x y

iscalar @[step_pure_def]
def «%S».wrapping_add (x y : «%S») : «%S» := @IScalar.wrapping_add IScalarTy.«%S» x y

/- [core::num::{_}::wrapping_add] -/
uscalar @[step_pure_def]
def core.num.«%S».wrapping_add : «%S» → «%S» → «%S» := @UScalar.wrapping_add UScalarTy.«%S»

/- [core::num::{_}::wrapping_add] -/
iscalar @[step_pure_def]
def core.num.«%S».wrapping_add : «%S» → «%S» → «%S»  := @IScalar.wrapping_add IScalarTy.«%S»

@[simp, bvify] theorem UScalar.wrapping_add_toBitVec_eq {ty} (x y : UScalar ty) :
  (wrapping_add x y).toBitVec = x.toBitVec + y.toBitVec := by
  simp only [wrapping_add]

uscalar @[simp, bvify, grind =, agrind =] theorem «%S».wrapping_add_bv_eq (x y : «%S») :
  («%S».wrapping_add x y).toBitVec = x.toBitVec + y.toBitVec := by
  simp [«%S».wrapping_add]

uscalar @[simp, bvify, grind =, agrind =] theorem core.num.«%S».wrapping_add_bv_eq (x y : «%S») :
  (core.num.«%S».wrapping_add x y).toBitVec = x.toBitVec + y.toBitVec := by
  simp [core.num.«%S».wrapping_add]

@[simp, bvify] theorem IScalar.wrapping_add_toBitVec_eq {ty} (x y : IScalar ty) :
  (wrapping_add x y).toBitVec = x.toBitVec + y.toBitVec := by
  simp only [wrapping_add]

iscalar @[simp, bvify, grind =, agrind =] theorem «%S».wrapping_add_bv_eq (x y : «%S») :
  («%S».wrapping_add x y).toBitVec = x.toBitVec + y.toBitVec := by
  simp [«%S».wrapping_add]

iscalar @[simp, bvify, grind =, agrind =] theorem core.num.«%S».wrapping_add_bv_eq (x y : «%S») :
  (core.num.«%S».wrapping_add x y).toBitVec = x.toBitVec + y.toBitVec := by
  simp [core.num.«%S».wrapping_add]

@[simp] theorem UScalar.wrapping_add_toNat_eq {ty} (x y : UScalar ty) :
  (wrapping_add x y).toNat = (x.toNat + y.toNat) % (UScalar.size ty) := by
  simp only [wrapping_add, toNat, size]
  have : 0 < 2^ty.numBits := by simp
  have : 2 ^ ty.numBits - 1 + 1 = 2^ty.numBits := by omega
  simp only [BitVec.toNat_add, toBitVec_toNat]

uscalar @[simp, grind =, agrind =] theorem «%S».wrapping_add_val_eq (x y : «%S») :
  («%S».wrapping_add x y).toNat = (x.toNat + y.toNat) % (UScalar.size .«%S») :=
  UScalar.wrapping_add_toNat_eq x y

uscalar @[simp, grind =, agrind =] theorem core.num.«%S».wrapping_add_val_eq (x y : «%S») :
  (core.num.«%S».wrapping_add x y).toNat = (x.toNat + y.toNat) % (UScalar.size .«%S») :=
  UScalar.wrapping_add_toNat_eq x y

@[simp] theorem IScalar.wrapping_add_toInt_eq {ty} (x y : IScalar ty) :
  (wrapping_add x y).toInt = Int.bmod (x.toInt + y.toInt) (2^ty.numBits) := by
  simp only [wrapping_add, toInt, ]
  simp only [BitVec.toInt_add, toBitVec_toInt_eq]

iscalar @[simp, grind =, agrind =] theorem «%S».wrapping_add_val_eq (x y : «%S») :
  («%S».wrapping_add x y).toInt = Int.bmod (x.toInt + y.toInt) (2^ %BitWidth) :=
  IScalar.wrapping_add_toInt_eq x y

iscalar @[simp, grind =, agrind =] theorem core.num.«%S».wrapping_add_val_eq (x y : «%S») :
  (core.num.«%S».wrapping_add x y).toInt = Int.bmod (x.toInt + y.toInt) (2^ %BitWidth) :=
  IScalar.wrapping_add_toInt_eq x y

end Aeneas.Std
