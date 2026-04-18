import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Elab

namespace Aeneas.Std

open Result Error ScalarElab

/-!
# Wrapping Sub
-/

def UScalar.wrapping_sub {ty} (x y : UScalar ty) : UScalar ty := ⟨ x.toBitVec - y.toBitVec ⟩

def IScalar.wrapping_sub {ty} (x y : IScalar ty) : IScalar ty := ⟨ x.toBitVec - y.toBitVec ⟩

uscalar @[step_pure_def]
def «%S».wrapping_sub : «%S» → «%S» → «%S» := @UScalar.wrapping_sub UScalarTy.«%S»

iscalar @[step_pure_def]
def «%S».wrapping_sub : «%S» → «%S» → «%S»  := @IScalar.wrapping_sub IScalarTy.«%S»

/- [core::num::{_}::wrapping_sub] -/
uscalar @[step_pure_def]
def core.num.«%S».wrapping_sub : «%S» → «%S» → «%S» := @UScalar.wrapping_sub UScalarTy.«%S»

/- [core::num::{_}::wrapping_sub] -/
iscalar @[step_pure_def]
def core.num.«%S».wrapping_sub : «%S» → «%S» → «%S»  := @IScalar.wrapping_sub IScalarTy.«%S»

@[simp, bvify] theorem UScalar.wrapping_sub_toBitVec_eq {ty} (x y : UScalar ty) :
  (wrapping_sub x y).toBitVec = x.toBitVec - y.toBitVec := by
  simp only [wrapping_sub]

uscalar @[simp, bvify, grind =, agrind =] theorem «%S».wrapping_sub_bv_eq (x y : «%S») :
  («%S».wrapping_sub x y).toBitVec = x.toBitVec - y.toBitVec := by
  simp [«%S».wrapping_sub]

uscalar @[simp, bvify, grind =, agrind =] theorem core.num.«%S».wrapping_sub_bv_eq (x y : «%S») :
  (core.num.«%S».wrapping_sub x y).toBitVec = x.toBitVec - y.toBitVec := by
  simp [core.num.«%S».wrapping_sub]

@[simp, bvify] theorem IScalar.wrapping_sub_toBitVec_eq {ty} (x y : IScalar ty) :
  (wrapping_sub x y).toBitVec = x.toBitVec - y.toBitVec := by
  simp only [wrapping_sub]

iscalar @[simp, bvify, grind =, agrind =] theorem «%S».wrapping_sub_bv_eq (x y : «%S») :
  («%S».wrapping_sub x y).toBitVec = x.toBitVec - y.toBitVec := by
  simp [«%S».wrapping_sub]

iscalar @[simp, bvify, grind =, agrind =] theorem core.num.«%S».wrapping_sub_bv_eq (x y : «%S») :
  (core.num.«%S».wrapping_sub x y).toBitVec = x.toBitVec - y.toBitVec := by
  simp [core.num.«%S».wrapping_sub]

@[simp] theorem UScalar.wrapping_sub_toNat_eq {ty} (x y : UScalar ty) :
  (wrapping_sub x y).toNat = (x.toNat + (UScalar.size ty - y.toNat)) % UScalar.size ty := by
  simp only [wrapping_sub, toNat, size]
  have : 0 < 2^ty.numBits := by simp
  have : 2 ^ ty.numBits - 1 + 1 = 2^ty.numBits := by omega
  simp only [BitVec.toNat_sub, toBitVec_toNat]
  ring_nf

uscalar @[simp, grind =, agrind =] theorem «%S».wrapping_sub_val_eq (x y : «%S») :
  («%S».wrapping_sub x y).toNat = (x.toNat + (UScalar.size .«%S» - y.toNat)) % UScalar.size .«%S» :=
  UScalar.wrapping_sub_toNat_eq x y

uscalar @[simp, grind =, agrind =] theorem core.num.«%S».wrapping_sub_val_eq (x y : «%S») :
  (core.num.«%S».wrapping_sub x y).toNat = (x.toNat + (UScalar.size .«%S» - y.toNat)) % UScalar.size .«%S» :=
  UScalar.wrapping_sub_toNat_eq x y

@[simp] theorem IScalar.wrapping_sub_toInt_eq {ty} (x y : IScalar ty) :
  (wrapping_sub x y).toInt = Int.bmod (x.toInt - y.toInt) (2^ty.numBits) := by
  simp only [wrapping_sub, toInt]
  simp only [BitVec.toInt_sub, toBitVec_toInt_eq]

iscalar @[simp, grind =, agrind =] theorem «%S».wrapping_sub_val_eq (x y : «%S») :
  («%S».wrapping_sub x y).toInt = Int.bmod (x.toInt - y.toInt) (2^ %BitWidth) :=
  IScalar.wrapping_sub_toInt_eq x y

iscalar @[simp, grind =, agrind =] theorem core.num.«%S».wrapping_sub_val_eq (x y : «%S») :
  (core.num.«%S».wrapping_sub x y).toInt = Int.bmod (x.toInt - y.toInt) (2^ %BitWidth) :=
  IScalar.wrapping_sub_toInt_eq x y

end Aeneas.Std
