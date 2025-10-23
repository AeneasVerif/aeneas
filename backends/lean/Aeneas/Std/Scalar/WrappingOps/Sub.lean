import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Elab

namespace Aeneas.Std

open Result Error ScalarElab

/-!
# Wrapping Sub
-/

def UScalar.wrapping_sub {ty} (x y : UScalar ty) : UScalar ty := ⟨ x.bv - y.bv ⟩

/- [core::num::{u8}::wrapping_sub] -/
uscalar @[progress_pure_def]
def core.num.«%S».wrapping_sub : «%S» → «%S» → «%S» := @UScalar.wrapping_sub UScalarTy.«%S»

def IScalar.wrapping_sub {ty} (x y : IScalar ty) : IScalar ty := ⟨ x.bv - y.bv ⟩

/- [core::num::{i8}::wrapping_sub] -/
iscalar @[progress_pure_def]
def core.num.«%S».wrapping_sub : «%S» → «%S» → «%S»  := @IScalar.wrapping_sub IScalarTy.«%S»

@[simp, bvify_simps] theorem UScalar.wrapping_sub_bv_eq {ty} (x y : UScalar ty) :
  (wrapping_sub x y).bv = x.bv - y.bv := by
  simp only [wrapping_sub]

uscalar @[simp, bvify_simps] theorem «%S».wrapping_sub_bv_eq (x y : «%S») :
  (core.num.«%S».wrapping_sub x y).bv = x.bv - y.bv := by
  simp [core.num.«%S».wrapping_sub, bv]

@[simp, bvify_simps] theorem IScalar.wrapping_sub_bv_eq {ty} (x y : IScalar ty) :
  (wrapping_sub x y).bv = x.bv - y.bv := by
  simp only [wrapping_sub]

iscalar @[simp, bvify_simps] theorem «%S».wrapping_sub_bv_eq (x y : «%S») :
  (core.num.«%S».wrapping_sub x y).bv = x.bv - y.bv := by
  simp [core.num.«%S».wrapping_sub, bv]

@[simp] theorem UScalar.wrapping_sub_val_eq {ty} (x y : UScalar ty) :
  (wrapping_sub x y).val = (x.val + (UScalar.size ty - y.val)) % UScalar.size ty := by
  simp only [wrapping_sub, val, size]
  have : 0 < 2^ty.numBits := by simp
  have : 2 ^ ty.numBits - 1 + 1 = 2^ty.numBits := by omega
  simp only [BitVec.toNat_sub, bv_toNat]
  ring_nf

uscalar @[simp] theorem «%S».wrapping_sub_val_eq (x y : «%S») :
  (core.num.«%S».wrapping_sub x y).val = (x.val + (UScalar.size .«%S» - y.val)) % UScalar.size .«%S» :=
  UScalar.wrapping_sub_val_eq x y

@[simp] theorem IScalar.wrapping_sub_val_eq {ty} (x y : IScalar ty) :
  (wrapping_sub x y).val = Int.bmod (x.val - y.val) (2^ty.numBits) := by
  simp only [wrapping_sub, val]
  simp only [BitVec.toInt_sub, bv_toInt_eq]

iscalar @[simp] theorem «%S».wrapping_sub_val_eq (x y : «%S») :
  (core.num.«%S».wrapping_sub x y).val = Int.bmod (x.val - y.val) (2^ %BitWidth) :=
  IScalar.wrapping_sub_val_eq x y

end Aeneas.Std
