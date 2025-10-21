import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Elab

namespace Aeneas.Std

open Result Error ScalarElab

/-!
# Wrapping Add
-/

def UScalar.wrapping_add {ty} (x y : UScalar ty) : UScalar ty := ⟨ x.bv + y.bv ⟩

/- [core::num::{u8}::wrapping_add] -/
uscalar @[progress_pure_def]
def core.num.«%S».wrapping_add : «%S» → «%S» → «%S» := @UScalar.wrapping_add UScalarTy.«%S»

def IScalar.wrapping_add {ty} (x y : IScalar ty) : IScalar ty := ⟨ x.bv + y.bv ⟩

/- [core::num::{i8}::wrapping_add] -/
iscalar @[progress_pure_def]
def core.num.«%S».wrapping_add : «%S» → «%S» → «%S»  := @IScalar.wrapping_add IScalarTy.«%S»

@[simp, bvify_simps] theorem UScalar.wrapping_add_bv_eq {ty} (x y : UScalar ty) :
  (wrapping_add x y).bv = x.bv + y.bv := by
  simp only [wrapping_add]

uscalar @[simp, bvify_simps] theorem «%S».wrapping_add_bv_eq (x y : «%S») :
  (core.num.«%S».wrapping_add x y).bv = x.bv + y.bv := by
  simp [core.num.«%S».wrapping_add, bv]

@[simp, bvify_simps] theorem IScalar.wrapping_add_bv_eq {ty} (x y : IScalar ty) :
  (wrapping_add x y).bv = x.bv + y.bv := by
  simp only [wrapping_add]

iscalar @[simp, bvify_simps] theorem «%S».wrapping_add_bv_eq (x y : «%S») :
  (core.num.«%S».wrapping_add x y).bv = x.bv + y.bv := by
  simp [core.num.«%S».wrapping_add, bv]

@[simp] theorem UScalar.wrapping_add_val_eq {ty} (x y : UScalar ty) :
  (wrapping_add x y).val = (x.val + y.val) % (UScalar.size ty) := by
  simp only [wrapping_add, val, size]
  have : 0 < 2^ty.numBits := by simp
  have : 2 ^ ty.numBits - 1 + 1 = 2^ty.numBits := by omega
  simp only [BitVec.toNat_add, bv_toNat]

uscalar @[simp] theorem «%S».wrapping_add_val_eq (x y : «%S») :
  (core.num.«%S».wrapping_add x y).val = (x.val + y.val) % (UScalar.size .«%S») :=
  UScalar.wrapping_add_val_eq x y

@[simp] theorem IScalar.wrapping_add_val_eq {ty} (x y : IScalar ty) :
  (wrapping_add x y).val = Int.bmod (x.val + y.val) (2^ty.numBits) := by
  simp only [wrapping_add, val, ]
  simp only [BitVec.toInt_add, bv_toInt_eq]

iscalar @[simp] theorem «%S».wrapping_add_val_eq (x y : «%S») :
  (core.num.«%S».wrapping_add x y).val = Int.bmod (x.val + y.val) (2^ %BitWidth) :=
  IScalar.wrapping_add_val_eq x y

end Aeneas.Std
