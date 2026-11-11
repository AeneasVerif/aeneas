module
public import Aeneas.Std.Scalar.Core
public import Aeneas.Std.Scalar.Elab
public section

namespace Aeneas.Std

open Result Error ScalarElab

/-!
# Saturating Operations
-/

/-!
Saturating add: unsigned
-/
def UScalar.saturating_add {ty : UScalarTy} (x y : UScalar ty) : UScalar ty :=
  ⟨ BitVec.ofNat _ (Min.min (UScalar.max ty) (x.val + y.val)) ⟩

/- [core::num::{u8}::saturating_add] -/
uscalar def core.num.«%S».saturating_add := @UScalar.saturating_add UScalarTy.«%S»

/-!
Saturating add: signed
-/
def IScalar.saturating_add {ty : IScalarTy} (x y : IScalar ty) : IScalar ty :=
  ⟨ BitVec.ofInt _ (Max.max (IScalar.min ty) (Min.min (IScalar.max ty) (x.val + y.val))) ⟩

/- [core::num::{i8}::saturating_add] -/
iscalar def core.num.«%S».saturating_add := @IScalar.saturating_add IScalarTy.«%S»

/-!
Saturating sub: unsigned
-/
def UScalar.saturating_sub {ty : UScalarTy} (x y : UScalar ty) : UScalar ty :=
  ⟨ BitVec.ofNat _ (Max.max 0 (x.val - y.val)) ⟩

/- [core::num::{u8}::saturating_sub] -/
uscalar def core.num.«%S».saturating_sub := @UScalar.saturating_sub UScalarTy.«%S»

/-!
Saturating sub: signed
-/
def IScalar.saturating_sub {ty : IScalarTy} (x y : IScalar ty) : IScalar ty :=
  ⟨ BitVec.ofInt _ (Max.max (IScalar.min ty) (Min.min (IScalar.max ty) (x.val - y.val))) ⟩

/- [core::num::{i8}::saturating_sub] -/
iscalar def core.num.«%S».saturating_sub := @IScalar.saturating_sub IScalarTy.«%S»

/-!
## Value Specifications
-/

@[simp] theorem UScalar.saturating_add_val_eq {ty} (x y : UScalar ty) :
  (saturating_add x y).val = Min.min (x.val + y.val) (UScalar.max ty) := by
  have h : Min.min (UScalar.max ty) (x.val + y.val) < 2 ^ ty.numBits := by
    have := min_le_left (UScalar.max ty) (x.val + y.val)
    have : 0 < 2 ^ ty.numBits := by simp
    simp only [UScalar.max] at *
    omega
  change (BitVec.ofNat ty.numBits (Min.min (UScalar.max ty) (x.val + y.val))).toNat = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, min_comm]

@[simp] theorem IScalar.saturating_add_val_eq {ty} (x y : IScalar ty) :
  (saturating_add x y).val =
    Max.max (IScalar.min ty) (Min.min (IScalar.max ty) (x.val + y.val)) := by
  change (BitVec.ofInt ty.numBits _).toInt = _
  apply BitVec.toInt_ofInt_eq_self (by have := ty.numBits_nonzero; omega)
  · have := le_max_left (IScalar.min ty) (Min.min (IScalar.max ty) (x.val + y.val))
    simpa only [IScalar.min] using this
  · have := min_le_left (IScalar.max ty) (x.val + y.val)
    have : (0 : Int) < 2 ^ (ty.numBits - 1) := by simp
    simp only [IScalar.min, IScalar.max] at *
    omega

@[simp] theorem UScalar.saturating_sub_val_eq {ty} (x y : UScalar ty) :
  (saturating_sub x y).val = x.val - y.val := by
  change (BitVec.ofNat ty.numBits (Max.max 0 (x.val - y.val))).toNat = _
  simp only [Nat.zero_max, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) x.hBounds)

@[simp] theorem IScalar.saturating_sub_val_eq {ty} (x y : IScalar ty) :
  (saturating_sub x y).val =
    Max.max (IScalar.min ty) (Min.min (IScalar.max ty) (x.val - y.val)) := by
  change (BitVec.ofInt ty.numBits _).toInt = _
  apply BitVec.toInt_ofInt_eq_self (by have := ty.numBits_nonzero; omega)
  · have := le_max_left (IScalar.min ty) (Min.min (IScalar.max ty) (x.val - y.val))
    simpa only [IScalar.min] using this
  · have := min_le_left (IScalar.max ty) (x.val - y.val)
    have : (0 : Int) < 2 ^ (ty.numBits - 1) := by simp
    simp only [IScalar.min, IScalar.max] at *
    omega

uscalar @[simp, step_pure saturating_add x y]
theorem core.num.«%S».saturating_add_val_eq (x y : «%S») :
  (saturating_add x y).val = Min.min (x.val + y.val) (UScalar.max .«%S») :=
  UScalar.saturating_add_val_eq x y

iscalar @[simp, step_pure saturating_add x y]
theorem core.num.«%S».saturating_add_val_eq (x y : «%S») :
  (saturating_add x y).val =
    Max.max (IScalar.min .«%S») (Min.min (IScalar.max .«%S») (x.val + y.val)) :=
  IScalar.saturating_add_val_eq x y

uscalar @[simp, step_pure saturating_sub x y]
theorem core.num.«%S».saturating_sub_val_eq (x y : «%S») :
  (saturating_sub x y).val = x.val - y.val :=
  UScalar.saturating_sub_val_eq x y

iscalar @[simp, step_pure saturating_sub x y]
theorem core.num.«%S».saturating_sub_val_eq (x y : «%S») :
  (saturating_sub x y).val =
    Max.max (IScalar.min .«%S») (Min.min (IScalar.max .«%S») (x.val - y.val)) :=
  IScalar.saturating_sub_val_eq x y

end Aeneas.Std
