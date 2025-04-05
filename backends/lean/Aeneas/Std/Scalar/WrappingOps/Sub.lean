import Aeneas.Std.Scalar.Core

namespace Aeneas.Std

open Result Error

/-!
# Wrapping Sub
-/

def UScalar.wrapping_sub {ty} (x y : UScalar ty) : UScalar ty := ⟨ x.bv - y.bv ⟩

/- [core::num::{u8}::wrapping_sub] -/
@[progress_pure_def]
def core.num.U8.wrapping_sub : U8 → U8 → U8 := @UScalar.wrapping_sub UScalarTy.U8

/- [core::num::{u16}::wrapping_sub] -/
@[progress_pure_def]
def core.num.U16.wrapping_sub : U16 → U16 → U16  := @UScalar.wrapping_sub UScalarTy.U16

/- [core::num::{u32}::wrapping_sub] -/
@[progress_pure_def]
def core.num.U32.wrapping_sub : U32 → U32 → U32  := @UScalar.wrapping_sub UScalarTy.U32

/- [core::num::{u64}::wrapping_sub] -/
@[progress_pure_def]
def core.num.U64.wrapping_sub : U64 → U64 → U64  := @UScalar.wrapping_sub UScalarTy.U64

/- [core::num::{u128}::wrapping_sub] -/
@[progress_pure_def]
def core.num.U128.wrapping_sub : U128 → U128 → U128 := @UScalar.wrapping_sub UScalarTy.U128

/- [core::num::{usize}::wrapping_sub] -/
@[progress_pure_def]
def core.num.Usize.wrapping_sub : Usize → Usize → Usize  := @UScalar.wrapping_sub UScalarTy.Usize

def IScalar.wrapping_sub {ty} (x y : IScalar ty) : IScalar ty := ⟨ x.bv - y.bv ⟩

/- [core::num::{i8}::wrapping_sub] -/
@[progress_pure_def]
def core.num.I8.wrapping_sub : I8 → I8 → I8  := @IScalar.wrapping_sub IScalarTy.I8

/- [core::num::{i16}::wrapping_sub] -/
@[progress_pure_def]
def core.num.I16.wrapping_sub : I16 → I16 → I16  := @IScalar.wrapping_sub IScalarTy.I16

/- [core::num::{i32}::wrapping_sub] -/
@[progress_pure_def]
def core.num.I32.wrapping_sub : I32 → I32 → I32  := @IScalar.wrapping_sub IScalarTy.I32

/- [core::num::{i64}::wrapping_sub] -/
@[progress_pure_def]
def core.num.I64.wrapping_sub : I64 → I64 → I64 := @IScalar.wrapping_sub IScalarTy.I64

/- [core::num::{i128}::wrapping_sub] -/
@[progress_pure_def]
def core.num.I128.wrapping_sub : I128 → I128 → I128  := @IScalar.wrapping_sub IScalarTy.I128

/- [core::num::{isize}::wrapping_sub] -/
@[progress_pure_def]
def core.num.Isize.wrapping_sub : Isize → Isize → Isize  := @IScalar.wrapping_sub IScalarTy.Isize

@[simp, bvify_simps] theorem UScalar.wrapping_sub_bv_eq {ty} (x y : UScalar ty) :
  (wrapping_sub x y).bv = x.bv - y.bv := by
  simp [wrapping_sub]

@[simp, bvify_simps] theorem U8.wrapping_sub_bv_eq (x y : U8) :
  (core.num.U8.wrapping_sub x y).bv = x.bv - y.bv := by
  simp [core.num.U8.wrapping_sub, bv]

@[simp, bvify_simps] theorem U16.wrapping_sub_bv_eq (x y : U16) :
  (core.num.U16.wrapping_sub x y).bv = x.bv - y.bv := by
  simp [core.num.U16.wrapping_sub, bv]

@[simp, bvify_simps] theorem U32.wrapping_sub_bv_eq (x y : U32) :
  (core.num.U32.wrapping_sub x y).bv = x.bv - y.bv := by
  simp [core.num.U32.wrapping_sub, bv]

@[simp, bvify_simps] theorem U64.wrapping_sub_bv_eq (x y : U64) :
  (core.num.U64.wrapping_sub x y).bv = x.bv - y.bv := by
  simp [core.num.U64.wrapping_sub, bv]

@[simp, bvify_simps] theorem U128.wrapping_sub_bv_eq (x y : U128) :
  (core.num.U128.wrapping_sub x y).bv = x.bv - y.bv := by
  simp [core.num.U128.wrapping_sub, bv]

@[simp, bvify_simps] theorem Usize.wrapping_sub_bv_eq (x y : Usize) :
  (core.num.Usize.wrapping_sub x y).bv = x.bv - y.bv := by
  simp [core.num.Usize.wrapping_sub, bv]

@[simp, bvify_simps] theorem IScalar.wrapping_sub_bv_eq {ty} (x y : IScalar ty) :
  (wrapping_sub x y).bv = x.bv - y.bv := by
  simp [wrapping_sub]

@[simp, bvify_simps] theorem I8.wrapping_sub_bv_eq (x y : I8) :
  (core.num.I8.wrapping_sub x y).bv = x.bv - y.bv := by
  simp [core.num.I8.wrapping_sub, bv]

@[simp, bvify_simps] theorem I16.wrapping_sub_bv_eq (x y : I16) :
  (core.num.I16.wrapping_sub x y).bv = x.bv - y.bv := by
  simp [core.num.I16.wrapping_sub, bv]

@[simp, bvify_simps] theorem I32.wrapping_sub_bv_eq (x y : I32) :
  (core.num.I32.wrapping_sub x y).bv = x.bv - y.bv := by
  simp [core.num.I32.wrapping_sub, bv]

@[simp, bvify_simps] theorem I64.wrapping_sub_bv_eq (x y : I64) :
  (core.num.I64.wrapping_sub x y).bv = x.bv - y.bv := by
  simp [core.num.I64.wrapping_sub, bv]

@[simp, bvify_simps] theorem I128.wrapping_sub_bv_eq (x y : I128) :
  (core.num.I128.wrapping_sub x y).bv = x.bv - y.bv := by
  simp [core.num.I128.wrapping_sub, bv]

@[simp, bvify_simps] theorem Isize.wrapping_sub_bv_eq (x y : Isize) :
  (core.num.Isize.wrapping_sub x y).bv = x.bv - y.bv := by
  simp [core.num.Isize.wrapping_sub, bv]

@[simp] theorem UScalar.wrapping_sub_val_eq {ty} (x y : UScalar ty) :
  (wrapping_sub x y).val = (x.val + (UScalar.size ty - y.val)) % UScalar.size ty := by
  simp only [wrapping_sub, val, size]
  have : 0 < 2^ty.numBits := by simp
  have : 2 ^ ty.numBits - 1 + 1 = 2^ty.numBits := by omega
  simp [this]
  ring_nf

@[simp] theorem U8.wrapping_sub_val_eq (x y : U8) :
  (core.num.U8.wrapping_sub x y).val = (x.val + (UScalar.size .U8 - y.val)) % UScalar.size .U8 :=
  UScalar.wrapping_sub_val_eq x y

@[simp] theorem U16.wrapping_sub_val_eq (x y : U16) :
  (core.num.U16.wrapping_sub x y).val = (x.val + (UScalar.size .U16 - y.val)) % UScalar.size .U16 :=
  UScalar.wrapping_sub_val_eq x y

@[simp] theorem U32.wrapping_sub_val_eq (x y : U32) :
  (core.num.U32.wrapping_sub x y).val = (x.val + (UScalar.size .U32 - y.val)) % UScalar.size .U32 :=
  UScalar.wrapping_sub_val_eq x y

@[simp] theorem U64.wrapping_sub_val_eq (x y : U64) :
  (core.num.U64.wrapping_sub x y).val = (x.val + (UScalar.size .U64 - y.val)) % UScalar.size .U64 :=
  UScalar.wrapping_sub_val_eq x y

@[simp] theorem U128.wrapping_sub_val_eq (x y : U128) :
  (core.num.U128.wrapping_sub x y).val = (x.val + (UScalar.size .U128 - y.val)) % UScalar.size .U128 :=
  UScalar.wrapping_sub_val_eq x y

@[simp] theorem Usize.wrapping_sub_val_eq (x y : Usize) :
  (core.num.Usize.wrapping_sub x y).val = (x.val + (UScalar.size .Usize - y.val)) % UScalar.size .Usize :=
  UScalar.wrapping_sub_val_eq x y

@[simp] theorem IScalar.wrapping_sub_val_eq {ty} (x y : IScalar ty) :
  (wrapping_sub x y).val = Int.bmod (x.val - y.val) (2^ty.numBits) := by
  simp only [wrapping_sub, val]
  simp

@[simp] theorem I8.wrapping_sub_val_eq (x y : I8) :
  (core.num.I8.wrapping_sub x y).val = Int.bmod (x.val - y.val) (2^8) :=
  IScalar.wrapping_sub_val_eq x y

@[simp] theorem I16.wrapping_sub_val_eq (x y : I16) :
  (core.num.I16.wrapping_sub x y).val = Int.bmod (x.val - y.val) (2^16) :=
  IScalar.wrapping_sub_val_eq x y

@[simp] theorem I32.wrapping_sub_val_eq (x y : I32) :
  (core.num.I32.wrapping_sub x y).val = Int.bmod (x.val - y.val) (2^32) :=
  IScalar.wrapping_sub_val_eq x y

@[simp] theorem I64.wrapping_sub_val_eq (x y : I64) :
  (core.num.I64.wrapping_sub x y).val = Int.bmod (x.val - y.val) (2^64) :=
  IScalar.wrapping_sub_val_eq x y

@[simp] theorem I128.wrapping_sub_val_eq (x y : I128) :
  (core.num.I128.wrapping_sub x y).val = Int.bmod (x.val - y.val) (2^128) :=
  IScalar.wrapping_sub_val_eq x y

@[simp] theorem Isize.wrapping_sub_val_eq (x y : Isize) :
  (core.num.Isize.wrapping_sub x y).val = Int.bmod (x.val - y.val) (2^System.Platform.numBits) :=
  IScalar.wrapping_sub_val_eq x y

end Aeneas.Std
