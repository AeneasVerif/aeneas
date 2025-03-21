import Aeneas.Std.Scalar.Core

namespace Aeneas.Std

open Result Error
/-!
# Wrapping Add
-/

def UScalar.wrapping_add {ty} (x y : UScalar ty) : UScalar ty := ⟨ x.bv + y.bv ⟩

/- [core::num::{u8}::wrapping_add] -/
@[progress_pure_def]
def core.num.U8.wrapping_add : U8 → U8 → U8 := @UScalar.wrapping_add UScalarTy.U8

/- [core::num::{u16}::wrapping_add] -/
@[progress_pure_def]
def core.num.U16.wrapping_add : U16 → U16 → U16  := @UScalar.wrapping_add UScalarTy.U16

/- [core::num::{u32}::wrapping_add] -/
@[progress_pure_def]
def core.num.U32.wrapping_add : U32 → U32 → U32  := @UScalar.wrapping_add UScalarTy.U32

/- [core::num::{u64}::wrapping_add] -/
@[progress_pure_def]
def core.num.U64.wrapping_add : U64 → U64 → U64  := @UScalar.wrapping_add UScalarTy.U64

/- [core::num::{u128}::wrapping_add] -/
@[progress_pure_def]
def core.num.U128.wrapping_add : U128 → U128 → U128 := @UScalar.wrapping_add UScalarTy.U128

/- [core::num::{usize}::wrapping_add] -/
@[progress_pure_def]
def core.num.Usize.wrapping_add : Usize → Usize → Usize  := @UScalar.wrapping_add UScalarTy.Usize

def IScalar.wrapping_add {ty} (x y : IScalar ty) : IScalar ty := ⟨ x.bv + y.bv ⟩

/- [core::num::{i8}::wrapping_add] -/
@[progress_pure_def]
def core.num.I8.wrapping_add : I8 → I8 → I8  := @IScalar.wrapping_add IScalarTy.I8

/- [core::num::{i16}::wrapping_add] -/
@[progress_pure_def]
def core.num.I16.wrapping_add : I16 → I16 → I16  := @IScalar.wrapping_add IScalarTy.I16

/- [core::num::{i32}::wrapping_add] -/
@[progress_pure_def]
def core.num.I32.wrapping_add : I32 → I32 → I32  := @IScalar.wrapping_add IScalarTy.I32

/- [core::num::{i64}::wrapping_add] -/
@[progress_pure_def]
def core.num.I64.wrapping_add : I64 → I64 → I64 := @IScalar.wrapping_add IScalarTy.I64

/- [core::num::{i128}::wrapping_add] -/
@[progress_pure_def]
def core.num.I128.wrapping_add : I128 → I128 → I128  := @IScalar.wrapping_add IScalarTy.I128

/- [core::num::{isize}::wrapping_add] -/
@[progress_pure_def]
def core.num.Isize.wrapping_add : Isize → Isize → Isize  := @IScalar.wrapping_add IScalarTy.Isize

@[simp, bvify_simps] theorem UScalar.wrapping_add_bv_eq {ty} (x y : UScalar ty) :
  (wrapping_add x y).bv = x.bv + y.bv := by
  simp [wrapping_add]

@[simp, bvify_simps] theorem U8.wrapping_add_bv_eq (x y : U8) :
  (core.num.U8.wrapping_add x y).bv = x.bv + y.bv := by
  simp [core.num.U8.wrapping_add, bv]

@[simp, bvify_simps] theorem U16.wrapping_add_bv_eq (x y : U16) :
  (core.num.U16.wrapping_add x y).bv = x.bv + y.bv := by
  simp [core.num.U16.wrapping_add, bv]

@[simp, bvify_simps] theorem U32.wrapping_add_bv_eq (x y : U32) :
  (core.num.U32.wrapping_add x y).bv = x.bv + y.bv := by
  simp [core.num.U32.wrapping_add, bv]

@[simp, bvify_simps] theorem U64.wrapping_add_bv_eq (x y : U64) :
  (core.num.U64.wrapping_add x y).bv = x.bv + y.bv := by
  simp [core.num.U64.wrapping_add, bv]

@[simp, bvify_simps] theorem U128.wrapping_add_bv_eq (x y : U128) :
  (core.num.U128.wrapping_add x y).bv = x.bv + y.bv := by
  simp [core.num.U128.wrapping_add, bv]

@[simp, bvify_simps] theorem Usize.wrapping_add_bv_eq (x y : Usize) :
  (core.num.Usize.wrapping_add x y).bv = x.bv + y.bv := by
  simp [core.num.Usize.wrapping_add, bv]

@[simp, bvify_simps] theorem IScalar.wrapping_add_bv_eq {ty} (x y : IScalar ty) :
  (wrapping_add x y).bv = x.bv + y.bv := by
  simp [wrapping_add]

@[simp, bvify_simps] theorem I8.wrapping_add_bv_eq (x y : I8) :
  (core.num.I8.wrapping_add x y).bv = x.bv + y.bv := by
  simp [core.num.I8.wrapping_add, bv]

@[simp, bvify_simps] theorem I16.wrapping_add_bv_eq (x y : I16) :
  (core.num.I16.wrapping_add x y).bv = x.bv + y.bv := by
  simp [core.num.I16.wrapping_add, bv]

@[simp, bvify_simps] theorem I32.wrapping_add_bv_eq (x y : I32) :
  (core.num.I32.wrapping_add x y).bv = x.bv + y.bv := by
  simp [core.num.I32.wrapping_add, bv]

@[simp, bvify_simps] theorem I64.wrapping_add_bv_eq (x y : I64) :
  (core.num.I64.wrapping_add x y).bv = x.bv + y.bv := by
  simp [core.num.I64.wrapping_add, bv]

@[simp, bvify_simps] theorem I128.wrapping_add_bv_eq (x y : I128) :
  (core.num.I128.wrapping_add x y).bv = x.bv + y.bv := by
  simp [core.num.I128.wrapping_add, bv]

@[simp, bvify_simps] theorem Isize.wrapping_add_bv_eq (x y : Isize) :
  (core.num.Isize.wrapping_add x y).bv = x.bv + y.bv := by
  simp [core.num.Isize.wrapping_add, bv]

@[simp] theorem UScalar.wrapping_add_val_eq {ty} (x y : UScalar ty) :
  (wrapping_add x y).val = (x.val + y.val) % (UScalar.size ty) := by
  simp only [wrapping_add, val, size]
  have : 0 < 2^ty.numBits := by simp
  have : 2 ^ ty.numBits - 1 + 1 = 2^ty.numBits := by omega
  simp [this]

@[simp] theorem U8.wrapping_add_val_eq (x y : U8) :
  (core.num.U8.wrapping_add x y).val = (x.val + y.val) % (UScalar.size .U8) :=
  UScalar.wrapping_add_val_eq x y

@[simp] theorem U16.wrapping_add_val_eq (x y : U16) :
  (core.num.U16.wrapping_add x y).val = (x.val + y.val) % (UScalar.size .U16) :=
  UScalar.wrapping_add_val_eq x y

@[simp] theorem U32.wrapping_add_val_eq (x y : U32) :
  (core.num.U32.wrapping_add x y).val = (x.val + y.val) % (UScalar.size .U32) :=
  UScalar.wrapping_add_val_eq x y

@[simp] theorem U64.wrapping_add_val_eq (x y : U64) :
  (core.num.U64.wrapping_add x y).val = (x.val + y.val) % (UScalar.size .U64) :=
  UScalar.wrapping_add_val_eq x y

@[simp] theorem U128.wrapping_add_val_eq (x y : U128) :
  (core.num.U128.wrapping_add x y).val = (x.val + y.val) % (UScalar.size .U128) :=
  UScalar.wrapping_add_val_eq x y

@[simp] theorem Usize.wrapping_add_val_eq (x y : Usize) :
  (core.num.Usize.wrapping_add x y).val = (x.val + y.val) % (UScalar.size .Usize) :=
  UScalar.wrapping_add_val_eq x y

@[simp] theorem IScalar.wrapping_add_val_eq {ty} (x y : IScalar ty) :
  (wrapping_add x y).val = Int.bmod (x.val + y.val) (2^ty.numBits) := by
  simp only [wrapping_add, val]
  simp

@[simp] theorem I8.wrapping_add_val_eq (x y : I8) :
  (core.num.I8.wrapping_add x y).val = Int.bmod (x.val + y.val) (2^8) :=
  IScalar.wrapping_add_val_eq x y

@[simp] theorem I16.wrapping_add_val_eq (x y : I16) :
  (core.num.I16.wrapping_add x y).val = Int.bmod (x.val + y.val) (2^16) :=
  IScalar.wrapping_add_val_eq x y

@[simp] theorem I32.wrapping_add_val_eq (x y : I32) :
  (core.num.I32.wrapping_add x y).val = Int.bmod (x.val + y.val) (2^32) :=
  IScalar.wrapping_add_val_eq x y

@[simp] theorem I64.wrapping_add_val_eq (x y : I64) :
  (core.num.I64.wrapping_add x y).val = Int.bmod (x.val + y.val) (2^64) :=
  IScalar.wrapping_add_val_eq x y

@[simp] theorem I128.wrapping_add_val_eq (x y : I128) :
  (core.num.I128.wrapping_add x y).val = Int.bmod (x.val + y.val) (2^128) :=
  IScalar.wrapping_add_val_eq x y

@[simp] theorem Isize.wrapping_add_val_eq (x y : Isize) :
  (core.num.Isize.wrapping_add x y).val = Int.bmod (x.val + y.val) (2^System.Platform.numBits) :=
  IScalar.wrapping_add_val_eq x y

end Aeneas.Std
