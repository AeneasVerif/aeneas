import Aeneas.Std.Scalar.Core

namespace Aeneas.Std

open Result Error

/-!
# Saturating Operations
-/

/-!
Saturating add: unsigned
-/
def UScalar.saturating_add {ty : UScalarTy} (x y : UScalar ty) : UScalar ty :=
  ⟨ BitVec.ofNat _ (Min.min (UScalar.max ty) (x.val + y.val)) ⟩

/- [core::num::{u8}::saturating_add] -/
def core.num.U8.saturating_add := @UScalar.saturating_add UScalarTy.U8

/- [core::num::{u16}::saturating_add] -/
def core.num.U16.saturating_add := @UScalar.saturating_add UScalarTy.U16

/- [core::num::{u32}::saturating_add] -/
def core.num.U32.saturating_add := @UScalar.saturating_add UScalarTy.U32

/- [core::num::{u64}::saturating_add] -/
def core.num.U64.saturating_add := @UScalar.saturating_add UScalarTy.U64

/- [core::num::{u128}::saturating_add] -/
def core.num.U128.saturating_add := @UScalar.saturating_add UScalarTy.U128

/- [core::num::{usize}::saturating_add] -/
def core.num.Usize.saturating_add := @UScalar.saturating_add UScalarTy.Usize

/-!
Saturating add: signed
-/
def IScalar.saturating_add {ty : IScalarTy} (x y : IScalar ty) : IScalar ty :=
  ⟨ BitVec.ofInt _ (Max.max (IScalar.min ty) (Min.min (IScalar.max ty) (x.val + y.val))) ⟩

/- [core::num::{i8}::saturating_add] -/
def core.num.I8.saturating_add := @IScalar.saturating_add IScalarTy.I8

/- [core::num::{i16}::saturating_add] -/
def core.num.I16.saturating_add := @IScalar.saturating_add IScalarTy.I16

/- [core::num::{i32}::saturating_add] -/
def core.num.I32.saturating_add := @IScalar.saturating_add IScalarTy.I32

/- [core::num::{i64}::saturating_add] -/
def core.num.I64.saturating_add := @IScalar.saturating_add IScalarTy.I64

/- [core::num::{i128}::saturating_add] -/
def core.num.I128.saturating_add := @IScalar.saturating_add IScalarTy.I128

/- [core::num::{isize}::saturating_add] -/
def core.num.Isize.saturating_add := @IScalar.saturating_add IScalarTy.Isize

/-!
Saturating sub: unsigned
-/
def UScalar.saturating_sub {ty : UScalarTy} (x y : UScalar ty) : UScalar ty :=
  ⟨ BitVec.ofNat _ (Max.max 0 (x.val - y.val)) ⟩

/- [core::num::{u8}::saturating_sub] -/
def core.num.U8.saturating_sub := @UScalar.saturating_sub UScalarTy.U8

/- [core::num::{u16}::saturating_sub] -/
def core.num.U16.saturating_sub := @UScalar.saturating_sub UScalarTy.U16

/- [core::num::{u32}::saturating_sub] -/
def core.num.U32.saturating_sub := @UScalar.saturating_sub UScalarTy.U32

/- [core::num::{u64}::saturating_sub] -/
def core.num.U64.saturating_sub := @UScalar.saturating_sub UScalarTy.U64

/- [core::num::{u128}::saturating_sub] -/
def core.num.U128.saturating_sub := @UScalar.saturating_sub UScalarTy.U128

/- [core::num::{usize}::saturating_sub] -/
def core.num.Usize.saturating_sub := @UScalar.saturating_sub UScalarTy.Usize

/-!
Saturating sub: signed
-/
def IScalar.saturating_sub {ty : IScalarTy} (x y : IScalar ty) : IScalar ty :=
  ⟨ BitVec.ofInt _ (Max.max (IScalar.min ty) (Min.min (IScalar.max ty) (x.val - y.val))) ⟩

/- [core::num::{i8}::saturating_sub] -/
def core.num.I8.saturating_sub := @IScalar.saturating_sub IScalarTy.I8

/- [core::num::{i16}::saturating_sub] -/
def core.num.I16.saturating_sub := @IScalar.saturating_sub IScalarTy.I16

/- [core::num::{i32}::saturating_sub] -/
def core.num.I32.saturating_sub := @IScalar.saturating_sub IScalarTy.I32

/- [core::num::{i64}::saturating_sub] -/
def core.num.I64.saturating_sub := @IScalar.saturating_sub IScalarTy.I64

/- [core::num::{i128}::saturating_sub] -/
def core.num.I128.saturating_sub := @IScalar.saturating_sub IScalarTy.I128

/- [core::num::{isize}::saturating_sub] -/
def core.num.Isize.saturating_sub := @IScalar.saturating_sub IScalarTy.Isize

end Aeneas.Std
