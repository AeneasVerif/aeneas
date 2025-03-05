import Aeneas.Std.Scalar.Core

namespace Aeneas.Std

/-!
# Rotate
-/

/-!
## Rotate Left
-/
def UScalar.rotate_left {ty} (x : UScalar ty) (shift : U32) : UScalar ty :=
  ⟨ x.bv.rotateLeft shift.val ⟩

/- [core::num::{u8}::rotate_left] -/
@[progress_pure_def]
def core.num.U8.rotate_left : U8 → U32 → U8 := @UScalar.rotate_left .U8

/- [core::num::{u16}::rotate_left] -/
@[progress_pure_def]
def core.num.U16.rotate_left : U16 → U32 → U16 := @UScalar.rotate_left .U16

/- [core::num::{u32}::rotate_left] -/
@[progress_pure_def]
def core.num.U32.rotate_left : U32 → U32 → U32 := @UScalar.rotate_left .U32

/- [core::num::{u64}::rotate_left] -/
@[progress_pure_def]
def core.num.U64.rotate_left : U64 → U32 → U64 := @UScalar.rotate_left .U64

/- [core::num::{u128}::rotate_left] -/
@[progress_pure_def]
def core.num.U128.rotate_left : U128 → U32 → U128 := @UScalar.rotate_left .U128

/- [core::num::{usize}::rotate_left] -/
@[progress_pure_def]
def core.num.Usize.rotate_left : Usize → U32 → Usize := @UScalar.rotate_left .Usize

def IScalar.rotate_left {ty} (x : IScalar ty) (shift : U32) : IScalar ty :=
  ⟨ x.bv.rotateLeft shift.val ⟩

/- [core::num::{u8}::rotate_left] -/
@[progress_pure_def]
def core.num.I8.rotate_left : I8 → U32 → I8 := @IScalar.rotate_left .I8

/- [core::num::{u16}::rotate_left] -/
@[progress_pure_def]
def core.num.I16.rotate_left : I16 → U32 → I16 := @IScalar.rotate_left .I16

/- [core::num::{u32}::rotate_left] -/
@[progress_pure_def]
def core.num.I32.rotate_left : I32 → U32 → I32 := @IScalar.rotate_left .I32

/- [core::num::{u64}::rotate_left] -/
@[progress_pure_def]
def core.num.I64.rotate_left : I64 → U32 → I64 := @IScalar.rotate_left .I64

/- [core::num::{u128}::rotate_left] -/
@[progress_pure_def]
def core.num.I128.rotate_left : I128 → U32 → I128 := @IScalar.rotate_left .I128

/- [core::num::{usize}::rotate_left] -/
@[progress_pure_def]
def core.num.Isize.rotate_left : Isize → U32 → Isize := @IScalar.rotate_left .Isize

/-!
## Rotate Left
-/
def UScalar.rotate_right {ty} (x : UScalar ty) (shift : U32) : UScalar ty :=
  ⟨ x.bv.rotateLeft shift.val ⟩

/- [core::num::{u8}::rotate_right] -/
@[progress_pure_def]
def core.num.U8.rotate_right : U8 → U32 → U8 := @UScalar.rotate_right .U8

/- [core::num::{u16}::rotate_right] -/
@[progress_pure_def]
def core.num.U16.rotate_right : U16 → U32 → U16 := @UScalar.rotate_right .U16

/- [core::num::{u32}::rotate_right] -/
@[progress_pure_def]
def core.num.U32.rotate_right : U32 → U32 → U32 := @UScalar.rotate_right .U32

/- [core::num::{u64}::rotate_right] -/
@[progress_pure_def]
def core.num.U64.rotate_right : U64 → U32 → U64 := @UScalar.rotate_right .U64

/- [core::num::{u128}::rotate_right] -/
@[progress_pure_def]
def core.num.U128.rotate_right : U128 → U32 → U128 := @UScalar.rotate_right .U128

/- [core::num::{usize}::rotate_right] -/
@[progress_pure_def]
def core.num.Usize.rotate_right : Usize → U32 → Usize := @UScalar.rotate_right .Usize

def IScalar.rotate_right {ty} (x : IScalar ty) (shift : U32) : IScalar ty :=
  ⟨ x.bv.rotateLeft shift.val ⟩

/- [core::num::{u8}::rotate_right] -/
@[progress_pure_def]
def core.num.I8.rotate_right : I8 → U32 → I8 := @IScalar.rotate_right .I8

/- [core::num::{u16}::rotate_right] -/
@[progress_pure_def]
def core.num.I16.rotate_right : I16 → U32 → I16 := @IScalar.rotate_right .I16

/- [core::num::{u32}::rotate_right] -/
@[progress_pure_def]
def core.num.I32.rotate_right : I32 → U32 → I32 := @IScalar.rotate_right .I32

/- [core::num::{u64}::rotate_right] -/
@[progress_pure_def]
def core.num.I64.rotate_right : I64 → U32 → I64 := @IScalar.rotate_right .I64

/- [core::num::{u128}::rotate_right] -/
@[progress_pure_def]
def core.num.I128.rotate_right : I128 → U32 → I128 := @IScalar.rotate_right .I128

/- [core::num::{usize}::rotate_right] -/
@[progress_pure_def]
def core.num.Isize.rotate_right : Isize → U32 → Isize := @IScalar.rotate_right .Isize

end Aeneas.Std
