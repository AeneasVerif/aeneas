module
public import Aeneas.Std.Scalar.Core
public import Aeneas.Std.Scalar.Elab
public section

namespace Aeneas.Std

open ScalarElab

/-!
# Rotate
-/

/-!
## Rotate Left
-/
@[expose] def UScalar.rotate_left {ty} (x : UScalar ty) (shift : U32) : UScalar ty :=
  ⟨ x.bv.rotateLeft shift.val ⟩

/- [core::num::{u8}::rotate_left] -/
uscalar @[expose, step_pure_def]
def core.num.«%S».rotate_left : «%S» → U32 → «%S» := @UScalar.rotate_left .«%S»

@[expose] def IScalar.rotate_left {ty} (x : IScalar ty) (shift : U32) : IScalar ty :=
  ⟨ x.bv.rotateLeft shift.val ⟩

/- [core::num::{u8}::rotate_left] -/
iscalar @[expose, step_pure_def]
def core.num.«%S».rotate_left : «%S» → U32 → «%S» := @IScalar.rotate_left .«%S»

/-!
## Rotate Right
-/
@[expose] def UScalar.rotate_right {ty} (x : UScalar ty) (shift : U32) : UScalar ty :=
  ⟨ x.bv.rotateRight shift.val ⟩

/- [core::num::{u8}::rotate_right] -/
uscalar @[expose, step_pure_def]
def core.num.«%S».rotate_right : «%S» → U32 → «%S» := @UScalar.rotate_right .«%S»

@[expose] def IScalar.rotate_right {ty} (x : IScalar ty) (shift : U32) : IScalar ty :=
  ⟨ x.bv.rotateRight shift.val ⟩

/- [core::num::{u8}::rotate_right] -/
iscalar @[expose, step_pure_def]
def core.num.«%S».rotate_right : «%S» → U32 → «%S» := @IScalar.rotate_right .«%S»

end Aeneas.Std
