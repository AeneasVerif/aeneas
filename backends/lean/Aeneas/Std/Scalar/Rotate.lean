import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Elab

namespace Aeneas.Std

open ScalarElab

/-!
# Rotate
-/

/-!
## Rotate Left
-/
def UScalar.rotate_left {ty} (x : UScalar ty) (shift : U32) : UScalar ty :=
  ⟨ x.bv.rotateLeft shift.val ⟩

/- [core::num::{u8}::rotate_left] -/
uscalar @[progress_pure_def]
def core.num.«%S».rotate_left : «%S» → U32 → «%S» := @UScalar.rotate_left .«%S»

def IScalar.rotate_left {ty} (x : IScalar ty) (shift : U32) : IScalar ty :=
  ⟨ x.bv.rotateLeft shift.val ⟩

/- [core::num::{u8}::rotate_left] -/
iscalar @[progress_pure_def]
def core.num.«%S».rotate_left : «%S» → U32 → «%S» := @IScalar.rotate_left .«%S»

/-!
## Rotate Left
-/
def UScalar.rotate_right {ty} (x : UScalar ty) (shift : U32) : UScalar ty :=
  ⟨ x.bv.rotateLeft shift.val ⟩

/- [core::num::{u8}::rotate_right] -/
uscalar @[progress_pure_def]
def core.num.«%S».rotate_right : «%S» → U32 → «%S» := @UScalar.rotate_right .«%S»

def IScalar.rotate_right {ty} (x : IScalar ty) (shift : U32) : IScalar ty :=
  ⟨ x.bv.rotateLeft shift.val ⟩

/- [core::num::{u8}::rotate_right] -/
iscalar @[progress_pure_def]
def core.num.«%S».rotate_right : «%S» → U32 → «%S» := @IScalar.rotate_right .«%S»

end Aeneas.Std
