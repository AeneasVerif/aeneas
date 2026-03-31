import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Elab

namespace Aeneas.Std

open ScalarElab WP

/-!
# Rotate
-/

/-!
## Rotate Left
-/
def UScalar.rotate_left {ty} (x : UScalar ty) (shift : U32) : UScalar ty :=
  ⟨ x.bv.rotateLeft shift.val ⟩

/- [core::num::{u8}::rotate_left] -/
uscalar @[step_pure_def]
def core.num.«%S».rotate_left : «%S» → U32 → «%S» := @UScalar.rotate_left .«%S»

def IScalar.rotate_left {ty} (x : IScalar ty) (shift : U32) : IScalar ty :=
  ⟨ x.bv.rotateLeft shift.val ⟩

/- [core::num::{u8}::rotate_left] -/
iscalar @[step_pure_def]
def core.num.«%S».rotate_left : «%S» → U32 → «%S» := @IScalar.rotate_left .«%S»

/-!
## Rotate Right
-/
def UScalar.rotate_right {ty} (x : UScalar ty) (shift : U32) : UScalar ty :=
  ⟨ x.bv.rotateRight shift.val ⟩

/- [core::num::{u8}::rotate_right] -/
uscalar @[step_pure_def]
def core.num.«%S».rotate_right : «%S» → U32 → «%S» := @UScalar.rotate_right .«%S»

def IScalar.rotate_right {ty} (x : IScalar ty) (shift : U32) : IScalar ty :=
  ⟨ x.bv.rotateRight shift.val ⟩

/- [core::num::{u8}::rotate_right] -/
iscalar @[step_pure_def]
def core.num.«%S».rotate_right : «%S» → U32 → «%S» := @IScalar.rotate_right .«%S»

/-!
## Rotate: Theorems
-/

@[step]
theorem UScalar.rotate_left_spec {ty} (x : UScalar ty) (shift : U32) :
  lift (UScalar.rotate_left x shift) ⦃ z => z.bv = x.bv.rotateLeft shift.val ⦄ := by
  simp [lift, rotate_left]

@[step]
theorem UScalar.rotate_right_spec {ty} (x : UScalar ty) (shift : U32) :
  lift (UScalar.rotate_right x shift) ⦃ z => z.bv = x.bv.rotateRight shift.val ⦄ := by
  simp [lift, rotate_right]

@[step]
theorem IScalar.rotate_left_spec {ty} (x : IScalar ty) (shift : U32) :
  lift (IScalar.rotate_left x shift) ⦃ z => z.bv = x.bv.rotateLeft shift.val ⦄ := by
  simp [lift, rotate_left]

@[step]
theorem IScalar.rotate_right_spec {ty} (x : IScalar ty) (shift : U32) :
  lift (IScalar.rotate_right x shift) ⦃ z => z.bv = x.bv.rotateRight shift.val ⦄ := by
  simp [lift, rotate_right]

@[simp, bvify, grind =, agrind =] theorem UScalar.bv_rotate_left {ty} (x : UScalar ty) (s : U32) : (UScalar.rotate_left x s).bv = x.bv.rotateLeft s.val := by rfl
@[simp, bvify, grind =, agrind =] theorem UScalar.bv_rotate_right {ty} (x : UScalar ty) (s : U32) : (UScalar.rotate_right x s).bv = x.bv.rotateRight s.val := by rfl
@[simp, bvify, grind =, agrind =] theorem IScalar.bv_rotate_left {ty} (x : IScalar ty) (s : U32) : (IScalar.rotate_left x s).bv = x.bv.rotateLeft s.val := by rfl
@[simp, bvify, grind =, agrind =] theorem IScalar.bv_rotate_right {ty} (x : IScalar ty) (s : U32) : (IScalar.rotate_right x s).bv = x.bv.rotateRight s.val := by rfl

end Aeneas.Std
