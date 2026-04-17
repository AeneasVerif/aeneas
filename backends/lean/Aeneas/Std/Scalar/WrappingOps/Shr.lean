import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Elab

namespace Aeneas.Std

open Result Error ScalarElab

/-!
# Wrapping Shr

Wrapping (modular) shift right. Computes `x >> (s % BITS)`, wrapping the shift amount.
For unsigned types this is a logical shift; for signed types an arithmetic shift.
-/

def UScalar.wrapping_shr {ty} (x : UScalar ty) (s : Nat) : UScalar ty :=
  ⟨ x.bv.ushiftRight (s % ty.numBits) ⟩

def IScalar.wrapping_shr {ty} (x : IScalar ty) (s : Nat) : IScalar ty :=
  ⟨ x.bv.sshiftRight (s % ty.numBits) ⟩

uscalar @[step_pure_def]
def «%S».wrapping_shr (x : «%S») (s : Nat) : «%S» := @UScalar.wrapping_shr UScalarTy.«%S» x s

iscalar @[step_pure_def]
def «%S».wrapping_shr (x : «%S») (s : Nat) : «%S» := @IScalar.wrapping_shr IScalarTy.«%S» x s

/- [core::num::{_}::wrapping_shr] -/
uscalar @[step_pure_def]
def core.num.«%S».wrapping_shr : «%S» → Nat → «%S» := @UScalar.wrapping_shr UScalarTy.«%S»

/- [core::num::{_}::wrapping_shr] -/
iscalar @[step_pure_def]
def core.num.«%S».wrapping_shr : «%S» → Nat → «%S» := @IScalar.wrapping_shr IScalarTy.«%S»

@[simp, bvify] theorem UScalar.wrapping_shr_bv_eq {ty} (x : UScalar ty) (s : Nat) :
  (wrapping_shr x s).bv = x.bv.ushiftRight (s % ty.numBits) := by
  simp only [wrapping_shr]

uscalar @[simp, bvify, grind =, agrind =] theorem «%S».wrapping_shr_bv_eq (x : «%S») (s : Nat) :
  («%S».wrapping_shr x s).bv = x.bv.ushiftRight (s % %BitWidth) := by
  simp [«%S».wrapping_shr]

uscalar @[simp, bvify, grind =, agrind =] theorem core.num.«%S».wrapping_shr_bv_eq (x : «%S») (s : Nat) :
  (core.num.«%S».wrapping_shr x s).bv = x.bv.ushiftRight (s % %BitWidth) := by
  simp [core.num.«%S».wrapping_shr]

@[simp, bvify] theorem IScalar.wrapping_shr_bv_eq {ty} (x : IScalar ty) (s : Nat) :
  (wrapping_shr x s).bv = x.bv.sshiftRight (s % ty.numBits) := by
  simp only [wrapping_shr]

iscalar @[simp, bvify, grind =, agrind =] theorem «%S».wrapping_shr_bv_eq (x : «%S») (s : Nat) :
  («%S».wrapping_shr x s).bv = x.bv.sshiftRight (s % %BitWidth) := by
  simp [«%S».wrapping_shr]

iscalar @[simp, bvify, grind =, agrind =] theorem core.num.«%S».wrapping_shr_bv_eq (x : «%S») (s : Nat) :
  (core.num.«%S».wrapping_shr x s).bv = x.bv.sshiftRight (s % %BitWidth) := by
  simp [core.num.«%S».wrapping_shr]

end Aeneas.Std
