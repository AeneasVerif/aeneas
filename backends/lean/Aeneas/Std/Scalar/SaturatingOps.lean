import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Elab

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

end Aeneas.Std
