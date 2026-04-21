import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Elab
import Aeneas.Std.Core.Cmp

namespace Aeneas.Std

open Result ScalarElab

/-!
# PartialEq, Eq, PartialOrd, Ord
-/

/- [core::cmp::impls::{core::cmp::PartialEq<u8> for u8}::eq]:
   Name pattern: core::cmp::impls::{core::cmp::PartialEq<u8, u8>}::eq -/
scalar @[simp] abbrev core.cmp.impls.PartialEq'S.eq (x y : «%S») : Bool := x = y

scalar @[simp] abbrev core.cmp.impls.PartialEq'S.ne (x y : «%S») : Bool := ¬ x = y

/- Trait implementation: [core::cmp::impls::{core::cmp::PartialEq<u8> for u8}]
   Name pattern: core::cmp::PartialEq<u8, u8> -/
scalar @[reducible] def core.cmp.PartialEq'S : core.cmp.PartialEq «%S» «%S» := {
  eq := liftFun2 core.cmp.impls.PartialEq'S.eq
  ne := liftFun2 core.cmp.impls.PartialEq'S.ne }

/- Trait implementation: [core::cmp::impls::{core::cmp::Eq for u8}]
   Name pattern: core::cmp::Eq<u8> -/
scalar @[reducible] def core.cmp.Eq'S : core.cmp.Eq «%S» := {
  partialEqInst := core.cmp.PartialEq'S }

/- [core::cmp::impls::{core::cmp::PartialOrd<u8> for u8}::partial_cmp]:
   Name pattern: core::cmp::impls::{core::cmp::PartialOrd<u8, u8>}::partial_cmp -/
uscalar def core.cmp.impls.PartialOrd'S.partial_cmp (x y : «%S») : Option Ordering := some (compare x.toNat y.toNat)
iscalar def core.cmp.impls.PartialOrd'S.partial_cmp (x y : «%S») : Option Ordering := some (compare x.toInt y.toInt)

/- [core::cmp::impls::{core::cmp::Ord for u8}::cmp]:
   Name pattern: core::cmp::impls::{core::cmp::Ord<u8>}::cmp -/
uscalar @[simp] abbrev core.cmp.impls.Ord'S.cmp (x y : «%S») : Ordering := compare x.toNat y.toNat
iscalar @[simp] abbrev core.cmp.impls.Ord'S.cmp (x y : «%S») : Ordering := compare x.toInt y.toInt

/- [core::cmp::impls::{core::cmp::PartialOrd<u8> for u8}::lt]:
   Name pattern: core::cmp::impls::{core::cmp::PartialOrd<u8, u8>}::lt -/
uscalar def core.cmp.impls.PartialOrd'S.lt (x y : «%S») : Bool := x.toNat < y.toNat
iscalar def core.cmp.impls.PartialOrd'S.lt (x y : «%S») : Bool := x.toInt < y.toInt

/- [core::cmp::impls::{core::cmp::PartialOrd<u8> for u8}::le]:
   Name pattern: core::cmp::impls::{core::cmp::PartialOrd<u8, u8>}::le -/
uscalar def core.cmp.impls.PartialOrd'S.le (x y : «%S») : Bool := x.toNat ≤ y.toNat
iscalar def core.cmp.impls.PartialOrd'S.le (x y : «%S») : Bool := x.toInt ≤ y.toInt

/- [core::cmp::impls::{core::cmp::PartialOrd<u8> for u8}::gt]:
   Name pattern: core::cmp::impls::{core::cmp::PartialOrd<u8, u8>}::gt -/
uscalar def core.cmp.impls.PartialOrd'S.gt (x y : «%S») : Bool := x.toNat > y.toNat
iscalar def core.cmp.impls.PartialOrd'S.gt (x y : «%S») : Bool := x.toInt > y.toInt

/- [core::cmp::impls::{core::cmp::PartialOrd<u8> for u8}::ge]:
   Name pattern: core::cmp::impls::{core::cmp::PartialOrd<u8, u8>}::ge -/
uscalar def core.cmp.impls.PartialOrd'S.ge (x y : «%S») : Bool := x.toNat ≥ y.toNat
iscalar def core.cmp.impls.PartialOrd'S.ge (x y : «%S») : Bool := x.toInt ≥ y.toInt

/- Trait implementation: [core::cmp::impls::{core::cmp::PartialOrd<u8> for u8}]
   Name pattern: core::cmp::PartialOrd<u8, u8> -/
scalar @[reducible] def core.cmp.PartialOrd'S : core.cmp.PartialOrd «%S» «%S» := {
  partialEqInst := core.cmp.PartialEq'S
  partial_cmp := liftFun2 core.cmp.impls.PartialOrd'S.partial_cmp
  lt := liftFun2 core.cmp.impls.PartialOrd'S.lt
  le := liftFun2 core.cmp.impls.PartialOrd'S.le
  gt := liftFun2 core.cmp.impls.PartialOrd'S.gt
  ge := liftFun2 core.cmp.impls.PartialOrd'S.ge }

/- Name pattern: core::cmp::impls::{core::cmp::Ord<SCALAR>}::min -/
scalar @[step_pure_def] def core.cmp.impls.Ord'S.min (x y : «%S») : «%S» := if x < y then x else y

uscalar @[simp, scalar_tac_simps] theorem core.cmp.impls.Ord'S.min_toNat (x y : «%S») : (min x y).toNat = Min.min x.toNat y.toNat := by simp [min]; split <;> simp <;> omega
iscalar @[simp, scalar_tac_simps] theorem core.cmp.impls.Ord'S.min_toInt (x y : «%S») : (min x y).toInt = Min.min x.toInt y.toInt := by simp [min]; split <;> simp <;> omega

/- Name pattern: core::cmp::impls::{core::cmp::Ord<SCALAR>}::max -/
scalar @[step_pure_def] def core.cmp.impls.Ord'S.max (x y : «%S») : «%S» := if x < y then y else x

uscalar @[simp, scalar_tac_simps] theorem core.cmp.impls.Ord'S.max_toNat (x y : «%S») : (max x y).toNat = Max.max x.toNat y.toNat := by simp [max]; split <;> simp <;> omega
iscalar @[simp, scalar_tac_simps] theorem core.cmp.impls.Ord'S.max_toInt (x y : «%S») : (max x y).toInt = Max.max x.toInt y.toInt := by simp [max]; split <;> simp <;> omega

/- Name pattern: core::cmp::impls::{core::cmp::Ord<SCALAR>}::clamp -/
def UScalar.clamp {ty} (self min max : UScalar ty) : Result (UScalar ty) := do
  massert (min.toNat ≤ max.toNat)
  if self.toNat < min.toNat then ok min
  else if self.toNat > max.toNat then ok max
  else ok self

def IScalar.clamp {ty} (self min max : IScalar ty) : Result (IScalar ty) := do
  massert (min.toInt ≤ max.toInt)
  if self.toInt < min.toInt then ok min
  else if self.toInt > max.toInt then ok max
  else ok self

uscalar def core.cmp.impls.Ord'S.clamp (self min max : «%S») : Result «%S» := UScalar.clamp self min max
iscalar def core.cmp.impls.Ord'S.clamp (self min max : «%S») : Result «%S» := IScalar.clamp self min max

/- Trait implementation: [core::cmp::impls::{core::cmp::Ord for u8}]
   Name pattern: core::cmp::Ord<u8> -/
scalar @[reducible] def core.cmp.Ord'S : core.cmp.Ord «%S» := {
  eqInst := core.cmp.Eq'S
  partialOrdInst := core.cmp.PartialOrd'S
  cmp := liftFun2 core.cmp.impls.Ord'S.cmp
  max := liftFun2 core.cmp.impls.Ord'S.max
  min := liftFun2 core.cmp.impls.Ord'S.min
  clamp := core.cmp.impls.Ord'S.clamp }

end Aeneas.Std
