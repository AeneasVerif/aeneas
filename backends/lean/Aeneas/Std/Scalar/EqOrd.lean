import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Elab

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
scalar def core.cmp.impls.PartialOrd'S.partial_cmp (x y : «%S») : Option Ordering := some (compare x.val y.val)

/- [core::cmp::impls::{core::cmp::Ord for u8}::cmp]:
   Name pattern: core::cmp::impls::{core::cmp::Ord<u8>}::cmp -/
scalar @[simp] abbrev core.cmp.impls.Ord'S.cmp (x y : «%S») : Ordering := compare x.val y.val

/- [core::cmp::impls::{core::cmp::PartialOrd<u8> for u8}::lt]:
   Name pattern: core::cmp::impls::{core::cmp::PartialOrd<u8, u8>}::lt -/
scalar def core.cmp.impls.PartialOrd'S.lt (x y : «%S») : Bool := x.val < y.val

/- [core::cmp::impls::{core::cmp::PartialOrd<u8> for u8}::le]:
   Name pattern: core::cmp::impls::{core::cmp::PartialOrd<u8, u8>}::le -/
scalar def core.cmp.impls.PartialOrd'S.le (x y : «%S») : Bool := x.val ≤ y.val

/- [core::cmp::impls::{core::cmp::PartialOrd<u8> for u8}::gt]:
   Name pattern: core::cmp::impls::{core::cmp::PartialOrd<u8, u8>}::gt -/
scalar def core.cmp.impls.PartialOrd'S.gt (x y : «%S») : Bool := x.val > y.val

/- [core::cmp::impls::{core::cmp::PartialOrd<u8> for u8}::ge]:
   Name pattern: core::cmp::impls::{core::cmp::PartialOrd<u8, u8>}::ge -/
scalar def core.cmp.impls.PartialOrd'S.ge (x y : «%S») : Bool := x.val ≥ y.val

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
scalar @[progress_pure_def] def core.cmp.impls.Ord'S.min (x y : «%S») : «%S» := if x < y then x else y

scalar @[simp, scalar_tac_simps] theorem core.cmp.impls.Ord'S.min_val (x y : «%S») : (min x y).val = Min.min x.val y.val := by simp [min]; split <;> simp <;> omega

/- Name pattern: core::cmp::impls::{core::cmp::Ord<SCALAR>}::max -/
scalar @[progress_pure_def] def core.cmp.impls.Ord'S.max (x y : «%S») : «%S» := if x < y then y else x

scalar @[simp, scalar_tac_simps] theorem core.cmp.impls.Ord'S.max_val (x y : «%S») : (max x y).val = Max.max x.val y.val := by simp [max]; split <;> simp <;> omega

/- Name pattern: core::cmp::impls::{core::cmp::Ord<SCALAR>}::clamp -/
def UScalar.clamp {ty} (self min max : UScalar ty) : Result (UScalar ty) := do
  massert (min.val ≤ max.val)
  if self.val < min.val then ok min
  else if self.val > max.val then ok max
  else ok self

def IScalar.clamp {ty} (self min max : IScalar ty) : Result (IScalar ty) := do
  massert (min.val ≤ max.val)
  if self.val < min.val then ok min
  else if self.val > max.val then ok max
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
