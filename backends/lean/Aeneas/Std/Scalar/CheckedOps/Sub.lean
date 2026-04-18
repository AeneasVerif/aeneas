import Aeneas.Std.Scalar.Ops.Sub
import Aeneas.Std.Scalar.Elab

namespace Aeneas.Std

open Result Error Arith ScalarElab

/-!
# Checked Subtraction: Definitions
-/

/- [core::num::{T}::checked_sub] -/
def core.num.checked_sub_UScalar {ty} (x y : UScalar ty) : Option (UScalar ty) :=
  Option.ofResult (x - y)

uscalar def «%S».checked_sub (x y : «%S») : Option «%S» := core.num.checked_sub_UScalar x y

/- [core::num::{T}::checked_sub] -/
def core.num.checked_sub_IScalar {ty} (x y : IScalar ty) : Option (IScalar ty) :=
  Option.ofResult (x - y)

iscalar def «%S».checked_sub (x y : «%S») : Option «%S» := core.num.checked_sub_IScalar x y

/-!
# Checked Sub: Theorems
-/

/-!
Unsigned checked sub
-/
theorem core.num.checked_sub_UScalar_bv_spec {ty} (x y : UScalar ty) :
  match core.num.checked_sub_UScalar x y with
  | some z => y.toNat ≤ x.toNat ∧ z.toNat = x.toNat - y.toNat ∧ z.toBitVec = x.toBitVec - y.toBitVec
  | none => x.toNat < y.toNat := by
  have h := UScalar.sub_equiv x y
  have hsub : x - y = UScalar.sub x y := by rfl
  rw [hsub] at h
  cases hEq : UScalar.sub x y <;> simp_all [Option.ofResult, checked_sub_UScalar]

uscalar @[step_pure «%S».checked_sub x y]
theorem «%S».checked_sub_bv_spec (x y : «%S») :
  match «%S».checked_sub x y with
  | some z => y.toNat ≤ x.toNat ∧ z.toNat = x.toNat - y.toNat ∧ z.toBitVec = x.toBitVec - y.toBitVec
  | none => x.toNat < y.toNat := by
  have := core.num.checked_sub_UScalar_bv_spec x y
  simp_all [«%S».checked_sub, «%S».toBitVec]
  cases h: core.num.checked_sub_UScalar x y <;> simp_all

/-!
Signed checked sub
-/
theorem core.num.checked_sub_IScalar_bv_spec {ty} (x y : IScalar ty) :
  match core.num.checked_sub_IScalar x y with
  | some z => IScalar.min ty ≤ x.toInt - y.toInt ∧ x.toInt - y.toInt ≤ IScalar.max ty ∧ z.toInt = x.toInt - y.toInt ∧ z.toBitVec = x.toBitVec - y.toBitVec
  | none => ¬ (IScalar.min ty ≤ x.toInt - y.toInt ∧ x.toInt - y.toInt ≤ IScalar.max ty) := by
  have h := IScalar.sub_equiv x y
  have hsub : x - y = IScalar.sub x y := by rfl
  rw [hsub] at h
  cases hEq : IScalar.sub x y <;> simp_all [Option.ofResult, checked_sub_IScalar, IScalar.min, IScalar.max] <;>
  (have : 0 < 2^ty.numBits := by simp) <;>
  omega

iscalar @[step_pure «%S».checked_sub x y]
theorem «%S».checked_sub_bv_spec (x y : «%S») :
  match core.num.checked_sub_IScalar x y with
  | some z => «%S».min ≤ x.toInt - y.toInt ∧ x.toInt - y.toInt ≤ «%S».max ∧ z.toInt = x.toInt - y.toInt ∧ z.toBitVec = x.toBitVec - y.toBitVec
  | none => ¬ («%S».min ≤ x.toInt - y.toInt ∧ x.toInt - y.toInt ≤ «%S».max) := by
  have := core.num.checked_sub_IScalar_bv_spec x y
  simp_all only [IScalar.min, IScalar.max, «%S».toBitVec, «%S».min, «%S».max, «%S».numBits]
  cases h: core.num.checked_sub_IScalar x y <;> simp_all only <;> simp

end Aeneas.Std
