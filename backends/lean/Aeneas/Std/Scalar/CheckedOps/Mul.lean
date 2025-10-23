import Aeneas.Std.Scalar.Ops.Mul
import Aeneas.Std.Scalar.Elab

namespace Aeneas.Std

open Result Error Arith ScalarElab

/-!
# Checked Multiplication: Definitions
-/

/- [core::num::{T}::checked_mul] -/
def core.num.checked_mul_UScalar {ty} (x y : UScalar ty) : Option (UScalar ty) :=
  Option.ofResult (UScalar.mul x y)

uscalar def «%S».checked_mul (x y : «%S») : Option «%S» := core.num.checked_mul_UScalar x y

/- [core::num::{T}::checked_mul] -/
def core.num.checked_mul_IScalar {ty} (x y : IScalar ty) : Option (IScalar ty) :=
  Option.ofResult (IScalar.mul x y)

iscalar def «%S».checked_mul (x y : «%S») : Option «%S» := core.num.checked_mul_IScalar x y

/-!
# Checked Mul: Theorems
-/

/-!
Unsigned checked mul
-/
theorem core.num.checked_mul_UScalar_bv_spec {ty} (x y : UScalar ty) :
  match core.num.checked_mul_UScalar x y with
  | some z => x.val * y.val ≤ UScalar.max ty ∧ z.val = x.val * y.val ∧ z.bv = x.bv * y.bv
  | none => UScalar.max ty < x.val * y.val := by
  have h := UScalar.mul_equiv x y
  simp [checked_mul_UScalar]
  cases hEq : UScalar.mul x y <;> simp_all [Option.ofResult]

uscalar @[progress_pure «%S».checked_mul x y]
theorem «%S».checked_mul_bv_spec (x y : «%S») :
  match «%S».checked_mul x y with
  | some z => x.val * y.val ≤ «%S».max ∧ z.val = x.val * y.val ∧ z.bv = x.bv * y.bv
  | none => «%S».max < x.val * y.val := by
  have := core.num.checked_mul_UScalar_bv_spec x y
  simp_all only [«%S».checked_mul, UScalar.max, «%S».bv, «%S».max, «%S».numBits]
  cases h: core.num.checked_mul_UScalar x y <;> simp_all only [and_self]

/-!
Signed checked mul
-/
theorem core.num.checked_mul_IScalar_bv_spec {ty} (x y : IScalar ty) :
  match core.num.checked_mul_IScalar x y with
  | some z => IScalar.min ty ≤ x.val * y.val ∧ x.val * y.val ≤ IScalar.max ty ∧ z.val = x.val * y.val ∧ z.bv = x.bv * y.bv
  | none => ¬ (IScalar.min ty ≤ x.val * y.val ∧ x.val * y.val ≤ IScalar.max ty) := by
  have h := IScalar.mul_equiv x y
  simp [checked_mul_IScalar]
  cases hEq : IScalar.mul x y <;> simp_all [Option.ofResult]

iscalar @[progress_pure «%S».checked_mul x y]
theorem «%S».checked_mul_bv_spec (x y : «%S») :
  match core.num.checked_mul_IScalar x y with
  | some z => «%S».min ≤ x.val * y.val ∧ x.val * y.val ≤ «%S».max ∧ z.val = x.val * y.val ∧ z.bv = x.bv * y.bv
  | none => ¬ («%S».min ≤ x.val * y.val ∧ x.val * y.val ≤ «%S».max) := by
  have := core.num.checked_mul_IScalar_bv_spec x y
  simp_all only [IScalar.min, IScalar.max, «%S».bv, «%S».min, «%S».max, «%S».numBits]
  cases h: core.num.checked_mul_IScalar x y <;> simp_all only [not_false_eq_true, and_self]

end Aeneas.Std
