import Aeneas.Std.Scalar.Ops.Add
import Aeneas.Std.Scalar.Elab

namespace Aeneas.Std

open Result Error Arith ScalarElab

/-!
# Checked Addition: Definitions
-/

/- [core::num::{T}::checked_add] -/
def core.num.checked_add_UScalar {ty} (x y : UScalar ty) : Option (UScalar ty) :=
  Option.ofResult (x + y)

uscalar def «%S».checked_add (x y : «%S») : Option «%S» := core.num.checked_add_UScalar x y

/- [core::num::{T}::checked_add] -/
def core.num.checked_add_IScalar {ty} (x y : IScalar ty) : Option (IScalar ty) :=
  Option.ofResult (x + y)

iscalar def «%S».checked_add (x y : «%S») : Option «%S» := core.num.checked_add_IScalar x y

/-!
# Checked Add: Theorems
-/

/-!
Unsigned checked add
-/
theorem core.num.checked_add_UScalar_bv_spec {ty} (x y : UScalar ty) :
  match core.num.checked_add_UScalar x y with
  | some z => x.val + y.val ≤ UScalar.max ty ∧ z.val = x.val + y.val ∧ z.bv = x.bv + y.bv
  | none => UScalar.max ty < x.val + y.val := by
  have h := UScalar.add_equiv x y
  have hAdd : x + y = UScalar.add x y := by rfl
  rw [hAdd] at h
  cases hEq : UScalar.add x y <;> simp_all [Option.ofResult, checked_add_UScalar, UScalar.max] <;>
  (have : 0 < 2^ty.numBits := by simp) <;>
  omega

uscalar @[progress_pure «%S».checked_add x y]
theorem «%S».checked_add_bv_spec (x y : «%S») :
  match «%S».checked_add x y with
  | some z => x.val + y.val ≤ «%S».max ∧ z.val = x.val + y.val ∧ z.bv = x.bv + y.bv
  | none => «%S».max < x.val + y.val := by
  have := core.num.checked_add_UScalar_bv_spec x y
  simp_all [«%S».checked_add, UScalar.max, «%S».bv]
  cases h: core.num.checked_add_UScalar x y <;> simp_all [«%S».max, «%S».numBits]

/-!
Signed checked add
-/
theorem core.num.checked_add_IScalar_bv_spec {ty} (x y : IScalar ty) :
  match core.num.checked_add_IScalar x y with
  | some z => IScalar.min ty ≤ x.val + y.val ∧ x.val + y.val ≤ IScalar.max ty ∧ z.val = x.val + y.val ∧ z.bv = x.bv + y.bv
  | none => ¬ (IScalar.min ty ≤ x.val + y.val ∧ x.val + y.val ≤ IScalar.max ty) := by
  have h := IScalar.add_equiv x y
  have hAdd : x + y = IScalar.add x y := by rfl
  rw [hAdd] at h
  cases hEq : IScalar.add x y <;> simp_all [Option.ofResult, checked_add_IScalar, IScalar.min, IScalar.max] <;>
  omega

iscalar @[progress_pure «%S».checked_add x y]
theorem «%S».checked_add_bv_spec (x y : «%S») :
  match core.num.checked_add_IScalar x y with
  | some z => «%S».min ≤ x.val + y.val ∧ x.val + y.val ≤ «%S».max ∧ z.val = x.val + y.val ∧ z.bv = x.bv + y.bv
  | none => ¬ («%S».min ≤ x.val + y.val ∧ x.val + y.val ≤ «%S».max) := by
  have := core.num.checked_add_IScalar_bv_spec x y
  simp_all only [IScalar.min, IScalar.max, «%S».bv, «%S».min, «%S».max, «%S».numBits]
  cases h: core.num.checked_add_IScalar x y <;> simp_all only [] <;> simp

end Aeneas.Std
