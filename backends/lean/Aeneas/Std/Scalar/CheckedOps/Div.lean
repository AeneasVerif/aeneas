import Aeneas.Std.Scalar.Ops.Div
import Aeneas.Std.Scalar.Elab

namespace Aeneas.Std

open Result Error Arith ScalarElab

/-!
# Checked Division: Definitions
-/

/- [core::num::{T}::checked_div] -/
def core.num.checked_div_UScalar {ty} (x y : UScalar ty) : Option (UScalar ty) :=
  Option.ofResult (UScalar.div x y)

uscalar def «%S».checked_div (x y : «%S») : Option «%S» := core.num.checked_div_UScalar x y

/- [core::num::{T}::checked_div] -/
def core.num.checked_div_IScalar {ty} (x y : IScalar ty) : Option (IScalar ty) :=
  Option.ofResult (IScalar.div x y)

iscalar def «%S».checked_div (x y : «%S») : Option «%S» := core.num.checked_div_IScalar x y

/-!
# Checked Division: Theorems
-/

/-!
Unsigned checked div
-/
theorem core.num.checked_div_UScalar_bv_spec {ty} (x y : UScalar ty) :
  match core.num.checked_div_UScalar x y with
  | some z => y.val ≠ 0 ∧ z.val = x.val / y.val ∧ z.bv = x.bv / y.bv
  | none => y.val = 0 := by
  simp [checked_div_UScalar, Option.ofResult, UScalar.div]
  split_ifs
  . zify at *
    simp_all
  . rename_i hnz
    simp
    have hnz' : y.val ≠ 0 := by zify at *; simp_all
    have ⟨ z, hz ⟩ := UScalar.div_bv_spec x hnz'
    have : x / y = x.div y := by rfl
    simp [this, UScalar.div, hnz] at hz
    simp [hz, hnz']

uscalar @[progress_pure «%S».checked_div x y]
theorem «%S».checked_div_bv_spec (x y : «%S») :
  match «%S».checked_div x y with
  | some z => y.val ≠ 0 ∧ z.val = x.val / y.val ∧ z.bv = x.bv / y.bv
  | none => y.val = 0 := by
  have := core.num.checked_div_UScalar_bv_spec x y
  simp_all [«%S».checked_div, «%S».bv]
  cases h: core.num.checked_div_UScalar x y <;> simp_all

/-!
Signed checked div
-/
theorem core.num.checked_div_IScalar_bv_spec {ty} (x y : IScalar ty) :
  match core.num.checked_div_IScalar x y with
  | some z => y.val ≠ 0 ∧ ¬ (x.val = IScalar.min ty ∧ y.val = -1) ∧ z.val = Int.tdiv x.val y.val ∧ z.bv = BitVec.sdiv x.bv y.bv
  | none => y.val = 0 ∨ (x.val = IScalar.min ty ∧ y.val = -1) := by
  simp [checked_div_IScalar, Option.ofResult, IScalar.div]
  split_ifs
  . zify at *
    simp_all
  . rename_i hnz hNoOverflow
    simp
    have hnz' : y.val ≠ 0 := by zify at *; simp_all
    have ⟨ z, hz ⟩ := @IScalar.div_bv_spec _ x y hnz' (by simp; tauto)
    have : x / y = x.div y := by rfl
    simp [this, IScalar.div, hnz] at hz
    split_ifs at hz
    simp at hz
    simp [hz, hnz']
    tauto
  . simp_all

iscalar @[progress_pure «%S».checked_div x y]
theorem «%S».checked_div_bv_spec (x y : «%S») :
  match core.num.checked_div_IScalar x y with
  | some z => y.val ≠ 0 ∧ ¬ (x.val = «%S».min ∧ y.val = -1) ∧ z.val = Int.tdiv x.val y.val ∧ z.bv = BitVec.sdiv x.bv y.bv
  | none => y.val = 0 ∨ (x.val = «%S».min ∧ y.val = -1) := by
  have := core.num.checked_div_IScalar_bv_spec x y
  simp_all only [«%S».bv, IScalar.min, «%S».min, «%S».numBits]
  cases h: core.num.checked_div_IScalar x y <;> simp_all only [ne_eq, not_false_eq_true, and_self]

end Aeneas.Std
