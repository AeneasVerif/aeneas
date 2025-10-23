import Aeneas.Std.Scalar.Ops.Rem
import Aeneas.Std.Scalar.Elab

namespace Aeneas.Std

open Result Error Arith ScalarElab

/-!
# Checked Remainder: Definitions
-/

/- [core::num::{T}::checked_rem] -/
def core.num.checked_rem_UScalar {ty} (x y : UScalar ty) : Option (UScalar ty) :=
  Option.ofResult (UScalar.rem x y)

uscalar def «%S».checked_rem (x y : «%S») : Option «%S» := core.num.checked_rem_UScalar x y

/- [core::num::{T}::checked_rem] -/
def core.num.checked_rem_IScalar {ty} (x y : IScalar ty) : Option (IScalar ty) :=
  Option.ofResult (IScalar.rem x y)

iscalar def «%S».checked_rem (x y : «%S») : Option «%S» := core.num.checked_rem_IScalar x y

/-!
# Checked Remained
-/

/-!
Unsigned checked remainder
-/
theorem core.num.checked_rem_UScalar_bv_spec {ty} (x y : UScalar ty) :
  match core.num.checked_rem_UScalar x y with
  | some z => y.val ≠ 0 ∧ z.val = x.val % y.val ∧ z.bv = x.bv % y.bv
  | none => y.val = 0 := by
  simp [checked_rem_UScalar, Option.ofResult, UScalar.rem]
  split_ifs
  . zify at *
    simp_all
  . rename_i hnz
    simp
    have hnz' : y.val ≠ 0 := by zify at *; simp_all
    have ⟨ z, hz ⟩ := UScalar.rem_bv_spec x hnz'
    have : x % y = x.rem y := by rfl
    simp [this, UScalar.rem, hnz] at hz
    simp [hz, hnz']

uscalar @[progress_pure «%S».checked_rem x y]
theorem «%S».checked_rem_bv_spec (x y : «%S») :
  match «%S».checked_rem x y with
  | some z => y.val ≠ 0 ∧ z.val = x.val % y.val ∧ z.bv = x.bv % y.bv
  | none => y.val = 0 := by
  have := core.num.checked_rem_UScalar_bv_spec x y
  simp_all [«%S».checked_rem, «%S».bv]
  cases h: core.num.checked_rem_UScalar x y <;> simp_all

/-!
Signed checked rem
-/
theorem core.num.checked_rem_IScalar_bv_spec {ty} (x y : IScalar ty) :
  match core.num.checked_rem_IScalar x y with
  | some z => y.val ≠ 0 ∧ z.val = Int.tmod x.val y.val ∧ z.bv = BitVec.srem x.bv y.bv
  | none => y.val = 0 := by
  simp [checked_rem_IScalar, Option.ofResult, IScalar.rem]
  split_ifs
  . zify at *
    simp_all
  . rename_i hnz
    simp
    have hnz' : y.val ≠ 0 := by zify at *; simp_all
    have ⟨ z, hz ⟩ := @IScalar.rem_bv_spec _ x y hnz'
    have : x % y = x.rem y := by rfl
    simp [this, IScalar.rem, hnz] at hz
    simp [*]

iscalar @[progress_pure «%S».checked_rem x y]
theorem «%S».checked_rem_bv_spec (x y : «%S») :
  match core.num.checked_rem_IScalar x y with
  | some z => y.val ≠ 0 ∧ z.val = Int.tmod x.val y.val ∧ z.bv = BitVec.srem x.bv y.bv
  | none => y.val = 0 := by
  have := core.num.checked_rem_IScalar_bv_spec x y
  simp_all only [«%S».bv]
  cases h: core.num.checked_rem_IScalar x y <;> simp_all

end Aeneas.Std
