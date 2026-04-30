import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Elab
import Aeneas.Std.Scalar.Ops

namespace Aeneas.Std

open Result Error ScalarElab

/-!
# Overflowing Division
-/

def UScalar.overflowing_div {ty} (x y : UScalar ty) : Result (UScalar ty × Bool) :=
  if y.bv != 0 then ok (⟨ BitVec.udiv x.bv y.bv ⟩, false) else fail divisionByZero

def IScalar.overflowing_div {ty} (x y : IScalar ty) : Result (IScalar ty × Bool) :=
  if y.val != 0 then ok (⟨ BitVec.sdiv x.bv y.bv ⟩, BitVec.sdivOverflow x.bv y.bv)
  else fail divisionByZero

uscalar @[step_pure_def]
def «%S».overflowing_div (x y : «%S») : Result («%S» × Bool) := @UScalar.overflowing_div .«%S» x y

iscalar @[step_pure_def]
def «%S».overflowing_div (x y : «%S») : Result («%S» × Bool) := @IScalar.overflowing_div .«%S» x y

/- [core::num::{_}::overflowing_div] -/
uscalar @[step_pure_def]
def core.num.«%S».overflowing_div := @UScalar.overflowing_div .«%S»

/- [core::num::{_}::overflowing_div] -/
iscalar @[step_pure_def]
def core.num.«%S».overflowing_div := @IScalar.overflowing_div .«%S»

attribute [-simp] Bool.exists_bool

/-!
## Spec Theorems
-/

theorem UScalar.overflowing_div_eq {ty} (x y : UScalar ty) :
  overflowing_div x y = (·, false) <$> UScalar.div x y
  := by
    simp[overflowing_div, UScalar.div]
    rw [map_eq_bind_pure_comp]
    split<;>simp[pure]


uscalar @[step_pure overflowing_div x y]
theorem core.num.«%S».overflowing_div_eq (x y : «%S») :
  overflowing_div x y = (·, false) <$> UScalar.div x y
  := UScalar.overflowing_div_eq x y

/-!
## Additional Theorems
-/

@[simp]
theorem UScalar.overflowing_div_one {ty} (x : UScalar ty) :
  overflowing_div x one = .ok (x, false) := by
  simp[overflowing_div, one_bv]
  exact UScalarTy.numBits_nonzero ty


@[simp]
theorem IScalar.overflowing_div_one {ty} (x : IScalar ty) :
  overflowing_div x one = .ok (x, false) := by
  simp [overflowing_div, BitVec.sdiv_one, one_bv, BitVec.sdivOverflow_eq, BitVec.sdivOverflow_eq]
  intro _ _
  cases ty <;> try simp
  cases System.Platform.numBits_eq<;>rename_i h<;>rw[h]<;>grind


uscalar @[simp]
theorem core.num.«%S».overflowing_div_one(x : «%S») :
  overflowing_div x UScalar.one = .ok (x, false) := UScalar.overflowing_div_one x

iscalar @[simp]
theorem core.num.«%S».overflowing_div_one(x : «%S») :
  overflowing_div x IScalar.one = .ok (x, false) := IScalar.overflowing_div_one x


@[simp]
theorem UScalar.overflowing_div_zero {ty} (x : UScalar ty) :
  overflowing_div x zero = .fail divisionByZero := by
  simp[overflowing_div, zero_bv]

@[simp]
theorem IScalar.overflowing_div_zero {ty} (x : IScalar ty) :
  overflowing_div x zero = .fail divisionByZero := by
  simp[overflowing_div]

uscalar @[simp]
theorem core.num.«%S».overflowing_div_zero(x : «%S») :
  overflowing_div x UScalar.zero = .fail divisionByZero := UScalar.overflowing_div_zero x

iscalar @[simp]
theorem core.num.«%S».overflowing_div_zero(x : «%S») :
  overflowing_div x IScalar.zero = .fail divisionByZero := IScalar.overflowing_div_zero x


@[simp]
theorem UScalar.overflowing_div_self {ty} (x : UScalar ty) (h: x.bv ≠ 0) :
  overflowing_div x x = .ok (one, false) := by
  have h': x.bv ≠ 0#ty.numBits :=  by simp; exact Ne.intro h
  simp[overflowing_div, h']
  rw [←one_bv]

@[simp]
theorem IScalar.overflowing_div_self {ty} (x : IScalar ty) (h₁: x.bv ≠ 0) (h₂: x ≠ min ty) :
  overflowing_div x x = .ok (one, false) := by
  have h₄: x.bv ≠ 0#ty.numBits := by grind;
  have h₃: x.val ≠ 0 := by
    simp only [val, ← BitVec.toInt_zero (w := ty.numBits), Ne, BitVec.toInt_inj]
    exact h₄
  simp[overflowing_div, BitVec.sdivOverflow, h₃, h₄]
  simp[←one_bv]
  cases ty <;> try simp
  cases System.Platform.numBits_eq <;> rename_i h <;> rw [h] <;> simp


uscalar @[simp]
theorem core.num.«%S».overflowing_div_self (x : «%S») (h : x.bv ≠ 0) :
  overflowing_div x x = .ok (UScalar.one, false) := UScalar.overflowing_div_self x h

iscalar @[simp]
theorem core.num.«%S».overflowing_div_self (x : «%S») (h₁ : x.bv ≠ 0) (h₂ : x ≠ IScalar.min .«%S») :
  overflowing_div x x = .ok (IScalar.one, false) := IScalar.overflowing_div_self x h₁ h₂

end Aeneas.Std
