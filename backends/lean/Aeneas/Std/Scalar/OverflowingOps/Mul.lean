import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Elab

namespace Aeneas.Std

open ScalarElab

/-!
# Overflowing Multiplication
-/

def UScalar.overflowing_mul {ty} (x y : UScalar ty) : UScalar ty × Bool :=
  (⟨ x.bv * y.bv ⟩, BitVec.umulOverflow x.bv y.bv)

def IScalar.overflowing_mul {ty} (x y : IScalar ty) : IScalar ty × Bool :=
  (⟨ x.bv * y.bv ⟩, BitVec.smulOverflow x.bv y.bv)

uscalar @[step_pure_def]
def «%S».overflowing_mul (x y : «%S») : «%S» × Bool := @UScalar.overflowing_mul .«%S» x y

iscalar @[step_pure_def]
def «%S».overflowing_mul (x y : «%S») : «%S» × Bool := @IScalar.overflowing_mul .«%S» x y

/- [core::num::{_}::overflowing_mul] -/
uscalar @[step_pure_def]
def core.num.«%S».overflowing_mul := @UScalar.overflowing_mul .«%S»

/- [core::num::{_}::overflowing_mul] -/
iscalar @[step_pure_def]
def core.num.«%S».overflowing_mul := @IScalar.overflowing_mul .«%S»

/-!
## Spec Theorems
-/

theorem UScalar.overflowing_mul_eq {ty} (x y : UScalar ty) :
  let z := overflowing_mul x y
  if x.val * y.val > UScalar.max ty then
    z.fst.val = (x.val * y.val) % UScalar.size ty ∧
    z.snd = true
  else
    z.fst.val = x.val * y.val ∧
    z.snd = false
  := by
  simp [overflowing_mul, BitVec.umulOverflow]
  simp only [val, BitVec.toNat_mul, max]
  split <;> rename_i hLt
  · split_conjs
    · simp [size]
    · omega
  · split_conjs
    · apply Nat.mod_eq_of_lt
      grind
    · grind

uscalar @[step_pure overflowing_mul x y]
theorem core.num.«%S».overflowing_mul_eq (x y : «%S») :
  let z := overflowing_mul x y
  if x.val * y.val > UScalar.max .«%S» then z.fst.val = (x.val * y.val) % UScalar.size .«%S» ∧ z.snd = true
  else z.fst.val = x.val * y.val ∧ z.snd = false
  := UScalar.overflowing_mul_eq x y

/-!
## Additional Theorems
-/

theorem UScalar.overflowing_mul_comm {ty} (x y : UScalar ty) :
  overflowing_mul x y = overflowing_mul y x := by
  simp [overflowing_mul, BitVec.umulOverflow, Nat.mul_comm]
  exact BitVec.mul_comm x.bv y.bv

theorem IScalar.overflowing_mul_comm {ty} (x y : IScalar ty) :
  overflowing_mul x y = overflowing_mul y x := by
  simp [IScalar.overflowing_mul, BitVec.smulOverflow, Int.mul_comm]
  exact BitVec.mul_comm x.bv y.bv

uscalar
theorem core.num.«%S».overflowing_mul_comm (x y : «%S») :
  overflowing_mul x y = overflowing_mul y x := UScalar.overflowing_mul_comm x y

iscalar
theorem core.num.«%S».overflowing_mul_comm (x y : «%S») :
  overflowing_mul x y = overflowing_mul y x := IScalar.overflowing_mul_comm x y

theorem UScalar.overflowing_mul_assoc {ty} (x y z : UScalar ty) :
  (overflowing_mul (overflowing_mul x y).1 z).1 = (overflowing_mul x (overflowing_mul y z).1).1 := by
  simp [overflowing_mul]
  exact BitVec.mul_assoc x.bv y.bv z.bv

theorem IScalar.overflowing_mul_assoc {ty} (x y z : IScalar ty) :
  (overflowing_mul (overflowing_mul x y).1 z).1 = (overflowing_mul x (overflowing_mul y z).1).1 := by
  simp [overflowing_mul]
  exact BitVec.mul_assoc x.bv y.bv z.bv

uscalar
theorem core.num.«%S».overflowing_mul_assoc (x y z : «%S») :
  (overflowing_mul (overflowing_mul x y).1 z).1 = (overflowing_mul x (overflowing_mul y z).1).1 :=
  UScalar.overflowing_mul_assoc x y z

iscalar
theorem core.num.«%S».overflowing_mul_assoc (x y z : «%S») :
  (overflowing_mul (overflowing_mul x y).1 z).1 = (overflowing_mul x (overflowing_mul y z).1).1 :=
  IScalar.overflowing_mul_assoc x y z

@[simp]
theorem UScalar.overflowing_mul_zero {ty} (x: UScalar ty) :
  (overflowing_mul x UScalar.zero) = (zero, false) := by
  simp [overflowing_mul, BitVec.umulOverflow,  UScalar.zero, zero_bv]
  rfl

@[simp]
theorem IScalar.overflowing_mul_zero {ty} (x : IScalar ty) :
  (overflowing_mul x IScalar.zero) = (zero, false) := by
  simp [overflowing_mul, IScalar.zero, BitVec.smulOverflow, zero_bv]; rfl

uscalar @[simp]
theorem core.num.«%S».overflowing_mul_zero(x : «%S») :
  (overflowing_mul x UScalar.zero) = (UScalar.zero, false) :=
  UScalar.overflowing_mul_zero x

iscalar @[simp]
theorem core.num.«%S».overflowing_mul_zero(x : «%S») :
  (overflowing_mul x IScalar.zero) = (IScalar.zero, false) :=
   IScalar.overflowing_mul_zero x

@[simp]
theorem UScalar.overflowing_zero_mul {ty} (x: UScalar ty) :
  (overflowing_mul UScalar.zero x) = (zero, false) := by
  simp [overflowing_mul_comm]

@[simp]
theorem IScalar.overflowing_zero_mul {ty} (x : IScalar ty) :
  (overflowing_mul IScalar.zero x) = (zero, false) := by
  simp [overflowing_mul_comm]

uscalar @[simp]
theorem core.num.«%S».overflowing_zero_mul(x : «%S») :
  (overflowing_mul UScalar.zero x) = (UScalar.zero, false) :=
  UScalar.overflowing_zero_mul x

iscalar @[simp]
theorem core.num.«%S».overflowing_zero_mul(x : «%S») :
  (overflowing_mul IScalar.zero x) = (IScalar.zero, false) :=
   IScalar.overflowing_zero_mul x

@[simp]
theorem UScalar.overflowing_mul_one {ty} (x: UScalar ty) :
  (overflowing_mul x UScalar.one) = (x, false) := by
  simp [overflowing_mul, UScalar.one, BitVec.umulOverflow, one_bv]
  grind[Nat.one_mod_two_pow, x.hBounds]

@[simp]
theorem IScalar.overflowing_mul_one {ty} (x : IScalar ty) :
  (overflowing_mul x IScalar.one) = (x, false) := by
  have hw : 1 < ty.numBits := by
    simp[IScalarTy.numBits]; grind[System.Platform.numBits_eq]
  simp [overflowing_mul, IScalar.one, BitVec.smulOverflow, one_bv]
  grind[x.hBounds]

uscalar @[simp]
theorem core.num.«%S».overflowing_mul_one(x : «%S») :
  (overflowing_mul x UScalar.one) = (x, false) := UScalar.overflowing_mul_one x

iscalar @[simp]
theorem core.num.«%S».overflowing_mul_one(x : «%S») :
  (overflowing_mul x IScalar.one) = (x, false) := IScalar.overflowing_mul_one x

@[simp]
theorem UScalar.overflowing_one_mul {ty} (x: UScalar ty) :
  (overflowing_mul UScalar.one x) = (x, false) := by
  simp [overflowing_mul_comm]

@[simp]
theorem IScalar.overflowing_one_mul {ty} (x : IScalar ty) :
  (overflowing_mul IScalar.one x) = (x, false) := by
  simp [overflowing_mul_comm]

uscalar @[simp]
theorem core.num.«%S».overflowing_one_mul(x : «%S») :
  (overflowing_mul UScalar.one x) = (x, false) := UScalar.overflowing_one_mul x

iscalar @[simp]
theorem core.num.«%S».overflowing_one_mul(x : «%S») :
  (overflowing_mul IScalar.one x) = (x, false) := IScalar.overflowing_one_mul x

end Aeneas.Std
