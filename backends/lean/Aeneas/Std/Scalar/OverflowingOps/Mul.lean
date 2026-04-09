import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Elab

namespace Aeneas.Std

open ScalarElab

/-!
## Overflowing Multiplication
-/

def UScalar.overflowing_mul {ty} (x y : UScalar ty) : UScalar ty × Bool :=
  (⟨ x.bv * y.bv ⟩, 2^ty.numBits ≤ x.val * y.val)

def IScalar.overflowing_mul {ty} (x y : IScalar ty) : IScalar ty × Bool :=
  (⟨ x.bv * y.bv ⟩,
     ¬ (-2^(ty.numBits -1) ≤ x.val * y.val ∧ x.val * y.val < 2^(ty.numBits-1)))

/- [core::num::{u8}::overflowing_mul] -/
uscalar def core.num.«%S».overflowing_mul := @UScalar.overflowing_mul .«%S»

/- [core::num::{i8}::overflowing_mul] -/
iscalar def core.num.«%S».overflowing_mul := @IScalar.overflowing_mul .«%S»

theorem UScalar.overflowing_mul_eq {ty} (x y : UScalar ty) :
  let z := overflowing_mul x y
  if x.val * y.val > UScalar.max ty then
    z.fst.val = (x.val * y.val) % UScalar.size ty ∧
    z.snd = true
  else
    z.fst.val = x.val * y.val ∧
    z.snd = false
  := by
  simp [overflowing_mul]
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

theorem UScalar.overflowing_mul_comm {ty} (x y : UScalar ty) :
  overflowing_mul x y = overflowing_mul y x := by
  simp [overflowing_mul, Nat.mul_comm]
  exact BitVec.mul_comm x.bv y.bv

theorem IScalar.overflowing_mul_comm {ty} (x y : IScalar ty) :
  overflowing_mul x y = overflowing_mul y x := by
  simp [IScalar.overflowing_mul, Int.mul_comm]
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
  simp [overflowing_mul, UScalar.zero, zero_bv];rfl

@[simp]
theorem IScalar.overflowing_mul_zero {ty} (x : IScalar ty) :
  (overflowing_mul x IScalar.zero) = (zero, false) := by
  simp [overflowing_mul, IScalar.zero, zero_bv]; rfl

uscalar @[simp]
theorem core.num.«%S».overflowing_mul_zero(x : «%S») :
  (UScalar.overflowing_mul x UScalar.zero) = (UScalar.zero, false) :=
  UScalar.overflowing_mul_zero x

iscalar @[simp]
theorem core.num.«%S».overflowing_mul_zero(x : «%S») :
  (overflowing_mul x IScalar.zero) = (IScalar.zero, false) :=
   IScalar.overflowing_mul_zero x


@[simp]
theorem UScalar.overflowing_mul_one {ty} (x: UScalar ty) :
  (overflowing_mul x UScalar.one) = (x, false) := by
  simp [overflowing_mul, UScalar.one, hmax, one_bv];

@[simp]
theorem IScalar.overflowing_mul_one {ty} (x : IScalar ty) :
  (overflowing_mul x IScalar.one) = (x, false) := by
  simp [overflowing_mul, IScalar.one, hmax, hmin, one_bv]

uscalar @[simp]
theorem core.num.«%S».overflowing_mul_one(x : «%S») :
  (UScalar.overflowing_mul x UScalar.one) = (x, false) :=
  UScalar.overflowing_mul_one x

iscalar @[simp]
theorem core.num.«%S».overflowing_mul_one(x : «%S») :
  (overflowing_mul x IScalar.one) = (x, false) :=
   IScalar.overflowing_mul_one x

end Aeneas.Std
