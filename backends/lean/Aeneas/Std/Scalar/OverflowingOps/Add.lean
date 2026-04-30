import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Elab

namespace Aeneas.Std

open ScalarElab

/-!
# Overflowing Addition
-/

def UScalar.overflowing_add {ty} (x y : UScalar ty) : UScalar ty × Bool :=
  (⟨x.bv + y.bv⟩, BitVec.uaddOverflow x.bv y.bv)

def IScalar.overflowing_add {ty} (x y : IScalar ty) : IScalar ty × Bool :=
  (⟨x.bv + y.bv⟩, BitVec.saddOverflow x.bv y.bv)

uscalar @[step_pure_def]
def «%S».overflowing_add (x y : «%S») : «%S» × Bool := @UScalar.overflowing_add .«%S» x y

iscalar @[step_pure_def]
def «%S».overflowing_add (x y : «%S») : «%S» × Bool := @IScalar.overflowing_add .«%S» x y

/- [core::num::{_}::overflowing_add] -/
uscalar @[step_pure_def]
def core.num.«%S».overflowing_add := @UScalar.overflowing_add .«%S»

/- [core::num::{_}::overflowing_add] -/
iscalar @[step_pure_def]
def core.num.«%S».overflowing_add := @IScalar.overflowing_add .«%S»

attribute [-simp] Bool.exists_bool

/-!
## Spec Theorems
-/

theorem UScalar.overflowing_add_eq {ty} (x y : UScalar ty) :
  let z := overflowing_add x y
  if x.val + y.val > UScalar.max ty then
    z.fst.val + UScalar.size ty = x.val + y.val ∧
    z.snd = true
  else
    z.fst.val = x.val + y.val ∧
    z.snd = false
  := by
  simp [overflowing_add, BitVec.uaddOverflow]
  simp only [val, BitVec.toNat_add, max]
  split_ifs with hLt
  · constructor
    · have : (x.bv.toNat + y.bv.toNat) % 2^ty.numBits =
             (x.bv.toNat + y.bv.toNat - 2^ty.numBits) % 2^ty.numBits := by
        grind[Nat.mod_eq_sub_mod]
      rw [this]; clear this
      have := @Nat.mod_eq_of_lt (x.bv.toNat + y.bv.toNat - 2^ty.numBits) (2^ty.numBits) (by omega)
      rw [this]; clear this
      simp [size]
      scalar_tac
    . omega
  . split_conjs
    . apply Nat.mod_eq_of_lt
      omega
    . omega

uscalar @[step_pure overflowing_add x y]
theorem core.num.«%S».overflowing_add_eq (x y : «%S») :
  let z := overflowing_add x y
  if x.val + y.val > UScalar.max .«%S» then z.fst.val + UScalar.size .«%S» = x.val + y.val ∧ z.snd = true
  else z.fst.val = x.val + y.val ∧ z.snd = false
  := UScalar.overflowing_add_eq x y

/-!
## Additional Theorems
-/

theorem UScalar.overflowing_add_comm {ty} (x y : UScalar ty) :
  overflowing_add x y = overflowing_add y x := by
  simp[overflowing_add, BitVec.uaddOverflow]
  grind

theorem IScalar.overflowing_add_comm {ty} (x y : IScalar ty) :
  overflowing_add x y = overflowing_add y x := by
  simp[IScalar.overflowing_add,BitVec.saddOverflow]
  grind


uscalar
theorem core.num.«%S».overflowing_add_comm(x y : «%S») :
  overflowing_add x y = overflowing_add y x := UScalar.overflowing_add_comm x y

iscalar
theorem core.num.«%S».overflowing_add_comm(x y : «%S») :
  overflowing_add x y = overflowing_add y x := IScalar.overflowing_add_comm x y

theorem UScalar.overflowing_add_assoc {ty} (x y  z : UScalar ty) :
  (overflowing_add (overflowing_add x y).1 z).1 = (overflowing_add x (overflowing_add y z).1).1 := by
  simp [overflowing_add]
  simp [BitVec.add_assoc]

theorem IScalar.overflowing_add_assoc {ty} (x y  z : IScalar ty) :
  (overflowing_add (overflowing_add x y).1 z).1 = (overflowing_add x (overflowing_add y z).1).1 := by
  simp [overflowing_add]
  simp [BitVec.add_assoc]

uscalar
theorem core.num.«%S».overflowing_add_assoc(x y z : «%S») :
  (overflowing_add (overflowing_add x y).1 z).1 = (overflowing_add x (overflowing_add y z).1).1 :=
  UScalar.overflowing_add_assoc x y z

iscalar
theorem core.num.«%S».overflowing_add_assoc(x y z : «%S») :
  (overflowing_add (overflowing_add x y).1 z).1 = (overflowing_add x (overflowing_add y z).1).1 :=
  IScalar.overflowing_add_assoc x y z

@[simp]
theorem UScalar.overflowing_add_zero {ty} (x: UScalar ty) :
  (overflowing_add x UScalar.zero) = (x, false) := by
  simp [overflowing_add, UScalar.zero, BitVec.uaddOverflow, ofNatCore, UScalar.hBounds]

@[simp]
theorem IScalar.overflowing_add_zero {ty} (x : IScalar ty) :
  (overflowing_add x IScalar.zero) = (x, false) := by
  simp [overflowing_add, BitVec.saddOverflow, hmax, hmin, ofIntCore]

uscalar @[simp]
theorem core.num.«%S».overflowing_add_zero(x : «%S») :
  (overflowing_add x UScalar.zero) = (x, false) :=
  UScalar.overflowing_add_zero x

iscalar @[simp]
theorem core.num.«%S».overflowing_add_zero(x : «%S») :
  (overflowing_add x IScalar.zero) = (x, false) :=
   IScalar.overflowing_add_zero x

@[simp]
theorem UScalar.overflowing_zero_add {ty} (x: UScalar ty) :
  (overflowing_add UScalar.zero x) = (x, false) := by
  simp [overflowing_add_comm]

@[simp]
theorem IScalar.overflowing_zero_add {ty} (x : IScalar ty) :
  (overflowing_add IScalar.zero x) = (x, false) := by
  simp [overflowing_add_comm]

uscalar @[simp]
theorem core.num.«%S».overflowing_zero_add(x : «%S») :
  (overflowing_add UScalar.zero x) = (x, false) :=
  UScalar.overflowing_zero_add x

iscalar @[simp]
theorem core.num.«%S».overflowing_zero_add(x : «%S») :
  (overflowing_add IScalar.zero x) = (x, false) :=
   IScalar.overflowing_zero_add x

end Aeneas.Std
