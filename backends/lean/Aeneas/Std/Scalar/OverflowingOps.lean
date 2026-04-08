import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Elab

namespace Aeneas.Std

open ScalarElab

/-!
# Overflowing Operations
-/

/-
## Some Useful Abbreviations and Lemmas
-/

private abbrev UScalar.zero {ty : UScalarTy} : UScalar ty := UScalar.ofNatCore 0 (by simp)

private abbrev UScalar.one {ty : UScalarTy} : UScalar ty := UScalar.ofNatCore 1 (
    by simp[UScalarTy.numBits_nonzero]
  )

private abbrev IScalar.zero {ty : IScalarTy} : IScalar ty := IScalar.ofIntCore 0 (by simp)

private abbrev IScalar.one {ty : IScalarTy} : IScalar ty := IScalar.ofIntCore 1
  (
    by
    refine bound_suffices ty 1 ?_
    simp[cMin, rMin, I8.rMin, I16.rMin, I32.rMin, I64.rMin, I128.rMin, Isize.rMin, cMax, rMax, I8.rMax, I16.rMax, I32.rMax, I64.rMax, I128.rMax, Isize.rMax];
    grind
  )

theorem UScalar.zero_bv {ty : UScalarTy}: UScalar.zero.bv = BitVec.ofNat ty.numBits 0 := by
  simp[UScalar.zero, UScalar.ofNatCore]

theorem IScalar.zero_bv {ty : IScalarTy}: IScalar.zero.bv = BitVec.ofNat ty.numBits 0 := by
  simp[IScalar.zero, IScalar.ofIntCore]

theorem UScalar.one_bv {ty : UScalarTy}: UScalar.one.bv = BitVec.ofNat ty.numBits 1 := by
  simp[UScalar.one, UScalar.ofNatCore, BitVec.ofFin_eq_ofNat];

theorem IScalar.one_bv {ty : IScalarTy}: IScalar.one.bv = BitVec.ofNat ty.numBits 1 := by
  simp[IScalar.one, IScalar.ofIntCore]
  exact Eq.symm (BitVec.eq_of_toNat_eq rfl)

-- TODO: we should redefine this, in particular so that it doesn't live in the `Result` monad

/-!
## Overflowing Addition
-/

def UScalar.overflowing_add {ty} (x y : UScalar ty) : UScalar ty × Bool :=
  (⟨ BitVec.ofNat _ (x.val + y.val) ⟩, 2^ty.numBits ≤ x.val + y.val)

def IScalar.overflowing_add {ty} (x y : IScalar ty) : IScalar ty × Bool :=
  (⟨ BitVec.ofInt _ (x.val + y.val) ⟩,
     ¬ (-2^(ty.numBits -1) ≤ x.val + y.val ∧ x.val + y.val < 2^(ty.numBits-1)))

/- [core::num::{u8}::overflowing_add] -/
uscalar def core.num.«%S».overflowing_add := @UScalar.overflowing_add .«%S»

/- [core::num::{i8}::overflowing_add] -/
iscalar def core.num.«%S».overflowing_add := @IScalar.overflowing_add .«%S»

attribute [-simp] Bool.exists_bool

theorem UScalar.overflowing_add_eq {ty} (x y : UScalar ty) :
  let z := overflowing_add x y
  if x.val + y.val > UScalar.max ty then
    z.fst.val + UScalar.size ty = x.val + y.val ∧
    z.snd = true
  else
    z.fst.val = x.val + y.val ∧
    z.snd = false
  := by
  simp [overflowing_add]
  simp only [val, BitVec.toNat_ofNat, max]
  split <;> rename_i hLt
  . split_conjs
    . have : (x.bv.toNat + y.bv.toNat) % 2^ty.numBits =
             (x.bv.toNat + y.bv.toNat - 2^ty.numBits) % 2^ty.numBits := by
        rw [Nat.mod_eq_sub_mod]
        omega
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


theorem UScalar.overflowing_add_comm {ty} (x y : UScalar ty) :
  overflowing_add x y = overflowing_add y x := by
  simp[overflowing_add, Nat.add_comm]

theorem IScalar.overflowing_add_comm {ty} (x y : IScalar ty) :
  overflowing_add x y = overflowing_add y x := by
  simp[IScalar.overflowing_add, Int.add_comm]

uscalar
theorem core.num.«%S».overflowing_add_comm(x y : «%S») :
  overflowing_add x y = overflowing_add y x := UScalar.overflowing_add_comm x y

iscalar
theorem core.num.«%S».overflowing_add_comm(x y : «%S») :
  overflowing_add x y = overflowing_add y x := IScalar.overflowing_add_comm x y

theorem UScalar.overflowing_add_assoc {ty} (x y  z : UScalar ty) :
  (overflowing_add (overflowing_add x y).1 z).1 = (overflowing_add x (overflowing_add y z).1).1 := by
  simp [overflowing_add]
  simp [@BitVec.ofNat_add, BitVec.add_assoc]

theorem IScalar.overflowing_add_assoc {ty} (x y  z : IScalar ty) :
  (overflowing_add (overflowing_add x y).1 z).1 = (overflowing_add x (overflowing_add y z).1).1 := by
  simp [overflowing_add]
  simp [@BitVec.ofInt_add, BitVec.add_assoc]

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
  simp [overflowing_add, UScalar.zero, hmax]

@[simp]
theorem IScalar.overflowing_add_zero {ty} (x : IScalar ty) :
  (overflowing_add x IScalar.zero) = (x, false) := by
  simp [overflowing_add, hmax, hmin]

uscalar @[simp]
theorem core.num.«%S».overflowing_add_zero(x : «%S») :
  (overflowing_add x UScalar.zero) = (x, false) :=
  UScalar.overflowing_add_zero x

iscalar @[simp]
theorem core.num.«%S».overflowing_add_zero(x : «%S») :
  (overflowing_add x IScalar.zero) = (x, false) :=
   IScalar.overflowing_add_zero x

/-!
## Overflowing Subtraction
-/

def UScalar.overflowing_sub {ty} (x y : UScalar ty) : UScalar ty × Bool :=
  (⟨ x.bv - y.bv ⟩, x.val < y.val)

def IScalar.overflowing_sub {ty} (x y : IScalar ty) : IScalar ty × Bool :=
  (⟨ x.bv - y.bv ⟩,
     ¬ (-2^(ty.numBits -1) ≤ x.val - y.val ∧ x.val - y.val < 2^(ty.numBits-1)))

/- [core::num::{u8}::overflowing_sub] -/
uscalar def core.num.«%S».overflowing_sub := @UScalar.overflowing_sub .«%S»

/- [core::num::{i8}::overflowing_sub] -/
iscalar def core.num.«%S».overflowing_sub := @IScalar.overflowing_sub .«%S»

theorem UScalar.overflowing_sub_eq {ty} (x y : UScalar ty) :
  let z := overflowing_sub x y
  if x.val < y.val then
    z.fst.val + y.val = x.val + UScalar.size ty ∧
    z.snd = true
  else
    z.fst.val = x.val - y.val ∧
    z.snd = false
  := by
  simp [overflowing_sub]
  have hsub_toNat : (x.bv - y.bv).toNat =
      (x.val + (2 ^ ty.numBits - y.val)) % 2 ^ ty.numBits := by
    simp [BitVec.toNat_sub, bv_toNat, Nat.add_comm]
  have hsubval : (↑({ bv := x.bv - y.bv } : UScalar ty) : Nat) =
      (x.val + (2 ^ ty.numBits - y.val)) % 2 ^ ty.numBits := by
    exact hsub_toNat
  split
  case isTrue ht =>
    apply And.intro
    · rw [hsubval]
      have hmod :
          (x.val + (2 ^ ty.numBits - y.val)) % 2 ^ ty.numBits =
            x.val + (2 ^ ty.numBits - y.val) := by
        apply Nat.mod_eq_of_lt
        grind
      rw [hmod]
      rw [UScalar.size]
      grind
    · simp [ht]
  case isFalse hf =>
    apply And.intro
    · have hxy : y.val ≤ x.val := Nat.le_of_not_gt hf
      rw [hsubval]
      have hsubmod :
          (x.val + (2 ^ ty.numBits - y.val)) % 2 ^ ty.numBits =
            (x.val + (2 ^ ty.numBits - y.val) - 2 ^ ty.numBits) % 2 ^ ty.numBits := by
        rw [Nat.mod_eq_sub_mod]
        omega
      rw [hsubmod]
      have hsub : x.val + (2 ^ ty.numBits - y.val) - 2 ^ ty.numBits = x.val - y.val := by grind
      rw [hsub]
      apply Nat.mod_eq_of_lt
      grind
    · grind

uscalar @[step_pure overflowing_sub x y]
theorem core.num.«%S».overflowing_sub_eq (x y : «%S») :
  let z := overflowing_sub x y
  if x.val < y.val then z.fst.val + y.val = x.val + UScalar.size .«%S» ∧ z.snd = true
  else  z.fst.val = x.val - y.val ∧ z.snd = false
  := UScalar.overflowing_sub_eq x y


@[simp]
theorem UScalar.overflowing_sub_zero {ty} (x: UScalar ty) :
  (overflowing_sub x UScalar.zero) = (x, false) := by
  simp [overflowing_sub, UScalar.zero, zero_bv]


@[simp]
theorem IScalar.overflowing_sub_zero {ty} (x : IScalar ty) :
  (overflowing_sub x IScalar.zero) = (x, false) := by
  simp [overflowing_sub, hmax, hmin, zero_bv]

uscalar @[simp]
theorem core.num.«%S».overflowing_sub_zero(x : «%S») :
  (overflowing_sub x UScalar.zero) = (x, false) :=
  UScalar.overflowing_sub_zero x

iscalar @[simp]
theorem core.num.«%S».overflowing_sub_zero(x : «%S») :
  (overflowing_sub x IScalar.zero) = (x, false) :=
   IScalar.overflowing_sub_zero x


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
