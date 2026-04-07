import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Elab

namespace Aeneas.Std

open ScalarElab

/-!
# Overflowing Operations
-/

-- TODO: we should redefine this, in particular so that it doesn't live in the `Result` monad

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


end Aeneas.Std
