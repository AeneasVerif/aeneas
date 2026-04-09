import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Elab

namespace Aeneas.Std

open ScalarElab

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

end Aeneas.Std
