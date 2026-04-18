import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Elab

namespace Aeneas.Std

open ScalarElab

/-!
# Overflowing Operations
-/

-- TODO: we should redefine this, in particular so that it doesn't live in the `Result` monad

def UScalar.overflowing_add {ty} (x y : UScalar ty) : UScalar ty × Bool :=
  (⟨ BitVec.ofNat _ (x.toNat + y.toNat) ⟩, 2^ty.numBits ≤ x.toNat + y.toNat)

def IScalar.overflowing_add (ty : IScalarTy) (x y : IScalar ty) : IScalar ty × Bool :=
  (⟨ BitVec.ofInt _ (x.toInt + y.toInt) ⟩,
     ¬ (-2^(ty.numBits -1) ≤ x.toInt + y.toInt ∧ x.toInt + y.toInt < 2^(ty.numBits-1)))

/- [core::num::{u8}::overflowing_add] -/
uscalar def core.num.«%S».overflowing_add := @UScalar.overflowing_add .«%S»

/- [core::num::{i8}::overflowing_add] -/
iscalar def core.num.«%S».overflowing_add := @IScalar.overflowing_add .«%S»

attribute [-simp] Bool.exists_bool

theorem UScalar.overflowing_add_eq {ty} (x y : UScalar ty) :
  let z := overflowing_add x y
  if x.toNat + y.toNat > UScalar.max ty then
    z.fst.toNat + UScalar.size ty = x.toNat + y.toNat ∧
    z.snd = true
  else
    z.fst.toNat = x.toNat + y.toNat ∧
    z.snd = false
  := by
  simp [overflowing_add]
  simp only [toNat, BitVec.toNat_ofNat, max]
  split <;> rename_i hLt
  . split_conjs
    . have : (x.toBitVec.toNat + y.toBitVec.toNat) % 2^ty.numBits =
             (x.toBitVec.toNat + y.toBitVec.toNat - 2^ty.numBits) % 2^ty.numBits := by
        rw [Nat.mod_eq_sub_mod]
        omega
      rw [this]; clear this

      have := @Nat.mod_eq_of_lt (x.toBitVec.toNat + y.toBitVec.toNat - 2^ty.numBits) (2^ty.numBits) (by omega)
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
  if x.toNat + y.toNat > UScalar.max .«%S» then z.fst.toNat + UScalar.size .«%S» = x.toNat + y.toNat ∧ z.snd = true
  else z.fst.toNat = x.toNat + y.toNat ∧ z.snd = false
  := UScalar.overflowing_add_eq x y

end Aeneas.Std
