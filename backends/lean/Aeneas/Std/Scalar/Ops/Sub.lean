import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Misc
import Aeneas.Std.Scalar.Elab
import Aeneas.Tactic.Solver.ScalarTac
import Mathlib.Data.BitVec

namespace Aeneas.Std

open Result Error Arith ScalarElab WP

/-!
# Subtraction: Definitions
-/

def UScalar.sub {ty : UScalarTy} (x y : UScalar ty) : Result (UScalar ty) :=
  if x.toNat < y.toNat then fail .integerOverflow
  else ok ⟨ BitVec.ofNat _ (x.toNat - y.toNat) ⟩

def IScalar.sub {ty : IScalarTy} (x y : IScalar ty) : Result (IScalar ty) :=
  IScalar.tryMk ty (x.toInt - y.toInt)

def UScalar.try_sub {ty : UScalarTy} (x y : UScalar ty) : Option (UScalar ty) :=
  Option.ofResult (sub x y)

def IScalar.try_sub {ty : IScalarTy} (x y : IScalar ty) : Option (IScalar ty) :=
  Option.ofResult (sub x y)

class ResultSub (α : Type u) where
  sub : α → α → Result α

infixl:65 " -? " => ResultSub.sub

instance {ty} : ResultSub (UScalar ty) where
  sub x y := UScalar.sub x y

instance {ty} : ResultSub (IScalar ty) where
  sub x y := IScalar.sub x y


/-!
# Subtraction: Theorems
-/

theorem UScalar.sub_equiv {ty} (x y : UScalar ty) :
  match x -? y with
  | ok z =>
    y.toNat ≤ x.toNat ∧
    x.toNat = z.toNat + y.toNat ∧
    z.toBitVec = x.toBitVec - y.toBitVec
  | fail _ => x.toNat < y.toNat
  | _ => ⊥ := by
  have : x -? y = sub x y := by rfl
  simp [this, sub]
  dcases h : x.toNat < y.toNat <;> simp [h]
  simp_all
  simp only [UScalar.toNat]
  simp
  split_conjs
  . have: (x.toNat - y.toNat) % 2^ty.numBits = x.toNat - y.toNat := by
      have : 0 < 2^ty.numBits := by simp
      have := x.hBounds
      apply Nat.mod_eq_of_lt; omega
    simp [this]
    omega
  . zify; simp
    have : (x.toNat - y.toNat : Nat) = (x.toNat : Int) - y.toNat := by omega
    rw [this]; clear this
    ring_nf
    rw [Int.add_emod]
    have : ((2^ty.numBits - y.toNat) : Nat) % (2^ty.numBits : Int) =
           (- (y.toNat : Int)) % (2^ty.numBits : Int) := by
      have : (2^ty.numBits - y.toNat : Nat) = (2^ty.numBits : Int) - y.toNat := by
        have hBounds := y.hBounds
        zify at *; simp at *
        have : (2^ty.numBits : Nat) = (2^ty.numBits : Int) := by simp
        omega
      rw [this]
      -- TODO: Int.emod_sub_emod not in this version of mathlib
      have := Int.emod_add_emod (2^ty.numBits) (2^ty.numBits) (-y.toNat)
      ring_nf at this
      ring_nf
      rw [← this]
      simp
    rw [this]
    rw [← Int.add_emod]
    ring_nf

theorem IScalar.sub_equiv {ty} (x y : IScalar ty) :
  match x -? y with
  | ok z =>
    IScalar.inBounds ty (x.toInt - y.toInt) ∧
    z.toInt = x.toInt - y.toInt ∧
    z.toBitVec = x.toBitVec - y.toBitVec
  | fail _ => ¬ (IScalar.inBounds ty (x.toInt - y.toInt))
  | _ => ⊥ := by
  have : x -? y = sub x y := by rfl
  simp [this, sub]
  have h := tryMk_eq ty (↑x - ↑y)
  simp [inBounds] at h
  split at h <;> simp_all
  apply BitVec.eq_of_toInt_eq
  simp
  have := bmod_pow_numBits_eq_of_lt ty (x.toInt - y.toInt) (by omega) (by omega)
  simp [*]

/-!
Theorems with a specification which uses integers and bit-vectors
-/

/- Generic theorem - shouldn't be used much -/
theorem UScalar.sub_toBitVec_spec {ty} {x y : UScalar ty}
  (h : y.toNat ≤ x.toNat) :
  x -? y ⦃ z => z.toNat = x.toNat - y.toNat ∧ y.toNat ≤ x.toNat ∧ z.toBitVec = x.toBitVec - y.toBitVec ⦄ := by
  have h := @sub_equiv ty x y
  split at h <;> simp_all
  omega

/- Generic theorem - shouldn't be used much -/
theorem IScalar.sub_toBitVec_spec {ty} {x y : IScalar ty}
  (hmin : IScalar.min ty ≤ ↑x - ↑y)
  (hmax : ↑x - ↑y ≤ IScalar.max ty) :
  x -? y ⦃ z => (↑z : Int) = ↑x - ↑y ∧ z.toBitVec = x.toBitVec - y.toBitVec ⦄ := by
  have h := @sub_equiv ty x y
  split at h <;> simp_all [min, max]
  omega

uscalar theorem «%S».sub_bv_spec {x y : «%S»} (h : y.toNat ≤ x.toNat) :
  x -? y ⦃ z => z.toNat = x.toNat - y.toNat ∧ y.toNat ≤ x.toNat ∧ z.toBitVec = x.toBitVec - y.toBitVec ⦄ :=
  UScalar.sub_toBitVec_spec h

iscalar theorem «%S».sub_bv_spec {x y : «%S»}
  (hmin : «%S».min ≤ ↑x - ↑y) (hmax : ↑x - ↑y ≤ «%S».max) :
  x -? y ⦃ z => (↑z : Int) = ↑x - ↑y ∧ z.toBitVec = x.toBitVec - y.toBitVec ⦄ :=
  IScalar.sub_toBitVec_spec (by scalar_tac) (by scalar_tac)

/-!
Theorems with a specification which only uses integers
-/

/- Generic theorem - shouldn't be used much -/
@[step]
theorem UScalar.sub_spec {ty} {x y : UScalar ty}
  (h : y.toNat ≤ x.toNat) :
  x -? y ⦃ z => z.toNat = x.toNat - y.toNat ∧ y.toNat ≤ x.toNat ⦄ := by
  have h := @sub_equiv ty x y
  split at h <;> simp_all
  omega

/- Generic theorem - shouldn't be used much -/
@[step]
theorem IScalar.sub_spec {ty} {x y : IScalar ty}
  (hmin : IScalar.min ty ≤ ↑x - ↑y)
  (hmax : ↑x - ↑y ≤ IScalar.max ty) :
  x -? y ⦃ z => (↑z : Int) = ↑x - ↑y ⦄ := by
  have h := @sub_equiv ty x y
  split at h <;> simp_all [min, max]
  omega

uscalar @[step] theorem «%S».sub_spec {x y : «%S»} (h : y.toNat ≤ x.toNat) :
  x -? y ⦃ z => z.toNat = x.toNat - y.toNat ∧ y.toNat ≤ x.toNat ⦄ :=
  UScalar.sub_spec h

iscalar @[step] theorem «%S».sub_spec {x y : «%S»}
  (hmin : «%S».min ≤ ↑x - ↑y) (hmax : ↑x - ↑y ≤ «%S».max) :
  x -? y ⦃ z => (↑z : Int) = ↑x - ↑y ⦄ :=
  IScalar.sub_spec (by scalar_tac) (by scalar_tac)

end Aeneas.Std
