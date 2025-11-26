import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Misc
import Aeneas.Std.Scalar.Elab
import Aeneas.ScalarTac
import Mathlib.Data.BitVec

namespace Aeneas.Std

open Result Error Arith ScalarElab

/-!
# Subtraction: Definitions
-/

def UScalar.sub {ty : UScalarTy} (x y : UScalar ty) : Result (UScalar ty) :=
  if x.val < y.val then fail .integerOverflow
  else ok ⟨ BitVec.ofNat _ (x.val - y.val) ⟩

def IScalar.sub {ty : IScalarTy} (x y : IScalar ty) : Result (IScalar ty) :=
  IScalar.tryMk ty (x.val - y.val)

def UScalar.try_sub {ty : UScalarTy} (x y : UScalar ty) : Option (UScalar ty) :=
  Option.ofResult (sub x y)

def IScalar.try_sub {ty : IScalarTy} (x y : IScalar ty) : Option (IScalar ty) :=
  Option.ofResult (sub x y)

instance {ty} : HSub (UScalar ty) (UScalar ty) (Result (UScalar ty)) where
  hSub x y := UScalar.sub x y

instance {ty} : HSub (IScalar ty) (IScalar ty) (Result (IScalar ty)) where
  hSub x y := IScalar.sub x y


/-!
# Subtraction: Theorems
-/

theorem UScalar.sub_equiv {ty} (x y : UScalar ty) :
  match x - y with
  | ok z =>
    y.val ≤ x.val ∧
    x.val = z.val + y.val ∧
    z.bv = x.bv - y.bv
  | fail _ => x.val < y.val
  | _ => ⊥ := by
  have : x - y = sub x y := by rfl
  simp [this, sub]
  dcases h : x.val < y.val <;> simp [h]
  simp_all
  simp only [UScalar.val]
  simp
  split_conjs
  . have: (x.val - y.val) % 2^ty.numBits = x.val - y.val := by
      have : 0 < 2^ty.numBits := by simp
      have := x.hBounds
      apply Nat.mod_eq_of_lt; omega
    simp [this]
    omega
  . zify; simp
    have : (x.val - y.val : Nat) = (x.val : Int) - y.val := by omega
    rw [this]; clear this
    ring_nf
    rw [Int.add_emod]
    have : ((2^ty.numBits - y.val) : Nat) % (2^ty.numBits : Int) =
           (- (y.val : Int)) % (2^ty.numBits : Int) := by
      have : (2^ty.numBits - y.val : Nat) = (2^ty.numBits : Int) - y.val := by
        have hBounds := y.hBounds
        zify at *; simp at *
        have : (2^ty.numBits : Nat) = (2^ty.numBits : Int) := by simp
        omega
      rw [this]
      -- TODO: Int.emod_sub_emod not in this version of mathlib
      have := Int.emod_add_emod (2^ty.numBits) (2^ty.numBits) (-y.val)
      ring_nf at this
      ring_nf
      rw [← this]
      simp
    rw [this]
    rw [← Int.add_emod]
    ring_nf

theorem IScalar.sub_equiv {ty} (x y : IScalar ty) :
  match x - y with
  | ok z =>
    IScalar.inBounds ty (x.val - y.val) ∧
    z.val = x.val - y.val ∧
    z.bv = x.bv - y.bv
  | fail _ => ¬ (IScalar.inBounds ty (x.val - y.val))
  | _ => ⊥ := by
  have : x - y = sub x y := by rfl
  simp [this, sub]
  have h := tryMk_eq ty (↑x - ↑y)
  simp [inBounds] at h
  split at h <;> simp_all
  apply BitVec.eq_of_toInt_eq
  simp
  have := bmod_pow_numBits_eq_of_lt ty (x.val - y.val) (by omega) (by omega)
  simp [*]

/-!
Theorems with a specification which uses integers and bit-vectors
-/

/- Generic theorem - shouldn't be used much -/
theorem UScalar.sub_bv_spec {ty} {x y : UScalar ty}
  (h : y.val ≤ x.val) :
  ∃ z, x - y = ok z ∧ z.val = x.val - y.val ∧ y.val ≤ x.val ∧ z.bv = x.bv - y.bv := by
  have h := @sub_equiv ty x y
  split at h <;> simp_all
  omega

/- Generic theorem - shouldn't be used much -/
theorem IScalar.sub_bv_spec {ty} {x y : IScalar ty}
  (hmin : IScalar.min ty ≤ ↑x - ↑y)
  (hmax : ↑x - ↑y ≤ IScalar.max ty) :
  ∃ z, x - y = ok z ∧ (↑z : Int) = ↑x - ↑y ∧ z.bv = x.bv - y.bv := by
  have h := @sub_equiv ty x y
  split at h <;> simp_all [min, max]
  omega

uscalar theorem «%S».sub_bv_spec {x y : «%S»} (h : y.val ≤ x.val) :
  ∃ z, x - y = ok z ∧ z.val = x.val - y.val ∧ y.val ≤ x.val ∧ z.bv = x.bv - y.bv :=
  UScalar.sub_bv_spec h

iscalar theorem «%S».sub_bv_spec {x y : «%S»}
  (hmin : «%S».min ≤ ↑x - ↑y) (hmax : ↑x - ↑y ≤ «%S».max) :
  ∃ z, x - y = ok z ∧ (↑z : Int) = ↑x - ↑y ∧ z.bv = x.bv - y.bv :=
  IScalar.sub_bv_spec (by scalar_tac) (by scalar_tac)

/-!
Theorems with a specification which only uses integers
-/

/- Generic theorem - shouldn't be used much -/
@[progress]
theorem UScalar.sub_spec {ty} {x y : UScalar ty}
  (h : y.val ≤ x.val) :
  ∃ z, x - y = ok z ∧ z.val = x.val - y.val ∧ y.val ≤ x.val := by
  have h := @sub_equiv ty x y
  split at h <;> simp_all
  omega

/- Generic theorem - shouldn't be used much -/
@[progress]
theorem IScalar.sub_spec {ty} {x y : IScalar ty}
  (hmin : IScalar.min ty ≤ ↑x - ↑y)
  (hmax : ↑x - ↑y ≤ IScalar.max ty) :
  ∃ z, x - y = ok z ∧ (↑z : Int) = ↑x - ↑y := by
  have h := @sub_equiv ty x y
  split at h <;> simp_all [min, max]
  omega

uscalar @[progress] theorem «%S».sub_spec {x y : «%S»} (h : y.val ≤ x.val) :
  ∃ z, x - y = ok z ∧ z.val = x.val - y.val ∧ y.val ≤ x.val :=
  UScalar.sub_spec h

iscalar @[progress] theorem «%S».sub_spec {x y : «%S»}
  (hmin : «%S».min ≤ ↑x - ↑y) (hmax : ↑x - ↑y ≤ «%S».max) :
  ∃ z, x - y = ok z ∧ (↑z : Int) = ↑x - ↑y :=
  IScalar.sub_spec (by scalar_tac) (by scalar_tac)

end Aeneas.Std
