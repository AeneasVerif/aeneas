import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Misc
import Aeneas.Std.Scalar.Elab
import Aeneas.Tactic.Solver.ScalarTac
import Mathlib.Data.BitVec

namespace Aeneas.Std

open Result Error Arith ScalarElab WP

/-!
# Addition: Definitions
-/
def UScalar.add {ty : UScalarTy} (x y : UScalar ty) : Result (UScalar ty) :=
  UScalar.tryMk ty (x.toNat + y.toNat)

def IScalar.add {ty : IScalarTy} (x y : IScalar ty) : Result (IScalar ty) :=
  IScalar.tryMk ty (x.toInt + y.toInt)

def UScalar.try_add {ty : UScalarTy} (x y : UScalar ty) : Option (UScalar ty) :=
  Option.ofResult (add x y)

def IScalar.try_add {ty : IScalarTy} (x y : IScalar ty) : Option (IScalar ty) :=
  Option.ofResult (add x y)

instance {ty} : HAdd (UScalar ty) (UScalar ty) (Result (UScalar ty)) where
  hAdd x y := UScalar.add x y

instance {ty} : HAdd (IScalar ty) (IScalar ty) (Result (IScalar ty)) where
  hAdd x y := IScalar.add x y


/-!
# Addition: Theorems
-/

theorem UScalar.add_equiv {ty} (x y : UScalar ty) :
  match x + y with
  | ok z => x.toNat + y.toNat < 2^ty.numBits ∧
    z.toNat = x.toNat + y.toNat ∧
    z.toBitVec = x.toBitVec + y.toBitVec
  | fail _ => ¬ (UScalar.inBounds ty (x.toNat + y.toNat))
  | _ => ⊥ := by
  have : x + y = add x y := by rfl
  rw [this]
  simp [add]
  have h := tryMk_eq ty (↑x + ↑y)
  simp [inBounds] at h
  split at h <;> simp_all
  zify; simp
  zify at h
  have := @Int.emod_eq_of_lt (x.toNat + y.toNat) (2^ty.numBits) (by omega) (by omega)
  simp [*]

theorem IScalar.add_equiv {ty} (x y : IScalar ty) :
  match x + y with
  | ok z =>
    IScalar.inBounds ty (x.toInt + y.toInt) ∧
    z.toInt = x.toInt + y.toInt ∧
    z.toBitVec = x.toBitVec + y.toBitVec
  | fail _ => ¬ (IScalar.inBounds ty (x.toInt + y.toInt))
  | _ => ⊥ := by
  have : x + y = add x y := by rfl
  rw [this]
  simp [add]
  have h := tryMk_eq ty (↑x + ↑y)
  simp [inBounds] at h
  split at h <;> simp_all
  apply BitVec.eq_of_toInt_eq
  simp
  have := bmod_pow_numBits_eq_of_lt ty (x.toInt + y.toInt) (by omega) (by omega)
  simp [*]

/-!
Theorems about the addition, with a specification which uses
integers and bit-vectors.
-/

/-- Generic theorem - shouldn't be used much -/
theorem UScalar.add_toBitVec_spec {ty} {x y : UScalar ty}
  (hmax : ↑x + ↑y ≤ UScalar.max ty) :
  x + y ⦃ z => (↑z : Nat) = ↑x + ↑y ∧ z.toBitVec = x.toBitVec + y.toBitVec ⦄ := by
  have h := @add_equiv ty x y
  split at h <;> simp_all [max]
  have : 0 < 2^ty.numBits := by simp
  omega

/-- Generic theorem - shouldn't be used much -/
theorem IScalar.add_toBitVec_spec {ty}  {x y : IScalar ty}
  (hmin : IScalar.min ty ≤ ↑x + ↑y)
  (hmax : ↑x + ↑y ≤ IScalar.max ty) :
  x + y ⦃ z => (↑z : Int) = ↑x + ↑y ∧ z.toBitVec = x.toBitVec + y.toBitVec ⦄ := by
  have h := @add_equiv ty x y
  split at h <;> simp_all [min, max]
  omega

uscalar theorem «%S».add_bv_spec {x y : «%S»} (hmax : x.toNat + y.toNat ≤ «%S».max) :
  x + y ⦃ z => (↑z : Nat) = ↑x + ↑y ∧ z.toBitVec = x.toBitVec + y.toBitVec ⦄ :=
  UScalar.add_toBitVec_spec (by scalar_tac)

iscalar theorem «%S».add_bv_spec {x y : «%S»}
  (hmin : «%S».min ≤ ↑x + ↑y) (hmax : ↑x + ↑y ≤ «%S».max) :
  x + y ⦃ z => (↑z : Int) = ↑x + ↑y ∧ z.toBitVec = x.toBitVec + y.toBitVec ⦄ :=
  IScalar.add_toBitVec_spec (by scalar_tac) (by scalar_tac)

/-!
Theorems about the addition, with a specification which uses
only integers. Those are the most common to use, so we mark them with the
`step` attribute.
-/

/-- Generic theorem - shouldn't be used much -/
@[step]
theorem UScalar.add_spec {ty} {x y : UScalar ty}
  (hmax : ↑x + ↑y ≤ UScalar.max ty) :
  x + y ⦃ z => (↑z : Nat) = ↑x + ↑y ⦄ := by
  have h := @add_equiv ty x y
  split at h <;> simp_all [max]
  have : 0 < 2^ty.numBits := by simp
  omega

/-- Generic theorem - shouldn't be used much -/
@[step]
theorem IScalar.add_spec {ty} {x y : IScalar ty}
  (hmin : IScalar.min ty ≤ ↑x + ↑y)
  (hmax : ↑x + ↑y ≤ IScalar.max ty) :
  x + y ⦃ z => (↑z : Int) = ↑x + ↑y ⦄ := by
  have h := @add_equiv ty x y
  split at h <;> simp_all [min, max]
  omega

uscalar @[step] theorem «%S».add_spec {x y : «%S»} (hmax : x.toNat + y.toNat ≤ «%S».max) :
  x + y ⦃ z => (↑z : Nat) = ↑x + ↑y ⦄ :=
  UScalar.add_spec (by scalar_tac)

iscalar @[step] theorem «%S».add_spec {x y : «%S»}
  (hmin : «%S».min ≤ ↑x + ↑y) (hmax : ↑x + ↑y ≤ «%S».max) :
  x + y ⦃ z => (↑z : Int) = ↑x + ↑y ⦄ :=
  IScalar.add_spec (by scalar_tac) (by scalar_tac)

end Aeneas.Std
