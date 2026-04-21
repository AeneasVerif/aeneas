import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Misc
import Aeneas.Std.Scalar.Elab
import Aeneas.Tactic.Solver.ScalarTac
import Mathlib.Data.BitVec
import Mathlib.Data.Int.Init

namespace Aeneas.Std

open Result Error Arith ScalarElab WP

/-!
# Multiplication: Definitions
-/

def UScalar.mul {ty : UScalarTy} (x y : UScalar ty) : Result (UScalar ty) :=
  UScalar.tryMk ty (x.toNat * y.toNat)

def IScalar.mul {ty : IScalarTy} (x y : IScalar ty) : Result (IScalar ty) :=
  IScalar.tryMk ty (x.toInt * y.toInt)

def UScalar.try_mul {ty : UScalarTy} (x y : UScalar ty) : Option (UScalar ty) :=
  Option.ofResult (mul x y)

def IScalar.try_mul {ty : IScalarTy} (x y : IScalar ty) : Option (IScalar ty) :=
  Option.ofResult (mul x y)

class ResultMul (α : Type u) where
  mul : α → α → Result α

infixl:71 " *? " => ResultMul.mul

instance {ty} : ResultMul (UScalar ty) where
  mul x y := UScalar.mul x y

instance {ty} : ResultMul (IScalar ty) where
  mul x y := IScalar.mul x y

/-!
# Multiplication: Theorems
-/

/-!
Theorems with a specification which use integers and bit-vectors
-/

theorem UScalar.mul_equiv {ty} (x y : UScalar ty) :
  match mul x y with
  | ok z => x.toNat * y.toNat ≤ UScalar.max ty ∧ (↑z : Nat) = ↑x * ↑y ∧ z.toBitVec = x.toBitVec * y.toBitVec
  | fail _ => UScalar.max ty < x.toNat * y.toNat
  | .div => False := by
  simp only [mul]
  have := tryMk_eq ty (x.toNat * y.toNat)
  split <;> simp_all only [inBounds, true_and, not_lt, gt_iff_lt]
  simp_all only [tryMk, ofOption, tryMkOpt, check_bounds, decide_true, dite_true, ok.injEq]
  rename_i hEq; simp only [← hEq, ofNatCore, toNat]
  split_conjs
  . simp only [toBitVec_toNat, max]; omega
  . zify at this; zify; simp only [toBitVec_toNat, BitVec.toNat_ofFin, Nat.cast_mul, BitVec.toNat_mul,
    Int.natCast_emod, Nat.cast_pow, Nat.cast_ofNat] at *
    rw [Int.emod_eq_of_lt]
    . apply Int.pos_mul_pos_is_pos <;> simp
    . simp only [this]
  . have : 0 < 2^ty.numBits := by simp
    simp only [max, gt_iff_lt]
    omega

/-- Generic theorem - shouldn't be used much -/
theorem UScalar.mul_toBitVec_spec {ty} {x y : UScalar ty}
  (hmax : ↑x * ↑y ≤ UScalar.max ty) :
  x *? y ⦃ z => (↑z : Nat) = ↑x * ↑y ∧ z.toBitVec = x.toBitVec * y.toBitVec ⦄ := by
  have : x *? y = mul x y := by rfl
  have := mul_equiv x y
  split at this <;> simp_all [spec_ok, and_self, spec_fail]
  omega

theorem IScalar.mul_equiv {ty} (x y : IScalar ty) :
  match mul x y with
  | ok z => IScalar.min ty ≤ x.toInt * y.toInt ∧ x.toInt * y.toInt ≤ IScalar.max ty ∧ z.toInt = x.toInt * y.toInt ∧ z.toBitVec = x.toBitVec * y.toBitVec
  | fail _ => ¬(IScalar.min ty ≤ x.toInt * y.toInt ∧ x.toInt * y.toInt ≤ IScalar.max ty)
  | .div => False := by
  simp only [mul, not_and, not_le]
  have := tryMk_eq ty (x.toInt * y.toInt)
  split <;> simp_all only [inBounds, min, max, true_and, not_and, not_lt] <;>
  simp_all only [tryMk, ofOption, tryMkOpt, check_bounds, and_self, decide_true, dite_true,
    ok.injEq, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq] <;>
  rename_i hEq <;> simp only [← hEq, ofIntCore, toInt] <;>
  simp only [toBitVec_toInt_eq, ← BitVec.toInt_inj, BitVec.toInt_mul]
  . split_conjs
    . omega
    . simp only [BitVec.toInt, BitVec.toNat_ofFin, Int.ofNat_toNat, Nat.cast_pow, Nat.cast_ofNat,
      Int.bmod]
      have this : 2 * (x.toInt * y.toInt % 2 ^ ty.numBits).toNat < 2 ^ ty.numBits ↔
            x.toInt * y.toInt % 2 ^ ty.numBits < (2 ^ ty.numBits + 1) / 2 := by
        have hdiv : (2 : ℤ) ∣ 2 ^ ty.numBits := by
          have : ty.numBits = (ty.numBits - 1) + 1 := by
            have := ty.numBits_nonzero
            scalar_tac
          rw [this, Int.pow_succ]; simp
        have : (2^ty.numBits + 1 : Int) / 2 = 2^ty.numBits / 2 := by
          rw [Int.add_ediv_of_dvd_left]
          . simp
          . apply hdiv
        rw [this]; clear this
        have heq := @Int.div_lt_div_iff_of_dvd_of_pos (↑x * ↑y % 2 ^ ty.numBits) 1 (2 ^ ty.numBits) 2
          (by simp) (by simp) (by simp) hdiv
        simp only [EuclideanDomain.div_one, mul_one] at heq
        simp only [heq]
        have : (x.toInt * y.toInt % 2 ^ ty.numBits).toNat = x.toInt * y.toInt % 2 ^ ty.numBits := by
          scalar_tac
        scalar_tac
      simp only [this]
      split <;>
      simp_all only [iff_true, sup_eq_left, ge_iff_le, iff_false,
        not_lt, sub_left_inj, sup_eq_left] <;>
      omega
  . omega

/-- Generic theorem - shouldn't be used much -/
theorem IScalar.mul_toBitVec_spec {ty} {x y : IScalar ty}
  (hmin : IScalar.min ty ≤ ↑x * ↑y)
  (hmax : ↑x * ↑y ≤ IScalar.max ty) :
  x *? y ⦃ z => (↑z : Int) = ↑x * ↑y ∧ z.toBitVec = x.toBitVec * y.toBitVec ⦄ := by
  have : x *? y = mul x y := by rfl
  have := mul_equiv x y
  split at this <;> simp_all

uscalar theorem «%S».mul_bv_spec {x y : «%S»} (hmax : x.toNat * y.toNat ≤ «%S».max) :
  x *? y ⦃ z => (↑z : Nat) = ↑x * ↑y ∧ z.toBitVec = x.toBitVec * y.toBitVec ⦄ :=
  UScalar.mul_toBitVec_spec (by scalar_tac)

iscalar theorem «%S».mul_bv_spec {x y : «%S»}
  (hmin : «%S».min ≤ ↑x * ↑y) (hmax : ↑x * ↑y ≤ «%S».max) :
  x *? y ⦃ z => (↑z : Int) = ↑x * ↑y ∧ z.toBitVec = x.toBitVec * y.toBitVec ⦄ :=
  IScalar.mul_toBitVec_spec (by scalar_tac) (by scalar_tac)

/-!
Theorems with a specification which only use integers
-/

/-- Generic theorem - shouldn't be used much -/
theorem UScalar.mul_spec {ty} {x y : UScalar ty}
  (hmax : ↑x * ↑y ≤ UScalar.max ty) :
  x *? y ⦃ z => (↑z : Nat) = ↑x * ↑y ⦄ := by
  apply spec_mono
  apply UScalar.mul_toBitVec_spec hmax
  grind

/-- Generic theorem - shouldn't be used much -/
theorem IScalar.mul_spec {ty} {x y : IScalar ty}
  (hmin : IScalar.min ty ≤ ↑x * ↑y)
  (hmax : ↑x * ↑y ≤ IScalar.max ty) :
  x *? y ⦃ z => (↑z : Int) = ↑x * ↑y ⦄ := by
  apply spec_mono
  apply @IScalar.mul_toBitVec_spec ty x y (by scalar_tac) (by scalar_tac)
  grind

uscalar @[step] theorem «%S».mul_spec {x y : «%S»} (hmax : x.toNat * y.toNat ≤ «%S».max) :
  x *? y ⦃ z => (↑z : Nat) = ↑x * ↑y ⦄ :=
  UScalar.mul_spec (by scalar_tac)

iscalar @[step] theorem «%S».mul_spec {x y : «%S»}
  (hmin : «%S».min ≤ ↑x * ↑y) (hmax : ↑x * ↑y ≤ «%S».max) :
  (x *? y) ⦃ z => (↑z : Int) = ↑x * ↑y ⦄ :=
  IScalar.mul_spec (by scalar_tac) (by scalar_tac)

end Aeneas.Std
