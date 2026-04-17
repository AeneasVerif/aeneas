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
  UScalar.tryMk ty (x.val * y.val)

def IScalar.mul {ty : IScalarTy} (x y : IScalar ty) : Result (IScalar ty) :=
  IScalar.tryMk ty (x.val * y.val)

def UScalar.try_mul {ty : UScalarTy} (x y : UScalar ty) : Option (UScalar ty) :=
  Option.ofResult (mul x y)

def IScalar.try_mul {ty : IScalarTy} (x y : IScalar ty) : Option (IScalar ty) :=
  Option.ofResult (mul x y)

instance {ty} : HMul (UScalar ty) (UScalar ty) (Result (UScalar ty)) where
  hMul x y := UScalar.mul x y

instance {ty} : HMul (IScalar ty) (IScalar ty) (Result (IScalar ty)) where
  hMul x y := IScalar.mul x y

/-!
# Multiplication: Theorems
-/

/-!
Theorems with a specification which use integers and bit-vectors
-/

theorem UScalar.mul_equiv {ty} (x y : UScalar ty) :
  match mul x y with
  | ok z => x.val * y.val ≤ UScalar.max ty ∧ (↑z : Nat) = ↑x * ↑y ∧ z.bv = x.bv * y.bv
  | fail .integerOverflow => UScalar.max ty < x.val * y.val
  | _ => False := by
  simp only [mul]
  have := tryMk_eq ty (x.val * y.val)
  split <;> simp_all only [inBounds, true_and, not_lt, gt_iff_lt]
  simp_all only [tryMk, ofOption, tryMkOpt, check_bounds, decide_true, dite_true, ok.injEq]
  rename_i hEq; simp only [← hEq, ofNatCore, val]
  split_conjs
  . simp only [bv_toNat, max]; omega
  . zify at this; zify; simp only [bv_toNat, BitVec.toNat_ofFin, Nat.cast_mul, BitVec.toNat_mul,
    Int.natCast_emod, Nat.cast_pow, Nat.cast_ofNat] at *
    rw [Int.emod_eq_of_lt]
    . apply Int.pos_mul_pos_is_pos <;> simp
    . simp only [this]
  . have : 0 < 2^ty.numBits := by simp
    simp only [max, gt_iff_lt]
    omega

/-- Generic theorem - shouldn't be used much -/
theorem UScalar.mul_bv_spec {ty} {x y : UScalar ty}
  (hmax : ↑x * ↑y ≤ UScalar.max ty) :
  x * y ⦃ z => (↑z : Nat) = ↑x * ↑y ∧ z.bv = x.bv * y.bv ⦄ := by
  have : x * y = mul x y := by rfl
  have := mul_equiv x y
  split at this <;> simp_all [spec_ok, and_self, spec_fail]
  omega

theorem IScalar.mul_equiv {ty} (x y : IScalar ty) :
  match mul x y with
  | ok z => IScalar.min ty ≤ x.val * y.val ∧ x.val * y.val ≤ IScalar.max ty ∧ z.val = x.val * y.val ∧ z.bv = x.bv * y.bv
  | fail .integerOverflow => ¬(IScalar.min ty ≤ x.val * y.val ∧ x.val * y.val ≤ IScalar.max ty)
  | _ => False := by
  simp only [mul, not_and, not_le]
  have := tryMk_eq ty (x.val * y.val)
  split <;> simp_all only [inBounds, min, max, true_and, not_and, not_lt] <;>
  simp_all only [tryMk, ofOption, tryMkOpt, check_bounds, and_self, decide_true, dite_true,
    ok.injEq, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq] <;>
  rename_i hEq <;> simp only [← hEq, ofIntCore, val] <;>
  simp only [bv_toInt_eq, ← BitVec.toInt_inj, BitVec.toInt_mul]
  . split_conjs
    . omega
    . simp only [BitVec.toInt, BitVec.toNat_ofFin, Int.ofNat_toNat, Nat.cast_pow, Nat.cast_ofNat,
      Int.bmod]
      have this : 2 * (x.val * y.val % 2 ^ ty.numBits).toNat < 2 ^ ty.numBits ↔
            x.val * y.val % 2 ^ ty.numBits < (2 ^ ty.numBits + 1) / 2 := by
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
        have : (x.val * y.val % 2 ^ ty.numBits).toNat = x.val * y.val % 2 ^ ty.numBits := by
          scalar_tac
        scalar_tac
      simp only [this]
      split <;>
      simp_all only [iff_true, sup_eq_left, ge_iff_le, iff_false,
        not_lt, sub_left_inj, sup_eq_left] <;>
      omega
  . omega

/-- Generic theorem - shouldn't be used much -/
theorem IScalar.mul_bv_spec {ty} {x y : IScalar ty}
  (hmin : IScalar.min ty ≤ ↑x * ↑y)
  (hmax : ↑x * ↑y ≤ IScalar.max ty) :
  x * y ⦃ z => (↑z : Int) = ↑x * ↑y ∧ z.bv = x.bv * y.bv ⦄ := by
  have : x * y = mul x y := by rfl
  have := mul_equiv x y
  split at this <;> simp_all

uscalar theorem «%S».mul_bv_spec {x y : «%S»} (hmax : x.val * y.val ≤ «%S».max) :
  x * y ⦃ z => (↑z : Nat) = ↑x * ↑y ∧ z.bv = x.bv * y.bv ⦄ :=
  UScalar.mul_bv_spec (by scalar_tac)

iscalar theorem «%S».mul_bv_spec {x y : «%S»}
  (hmin : «%S».min ≤ ↑x * ↑y) (hmax : ↑x * ↑y ≤ «%S».max) :
  x * y ⦃ z => (↑z : Int) = ↑x * ↑y ∧ z.bv = x.bv * y.bv ⦄ :=
  IScalar.mul_bv_spec (by scalar_tac) (by scalar_tac)

/-!
Theorems with a specification which only use integers
-/

section mvcgen
open Std.Do
set_option mvcgen.warning false

/-- Generic theorem - shouldn't be used much -/
theorem UScalar.mul_mvcgen {ty} {x y : UScalar ty} {Q}
  (hmax : UScalar.max ty < ↑x * ↑y → (Q.2.1 .integerOverflow).down)
  (h : ∀ z : UScalar ty, (↑z : Nat) = ↑x * ↑y → (Q.1 z).down) :
  ⦃ ⌜ True ⌝ ⦄ (x * y) ⦃ Q ⦄ := by
  have heq := @UScalar.mul_equiv _ x y
  simp only [show UScalar.mul x y = x * y from rfl] at heq
  split at heq <;> try simp_all only []
    <;> (mvcgen; grind)

/-- Generic theorem - shouldn't be used much -/
theorem IScalar.mul_mvcgen {ty} {x y : IScalar ty} {Q}
  (hmin : ↑x * ↑y < IScalar.min ty → (Q.2.1 .integerOverflow).down)
  (hmax : IScalar.max ty < ↑x * ↑y → (Q.2.1 .integerOverflow).down)
  (h : ∀ z : IScalar ty, (↑z : Int) = ↑x * ↑y → (Q.1 z).down) :
  ⦃ ⌜ True ⌝ ⦄ (x * y) ⦃ Q ⦄ := by
  have heq := @IScalar.mul_equiv _ x y
  simp only [show IScalar.mul x y = x * y from rfl] at heq
  split at heq
    <;> try simp_all only [min, max]
    <;> (mvcgen; grind)

uscalar @[spec] theorem «%S».mul_mvcgen {Q} {x y : «%S»}
  (hmax : «%S».max < x.val * y.val → (Q.2.1 .integerOverflow).down)
  (h : ∀ z : «%S», (↑z : Nat) = ↑x * ↑y → (Q.1 z).down) :
  ⦃ ⌜ True ⌝ ⦄ (x * y) ⦃ Q ⦄ :=
  UScalar.mul_mvcgen (by scalar_tac) (fun _ _ => h _ (by scalar_tac))

iscalar @[spec] theorem «%S».mul_mvcgen {Q} {x y : «%S»}
  (hmin : ↑x * ↑y < «%S».min → (Q.2.1 .integerOverflow).down)
  (hmax : «%S».max < ↑x * ↑y → (Q.2.1 .integerOverflow).down)
  (h : ∀ z : «%S», (↑z : Int) = ↑x * ↑y → (Q.1 z).down) :
  ⦃ ⌜ True ⌝ ⦄ (x * y) ⦃ Q ⦄ :=
  IScalar.mul_mvcgen (by scalar_tac) (by scalar_tac) (fun _ _ => h _ (by scalar_tac))

end mvcgen

section step

/-- Generic theorem - shouldn't be used much -/
theorem UScalar.mul_spec {ty} {x y : UScalar ty}
  (hmax : ↑x * ↑y ≤ UScalar.max ty) :
  x * y ⦃ z => (↑z : Nat) = ↑x * ↑y ⦄ :=
  Result.spec_of_mvcgen (mul_mvcgen (by omega) (by simp))

/-- Generic theorem - shouldn't be used much -/
theorem IScalar.mul_spec {ty} {x y : IScalar ty}
  (hmin : IScalar.min ty ≤ ↑x * ↑y)
  (hmax : ↑x * ↑y ≤ IScalar.max ty) :
  x * y ⦃ z => (↑z : Int) = ↑x * ↑y ⦄ :=
  Result.spec_of_mvcgen (mul_mvcgen (by omega) (by omega) (by simp))

uscalar @[step] theorem «%S».mul_spec {x y : «%S»} (hmax : x.val * y.val ≤ «%S».max) :
  x * y ⦃ z => (↑z : Nat) = ↑x * ↑y ⦄ :=
  UScalar.mul_spec (by scalar_tac)

iscalar @[step] theorem «%S».mul_spec {x y : «%S»}
  (hmin : «%S».min ≤ ↑x * ↑y) (hmax : ↑x * ↑y ≤ «%S».max) :
  (x * y) ⦃ z => (↑z : Int) = ↑x * ↑y ⦄ :=
  IScalar.mul_spec (by scalar_tac) (by scalar_tac)

end step

end Aeneas.Std
