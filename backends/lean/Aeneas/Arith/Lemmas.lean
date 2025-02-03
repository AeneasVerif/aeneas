import Aeneas.ScalarTac.IntTac
import Aeneas.ScalarTac.ScalarTac
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.RingTheory.Int.Basic

namespace Aeneas.ScalarTac

@[nonlin_scalar_tac n % m]
theorem Int.emod_of_pos_disj (n m : Int) : m ≤ 0 ∨ (0 ≤ n % m ∧ n % m < m) := by
  if h: 0 < m then
    right; constructor
    . apply Int.emod_nonneg; omega
    . apply Int.emod_lt_of_pos; omega
  else left; omega

@[nonlin_scalar_tac n / m]
theorem Int.div_of_pos_disj (n m : Int) : n < 0 ∨ m < 0 ∨ (0 ≤ n / m ∧ n / m ≤ n) := by
  dcases hn: 0 ≤ n <;> dcases hm: 0 ≤ m <;> try simp_all
  right; right; constructor
  . apply Int.ediv_nonneg <;> omega
  . apply Int.ediv_le_self; omega

theorem Int.pos_mul_pos_is_pos (n m : Int) (hm : 0 ≤ m) (hn : 0 ≤ n): 0 ≤ m * n := by
  have h : (0 : Int) = 0 * 0 := by simp
  rw [h]
  apply mul_le_mul <;> norm_cast

@[nonlin_scalar_tac m * n]
theorem Int.pos_mul_pos_is_pos_disj (n m : Int) : m < 0 ∨ n < 0 ∨ 0 ≤ m * n := by
  cases h: (m < 0 : Bool) <;> simp_all
  cases h: (n < 0 : Bool) <;> simp_all
  right; right; apply pos_mul_pos_is_pos <;> tauto

-- Some tests
section

  -- Activate the rule set for non linear arithmetic
  set_option scalarTac.nonLin true

  example (x y : Int) (h : 0 ≤ x ∧ 0 ≤ y) : 0 ≤ x * y := by scalar_tac
  example (x y : Int) (h : 0 ≤ x ∧ 0 ≤ y) : 0 ≤ x / y := by scalar_tac

end

/-!
We list here a few arithmetic facts that are not in Mathlib.

TODO: PR for Mathlib?
-/

-- TODO: this should be in mathlib
theorem Int.gcd_add_mul_self (a b k : ℤ) :
  Int.gcd a (b + k * a) = Int.gcd a b := by
  apply Eq.symm
  have h := @Int.gcd_greatest a (b + k * a) (Int.gcd a b) (by simp)
  simp only [Nat.cast_inj] at h
  apply h
  . apply Int.gcd_dvd_left
  . apply dvd_add
    . apply Int.gcd_dvd_right
    . rw [dvd_mul]
      exists 1, gcd a b
      simp only [isUnit_one, IsUnit.dvd, one_mul, true_and]
      split_conjs
      apply Int.gcd_dvd_left
      rfl
  . intro e div_a div_bk
    have div_ka : e ∣ k * a := by
      rw [dvd_mul]
      exists 1, e
      simp [*]
    have div_b : e ∣ b := by
      have h : e ∣ (b + k * a) + (- k * a) := by
        apply dvd_add <;> simp [*]
      simp only [neg_mul, add_neg_cancel_right] at h
      apply h
    apply Int.dvd_gcd <;> assumption

-- TODO: this should be in mathlib
theorem Int.gcd_mod_same {a b : ℤ} :
  Int.gcd (a % b) b = Int.gcd a b := by
  have h1 : a % b = a - b * (a / b) := by
    have heq := Int.ediv_add_emod a b
    linarith
  have h2 := Int.gcd_add_mul_self b a (- (a / b))
  rw [h1]
  simp only [neg_mul] at h2
  conv at h2 => lhs; rw [Int.gcd_comm]
  conv => rhs; rw [Int.gcd_comm]
  convert h2 using 2
  ring_nf

theorem cancel_right_div_gcd_pos {m a b : ℤ}
  (c : Int) (hm : 0 < m) (hgcd : Int.gcd m c = 1)
  (h : (a * c) % m = (b * c) % m) :
  a % m = b % m := by
  have heq := Int.ModEq.cancel_right_div_gcd hm h
  simp only [hgcd, Nat.cast_one, EuclideanDomain.div_one] at heq
  apply heq

theorem cancel_right_div_gcd {m : ℤ} (a b c : Int) (hgcd : Int.gcd c m = 1)
  (h : (a * c) % m = (b * c) % m) :
  a % m = b % m := by
  rw [Int.gcd_comm] at hgcd
  if hm : m = 0 then
    simp_all only [Int.gcd_zero_left, EuclideanDomain.mod_zero, mul_eq_mul_right_iff]
    dcases hc : c = 0 <;> simp_all
  else
    if m ≤ 0 then
      have hm' : 0 < -m := by int_tac
      have hgcd' : Int.gcd (-m) c = 1 := by simp [hgcd]
      have hf := @cancel_right_div_gcd_pos (-m) a b c hm' hgcd'
      simp only [Int.emod_neg] at hf
      apply hf
      assumption
    else
      have hm : 0 < m := by simp_all
      have heq := Int.ModEq.cancel_right_div_gcd hm h
      simp only [hgcd, Nat.cast_one, EuclideanDomain.div_one] at heq
      apply heq

theorem cancel_left_div_gcd {m : ℤ} (a b c : Int) (hgcd : Int.gcd c m = 1)
  (h : (c * a) % m = (c * b) % m) :
  a % m = b % m := by
  have heq := cancel_right_div_gcd a b c hgcd
  apply heq
  ring_nf at *
  apply h

theorem times_mod_imp_div_mod (n : ℕ) (a b c : ℤ)
  (hdiv : a % b = 0)
  (hgcd : Int.gcd b n = 1)
  (heq : a % n = (c * b) % n) :
  (a / b) % n = c % n := by
  -- step 1: multiply by b on both sides
  apply (cancel_right_div_gcd (a / b) c b (by assumption))
  -- step 2: simplify (... / b) * b
  rw [Int.ediv_mul_cancel_of_emod_eq_zero hdiv]
  -- End of the proof
  apply heq

/-!
Some theorems to reason about equalities of the shape: `a % n = b % n`.

When encoutering such an equality a good proof strategy is to simply cast the integers into
`ZMod` which, being a ring, is convenient to work in. Below, we list a few simp theorems which
are necessary for this to work.
-/
theorem ZMod_int_cast_eq_int_cast_iff (n : ℕ) (a b : ℤ) :
  ((a : ZMod n) = (b : ZMod n)) ↔ (a % n = b % n) :=
  ZMod.intCast_eq_intCast_iff a b n

/-- The important theorem to convert a goal about equality modulo into a goal about the equalit of two terms in `ZMod` -/
theorem ZMod_eq_imp_mod_eq {n : ℕ} {a b : ℤ}
  (h : (a : ZMod n) = (b : ZMod n)) :
  a % n = b % n :=
  (@ZMod_int_cast_eq_int_cast_iff n a b).mp h

theorem mod_eq_imp_ZMod_eq {n : ℕ} {a b : ℤ}
  (h : a % n = b % n) :
  (a : ZMod n) = (b : ZMod n) :=
  (@ZMod_int_cast_eq_int_cast_iff n a b).mpr h

theorem ZMod_val_injective {n : ℕ} [NeZero n] {a b : ZMod n} (h : a.val = b.val) :
  a = b :=
  ZMod.val_injective n h

theorem ZMod.mul_inv_eq_int_gcd {n : ℕ} (a : ℤ) :
  (a : ZMod n) * (a : ZMod n)⁻¹ = Int.gcd a n := by
  if hn : n = 0 then
    simp only [hn, CharP.cast_eq_zero, Int.gcd_zero_right]
    rw [ZMod.mul_inv_eq_gcd]
    simp only [hn, Nat.gcd_zero_right]

    have h := @ZMod.intCast_eq_intCast_iff' (ZMod.val (a : ZMod n)) (Int.natAbs a) n
    simp only [Int.cast_natCast, Int.natCast_natAbs, hn, CharP.cast_eq_zero,
      EuclideanDomain.mod_zero] at h
    unfold ZMod.val
    rw [hn]
    simp only [Nat.cast_inj]
    rfl
  else
    have hn : 0 < n := by cases n <;> simp_all only [AddLeftCancelMonoid.add_eq_zero, one_ne_zero,
      and_false, not_false_eq_true, lt_add_iff_pos_left, add_pos_iff,
      zero_lt_one, or_true, not_true_eq_false]
    rw [ZMod.mul_inv_eq_gcd]
    rw [← Int.gcd_natCast_natCast]
    have hnz : NeZero n := by simp [neZero_iff, *]
    rw [← ZMod.cast_eq_val]
    -- Simplify `↑↑a`
    rw [ZMod.coe_intCast]
    rw [Int.gcd_mod_same]

/-- A theorem to work with division when converting integers to elements of `ZMod` -/
theorem div_to_ZMod {n : ℕ} {a b : ℤ} [NeZero n] (hDiv : b ∣ a) (hgcd : Int.gcd b n = 1) :
  ((a / b) : ZMod n) = (a : ZMod n) * (b : ZMod n)⁻¹ := by
  have h : (a / b) % (n : Int) = ((a % (n : Int)) * (b : ZMod n)⁻¹.cast) % (n : Int) := by
    apply times_mod_imp_div_mod
    . rw [← Int.dvd_iff_emod_eq_zero]
      assumption
    . assumption
    . apply ZMod_eq_imp_mod_eq
      simp only [Int.cast_mul, ZMod.intCast_mod, ZMod.intCast_cast, ZMod.cast_id', id_eq]
      rw [mul_assoc]
      have := @ZMod.mul_inv_eq_int_gcd n b
      rw [mul_comm] at this
      rw [this]
      rw [hgcd]
      simp
  have h1 := mod_eq_imp_ZMod_eq h
  rw [h1]
  simp

theorem bmod_eq_emod_eq_iff (n: ℕ) (a b: ℤ) :
  (a % n = b % n) ↔ (Int.bmod a n = Int.bmod b n) := by
  simp only [Int.bmod]
  apply Iff.intro <;> intro h
  . rw [h]
  . if h_a: a % n < (n + 1) / 2 then
      if h_b: b % n < (n + 1) / 2 then
        simp only [h_a, ↓reduceIte, h_b] at h
        exact h
      else
        simp only [h_a, ↓reduceIte, h_b] at h
        have ha' : 0 ≤ a % n := by apply Int.emod_nonneg; linarith
        have hb' : b % n - n < 0 := by
          have h : b % n < n := by apply Int.emod_lt_of_pos; linarith
          linarith
        linarith
    else
      if h_b: b % n < (n + 1) / 2 then
        simp only [h_a, ↓reduceIte, h_b] at h
        have ha' : 0 ≤ b % n := by apply Int.emod_nonneg; linarith
        have hb' : a % n - n < 0 := by
          have h : a % n < n := by apply Int.emod_lt_of_pos; linarith
          linarith
        linarith
      else
        simp only [h_a, ↓reduceIte, h_b, sub_left_inj] at h
        exact h

theorem ZMod_int_cast_eq_int_cast_bmod_iff (n : ℕ) (a b : ℤ) :
  ((a : ZMod n) = (b : ZMod n)) ↔ (Int.bmod a n = Int.bmod b n) := by
  apply Iff.trans
  apply ZMod_int_cast_eq_int_cast_iff
  apply bmod_eq_emod_eq_iff

theorem ZMod_eq_imp_bmod_eq {n : ℕ} {a b : ℤ}
  (h : (a : ZMod n) = (b : ZMod n)) :
  Int.bmod a n = Int.bmod b n :=
  (@ZMod_int_cast_eq_int_cast_bmod_iff n a b).mp h

end Aeneas.ScalarTac
