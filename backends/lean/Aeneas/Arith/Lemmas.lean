import Aeneas.ScalarTac.ScalarTac
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.RingTheory.Int.Basic
import Init.Data.Int.DivModLemmas
import Init.Data.BitVec.Lemmas

namespace Aeneas.Arith

/-- Small helper

    We used to use this for the list definitions, as some definitions like `index` used to
    manipulate integers and not natural numbers.

    We cover a set of cases which might imply inequality, to make sure that using
    this as the precondition of a `simp` lemma will allow the lemma to get correctly
    triggered.
    TODO: there should be something more systematic to do, with discharged procedures
    or simprocs I guess. -/
@[simp]
abbrev Int.not_eq (i j : Int) : Prop :=
  i ≠ j ∨ j ≠ i ∨ i < j ∨ j < i

theorem Int.not_eq_imp_not_eq {i j} : Int.not_eq i j → i ≠ j := by
  intro h g
  simp_all

@[simp]
abbrev Nat.not_eq (i j : Nat) : Prop :=
  i ≠ j ∨ j ≠ i ∨ i < j ∨ j < i

theorem Nat.not_eq_imp_not_eq {i j} : Nat.not_eq i j → i ≠ j := by
  intro h g
  simp_all


@[nonlin_scalar_tac n % m]
theorem Nat.mod_zero_or_lt (n m : Nat) : m = 0 ∨ (n % m < m) := by
  dcases h: m = 0
  . simp [h]
  . right
    apply Nat.mod_lt; omega

@[nonlin_scalar_tac n / m]
theorem Nat.div_zero_or_le (n m : Nat) : m = 0 ∨ (n / m ≤ n) := by
  dcases h: m = 0 <;> simp [*]
  apply Nat.div_le_self

theorem Int.self_le_ediv {x y : ℤ} (hx : x ≤ 0) (hy : 0 ≤ y) :
  x ≤ x / y := by
  dcases x <;> dcases y
  . simp_all
  . simp_all
  . rename_i x y
    rw [HDiv.hDiv, instHDiv]
    simp only [Div.div]
    rw [Int.ediv.eq_def]
    dcases y <;> simp only
    . omega
    . rename_i y
      have := @Nat.div_le_self x y.succ
      omega
  . simp_all

@[nonlin_scalar_tac n % m]
theorem Int.emod_neg_or_pos_lt (n m : Int) : m ≤ 0 ∨ (0 ≤ n % m ∧ n % m < m) := by
  if h: 0 < m then
    right; constructor
    . apply Int.emod_nonneg; omega
    . apply Int.emod_lt_of_pos; omega
  else left; omega

@[nonlin_scalar_tac n / m]
theorem Int.div_neg_or_pos_le (n m : Int) : n < 0 ∨ m < 0 ∨ (0 ≤ n / m ∧ n / m ≤ n) := by
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

@[scalar_tac b.toNat]
theorem Bool.toNat_eq (b : Bool) :
  (b = true ∧ b.toNat = 1) ∨ (b = false ∧ b.toNat = 0) := by
  cases b <;> simp

-- Some tests
section
  example (x y : Int) (h : 0 ≤ x ∧ 0 ≤ y) : 0 ≤ x * y := by scalar_tac +nonLin
  example (x y : Int) (h : 0 ≤ x ∧ 0 ≤ y) : 0 ≤ x / y := by scalar_tac +nonLin

end

theorem Int.le_div_eq_bound_imp_eq {x y bound : Int}
  (hx : 0 < x) (hBound : x ≤ bound) (hy : 0 < y) (hEq : x / y = bound) :
  x = bound ∧ y = 1 := by
  have hx : x = bound := by
    by_contra
    have : x < bound := by omega
    have := @Int.ediv_le_self x y (by omega)
    omega
  have hy : y = 1 := by
    by_contra
    have hLe := @Nat.div_le_div x.toNat bound.toNat y.toNat 2 (by omega) (by omega) (by simp)
    zify at hLe
    have : x.toNat = x := by omega
    rw [this] at hLe
    have : y.toNat = y := by omega
    rw [this] at hLe
    have : bound.toNat = bound := by omega
    rw [this] at hLe
    have : bound / 2 < bound := by
      rw [Int.ediv_lt_iff_lt_mul] <;> omega
    omega
  simp [hx, hy]

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
      have hm' : 0 < -m := by scalar_tac
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

theorem ZMod_nat_cast_eq_nat_cast_iff (n : ℕ) (a b : ℕ) :
  ((a : ZMod n) = (b : ZMod n)) ↔ (a % n = b % n) := by
  zify
  have := ZMod_int_cast_eq_int_cast_iff n a b
  simp at this
  apply this

theorem Nat.eq_mod_iff_eq_ZMod (n : ℕ) (a b : Nat) :
  (a % n = b % n) ↔ ((a : ZMod n) = (b : ZMod n)) := by
  rw [ZMod.natCast_eq_natCast_iff a b n]
  tauto

theorem Int.eq_mod_iff_eq_ZMod (n : ℕ) (a b : ℤ) :
  (a % n = b % n) ↔ ((a : ZMod n) = (b : ZMod n)) := by
  rw [ZMod.intCast_eq_intCast_iff a b n]
  tauto

/-- The important theorem to convert a goal about equality modulo into a goal about the equalit of two terms in `ZMod` -/
theorem ZMod_eq_imp_mod_eq {n : ℕ} {a b : ℤ}
  (h : (a : ZMod n) = (b : ZMod n)) :
  a % n = b % n :=
  (@ZMod_int_cast_eq_int_cast_iff n a b).mp h

theorem ZMod_nat_eq_imp_mod_eq {n : ℕ} {a b : Nat} (h : (a : ZMod n) = (b : ZMod n)) :
  a % n = b % n := by
  zify
  apply ZMod_eq_imp_mod_eq
  simp [*]

theorem Int.mod_eq_imp_ZMod_eq {n : ℕ} {a b : ℤ}
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
theorem div_to_ZMod {n : ℕ} {a : ℤ} {b : Nat} [NeZero n]
  (hDiv : (a : ZMod b) = 0) (hgcd : Int.gcd b n = 1) :
  ((a / (b : Int)) : ZMod n) = (a : ZMod n) * (b : ZMod n)⁻¹ := by
  have h : (a / b) % (n : Int) = ((a % (n : Int)) * (b : ZMod n)⁻¹.cast) % (n : Int) := by
    apply times_mod_imp_div_mod
    . have h : (0 : Int) = 0 % b := by simp
      rw [h]
      apply ZMod_eq_imp_mod_eq
      rw [hDiv]
      simp
    . assumption
    . apply ZMod_eq_imp_mod_eq
      simp only [Int.cast_mul, ZMod.intCast_mod, ZMod.intCast_cast, ZMod.cast_id', id_eq]
      rw [mul_assoc]
      have := @ZMod.mul_inv_eq_int_gcd n b
      norm_cast at *
      rw [mul_comm] at this
      rw [this]
      rw [hgcd]
      simp
  have h1 := Int.mod_eq_imp_ZMod_eq h
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


theorem ZMod.castInt_val_sub {n : ℕ} [inst: NeZero n] {a b : ZMod n} :
  (a - b).val = (a.val - (b.val : Int)) % n := by
  have : 0 ≤ ((a.val : Int) - (b.val : Int)) % n := by
    apply Int.emod_nonneg
    cases inst
    omega
  have : ((a.val : Int) - (b.val : Int)) % n < n := by
    apply Int.emod_lt_of_pos
    cases inst
    omega
  have := ZMod.val_add a (-b)
  ring_nf at this
  rw [this]
  push_cast
  rw [Int.eq_mod_iff_eq_ZMod]
  simp
  ring_nf

theorem ZMod.eq_iff_mod (p : ℕ) [NeZero p] (x y : ZMod p) :
  x = y ↔ x.val = y.val := by
  constructor
  . simp +contextual
  . apply ZMod_val_injective

@[simp]
theorem ZMod.val_sub' {n : ℕ} [NeZero n] (a b : ZMod n) : (a - b).val =
  (a.val + (n - b.val)) % n := by
  have : a - b = a + (n - b) := by
    have : (n : ZMod n) = 0 := by simp
    rw [this]
    ring_nf
  rw [this]
  simp only [ZMod.val_add]
  have : ((n : ZMod n) - b).val = (n - b.val) % n := by
    dcases hb : b = 0
    . simp only [CharP.cast_eq_zero, sub_self, ZMod.val_zero, tsub_zero, Nat.mod_self, hb]
    . have : NeZero b := by constructor; simp [*]
      have h0 : (n - b).val = n - b.val := by simp [ZMod.val_neg_of_ne_zero]
      have h1 := @ZMod.val_lt n _ (n - b)
      simp only [h0]
      rw [eq_comm]
      apply Nat.mod_eq_of_lt
      omega
  rw [this]
  simp only [Nat.add_mod_mod]
theorem BitVec.toNat_neq {n : ℕ} {x y : BitVec n} : x ≠ y ↔ x.toNat ≠ y.toNat := by
  simp [BitVec.toNat_eq]

/-!
Below we mark some theorems as `zify_simps` so that `zify` can convert (in-)equalities about
`BitVec` and `ZMod` to (in-)equalities about ℤ.
-/
-- TODO: those theorems should rather be "natify" (introduce a tactic)
attribute [zify_simps] BitVec.toNat_eq BitVec.toNat_neq BitVec.lt_def BitVec.le_def
                       BitVec.toNat_umod BitVec.toNat_add BitVec.toNat_sub BitVec.toNat_ofNat
                       BitVec.toNat_and BitVec.toNat_or BitVec.toNat_xor
attribute [zify_simps] ZMod.eq_iff_mod ZMod.val_intCast ZMod.val_add ZMod.val_sub ZMod.val_mul
                       ZMod.castInt_val_sub

theorem Int.bmod_pow2_eq_of_inBounds (n : ℕ) (x : Int)
  (h0 : - 2 ^ n ≤ x)
  (h1 : x < 2 ^ n) :
  Int.bmod x (2 ^ (n + 1)) = x := by
  rw [Int.bmod]
  have hPowEq : (2^(n+1) : Int) = 2* (2^n) := by rw [Int.pow_succ']
  have : (2^(n + 1) + 1) / 2 = (2^n : Int)  := by
    have := @Int.add_ediv_of_dvd_left (2^(n+1)) 1 2 (by simp [hPowEq])
    simp [this]
    rw [hPowEq]
    simp
  dcases hpos : 0 ≤ x
  . have : x % (2^(n + 1) : Int) = x := by
      apply Int.emod_eq_of_lt <;> omega
    simp [this]
    omega
  . simp at hpos
    have : x % (2^(n + 1) : Int) = x + 2^(n + 1) := by
      have : 0 ≤ x + 2^(n+1) := by omega
      have : x + 2^(n+1) < 2^(n+1) := by omega
      have := @Int.emod_eq_of_lt (x + 2^(n + 1)) (2^(n+1)) (by omega) (by omega)
      rw [← this]
      have := Int.eq_mod_iff_eq_ZMod (2^(n+1))
      simp at this
      rw [this]
      simp
      norm_cast
      simp
    simp [this]
    omega

theorem Int.bmod_pow2_eq_of_inBounds' (n : ℕ) (x : Int)
  (hn : n ≠ 0)
  (h0 : - 2 ^ (n - 1) ≤ x)
  (h1 : x < 2 ^ (n - 1)) :
  Int.bmod x (2 ^ n) = x := by
  have h := Int.bmod_pow2_eq_of_inBounds (n - 1) x
  have : n - 1 + 1 = n := by omega
  simp [this] at h
  apply h <;> omega

theorem Int.bmod_pow2_bounds (n : ℕ) (x : Int) :
  - 2^(n-1) ≤ Int.bmod x (2^n) ∧ Int.bmod x (2^n) < 2^(n-1) := by
  have h0 : 0 < 2^n := by simp

  have := @Int.le_bmod x (2^n) h0
  have := @Int.bmod_lt x (2^n) h0

  have : -2^(n-1) ≤ -(((2^n) : Nat) : Int)/2 := by
    dcases hn : n = 0
    . simp [hn]
    . have : n - 1 + 1 = n := by omega
      conv => rhs; rw [← this]
      rw [Nat.pow_succ]
      simp

  have : 2^(n-1) ≤ (2^n + 1) / 2 := by
    dcases hn : n = 0
    . simp [hn]
    . have : n - 1 + 1 = n := by omega
      conv => rhs; rw [← this]
      rw [Nat.pow_succ']
      have := @Nat.add_div_of_dvd_right (2 * 2 ^ (n - 1)) 1 2 (by simp)
      rw [this]
      simp

  omega

theorem BitVec.bounds (n : ℕ) (x : BitVec n) :
  - 2^(n-1) ≤ x.toInt ∧ x.toInt < 2^(n-1) := by
  rw [BitVec.toInt_eq_toNat_bmod]
  apply Int.bmod_pow2_bounds


theorem BitVec.toInt_neg_of_neg_eq_neg
  {n} (x : BitVec n) (h : n ≠ 0) (h0 : - 2^(n - 1) < x.toInt) (h1 : x.toInt < 0) :
  (-x).toInt = - x.toInt := by
  simp only [BitVec.toInt_eq_toNat_bmod, BitVec.toNat_umod]

  have hmsb := @BitVec.msb_eq_toInt _ x
  simp [h1] at hmsb

  have hmsb' := @BitVec.msb_eq_toNat _ x
  simp [hmsb] at hmsb'

  have hx := @BitVec.toInt_eq_msb_cond _ x
  simp [hmsb] at hx

  simp only [Int.bmod]

  have : x.toNat < 2^n := by cases x; simp

  have hPow : (2 ^ n + 1) / 2 = 2^(n - 1) := by
    have : n = n - 1 + 1 := by omega
    conv => lhs; rw [this]
    rw [Nat.pow_succ']
    rw [Nat.add_div_of_dvd_right] <;> simp

  have : (2^n : Nat) = (2^n: Int) := by simp -- TODO: this is annoying!

  have hxToNatModPow : (x.toNat : Int) % 2^n = x.toNat := by
    apply Int.emod_eq_of_lt <;> omega

  have hPowMinusXMod : ↑(2 ^ n - x.toNat : Nat) % (2 ^ n : Int) =
         (2 ^ n - x.toNat : Nat) := by
    apply Int.emod_eq_of_lt <;> omega

  have : (((-x).toNat : Int) % (2 ^ n : Nat) < ((2 ^ n : Nat) + 1 : Int) / 2) := by
    simp
    zify at hPow
    simp [hPow]
    rw [hPowMinusXMod]
    omega
  simp only [this]; simp

  have : ¬ ((↑(x.toNat : Nat) % 2 ^ n : Int) < (2 ^ n + 1) / 2) := by
    simp
    zify at hPow
    simp [hPow]
    omega
  simp only [this]; simp

  rw [hPowMinusXMod]

  rw [hxToNatModPow]

  omega

theorem BitVec.toInt_neg_of_pos_eq_neg
  {n} (x : BitVec n) (h : n ≠ 0) (h0 : 0 ≤ x.toInt) :
  (-x).toInt = - x.toInt := by
  simp only [BitVec.toInt_eq_toNat_bmod, BitVec.toNat_umod]

  have : -2^(n-1) ≤ x.toInt ∧ x.toInt < 2^(n-1) := by
    apply BitVec.bounds

  have hNotNeg : ¬ x.toInt < 0 := by omega

  have hmsb := @BitVec.msb_eq_toInt _ x
  simp [hNotNeg] at hmsb

  have hmsb' := @BitVec.msb_eq_toNat _ x
  simp [hmsb] at hmsb'

  have hx := @BitVec.toInt_eq_msb_cond _ x
  simp [hmsb] at hx

  simp
  have h2n : (2^n: Int) = (2^n:Nat) := by simp -- TODO: this is annoying
  rw [h2n]
  rw [Int.emod_bmod]

  have : (2^n - x.toNat : Nat) = (2^n - x.toNat : Int) := by omega
  rw [this]; clear this

  have hn : n - 1 + 1 = n := by omega

  have : (2^n - x.toNat : Int).bmod (2^n) = (-(x.toNat : Int)).bmod (2^n) := by
    rw [h2n]
    have : (2^n : Nat) - (x.toNat : Int) = -(x.toNat : Int) + (2^n : Nat) := by ring_nf
    rw [this]
    simp only [Int.bmod_add_cancel]
  rw [this]; clear this

  have : (-(x.toNat : Int)).bmod (2^n) = -(x.toNat) := by
    have := Int.bmod_pow2_eq_of_inBounds (n - 1) (-x.toNat) (by omega) (by omega)
    rw [hn] at this
    omega
  rw [this]; clear this

  have : (x.toNat : Int).bmod (2^n) = x.toNat := by
    have := Int.bmod_pow2_eq_of_inBounds (n - 1) x.toNat (by omega) (by omega)
    rw [hn] at this
    omega
  rw [this]

@[simp]
theorem Int.neg_tmod (x y : Int) : (- x).tmod y = - x.tmod y := by
  unfold Int.tmod
  dcases hx' : (-x) <;> dcases hx : x <;> dcases y <;> rename_i xn xn' yn <;> simp only
  . dcases xn <;> simp_all
    omega
  . dcases xn <;> simp_all
    omega
  . simp
    have : xn = xn' + 1 := by
      have : x = - Int.ofNat xn := by omega
      simp at this
      omega
    simp [this]
  . simp
    have : xn = xn' + 1 := by
      have : x = - Int.ofNat xn := by omega
      simp at this
      omega
    simp [this]
  . simp
    have : (xn + 1 : Int) = xn' := by
      have : x = - Int.negSucc xn := by omega
      simp at this
      have : x = xn + 1 := by omega
      simp at hx
      omega
    simp [this]
  . simp
    have : (xn + 1 : Int) = xn' := by
      have : x = - Int.negSucc xn := by omega
      simp at this
      have : x = xn + 1 := by omega
      simp at hx
      omega
    simp [this]
  . dcases xn <;> simp_all
    omega
  . dcases xn <;> simp_all
    omega

theorem Int.tmod_ge_of_neg (x y : Int) (hx : x < 0) :
  x ≤ x.tmod y := by
  have : (-x).tmod y = (-x) % y := by
    dcases hy : 0 ≤ y
    . rw [Int.tmod_eq_emod] <;> try omega
    . have : (-x).tmod y = (-x).tmod (-y) := by simp
      rw [this]
      rw [Int.tmod_eq_emod] <;> try omega
      simp
  have : x.tmod y = - ((-x) % y) := by
    have h : x.tmod y = - (-x).tmod y := by simp
    rw [h, this]
  have : (-x) % y ≤ (-x) := by
    dcases hy : 0 ≤ y
    . have hIneq := Nat.mod_le (-x).toNat y.toNat
      zify at hIneq
      have : (-x).toNat = -x := by omega
      rw [this] at hIneq
      have : y.toNat = y := by omega
      rw [this] at hIneq
      omega
    . have hIneq := Nat.mod_le (-x).toNat (-y).toNat
      zify at hIneq
      have : (-x).toNat = -x := by omega
      rw [this] at hIneq
      have : (-y).toNat = -y := by omega
      rw [this] at hIneq
      simp at hIneq
      omega
  omega

-- TODO: move to Mathlib
theorem Int.bmod_bmod_of_dvd (n : Int) {m k : Nat} (hDiv : m ∣ k) :
  (n.bmod k).bmod m = n.bmod m := by
  conv => lhs; arg 1; simp only [Int.bmod]
  rw [← bmod_eq_emod_eq_iff]
  have h : n % (k : Int) % (m : Int) = n % (m : Int) := by
    rw [Int.emod_emod_of_dvd]
    simp [Int.ofNat_dvd_left]
    apply hDiv
  split_ifs
  . apply h
  . rw [Int.sub_emod]
    have : (k : Int) % m = 0 := by
      apply Int.emod_eq_zero_of_dvd
      simp [Int.ofNat_dvd_left]
      apply hDiv
    simp [this, h]

@[simp]
theorem Int.mod_toNat_val (n m : Int) (h : m ≠ 0) :
  (n % m).toNat = n % m := by
  simp only [Int.ofNat_toNat, ne_eq, h, not_false_eq_true, Int.emod_nonneg, sup_of_le_left]

theorem Nat.lt_iff_BitVec_ofNat_lt (n : Nat) (x y : Nat) (hx : x < 2^n) (hy : y < 2^n) :
  x < y ↔ BitVec.ofNat n x < BitVec.ofNat n y := by
  have := Nat.mod_eq_of_lt hx
  have := Nat.mod_eq_of_lt hy
  simp [*]

theorem Nat.le_iff_BitVec_ofNat_le (n : Nat) (x y : Nat) (hx : x < 2^n) (hy : y < 2^n) :
  x ≤ y ↔ BitVec.ofNat n x ≤ BitVec.ofNat n y := by
  have := Nat.mod_eq_of_lt hx
  have := Nat.mod_eq_of_lt hy
  simp [*]

theorem Nat.eq_iff_BitVec_ofNat_eq (n : Nat) (x y : Nat) (hx : x < 2^n) (hy : y < 2^n) :
  x = y ↔ BitVec.ofNat n x = BitVec.ofNat n y := by
  have := Nat.mod_eq_of_lt hx
  have := Nat.mod_eq_of_lt hy
  constructor <;> intros
  . simp_all
  . have := BitVec.toNat_ofNat x n
    have := BitVec.toNat_ofNat y n
    simp_all

end Aeneas.Arith
