import Aeneas.SimpScalar.SimpScalar
import Aeneas.ReduceNat

@[simp_scalar_simps]
theorem Nat.mod_mod_of_pow_le (a n m : Nat) (h : m ≤ n) :
  a % b^n % b^m = a % b^m := by
  grind [Nat.mod_mod_of_dvd, Nat.pow_dvd_pow]

@[simp_scalar_simps]
theorem Nat.mod_mod_of_pow_le' (a n m : Nat) (h : n ≤ m) :
  a % b^n % b^m = a % b^n := by
  grind [Nat.mod_mod_of_dvd', Nat.pow_dvd_pow]

example (a n m : Nat) (h : n < m) : a % 2^n % 2^m = a % 2^n := by simp_scalar
example (a n m : Nat) (h : n > m) : a % 2^n % 2^m = a % 2^m := by simp_scalar

@[scalar_tac_simps]
theorem Nat.log2_0 : Nat.log2 0 = 0 := by rfl

@[scalar_tac_simps]
theorem Nat.log2_1 : Nat.log2 1 = 0 := by rfl

@[scalar_tac_simps]
theorem Nat.log2_two_lt {n} (h : 2 ≤ n) : Nat.log2 n = Nat.log2 (n / 2) + 1 := by
  rw [Nat.log2_def]
  simp [h]

example : Nat.log2 256 < 64 := by simp only [scalar_tac_simps]

@[simp_scalar_simps]
theorem Nat.zero_pow_eq_zero (h : n > 0) : 0 ^ n = 0 := by rw [zero_pow]; omega

@[simp_scalar_simps]
theorem Nat.zero_pow_zero_eq_one (h : n = 0) : 0 ^ n = 1 := by simp only [h, pow_zero]

@[simp_scalar_simps]
theorem Nat.mod_of_pow_eq_self (a n : Nat) (h : 1 < a ∧ 1 < n) :
  a % a^n = a := by
  have : a < a ^ n := by simp_scalar
  simp_scalar

theorem Nat.pow_mod_pow_eq_self (a n m : Nat) (ha : 1 < a) (h : n < m) :
  a ^ n % a ^ m = a ^ n := by
  have : a ^ n < a ^ m := by simp_scalar
  simp_scalar

@[simp_scalar_simps]
theorem Nat.pow_mod_pow_eq_self' (a n m : Nat) (h : 1 < a ∧ n < m) :
  a ^ n % a ^ m = a ^ n := by
  apply Nat.pow_mod_pow_eq_self <;> grind

attribute [simp_scalar_simps] Nat.pow_dvd_pow

@[simp_scalar_simps]
theorem Nat.pow_mod_pow_eq_zero (a n m : Nat) (h : m ≤ n) :
  a ^ n % a ^ m = 0 := by
  have : a ^ m ∣ a ^ n := by simp_scalar
  omega

@[simp_scalar_simps]
theorem Nat.or_mod_two_pow_iff_true (a b n : ℕ) :
  ((a ||| b) % 2 ^ n = a % 2 ^ n ||| b % 2 ^ n) ↔ True := by
  simp only [Nat.or_mod_two_pow]

@[simp_scalar_simps]
theorem Nat.or_mod_two_pow_iff_true' (a b n : ℕ) :
  (a % 2 ^ n ||| b % 2 ^ n = (a ||| b) % 2 ^ n) ↔ True := by
  simp only [Nat.or_mod_two_pow]

@[simp_scalar_simps]
theorem Nat.and_mod_two_pow_iff_true (a b n : ℕ) :
  ((a &&& b) % 2 ^ n = a % 2 ^ n &&& b % 2 ^ n) ↔ True := by
  simp only [Nat.and_mod_two_pow]

@[simp_scalar_simps]
theorem Nat.and_mod_two_pow_iff_true' (a b n : ℕ) :
  (a % 2 ^ n &&& b % 2 ^ n = (a &&& b) % 2 ^ n) ↔ True := by
  simp only [Nat.and_mod_two_pow]

@[simp_scalar_simps]
theorem Nat.xor_mod_two_pow_iff_true (a b n : ℕ) :
  ((a ^^^ b) % 2 ^ n = a % 2 ^ n ^^^ b % 2 ^ n) ↔ True := by
  simp only [Nat.xor_mod_two_pow]

@[simp_scalar_simps]
theorem Nat.xor_mod_two_pow_iff_true' (a b n : ℕ) :
  (a % 2 ^ n ^^^ b % 2 ^ n = (a ^^^ b) % 2 ^ n) ↔ True := by
  simp only [Nat.xor_mod_two_pow]

@[simp_scalar_simps]
theorem Nat.mod_pow_eq_zero {a n : Nat} (h : n ≤ 1) : a % a^n = 0 := by
  have : n = 0 ∨ n = 1 := by omega
  cases this <;> simp only [pow_zero, pow_one, mod_one, mod_self, *]

attribute [simp_scalar_simps] Nat.zero_mod pow_zero pow_one

@[simp_scalar_simps]
theorem Nat.one_lt_pow'' {a n : Nat} (h : 1 < a ∧ 1 ≤ n) : 1 < a^n := by
  apply Nat.one_lt_pow <;> omega

theorem Nat.one_mod_pow_eq_one {a n : Nat} (ha : 1 < a) (hn : 1 ≤ n) : 1 % a^n = 1 := by
  have : 1 < a ^n := by simp_scalar
  simp_scalar

@[simp_scalar_simps]
theorem Nat.one_mod_pow_eq_one' {a n : Nat} (h : 1 < a ∧ 1 ≤ n) : 1 % a^n = 1 := by
  apply Nat.one_mod_pow_eq_one <;> omega

/-!
# isPowerOfTwo'

We need a computable variant of `isPowerOfTwo` so that we can use it as a precondition in
some theorems (in particular, some `bvify_simps` theorems), so that such a precondition can
be discharged by `simp`.
-/

/-- Computable variant of `isPowerOfTwo`. -/
def Nat.isPowerOfTwo' (n : Nat) : Bool :=
  if n = 0 then false
  else if n = 1 then true
  else if n % 2 = 0 then isPowerOfTwo' (n / 2)
  else false

@[scalar_tac_simps]
def Nat.isPowerOfTwo'_zero : Nat.isPowerOfTwo' 0 = false := by
  simp [Nat.isPowerOfTwo']

@[scalar_tac_simps]
def Nat.isPowerOfTwo'_one : Nat.isPowerOfTwo' 1 = true := by
  simp [Nat.isPowerOfTwo']

/-- Carefully control the recursive case of `Nat.isPowerOfTwo'` to avoid infinite unfoldings. -/
@[scalar_tac_simps]
def Nat.isPowerOfTwo'_div (h : n > 1 ∧ n % 2 = 0) :
  Nat.isPowerOfTwo' n ↔ Nat.isPowerOfTwo' (n / 2) := by
  grind [Nat.isPowerOfTwo']

example : Nat.isPowerOfTwo' 65536 := by simp [scalar_tac_simps, simp_bool_prop_simps]

theorem Nat.isPowerOfTwo'_iff (n : Nat) :
  Nat.isPowerOfTwo' n ↔ Nat.isPowerOfTwo n := by
  if h: n = 0 then
    simp only [isPowerOfTwo', ↓reduceIte, Bool.false_eq_true, isPowerOfTwo,
      Aeneas.ReduceNat.reduceNatEq, Nat.pow_eq_zero, OfNat.ofNat_ne_zero, ne_eq, false_and,
      exists_const, h]
  else if h: n = 1 then
    simp only [h, isPowerOfTwo', one_ne_zero, ↓reduceIte, isPowerOfTwo,
      Aeneas.ReduceNat.reduceNatEq, Nat.pow_eq_one, OfNat.ofNat_ne_one, false_or, exists_eq]
  else if h: n % 2 = 0 then
    unfold Nat.isPowerOfTwo'
    have := Nat.isPowerOfTwo'_iff (n / 2)
    have : (n / 2).isPowerOfTwo ↔ n.isPowerOfTwo := by
      constructor <;> intro hp <;> unfold isPowerOfTwo at * <;> replace ⟨ k, hp ⟩ := hp
      · exists k + 1
        grind
      · exists k - 1
        simp only [hp]
        cases k <;> grind
    grind
  else
    simp only [isPowerOfTwo', ↓reduceIte, Bool.false_eq_true, isPowerOfTwo, false_iff, not_exists, *]
    intro k h
    simp_all only [Nat.pow_eq_zero, OfNat.ofNat_ne_zero, ne_eq, false_and, not_false_eq_true,
      Nat.pow_eq_one, OfNat.ofNat_ne_one, false_or, two_pow_mod_two_eq_zero, _root_.not_lt,
      nonpos_iff_eq_zero]
