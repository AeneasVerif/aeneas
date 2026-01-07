import Aeneas.SimpScalar.SimpScalar
import Aeneas.ReduceNat

section

  open Aeneas Utils Lean Meta

  initialize registerTraceClass `ReduceLog2

  -- TODO: the pattern `Nat.log2 (@OfNat.ofNat _ _ _)` doesn't work
  simproc Nat.reduceLog2 (Nat.log2 _) := fun e => do
    match e.consumeMData.getAppFnArgs with
    | (``Nat.log2, #[value]) =>
      trace[ReduceLog2] "- value: {value}"
      -- Retrieve the value
      let value ← if let some value := exprToNat? value then pure value else return .continue
      -- Compute the log
      let log := value.log2
      trace[ReduceLog2] "- value.log2: {log}"
      -- Create the new expression - the proof is by reflection
      return .visit {expr := .lit (.natVal log)}
    | _ => return .continue

  example : (2^128).log2 = 128 := by simp

  attribute [scalar_tac_simps, simp_scalar_simps] Nat.reduceLog2

end

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
@[scalar_tac_simps, simp_scalar_simps]
def Nat.isPowerOfTwo' (n : Nat) : Bool := 2 ^ n.log2 = n

example : Nat.isPowerOfTwo' 65536 := by simp [scalar_tac_simps]
example : Nat.isPowerOfTwo' (2^256) := by simp [scalar_tac_simps]

theorem Nat.isPowerOfTwo'_iff (n : Nat) :
  Nat.isPowerOfTwo' n ↔ Nat.isPowerOfTwo n := by
  simp [Nat.isPowerOfTwo', Nat.isPowerOfTwo]
  constructor
  · grind
  · intro h
    have ⟨ k, h ⟩ := h
    have := @Nat.log2_two_pow k
    grind

/- This is often used with, e.g., `d = U32.size` -/
@[simp_scalar_simps↓]
theorem Nat.pow_two_mod_isPowerOfTwo'_eq_self (n : ℕ) (h : d.isPowerOfTwo' ∧ n < d.log2) : 2 ^ n % d = 2 ^ n := by
  have ⟨ k, h ⟩ : ∃ k, d = 2 ^ k ∧ n < k := by grind [Nat.isPowerOfTwo']
  simp_scalar [h]

@[simp_scalar_simps↓]
theorem Nat.pow_two_mod_isPowerOfTwo'_eq_zero (n : ℕ) (h : d.isPowerOfTwo' ∧ d.log2 ≤ n) : 2 ^ n % d = 0 := by
  have ⟨ k, h ⟩ : ∃ k, d = 2 ^ k ∧ k ≤ n := by grind [Nat.isPowerOfTwo']
  simp_scalar [h]

@[simp_scalar_simps↓]
theorem Nat.pow_two_lt_isPowerOfTwo' (n : ℕ) (h : d.isPowerOfTwo' ∧ n < d.log2) : 2 ^ n < d := by
  have ⟨ k, h ⟩ : ∃ k, d = 2 ^ k ∧ n < k := by grind [Nat.isPowerOfTwo']
  simp_scalar [h]

@[simp_scalar_simps↓]
theorem Nat.pow_two_lt_isPowerOfTwo'_iff_false (n : ℕ) (h : d.isPowerOfTwo' ∧ d.log2 ≤ n) : 2 ^ n < d ↔ False := by
  have ⟨ k, h ⟩ : ∃ k, d = 2 ^ k ∧ k ≤ n := by grind [Nat.isPowerOfTwo']
  simp_scalar [h]

@[simp_scalar_simps↓]
theorem Nat.mod_eq_self_iff (x y : ℕ) (hy : 0 < y) : (x % y = x ↔ x < y) := by
  simp only [Nat.mod_eq_iff, and_true, Nat.right_eq_add, mul_eq_zero, exists_or_eq_right,
    or_iff_right_iff_imp]
  omega
