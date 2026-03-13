import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace Aeneas.CryptoSolver

/-! ### Multiplication bounds -/

theorem Nat.mul_lt_of_lt_of_lt {a b ba bb : Nat}
    (ha : a < ba) (hb : b < bb) (hba : 0 < ba) : a * b < ba * bb := by
  nlinarith

theorem Nat.mul_le_of_le_of_le {a b ba bb : Nat}
    (ha : a ≤ ba) (hb : b ≤ bb) : a * b ≤ ba * bb :=
  Nat.mul_le_mul ha hb

/-! ### Modular arithmetic bounds -/

theorem Nat.mod_lt_of_pos' (a : Nat) {m : Nat} (hm : 0 < m) : a % m < m :=
  Nat.mod_lt a hm

/-! ### Division bounds -/

theorem Nat.div_le_of_le {a n : Nat} (ha : a ≤ n) (k : Nat) :
    a / k ≤ n :=
  Nat.le_trans (Nat.div_le_self a k) ha

/-! ### Combined limb operations -/

theorem Nat.limb_lo_bound' {a k : Nat} (hk : 0 < k) : a % 2 ^ k < 2 ^ k :=
  Nat.mod_lt a (by positivity)

/-! ### Bitwise bounds

These lemmas are re-exported from Lean 4 core for use in `simp` sets.
The core lemmas (`Nat.and_le_left`, etc.) are already available; we add
convenience wrappers and crypto-specific patterns here. -/

/-- Right shift reduces value: `x >>> k ≤ x` -/
theorem Nat.shiftRight_le_self (x k : Nat) : x >>> k ≤ x := by
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.div_le_self x (2 ^ k)

/-- Right shift reduces bit width: if `x < 2^n` then `x >>> k < 2^(n-k)` -/
theorem Nat.shiftRight_lt_of_lt_pow {x n k : Nat} (hx : x < 2 ^ n) (hk : k ≤ n) :
    x >>> k < 2 ^ (n - k) := by
  rw [Nat.shiftRight_eq_div_pow]
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k)]
  calc x < 2 ^ n := hx
    _ = 2 ^ (n - k + k) := by rw [Nat.sub_add_cancel hk]
    _ = 2 ^ (n - k) * 2 ^ k := by rw [Nat.pow_add]

/-- Left shift bound: if `x < 2^n` then `x <<< k < 2^(n+k)` -/
theorem Nat.shiftLeft_lt_of_lt_pow {x n k : Nat} (hx : x < 2 ^ n) :
    x <<< k < 2 ^ (n + k) := by
  rw [Nat.shiftLeft_eq]
  calc x * 2 ^ k < 2 ^ n * 2 ^ k := by
        exact (Nat.mul_lt_mul_right (Nat.two_pow_pos k)).mpr hx
    _ = 2 ^ (n + k) := by rw [Nat.pow_add]

end Aeneas.CryptoSolver
