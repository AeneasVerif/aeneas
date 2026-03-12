import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

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

end Aeneas.CryptoSolver
