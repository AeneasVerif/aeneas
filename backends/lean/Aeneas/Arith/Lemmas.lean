import Aeneas.ScalarTac.IntTac
import Aeneas.ScalarTac.ScalarTac

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

end Aeneas.ScalarTac
