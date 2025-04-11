import Lean
import Mathlib.Tactic.Linarith -- Introduces a lot of useful lemmas

namespace Aeneas

namespace ScalarTac

open Lean Elab Term Meta

-- TODO: move?
theorem ne_zero_is_lt_or_gt {x : Int} (hne : x ≠ 0) : x < 0 ∨ x > 0 := by
  cases h: x <;>
  simp_all only [Int.ofNat_eq_coe, Int.natCast_eq_zero, Int.natCast_pos,
    ne_eq, Int.negSucc_ne_zero, not_false_eq_true, Int.negSucc_lt_zero,
    gt_iff_lt, Int.negSucc_not_pos, or_false]
  rename_i n;
  cases n <;> simp_all

-- TODO: move?
theorem ne_is_lt_or_gt {x y : Int} (hne : x ≠ y) : x < y ∨ x > y := by
  have hne : x - y ≠ 0 := by
    simp
    intro h
    have: x = y := by omega
    simp_all
  have h := ne_zero_is_lt_or_gt hne
  match h with
  | .inl _ => left; omega
  | .inr _ => right; omega

-- TODO: move?
theorem add_one_le_iff_le_ne (n m : Nat) (h1 : m ≤ n) (h2 : m ≠ n) : m + 1 ≤ n := by
  -- Damn, those proofs on natural numbers are hard - I wish Omega was in mathlib4...
  simp [Nat.add_one_le_iff]
  simp [Nat.lt_iff_le_and_ne]
  simp_all

/- Induction over positive integers -/
-- TODO: move
theorem int_pos_ind (p : Int → Prop) :
  (zero:p 0) → (pos:∀ i, 0 ≤ i → p i → p (i + 1)) → ∀ i, 0 ≤ i → p i := by
  intro h0 hr i hpos
--  have heq : Int.toNat i = i := by
--    cases i <;> simp_all
  have ⟨ n, heq ⟩  : {n:Nat // n = i } := ⟨ Int.toNat i, by cases i <;> simp_all ⟩
  revert i
  induction n
  . intro i hpos heq
    cases i <;> simp_all
  . rename_i n hi
    intro i hpos heq
    cases i <;> simp_all
    rename_i m
    cases m <;> simp_all

/- WARNING: do not use this with `simp` as it might loop. The left-hand side indeed reduces to the
   righ-hand side, meaning the rewriting can be applied to `n` itself. -/
theorem ofNat_instOfNatNat_eq (n : Nat) : @OfNat.ofNat Nat n (instOfNatNat n) = n := by rfl

theorem Nat.le_imp_le_equiv_eq (i j : Nat) (h0 : i ≤ j) : j ≤ i ↔ i = j := by omega
theorem Int.le_imp_le_equiv_eq (i j : Int) (h0 : i ≤ j) : j ≤ i ↔ i = j := by omega

example (i : Int) (j : Nat) (h : i ≤ j) (h2 : j ≤ i) :
  i = j := by
  simp_all [Int.le_imp_le_equiv_eq]

end ScalarTac

end Aeneas
