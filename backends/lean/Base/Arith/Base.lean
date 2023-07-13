import Lean
import Std.Data.Int.Lemmas
import Mathlib.Tactic.Linarith

namespace Arith

open Lean Elab Term Meta

-- We can't define and use trace classes in the same file
initialize registerTraceClass `Arith

-- TODO: move?
theorem ne_zero_is_lt_or_gt {x : Int} (hne : x ≠ 0) : x < 0 ∨ x > 0 := by
  cases h: x <;> simp_all
  . rename_i n;
    cases n <;> simp_all
  . apply Int.negSucc_lt_zero

-- TODO: move?
theorem ne_is_lt_or_gt {x y : Int} (hne : x ≠ y) : x < y ∨ x > y := by
  have hne : x - y ≠ 0 := by
    simp
    intro h
    have: x = y := by linarith
    simp_all
  have h := ne_zero_is_lt_or_gt hne
  match h with
  | .inl _ => left; linarith
  | .inr _ => right; linarith


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

end Arith
