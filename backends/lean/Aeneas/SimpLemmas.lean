import Lean

namespace Aeneas

namespace Simp

/- This lemma is generally useful. It often happens that (because we
   make a split on a condition for instance) we have `x ≠ y` in the context
   and need to simplify `y ≠ x` somewhere. -/
@[simp]
theorem neq_imp {α : Type u} {x y : α} (h : ¬ x = y) : ¬ y = x := by intro; simp_all

/- This is generally useful, and doing without is actually quite cumbersome.

   Note that the following theorem does not seem to be necessary (we invert `x`
   and `y` in the conclusion), probably because of `neq_imp`:
   `¬ x = y → ¬ y == x`
 -/
@[simp]
theorem neq_imp_nbeq [BEq α] [LawfulBEq α] (x y : α) (heq : ¬ x = y) : ¬ x == y := by simp [*]

-- This simplification lemma is very useful especially for the kind of theorems we prove,
-- which are of the shape: `∃ x y ..., ... ∧ ... ∧ ...`.
-- Using this simp lemma often triggers simplifications like the instantiation of the
-- existential quantifiers when there is an equality somewhere:
-- `∃ x, x = y ∧ P x` gets rewritten to `P y`
attribute [simp] and_assoc

end Simp

end Aeneas
