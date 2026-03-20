import Lean

namespace Aeneas

namespace Simp

/- This lemma is sometimes useful. It can happen that (because we
   make a split on a condition for instance) we have `x ≠ y` in the context
   and need to simplify `y ≠ x` somewhere.
 -/
theorem neq_imp {α : Type u} {x y : α} (h : ¬ x = y) : ¬ y = x := by intro; simp_all

/- This is sometimes useful.

   Note that the following theorem does not seem to be necessary (we invert `x`
   and `y` in the conclusion), probably because of `neq_imp`:
   `¬ x = y → ¬ y == x`
 -/
theorem neq_imp_nbeq [BEq α] [LawfulBEq α] (x y : α) (heq : ¬ x = y) : ¬ x == y := by simp [*]

/- This simplification lemma is very useful especially for the kind of theorems we prove,
   which are of the shape: `∃ x y ..., ... ∧ ... ∧ ...`.
   Using this simp lemma often triggers simplifications like the instantiation of the
   existential quantifiers when there is an equality somewhere:
   `∃ x, x = y ∧ P x` gets rewritten to `P y` -/
attribute [simp] and_assoc

@[simp]
theorem decide_eq_not_decide (a b : Prop) [Decidable a] [Decidable b] :
  decide a = !decide b ↔ a = ¬ b := by
  by_cases a <;> simp_all

@[simp]
theorem not_decide_eq_decide (a b : Prop) [Decidable a] [Decidable b] :
  !decide a = decide b ↔ ¬ a = b := by
  by_cases a <;> simp_all

end Simp

end Aeneas
