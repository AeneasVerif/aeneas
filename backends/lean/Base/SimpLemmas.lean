import Lean

-- This simplification lemma is very useful especially for the kind of theorems we prove,
-- which are of the shape: `∃ x y ..., ... ∧ ... ∧ ...`.
-- Using this simp lemma often triggers simplifications like the instantiation of the
-- existential quantifiers when there is an equality somewhere:
-- `∃ x, x = y ∧ P x` gets rewritten to `P y`
attribute [simp] and_assoc
