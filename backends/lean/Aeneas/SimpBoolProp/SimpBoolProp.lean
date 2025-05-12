import Mathlib.Tactic.Tauto
import Aeneas.SimpBoolProp.Init

/-!
# `simp_bool_prop` lemmas and simp procedures
-/

namespace Aeneas.SimpBoolProp

open Lean Lean.Meta Lean.Parser.Tactic Lean.Elab.Tactic

attribute [simp_bool_prop_simps]
  reduceIte
  true_implies false_implies implies_true imp_false
  Bool.and_true Bool.true_and
  Bool.false_or Bool.or_false
  Bool.true_or Bool.or_true
  true_and and_true true_or or_true
  false_and and_false false_or or_false
  decide_eq_true_eq decide_eq_false_iff_not ne_eq
  false_eq_decide_iff true_eq_decide_iff
  not_false_eq_true not_true_eq_false
  not_or not_and
  Bool.not_or Bool.not_and
  Bool.not_true Bool.not_false
  Bool.not_eq_eq_eq_not
  Bool.true_eq_false Bool.false_eq_true
  Bool.or_eq_true Bool.and_eq_true
  decide_true decide_false Bool.and_self
  and_self
  iff_false iff_true
  forall_const
  exists_false

@[simp_bool_prop_simps]
theorem not_and_equiv_or_not (a b : Prop) : ¬ (a ∧ b) ↔ ¬ a ∨ ¬ b := by tauto

end Aeneas.SimpBoolProp
