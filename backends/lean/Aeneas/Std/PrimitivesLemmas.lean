import Aeneas.Std.Primitives
import Aeneas.Tactic.Step.Init
import Aeneas.Tactic.Conv.Bvify.Init

namespace Aeneas.Std

open Result WP

@[step]
theorem massert_spec (b : Prop) [Decidable b] (h : b) :
  massert b ⦃ _ => True ⦄ := by
  simp [massert, *]

@[simp, step_pre_simps, bvify]
theorem massert_ok (b : Prop) [Decidable b] : massert b = ok () ↔ b := by simp [massert]

@[simp, step_pre_simps, bvify]
theorem spec_massert (b : Prop) [Decidable b] : Std.WP.spec (massert b) P ↔ (b ∧ P ()) := by
  simp [massert]
  split <;> simp <;> grind

@[simp, global_simps] theorem massert_True : massert True = ok () := by simp [massert]
@[simp, global_simps] theorem massert_False : massert False = fail .assertionFailure := by simp [massert]

end Aeneas.Std
