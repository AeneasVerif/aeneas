module
public import Aeneas.Std.Primitives
public meta import Aeneas.Tactic.Step.Init
public meta import Aeneas.Tactic.Conv.Bvify.Init
public section

namespace Aeneas.Std

open Result WP

variable {H : Type (uh + 1)}

@[step]
theorem massert_spec (b : Prop) [Decidable b] (h : b) :
  (massert b : ResultAt H Unit) ⦃ _ => b ⦄ := by
  simp [massert, *]

@[simp, step_pre_simps, bvify]
theorem massert_ok (b : Prop) [Decidable b] : (massert b : ResultAt H Unit) = ok () ↔ b := by
  grind [massert, fail_not_ok]

@[simp, step_pre_simps, bvify]
theorem spec_massert (b : Prop) [Decidable b] :
    Std.WP.spec (massert b : ResultAt H Unit) P ↔ (b ∧ P ()) := by
  simp [massert]
  split <;> simp <;> grind

@[simp, global_simps] theorem massert_True : (massert True : ResultAt H Unit) = ok () := by
  simp [massert]
@[simp, global_simps] theorem massert_False :
    (massert False : ResultAt H Unit) = fail .assertionFailure := by
  simp [massert]

end Aeneas.Std
