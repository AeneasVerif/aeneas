module
import Aeneas.Data.Coinductive.Spec.SpecDerived
import all Init.Internal.Order.Basic

/-! # Non-termination: partial but not total correctness, for any effect specification -/

namespace Aeneas.Data.Coinductive.TotalTests

variable {E : Effect} {S : EffectSpec E}

/-! ## A productive infinite program -/

/-- Perform `event` forever, ignoring its answers. -/
def forever (event : E.I) : ITree E Unit :=
  .vis event fun _ => forever event
partial_fixpoint

/-- Partial correctness accepts a productive infinite program, as long as its event is safe. -/
theorem forever_partial {event : E.I} (hSafe : ∀ s, S.wp event (fun _ _ => True) s)
    (Q : S.Post Unit) (s : S.State) : PartialSpec S Q (forever event) s := by
  refine PartialSpec.coinduction (fun t _ => t = forever event) ?_ rfl
  rintro _ s' rfl
  rw [forever, SpecF.vis]
  exact S.wp_mono (fun _ _ _ => forever.eq_1 event) (hSafe s')

/-- Total correctness rejects a productive infinite program: since no event can guarantee
    `False`, a tree that never returns is never totally correct. -/
theorem forever_not_total (event : E.I) (Q : S.Post Unit) (s : S.State) :
    ¬ TotalSpec S Q (forever event) s := by
  intro hSpec
  refine TotalSpec.induction (P := fun t _ => t = forever event → False)
    (fun _ _ _ hEq => ?_) (fun _ k s' hWp hEq => ?_) hSpec rfl
  · rw [forever] at hEq
    exact not_vis_ret hEq
  · rw [forever] at hEq
    obtain ⟨rfl, hk⟩ := vis_inj hEq
    obtain rfl := eq_of_heq hk
    exact S.wp_noMiracle _ s' (S.wp_mono (fun _ _ h => h rfl) hWp)

/-! ## A silent infinite program -/

def silentLoop : ITree E Unit := do
  let _ ← (pure () : ITree E Unit)
  silentLoop
partial_fixpoint

theorem silentLoop_eq_div : (silentLoop : ITree E Unit) = ITree.div := by
  apply ITree.le_div_is_div
  refine silentLoop.fixpoint_induct (fun x => Lean.Order.PartialOrder.rel x ITree.div)
    (fun _ hc h => Lean.Order.csup_le hc h) ?_
  intro x hx
  simpa only [Bind.bind, ITree.pure_eq_ret, itree_ret_bind] using hx

/-- Total correctness rejects a silent infinite program. -/
example (Q : S.Post Unit) (s : S.State) : ¬ TotalSpec S Q silentLoop s := by
  rw [silentLoop_eq_div]
  exact TotalSpec.div_false

/-- Partial correctness accepts a silent infinite program. -/
example (Q : S.Post Unit) (s : S.State) : PartialSpec S Q silentLoop s := by
  rw [silentLoop_eq_div]
  exact PartialSpec.div

end Aeneas.Data.Coinductive.TotalTests
