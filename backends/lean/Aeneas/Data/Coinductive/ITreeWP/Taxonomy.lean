module
public import Aeneas.Data.Coinductive.ITreeWP.DWP
public import Aeneas.Data.Coinductive.ITreeWP.DWLP

@[expose] public section

/-! Relation between `DWP` and `DWLP` -/

namespace Aeneas.Data.Coinductive

universe u u' v w

variable {E : Effect.{v}} {α : Type u} {β : Type u'} {θ : EffectWP.{w, v} E}
variable [θ.Monotonic]

/-- DWP implies DWLP. -/
theorem DWP.toPartial (hSpec : DWP θ m Q s) : DWLP θ m Q s :=
  hSpec.induction (P := fun m => DWLP θ m Q) (fun _ _ hPost => DWLP.ret_iff.mpr hPost)
    fun _ _ _ hWp => .vis hWp

theorem DWP.and_partial [θ.Conjunctive] (h₁ : DWP θ m Q₁ s) (h₂ : DWLP θ m Q₂ s) :
    DWP θ m (fun value s' => Q₁ value s' ∧ Q₂ value s') s :=
  h₁.induction (P := fun t u => DWLP θ t Q₂ u → DWP θ t (fun value s' => Q₁ value s' ∧ Q₂ value s') u)
    (fun _ _ hPost hOther => DWP.ret_iff.mpr ⟨hPost, DWLP.ret_iff.mp hOther⟩)
    (fun _ _ _ hWp hOther => .vis (θ.wp_monotonic (fun _ _ h => h.1 h.2)
      (EffectWP.wp_and hWp hOther.vis_view)))
    h₂

/-- DWP rejects all loops -/
theorem dwp_no_loops [θ.Conjunctive] [θ.ExcludedMiracle]
    (hNever : DWLP θ m (fun _ _ => False) s) : ¬ DWP θ m Q s := by
  intro hSpec
  refine hSpec.induction (P := fun m s => DWLP θ m (fun _ _ => False) s → False)
    (fun _ _ _ h => DWLP.ret_iff.mp h) (fun effect k s hHandle h => ?_) hNever
  let C : θ.Post (E.O effect) := fun answer s' => DWLP θ (k answer) (fun _ _ => False) s'
  have hBoth := θ.wp_forall (C := fun b : Bool =>
      if b then C else fun answer s' => ¬ C answer s') false
    (by
      intro b
      cases b
      · exact hHandle
      · exact h.vis_view)
  exact θ.wp_excludedMiracle effect s (θ.wp_monotonic (fun _ _ h => h false (h true)) hBoth)

end Aeneas.Data.Coinductive

end
