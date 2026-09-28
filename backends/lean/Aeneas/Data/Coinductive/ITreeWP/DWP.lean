module
public import Aeneas.Data.Coinductive.ITreeWP.FunctionalWP
import all Aeneas.Data.Coinductive.ITreeWP.FunctionalWP
import all Init.Internal.Order.Basic

public section

namespace Aeneas.Data.Coinductive

open Lean.Order

universe u u' v w

variable {E : Effect.{v}} {α : Type u} {β : Type u'} {θ : EffectWP.{w, v} E}
variable [θ.Monotone]

local infix:50 " ≤ " => entails

/-! ## `DWP` defined as a least fixed point -/

def DWP (θ : EffectWP E) [θ.Monotone] (m : ITree E α) (Q : θ.Post α) : θ.Pre :=
  (FunctionalWP.hom False θ Q).lfp m

/-- Unfolding of `DWP` into its impredicative definition. -/
theorem DWP.def :
    DWP θ m Q s ↔ ∀ X : ITreePred θ α, FunctionalWP False θ Q X ≤ X → X m s := by
  simp [DWP, OrderHom.lfp, FunctionalWP.hom, entails_iff_le]

/-- DWP is the least fixpoint -/
theorem DWP.least : FunctionalWP False θ Q X ≤ X -> (fun m => DWP θ m Q) ≤ X :=
  OrderHom.lfp_le (FunctionalWP.hom False θ Q) (a := X)

theorem DWP.intro : FunctionalWP False θ Q (fun m => DWP θ m Q) m s -> DWP θ m Q s :=
  (FunctionalWP.hom False θ Q).map_lfp.le m s

theorem DWP.step : DWP θ m Q s -> FunctionalWP False θ Q (fun m => DWP θ m Q) m s :=
  (FunctionalWP.hom False θ Q).map_lfp.ge m s

/-- DWP is a fixed point -/
theorem DWP.fixedPoint : DWP θ m Q s ↔ FunctionalWP False θ Q (fun m => DWP θ m Q) m s :=
  ⟨DWP.step, DWP.intro⟩

@[expose] section

/-- Prove `P m s` by induction on total correctness, given `DWP θ m Q s`. -/
theorem DWP.induction {P : ITreePred θ α}
    (hRet : ∀ value s, Q value s → P (.ret value) s)
    (hVis : ∀ (event : E.I) (k : E.O event → ITree E α) (s : θ.State),
      θ.wp event (fun answer s' => P (k answer) s') s → P (.vis event k) s)
    (hSpec : DWP θ m Q s) : P m s := by
  refine DWP.least (X := P) (fun m' s' hLayer => ?_) m s hSpec
  revert hLayer
  cases m' using ITree.cases with
  | ret value =>
      simp only [ITree.pure_eq_ret, FunctionalWP.ret]
      exact hRet value s'
  | div =>
      simp only [FunctionalWP.div]
      exact False.elim
  | vis event k =>
      simp only [FunctionalWP.vis]
      exact hVis event k s'

/-! ## Constructors and destructors of `DWP` -/

theorem DWP.vis
    (hWp : θ.wp event (fun answer s' => DWP θ (k answer) Q s') s) :
    DWP θ (.vis event k) Q s :=
  intro (by simpa only [FunctionalWP.vis] using hWp)

@[simp]
theorem DWP.ret_iff :
    DWP θ (.ret value) Q s ↔ Q value s := by
  rw [DWP.fixedPoint, FunctionalWP.ret]

/-- Divergence is never totally correct. -/
theorem DWP.div_false (hSpec : DWP θ (ITree.div : ITree E α) Q s) : False := by
  simpa only [FunctionalWP.div] using hSpec.step

theorem DWP.vis_view (hSpec : DWP θ (.vis event k) Q s) :
    θ.wp event (fun answer s' => DWP θ (k answer) Q s') s := by
  simpa only [FunctionalWP.vis] using hSpec.step

/-! ## Structural rules -/

theorem DWP.mono (hSpec : DWP θ m Q s) (hQ : Q ≤ Q') :
    DWP θ m Q' s :=
  hSpec.induction (P := fun m => DWP θ m Q')
    (fun value s' hPost => DWP.ret_iff.mpr (hQ value s' hPost)) fun _ _ _ hWp => .vis hWp

theorem DWP.bind
    (hFirst : DWP θ m Q₁ s)
    (hK : ∀ value s', Q₁ value s' → DWP θ (k value) Q₂ s') :
    DWP θ (ITree.bind m k) Q₂ s :=
  hFirst.induction (P := fun t u => DWP θ (ITree.bind t k) Q₂ u)
    (fun value s' hPost => by
      simpa only [itree_ret_bind] using hK value s' hPost)
    fun _ _ _ hWp => by
      rw [itree_vis_bind]
      exact .vis hWp

theorem DWP.mono_le (hLe : m ⊑ m') (hSpec : DWP θ m Q s) :
    DWP θ m' Q s := by
  refine hSpec.induction
    (P := fun t u => ∀ t', t ⊑ t' → DWP θ t' Q u) ?_ ?_ m' hLe
  · intro value s' hPost t' hLe'
    rw [ITree.le_unfold] at hLe'
    obtain hDiv | ⟨value', hRet, rfl⟩ | ⟨_, _, _, hVis, _, _⟩ := hLe'
    · exact absurd hDiv not_ret_div
    · obtain rfl := ret_inj.mp hRet
      exact DWP.ret_iff.mpr hPost
    · exact absurd hVis not_vis_ret
  · intro event k s' hWp t' hLe'
    rw [ITree.le_unfold] at hLe'
    obtain hDiv | ⟨_, hRet, _⟩ | ⟨_, k₁, k₂, hVis, rfl, hLe''⟩ := hLe'
    · exact absurd hDiv.symm not_div_vis
    · exact absurd hRet.symm not_vis_ret
    · obtain ⟨rfl, hCont⟩ := vis_inj hVis
      obtain rfl := eq_of_heq hCont
      exact .vis (θ.wp_mono (fun answer _ hNext => hNext _ (hLe'' answer)) hWp)

end

end Aeneas.Data.Coinductive

end
