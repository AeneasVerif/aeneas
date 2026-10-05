module
public import Aeneas.Data.Coinductive.ITreeWP.FunctionalWP
import all Aeneas.Data.Coinductive.ITreeWP.FunctionalWP
import all Init.Internal.Order.Basic

/-!
# Demonic Weakest Precondition

`DWP θ m Q` is the weakest-precondition which guarantees that
the ITree `m` terminates and that its result satisfies `Q`.
We later use `DWP` to define Hoare triples for **total correctness**.
`θ` is the wp of individual effects (see `EffectWP.lean`), and it has to be monotonic,
conjunctive (to be demonic) and without miracles (to reject all loops).
"Demonic" means that the specification must hold for all possible answers of the effects,
guaranteeing that `Q` is satisfied for all final results of `m`.

`DWP` is defined as the least fixed point of `FunctionalWP` with divergence disallowed.
-/

public section

namespace Aeneas.Data.Coinductive

open Lean.Order

universe u u' v w

variable {E : Effect.{v}} {α : Type u} {β : Type u'} {θ : EffectWP.{w, v} E}
variable [θ.Monotone]

local infix:50 " ≤ " => entails

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
    (hVis : ∀ (effect : E.I) (k : E.O effect → ITree E α) (s : θ.State),
      θ.wp effect (fun answer s' => P (k answer) s') s → P (.vis effect k) s)
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
  | vis effect k =>
      simp only [FunctionalWP.vis]
      exact hVis effect k s'

/-! ## Constructors and destructors of `DWP` -/

theorem DWP.vis
    (hWp : θ.wp effect (fun answer s' => DWP θ (k answer) Q s') s) :
    DWP θ (.vis effect k) Q s :=
  intro (by simpa only [FunctionalWP.vis] using hWp)

@[simp]
theorem DWP.ret_iff :
    DWP θ (.ret value) Q s ↔ Q value s := by
  rw [DWP.fixedPoint, FunctionalWP.ret]

/-- Divergence is never totally correct. -/
theorem DWP.div_false (hSpec : DWP θ (ITree.div : ITree E α) Q s) : False := by
  simpa only [FunctionalWP.div] using hSpec.step

theorem DWP.vis_view (hSpec : DWP θ (.vis effect k) Q s) :
    θ.wp effect (fun answer s' => DWP θ (k answer) Q s') s := by
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

end

end Aeneas.Data.Coinductive

end
