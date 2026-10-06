module
public import Aeneas.Data.Coinductive.ITreeWP.FunctionalWP
import all Aeneas.Data.Coinductive.ITreeWP.FunctionalWP
import all Init.Internal.Order.Basic

/-!
# Demonic Weakest Liberal Precondition

`DWLP θ m Q` is the weakest-precondition which guarantees that,
*if* the ITree `m` terminates, then its result satisfies `Q`.
We later use DWLP to define Hoare triples for **partial correctness**.
`θ` is the wp of individual effects (see `EffectWP.lean`), and it has to be monotonic,
and conjunctive (to be demonic).
"Demonic" means that the specification must hold for all possible answers of the effects,
guaranteeing that `Q` is satisfied for all final results of `m`.
"Liberal" means that divergence is allowed and no guarantees are provided when `m`
diverges.

`DWLP` is defined as the greatest fixed point of `FunctionalWP` with divergence allowed.
-/

public section

namespace Aeneas.Data.Coinductive

open Lean.Order

universe u u' v w

variable {E : Effect.{v}} {α : Type u} {β : Type u'} {θ : EffectWP.{w, v} E}
variable [θ.Monotonic]

local infix:50 " ≤ " => entails

def DWLP (θ : EffectWP E) [θ.Monotonic] (m : ITree E α) (Q : θ.Post α) : θ.Pre :=
  (FunctionalWP.hom True θ Q).gfp m

/-- Unfolding of `DWLP` into its impredicative definition. -/
theorem DWLP.def :
    DWLP θ m Q s ↔ ∃ X : ITreePred θ α, X ≤ FunctionalWP True θ Q X ∧ X m s := by
  simp [DWLP, OrderHom.gfp, FunctionalWP.hom, entails_iff_le]

/-- DWLP is the greatest fixpoint -/
theorem DWLP.greatest : X ≤ FunctionalWP True θ Q X -> X ≤ (fun m => DWLP θ m Q) :=
  OrderHom.le_gfp (FunctionalWP.hom True θ Q) (a := X)

theorem DWLP.step :
    DWLP θ m Q s -> FunctionalWP True θ Q (fun m => DWLP θ m Q) m s :=
  (FunctionalWP.hom True θ Q).map_gfp.ge m s

theorem DWLP.intro : FunctionalWP True θ Q (fun m => DWLP θ m Q) m s -> DWLP θ m Q s :=
  (FunctionalWP.hom True θ Q).map_gfp.le m s

/-- DWLP is a fixed point -/
theorem DWLP.fixedPoint : DWLP θ m Q s ↔ FunctionalWP True θ Q (fun m => DWLP θ m Q) m s :=
  ⟨DWLP.step, DWLP.intro⟩

@[expose] section

/-- Prove `DWLP θ m Q s` by exhibiting a coinductive invariant. -/
theorem DWLP.coinduction
    (X : ITreePred θ α) (hClosed : X ≤ FunctionalWP True θ Q X) (hX : X m s) :
    DWLP θ m Q s :=
  DWLP.greatest hClosed m s hX

/-! ## Constructors and destructors of `DWLP` -/

@[simp]
theorem DWLP.div :
    DWLP θ (ITree.div : ITree E α) Q s :=
  intro (by simp only [FunctionalWP.div])

theorem DWLP.vis
    (hWp : θ.wp effect (fun answer s' => DWLP θ (k answer) Q s') s) :
    DWLP θ (.vis effect k) Q s :=
  intro (by simpa only [FunctionalWP.vis] using hWp)

@[simp]
theorem DWLP.ret_iff :
    DWLP θ (.ret value) Q s ↔ Q value s := by
  rw [DWLP.fixedPoint, FunctionalWP.ret]

theorem DWLP.vis_view (hSpec : DWLP θ (.vis effect k) Q s) :
    θ.wp effect (fun answer s' => DWLP θ (k answer) Q s') s := by
  simpa only [FunctionalWP.vis] using hSpec.step

theorem DWLP.mono (hSpec : DWLP θ m Q s) (hQ : Q ≤ Q') :
    DWLP θ m Q' s :=
  coinduction (fun m => DWLP θ m Q)
    (fun _ _ hSpec' => hSpec'.step.mono id hQ fun _ _ => id) hSpec

theorem DWLP.bind
    (hFirst : DWLP θ m Q₁ s)
    (hK : ∀ value s', Q₁ value s' → DWLP θ (k value) Q₂ s') :
    DWLP θ (ITree.bind m k) Q₂ s := by
  refine coinduction
    (fun t s' => (∃ m', t = ITree.bind m' k ∧ DWLP θ m' Q₁ s') ∨
      DWLP θ t Q₂ s')
    ?_ (Or.inl ⟨m, rfl, hFirst⟩)
  rintro t s' (⟨m', rfl, hSpec⟩ | hSpec)
  · revert hSpec
    cases m' using ITree.cases with
    | ret value =>
        simp only [ITree.pure_eq_ret, itree_ret_bind]
        intro hSpec
        exact ((hK value s' (DWLP.ret_iff.mp hSpec)).step).mono id (fun _ _ => id) fun _ _ => Or.inr
    | div => simp only [itree_div_bind, FunctionalWP.div, implies_true]
    | vis effect k' =>
        simp only [itree_vis_bind, FunctionalWP.vis]
        intro hSpec
        exact θ.wp_monotonic (fun _ _ hChild => Or.inl ⟨_, rfl, hChild⟩) hSpec.vis_view
  · exact hSpec.step.mono id (fun _ _ => id) fun _ _ => Or.inr

/-- Partial correctness is admissible. -/
theorem DWLP.admissible (θ : EffectWP E) [θ.Monotonic] [θ.Conjunctive]
    (Q : θ.Post α) (s : θ.State) :
    Lean.Order.admissible (fun m : ITree E α => DWLP θ m Q s) := by
  intro c hc hAll
  refine coinduction
    (fun t u => ∃ c' : ITree E α → Prop, ∃ hc' : chain c',
      (∀ x, c' x → DWLP θ x Q u) ∧ t = CCPO.csup hc')
    ?_ ⟨c, hc, hAll, rfl⟩
  rintro t u ⟨c', hc', hAll', rfl⟩
  generalize hEq : CCPO.csup hc' = t
  cases t using ITree.cases with
  | ret value =>
      simp only [ITree.pure_eq_ret, FunctionalWP.ret]
      exact DWLP.ret_iff.mp (hAll' _ (ITree.csup_ret_mem hc' hEq))
  | div => simp only [FunctionalWP.div]
  | vis effect k =>
      simp only [FunctionalWP.vis]
      -- Combine every approximation's demand.
      obtain ⟨k₀, hMem₀⟩ := ITree.csup_vis_mem hc' hEq
      have hChildren :
          θ.wp effect (fun answer u' =>
            ∀ k' : { k' : E.O effect → ITree E α // c' (ITree.vis effect k') },
              DWLP θ (k'.val answer) Q u') u :=
        θ.wp_forall ⟨k₀, hMem₀⟩ fun k' => (hAll' _ k'.property).vis_view
      -- Limit children are suprema of approximation children.
      obtain rfl : k = fun o => CCPO.csup (ITree.visChain_chain hc' effect o) := by
        rw [ITree.csup_vis hc' hMem₀] at hEq
        obtain ⟨-, hCont⟩ := vis_inj hEq.symm
        exact eq_of_heq hCont
      refine θ.wp_monotonic (fun answer u' hChild => ?_) hChildren
      exact ⟨ITree.visChain c' effect answer, ITree.visChain_chain hc' effect answer,
        by rintro _ ⟨k', hMem', rfl⟩; exact hChild ⟨k', hMem'⟩, rfl⟩

end

end Aeneas.Data.Coinductive

end
