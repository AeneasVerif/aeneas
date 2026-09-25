module
public import Aeneas.Data.Coinductive.Spec.Spec
import all Init.Internal.Order.Basic

@[expose] public section

/-!
# Reasoning rules for `TotalSpec` and `PartialSpec`
  derived from `Aeneas.Data.Coinductive.Spec.Spec`
-/

namespace Aeneas.Data.Coinductive

open Lean.Order

universe u u' v w

variable {E : Effect.{v}} {α : Type u} {β : Type u'} {S : EffectSpec.{w, v} E}

local infix:50 " ≤ " => entails

/-- Constructor-oriented form of `TotalSpec.least`: to prove `P` for every totally-correct tree,
    it suffices to show that `P` is closed under the `ret` and `vis` cases (the `div` case is
    vacuous). -/
theorem TotalSpec.induction {Q : S.Post α} {P : ITreePred S α}
    {m : ITree E α} {s : S.State}
    (hRet : ∀ value s, Q value s → P (.ret value) s)
    (hVis : ∀ (event : E.I) (k : E.O event → ITree E α) (s : S.State),
      S.wp event (fun answer s' => P (k answer) s') s → P (.vis event k) s)
    (hSpec : TotalSpec S Q m s) : P m s := by
  refine TotalSpec.least (X := P) (fun m' s' hLayer => ?_) m s hSpec
  revert hLayer
  cases m' using ITree.cases with
  | ret value =>
      simp only [ITree.pure_eq_ret, SpecF.ret]
      exact hRet value s'
  | div =>
      simp only [SpecF.div]
      exact False.elim
  | vis event k =>
      simp only [SpecF.vis]
      exact hVis event k s'

/-! ## Constructors and destructors of `TotalSpec` -/

theorem TotalSpec.vis {Q : S.Post α} {event : E.I}
    {k : E.O event → ITree E α} {s : S.State}
    (hWp : S.wp event (fun answer s' => TotalSpec S Q (k answer) s') s) :
    TotalSpec S Q (.vis event k) s :=
  intro (by simpa only [SpecF.vis] using hWp)

@[simp]
theorem TotalSpec.ret_iff {Q : S.Post α} {value : α} {s : S.State} :
    TotalSpec S Q (.ret value) s ↔ Q value s := by
  rw [TotalSpec.fixedPoint, SpecF.ret]

/-- Divergence is never totally correct. -/
theorem TotalSpec.div_false {Q : S.Post α} {s : S.State}
    (hSpec : TotalSpec S Q (ITree.div : ITree E α) s) : False := by
  simpa only [SpecF.div] using hSpec.step

theorem TotalSpec.vis_view {Q : S.Post α} {event : E.I}
    {k : E.O event → ITree E α} {s : S.State}
    (hSpec : TotalSpec S Q (.vis event k) s) :
    S.wp event (fun answer s' => TotalSpec S Q (k answer) s') s := by
  simpa only [SpecF.vis] using hSpec.step

/-- Pointwise form of `PartialSpec.greatest`: any post-fixed point `X` of `SpecF True S Q`
    implies `PartialSpec S Q`. -/
theorem PartialSpec.coinduction {Q : S.Post α} {m : ITree E α} {s : S.State}
    (X : ITreePred S α) (hClosed : X ≤ SpecF True S Q X) (hX : X m s) :
    PartialSpec S Q m s :=
  PartialSpec.greatest hClosed m s hX

/-! ## Constructors and destructors of `PartialSpec` -/

@[simp]
theorem PartialSpec.div {Q : S.Post α} {s : S.State} :
    PartialSpec S Q (ITree.div : ITree E α) s :=
  intro (by simp only [SpecF.div])

theorem PartialSpec.vis {Q : S.Post α} {event : E.I}
    {k : E.O event → ITree E α} {s : S.State}
    (hWp : S.wp event (fun answer s' => PartialSpec S Q (k answer) s') s) :
    PartialSpec S Q (.vis event k) s :=
  intro (by simpa only [SpecF.vis] using hWp)

@[simp]
theorem PartialSpec.ret_iff {Q : S.Post α} {value : α} {s : S.State} :
    PartialSpec S Q (.ret value) s ↔ Q value s := by
  rw [PartialSpec.fixedPoint, SpecF.ret]

theorem PartialSpec.vis_view {Q : S.Post α} {event : E.I}
    {k : E.O event → ITree E α} {s : S.State}
    (hSpec : PartialSpec S Q (.vis event k) s) :
    S.wp event (fun answer s' => PartialSpec S Q (k answer) s') s := by
  simpa only [SpecF.vis] using hSpec.step

/-- Lift total correctness to partial correctness. -/
theorem TotalSpec.toPartial {Q : S.Post α} {m : ITree E α}
    {s : S.State} (hSpec : TotalSpec S Q m s) : PartialSpec S Q m s :=
  hSpec.induction (P := PartialSpec S Q) (fun _ _ hPost => PartialSpec.ret_iff.mpr hPost)
    fun _ _ _ hWp => .vis hWp

/-! ## Structural rules -/

theorem TotalSpec.mono {Q Q' : S.Post α} {m : ITree E α} {s : S.State}
    (hSpec : TotalSpec S Q m s) (hQ : Q ≤ Q') :
    TotalSpec S Q' m s :=
  hSpec.induction (P := TotalSpec S Q')
    (fun value s' hPost => TotalSpec.ret_iff.mpr (hQ value s' hPost)) fun _ _ _ hWp => .vis hWp

theorem PartialSpec.mono {Q Q' : S.Post α} {m : ITree E α} {s : S.State}
    (hSpec : PartialSpec S Q m s) (hQ : Q ≤ Q') :
    PartialSpec S Q' m s :=
  coinduction (PartialSpec S Q)
    (fun _ _ hSpec' => hSpec'.step.mono id hQ fun _ _ => id) hSpec

theorem TotalSpec.bind {Q₁ : S.Post α} {Q₂ : S.Post β}
    {m : ITree E α} {k : α → ITree E β} {s : S.State}
    (hFirst : TotalSpec S Q₁ m s)
    (hK : ∀ value s', Q₁ value s' → TotalSpec S Q₂ (k value) s') :
    TotalSpec S Q₂ (ITree.bind m k) s :=
  hFirst.induction (P := fun t u => TotalSpec S Q₂ (ITree.bind t k) u)
    (fun value s' hPost => by
      simpa only [itree_ret_bind] using hK value s' hPost)
    fun _ _ _ hWp => by
      rw [itree_vis_bind]
      exact .vis hWp

theorem PartialSpec.bind {Q₁ : S.Post α} {Q₂ : S.Post β}
    {m : ITree E α} {k : α → ITree E β} {s : S.State}
    (hFirst : PartialSpec S Q₁ m s)
    (hK : ∀ value s', Q₁ value s' → PartialSpec S Q₂ (k value) s') :
    PartialSpec S Q₂ (ITree.bind m k) s := by
  refine coinduction
    (fun t s' => (∃ m', t = ITree.bind m' k ∧ PartialSpec S Q₁ m' s') ∨
      PartialSpec S Q₂ t s')
    ?_ (Or.inl ⟨m, rfl, hFirst⟩)
  rintro t s' (⟨m', rfl, hSpec⟩ | hSpec)
  · revert hSpec
    cases m' using ITree.cases with
    | ret value =>
        simp only [ITree.pure_eq_ret, itree_ret_bind]
        intro hSpec
        exact ((hK value s' (PartialSpec.ret_iff.mp hSpec)).step).mono id (fun _ _ => id) fun _ _ => Or.inr
    | div => simp only [itree_div_bind, SpecF.div, implies_true]
    | vis event k' =>
        simp only [itree_vis_bind, SpecF.vis]
        intro hSpec
        exact S.wp_mono (fun _ _ hChild => Or.inl ⟨_, rfl, hChild⟩) hSpec.vis_view
  · exact hSpec.step.mono id (fun _ _ => id) fun _ _ => Or.inr

theorem TotalSpec.mono_le {Q : S.Post α} {m m' : ITree E α} {s : S.State}
    (hLe : m ⊑ m') (hSpec : TotalSpec S Q m s) :
    TotalSpec S Q m' s := by
  refine hSpec.induction
    (P := fun t u => ∀ t', t ⊑ t' → TotalSpec S Q t' u) ?_ ?_ m' hLe
  · intro value s' hPost t' hLe'
    rw [ITree.le_unfold] at hLe'
    obtain hDiv | ⟨value', hRet, rfl⟩ | ⟨_, _, _, hVis, _, _⟩ := hLe'
    · exact absurd hDiv not_ret_div
    · obtain rfl := ret_inj.mp hRet
      exact TotalSpec.ret_iff.mpr hPost
    · exact absurd hVis not_vis_ret
  · intro event k s' hWp t' hLe'
    rw [ITree.le_unfold] at hLe'
    obtain hDiv | ⟨_, hRet, _⟩ | ⟨_, k₁, k₂, hVis, rfl, hLe''⟩ := hLe'
    · exact absurd hDiv.symm not_div_vis
    · exact absurd hRet.symm not_vis_ret
    · obtain ⟨rfl, hCont⟩ := vis_inj hVis
      obtain rfl := eq_of_heq hCont
      exact .vis (S.wp_mono (fun answer _ hNext => hNext _ (hLe'' answer)) hWp)

theorem PartialSpec.mono_le {Q : S.Post α} {m m' : ITree E α} {s : S.State}
    (hLe : m ⊑ m') (hSpec : PartialSpec S Q m' s) :
    PartialSpec S Q m s := by
  refine coinduction (fun t s' => ∃ t', t ⊑ t' ∧ PartialSpec S Q t' s') ?_
    ⟨m', hLe, hSpec⟩
  rintro t s' ⟨t', hLe', hSpec'⟩
  rw [ITree.le_unfold] at hLe'
  obtain rfl | ⟨value, rfl, rfl⟩ | ⟨event, k, k', rfl, rfl, hCont⟩ := hLe'
  · simp only [SpecF.div]
  · simpa only [SpecF.ret] using PartialSpec.ret_iff.mp hSpec'
  · simp only [SpecF.vis]
    exact S.wp_mono (fun answer _ hNext => ⟨_, hCont answer, hNext⟩)
      hSpec'.vis_view

/-! ## `PartialSpec` is admissible -/

/-- `EffectSpec.wp_conj` for a family indexed by a nonempty type. -/
theorem EffectSpec.wp_forall {ι : Sort u'} {event : E.I} {s : S.State}
    {C : ι → S.Post (E.O event)} (i₀ : ι) (hWp : ∀ i, S.wp event (C i) s) :
    S.wp event (fun answer s' => ∀ i, C i answer s') s := by
  refine S.wp_mono (fun _ _ hAll i => hAll (C i) ⟨i, rfl⟩)
    (S.wp_conj (fun X => ∃ i, X = C i) ⟨C i₀, i₀, rfl⟩ ?_)
  rintro X ⟨i, rfl⟩
  exact hWp i

/-- Partial correctness is admissible. -/
theorem PartialSpec.admissible (S : EffectSpec E) (Q : S.Post α) (s : S.State) :
    Lean.Order.admissible (fun m : ITree E α => PartialSpec S Q m s) := by
  intro c hc hAll
  refine coinduction
    (fun t u => ∃ c' : ITree E α → Prop, ∃ hc' : chain c',
      (∀ x, c' x → PartialSpec S Q x u) ∧ t = CCPO.csup hc')
    ?_ ⟨c, hc, hAll, rfl⟩
  rintro t u ⟨c', hc', hAll', rfl⟩
  generalize hEq : CCPO.csup hc' = t
  cases t using ITree.cases with
  | ret value =>
      simp only [ITree.pure_eq_ret, SpecF.ret]
      exact PartialSpec.ret_iff.mp (hAll' _ (ITree.csup_ret_mem hc' hEq))
  | div => simp only [SpecF.div]
  | vis event k =>
      simp only [SpecF.vis]
      -- Combine every approximation's demand.
      obtain ⟨k₀, hMem₀⟩ := ITree.csup_vis_mem hc' hEq
      have hChildren :
          S.wp event (fun answer u' =>
            ∀ k' : { k' : E.O event → ITree E α // c' (ITree.vis event k') },
              PartialSpec S Q (k'.val answer) u') u :=
        S.wp_forall ⟨k₀, hMem₀⟩ fun k' => (hAll' _ k'.property).vis_view
      -- Limit children are suprema of approximation children.
      obtain rfl : k = fun o => CCPO.csup (ITree.visChain_chain hc' event o) := by
        rw [ITree.csup_vis hc' hMem₀] at hEq
        obtain ⟨-, hCont⟩ := vis_inj hEq.symm
        exact eq_of_heq hCont
      refine S.wp_mono (fun answer u' hChild => ?_) hChildren
      exact ⟨ITree.visChain c' event answer, ITree.visChain_chain hc' event answer,
        by rintro _ ⟨k', hMem', rfl⟩; exact hChild ⟨k', hMem'⟩, rfl⟩

end Aeneas.Data.Coinductive

end
