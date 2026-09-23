module
public import Aeneas.Data.Coinductive.ITree
import all Init.Internal.Order.Basic

@[expose] public section

/-!
Generic total- and partial-correctness for interaction trees.
`TotalSpec` is a least fixed point; `PartialSpec` is a greatest fixed point.
-/

namespace Aeneas.Data.Coinductive

open Lean.Order

universe u u' v w

/-! ## Event handlers -/

/-- A stateful predicate-transformer handler for events. -/
structure Handler (E : Effect.{v}) where
  State : Type u -- the state used by the handler
  handle : (event : E.I) → State → (E.O event → State → Prop) → Prop
  handle_mono :
    ∀ {event : E.I} {s : State} {C C' : E.O event → State → Prop},
      (∀ answer s', C answer s' → C' answer s') →
      handle event s C → handle event s C'

variable {E : Effect.{v}} {α : Type u} {β : Type u'} {H : Handler.{w, v} E}

/-- A postcondition on a return value and the handler's final state. -/
abbrev HPost (H : Handler E) (α : Type u) := α → H.State → Prop

/-- A predicate on an interaction tree and the handler's current state. -/
abbrev ITreePred (H : Handler E) (α : Type u) := ITree E α → H.State → Prop

/-- Pointwise implication between postconditions (also used for `ITreePred`s, which are
    postconditions on trees). -/
def entails (P P' : HPost H α) : Prop :=
  ∀ r s, P r s → P' r s

local infix:50 " ≤ " => entails

/-! ## Common functor for the least/greatest fixed point -/
def SpecF (H : Handler E) (Q : HPost H α) (allowDivergence : Prop)
    (X : ITreePred H α) : ITreePred H α :=
  fun m s =>
    ITree.cases
      (motive := fun _ => Prop)
      (fun value => Q value s)
      allowDivergence
      (fun event k => H.handle event s fun answer s' => X (k answer) s')
      m

theorem SpecF.ret {Q : HPost H α} {allowDivergence : Prop} {X : ITreePred H α}
    {value : α} {s : H.State} :
    SpecF H Q allowDivergence X (.ret value) s = Q value s := by
  simp only [SpecF, ITree.cases.ret]

theorem SpecF.div {Q : HPost H α} {allowDivergence : Prop} {X : ITreePred H α}
    {s : H.State} :
    SpecF H Q allowDivergence X (ITree.div : ITree E α) s = allowDivergence := by
  simp only [SpecF, ITree.cases.div]

theorem SpecF.vis {Q : HPost H α} {allowDivergence : Prop} {X : ITreePred H α}
    {event : E.I} {k : E.O event → ITree E α} {s : H.State} :
    SpecF H Q allowDivergence X (.vis event k) s =
      H.handle event s fun answer s' => X (k answer) s' := by
  simp only [SpecF, ITree.cases.vis]

theorem SpecF.mono {Q Q' : HPost H α} {allowDivergence allowDivergence' : Prop}
    {X X' : ITreePred H α} {m : ITree E α} {s : H.State}
    (hQ : Q ≤ Q') (hDiv : allowDivergence → allowDivergence') (hX : X ≤ X')
    (hLayer : SpecF H Q allowDivergence X m s) :
    SpecF H Q' allowDivergence' X' m s := by
  revert hLayer
  cases m using ITree.cases with
  | ret value =>
      simp only [ITree.pure_eq_ret, SpecF.ret]
      exact hQ value s
  | div =>
      simp only [SpecF.div]
      exact hDiv
  | vis event k =>
      simp only [SpecF.vis]
      exact H.handle_mono fun answer s' => hX (k answer) s'

theorem SpecF.mono_tail {Q : HPost H α} {allowDivergence : Prop}
    {X X' : ITreePred H α} {m : ITree E α} {s : H.State}
    (hX : X ≤ X') (hLayer : SpecF H Q allowDivergence X m s) :
    SpecF H Q allowDivergence X' m s :=
  hLayer.mono (fun _ _ => id) id hX

/-! ## Total correctness as the least fixed point of `SpecF H Q False`. -/
def TotalSpec (H : Handler E) (Q : HPost H α) : ITreePred H α :=
  fun m s =>
    ∀ X : ITreePred H α, SpecF H Q False X ≤ X → X m s

/-! ## Partial correctness as the greatest fixed point of `SpecF H Q True`. -/
def PartialSpec (H : Handler E) (Q : HPost H α) : ITreePred H α :=
  fun m s =>
    ∃ X : ITreePred H α, X ≤ SpecF H Q True X ∧ X m s

/-! ### The constructors and destructors of `TotalSpec` -/

theorem TotalSpec.induction {Q : HPost H α} {P : ITreePred H α}
    {m : ITree E α} {s : H.State}
    (hRet : ∀ value s, Q value s → P (.ret value) s)
    (hVis : ∀ (event : E.I) (k : E.O event → ITree E α) (s : H.State),
      H.handle event s (fun answer s' => P (k answer) s') → P (.vis event k) s)
    (hSpec : TotalSpec H Q m s) : P m s := by
  refine hSpec P fun m' s' hLayer => ?_
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

theorem TotalSpec.intro {Q : HPost H α} {m : ITree E α} {s : H.State}
    (hLayer : SpecF H Q False (TotalSpec H Q) m s) : TotalSpec H Q m s :=
  fun X hClosed => hClosed m s (hLayer.mono_tail fun _ _ hSpec => hSpec X hClosed)

theorem TotalSpec.step {Q : HPost H α} {m : ITree E α} {s : H.State}
    (hSpec : TotalSpec H Q m s) : SpecF H Q False (TotalSpec H Q) m s :=
  hSpec.induction
    (P := SpecF H Q False (TotalSpec H Q))
    (fun _ _ hPost => by simpa only [SpecF.ret] using hPost)
    fun _ _ _ hHandle => by
      simpa only [SpecF.vis] using
        H.handle_mono (fun _ _ hLayer => TotalSpec.intro hLayer) hHandle

theorem TotalSpec.ret {Q : HPost H α} {value : α} {s : H.State}
    (hPost : Q value s) : TotalSpec H Q (.ret value) s :=
  intro (by simpa only [SpecF.ret] using hPost)

theorem TotalSpec.vis {Q : HPost H α} {event : E.I}
    {k : E.O event → ITree E α} {s : H.State}
    (hHandle : H.handle event s fun answer s' => TotalSpec H Q (k answer) s') :
    TotalSpec H Q (.vis event k) s :=
  intro (by simpa only [SpecF.vis] using hHandle)

theorem TotalSpec.ret_post {Q : HPost H α} {value : α} {s : H.State}
    (hSpec : TotalSpec H Q (.ret value) s) : Q value s := by
  simpa only [SpecF.ret] using hSpec.step

@[simp]
theorem TotalSpec.ret_iff {Q : HPost H α} {value : α} {s : H.State} :
    TotalSpec H Q (.ret value) s ↔ Q value s :=
  ⟨TotalSpec.ret_post, TotalSpec.ret⟩

/-- Divergence is never totally correct. -/
theorem TotalSpec.div_false {Q : HPost H α} {s : H.State}
    (hSpec : TotalSpec H Q (ITree.div : ITree E α) s) : False := by
  simpa only [SpecF.div] using hSpec.step

theorem TotalSpec.vis_view {Q : HPost H α} {event : E.I}
    {k : E.O event → ITree E α} {s : H.State}
    (hSpec : TotalSpec H Q (.vis event k) s) :
    H.handle event s fun answer s' => TotalSpec H Q (k answer) s' := by
  simpa only [SpecF.vis] using hSpec.step

/-! ### The constructors and destructors of `PartialSpec` -/

theorem PartialSpec.coinduction {Q : HPost H α} {m : ITree E α} {s : H.State}
    (X : ITreePred H α) (hClosed : X ≤ SpecF H Q True X) (hX : X m s) :
    PartialSpec H Q m s :=
  ⟨X, hClosed, hX⟩

theorem PartialSpec.step {Q : HPost H α} {m : ITree E α} {s : H.State}
    (hSpec : PartialSpec H Q m s) : SpecF H Q True (PartialSpec H Q) m s := by
  obtain ⟨X, hClosed, hX⟩ := hSpec
  exact (hClosed m s hX).mono_tail fun m' s' hX' => ⟨X, hClosed, hX'⟩

theorem PartialSpec.intro {Q : HPost H α} {m : ITree E α} {s : H.State}
    (hLayer : SpecF H Q True (PartialSpec H Q) m s) : PartialSpec H Q m s := by
  refine coinduction
    (fun m' s' => PartialSpec H Q m' s' ∨ (m' = m ∧ s' = s)) ?_ (Or.inr ⟨rfl, rfl⟩)
  rintro m' s' (hSpec | ⟨rfl, rfl⟩)
  · exact hSpec.step.mono_tail fun _ _ => Or.inl
  · exact hLayer.mono_tail fun _ _ => Or.inl

theorem PartialSpec.ret {Q : HPost H α} {value : α} {s : H.State}
    (hPost : Q value s) : PartialSpec H Q (.ret value) s :=
  intro (by simpa only [SpecF.ret] using hPost)

@[simp]
theorem PartialSpec.div {Q : HPost H α} {s : H.State} :
    PartialSpec H Q (ITree.div : ITree E α) s :=
  intro (by simp only [SpecF.div])

theorem PartialSpec.vis {Q : HPost H α} {event : E.I}
    {k : E.O event → ITree E α} {s : H.State}
    (hHandle : H.handle event s fun answer s' => PartialSpec H Q (k answer) s') :
    PartialSpec H Q (.vis event k) s :=
  intro (by simpa only [SpecF.vis] using hHandle)

theorem PartialSpec.ret_post {Q : HPost H α} {value : α} {s : H.State}
    (hSpec : PartialSpec H Q (.ret value) s) : Q value s := by
  simpa only [SpecF.ret] using hSpec.step

@[simp]
theorem PartialSpec.ret_iff {Q : HPost H α} {value : α} {s : H.State} :
    PartialSpec H Q (.ret value) s ↔ Q value s :=
  ⟨PartialSpec.ret_post, PartialSpec.ret⟩

theorem PartialSpec.vis_view {Q : HPost H α} {event : E.I}
    {k : E.O event → ITree E α} {s : H.State}
    (hSpec : PartialSpec H Q (.vis event k) s) :
    H.handle event s fun answer s' => PartialSpec H Q (k answer) s' := by
  simpa only [SpecF.vis] using hSpec.step

/-- Lift total correctness to partial correctness. -/
theorem TotalSpec.toPartial {Q : HPost H α} {m : ITree E α}
    {s : H.State} (hSpec : TotalSpec H Q m s) : PartialSpec H Q m s :=
  hSpec.induction (P := PartialSpec H Q) (fun _ _ hPost => .ret hPost)
    fun _ _ _ hHandle => .vis hHandle

/-! ## Structural rules -/

theorem TotalSpec.mono {Q Q' : HPost H α} {m : ITree E α} {s : H.State}
    (hSpec : TotalSpec H Q m s) (hQ : Q ≤ Q') :
    TotalSpec H Q' m s :=
  hSpec.induction (P := TotalSpec H Q')
    (fun value s' hPost => .ret (hQ value s' hPost)) fun _ _ _ hHandle => .vis hHandle

theorem PartialSpec.mono {Q Q' : HPost H α} {m : ITree E α} {s : H.State}
    (hSpec : PartialSpec H Q m s) (hQ : Q ≤ Q') :
    PartialSpec H Q' m s :=
  coinduction (PartialSpec H Q)
    (fun _ _ hSpec' => hSpec'.step.mono hQ id fun _ _ => id) hSpec

theorem TotalSpec.bind {Q₁ : HPost H α} {Q₂ : HPost H β}
    {m : ITree E α} {k : α → ITree E β} {s : H.State}
    (hFirst : TotalSpec H Q₁ m s)
    (hK : ∀ value s', Q₁ value s' → TotalSpec H Q₂ (k value) s') :
    TotalSpec H Q₂ (ITree.bind m k) s :=
  hFirst.induction (P := fun t u => TotalSpec H Q₂ (ITree.bind t k) u)
    (fun value s' hPost => by
      simpa only [itree_ret_bind] using hK value s' hPost)
    fun _ _ _ hHandle => by
      rw [itree_vis_bind]
      exact .vis hHandle

theorem PartialSpec.bind {Q₁ : HPost H α} {Q₂ : HPost H β}
    {m : ITree E α} {k : α → ITree E β} {s : H.State}
    (hFirst : PartialSpec H Q₁ m s)
    (hK : ∀ value s', Q₁ value s' → PartialSpec H Q₂ (k value) s') :
    PartialSpec H Q₂ (ITree.bind m k) s := by
  refine coinduction
    (fun t s' => (∃ m', t = ITree.bind m' k ∧ PartialSpec H Q₁ m' s') ∨
      PartialSpec H Q₂ t s')
    ?_ (Or.inl ⟨m, rfl, hFirst⟩)
  rintro t s' (⟨m', rfl, hSpec⟩ | hSpec)
  · revert hSpec
    cases m' using ITree.cases with
    | ret value =>
        simp only [ITree.pure_eq_ret, itree_ret_bind]
        intro hSpec
        exact ((hK value s' hSpec.ret_post).step).mono_tail fun _ _ => Or.inr
    | div => simp only [itree_div_bind, SpecF.div, implies_true]
    | vis event k' =>
        simp only [itree_vis_bind, SpecF.vis]
        intro hSpec
        exact H.handle_mono (fun _ _ hChild => Or.inl ⟨_, rfl, hChild⟩) hSpec.vis_view
  · exact hSpec.step.mono_tail fun _ _ => Or.inr

theorem TotalSpec.mono_le {Q : HPost H α} {m m' : ITree E α} {s : H.State}
    (hLe : m ⊑ m') (hSpec : TotalSpec H Q m s) :
    TotalSpec H Q m' s := by
  refine hSpec.induction
    (P := fun t u => ∀ t', t ⊑ t' → TotalSpec H Q t' u) ?_ ?_ m' hLe
  · intro value s' hPost t' hLe'
    rw [ITree.le_unfold] at hLe'
    obtain hDiv | ⟨value', hRet, rfl⟩ | ⟨_, _, _, hVis, _, _⟩ := hLe'
    · exact absurd hDiv not_ret_div
    · obtain rfl := ret_inj.mp hRet
      exact .ret hPost
    · exact absurd hVis not_vis_ret
  · intro event k s' hHandle t' hLe'
    rw [ITree.le_unfold] at hLe'
    obtain hDiv | ⟨_, hRet, _⟩ | ⟨_, k₁, k₂, hVis, rfl, hLe''⟩ := hLe'
    · exact absurd hDiv.symm not_div_vis
    · exact absurd hRet.symm not_vis_ret
    · obtain ⟨rfl, hCont⟩ := vis_inj hVis
      obtain rfl := eq_of_heq hCont
      exact .vis (H.handle_mono (fun answer _ hNext => hNext _ (hLe'' answer)) hHandle)

theorem PartialSpec.mono_le {Q : HPost H α} {m m' : ITree E α} {s : H.State}
    (hLe : m ⊑ m') (hSpec : PartialSpec H Q m' s) :
    PartialSpec H Q m s := by
  refine coinduction (fun t s' => ∃ t', t ⊑ t' ∧ PartialSpec H Q t' s') ?_
    ⟨m', hLe, hSpec⟩
  rintro t s' ⟨t', hLe', hSpec'⟩
  rw [ITree.le_unfold] at hLe'
  obtain rfl | ⟨value, rfl, rfl⟩ | ⟨event, k, k', rfl, rfl, hCont⟩ := hLe'
  · simp only [SpecF.div]
  · simpa only [SpecF.ret] using hSpec'.ret_post
  · simp only [SpecF.vis]
    exact H.handle_mono (fun answer _ hNext => ⟨_, hCont answer, hNext⟩)
      hSpec'.vis_view

/-! ## PartialSpec is admissible -/

namespace Handler

/-- A handler is *conjunctive* if, whenever it satisfies each continuation, it also satisfies their conjunction.

    Reading `H.handle e s C` as the triple `e {C}`: if `e {C₁} ∧ e {C₂} ∧ … ∧ e {Cₙ}`, then
    `e {fun a s' => C₁ a s' ∧ C₂ a s' ∧ … ∧ Cₙ a s'}`. The definition below asks this for any
    nonempty (possibly infinite) family of continuations, given by the predicate `Demands`.

    Deterministic events and demonic choice (`∀ answer, C answer s`) are conjunctive. Angelic
    choice (`∃ answer, C answer s`) is not: each demand may be met by a different answer, with no
    single answer meeting all of them.

    This is what makes `PartialSpec` admissible: a `vis` node at the supremum of a chain must
    satisfy the demands of all its approximations at once. -/
def Conjunctive (H : Handler E) : Prop :=
  ∀ {event : E.I} {s : H.State}
    (Demands : HPost H (E.O event) → Prop), (∃ C, Demands C) →
    (∀ C, Demands C → H.handle event s C) →
    H.handle event s fun answer s' => ∀ C, Demands C → C answer s'

theorem Conjunctive.handle_forall {ι : Sort u'} {event : E.I} {s : H.State}
    {C : ι → HPost H (E.O event)} (hConj : H.Conjunctive) (i₀ : ι)
    (hHandle : ∀ i, H.handle event s (C i)) :
    H.handle event s fun answer s' => ∀ i, C i answer s' := by
  refine H.handle_mono (fun _ _ hAll i => hAll (C i) ⟨i, rfl⟩)
    (hConj (fun X => ∃ i, X = C i) ⟨C i₀, i₀, rfl⟩ ?_)
  rintro X ⟨i, rfl⟩
  exact hHandle i

end Handler

/-- Partial correctness with a conjunctive handler is admissible. -/
theorem PartialSpec.admissible (hConj : H.Conjunctive) (Q : HPost H α) (s : H.State) :
    Lean.Order.admissible (fun m : ITree E α => PartialSpec H Q m s) := by
  intro c hc hAll
  refine coinduction
    (fun t u => ∃ c' : ITree E α → Prop, ∃ hc' : chain c',
      (∀ x, c' x → PartialSpec H Q x u) ∧ t = CCPO.csup hc')
    ?_ ⟨c, hc, hAll, rfl⟩
  rintro t u ⟨c', hc', hAll', rfl⟩
  generalize hEq : CCPO.csup hc' = t
  cases t using ITree.cases with
  | ret value =>
      simp only [ITree.pure_eq_ret, SpecF.ret]
      exact (hAll' _ (ITree.csup_ret_mem hc' hEq)).ret_post
  | div => simp only [SpecF.div]
  | vis event k =>
      simp only [SpecF.vis]
      -- Combine every approximation's demand.
      obtain ⟨k₀, hMem₀⟩ := ITree.csup_vis_mem hc' hEq
      have hChildren :
          H.handle event u fun answer u' =>
            ∀ k' : { k' : E.O event → ITree E α // c' (ITree.vis event k') },
              PartialSpec H Q (k'.val answer) u' :=
        hConj.handle_forall ⟨k₀, hMem₀⟩ fun k' => (hAll' _ k'.property).vis_view
      -- Limit children are suprema of approximation children.
      obtain rfl : k = fun o => CCPO.csup (ITree.visChain_chain hc' event o) := by
        rw [ITree.csup_vis hc' hMem₀] at hEq
        obtain ⟨-, hCont⟩ := vis_inj hEq.symm
        exact eq_of_heq hCont
      refine H.handle_mono (fun answer u' hChild => ?_) hChildren
      exact ⟨ITree.visChain c' event answer, ITree.visChain_chain hc' event answer,
        by rintro _ ⟨k', hMem', rfl⟩; exact hChild ⟨k', hMem'⟩, rfl⟩

end Aeneas.Data.Coinductive

end
