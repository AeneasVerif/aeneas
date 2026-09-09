import Aeneas.Data.Coinductive.StateMachine

/-!
Generic total- and partial-correctness judgments for interaction trees.
`TotalSpec` is a least fixed point; `PartialSpec` is a greatest fixed point
that permits divergence but not stuck events.
-/

namespace Aeneas.Data.Coinductive

open Lean.Order

universe u u' v w

variable {E : Effect.{v}} {α : Type u} {β : Type u'} {M : StateMachine.{w, v} E}

/-! ## One layer of a correctness judgment -/

/-- One correctness layer: returns use `Q`, divergence uses `Div`, and events
delegate to `M.handle`. -/
def SpecF (M : StateMachine E) (Q : α → M.State → Prop) (Div : Prop)
    (X : ITree E α → M.State → Prop) (m : ITree E α) (s : M.State) : Prop :=
  ITree.cases
    (motive := fun _ => Prop)
    (fun value => Q value s)
    Div
    (fun event k => M.handle event s fun answer s' => X (k answer) s')
    m

/-! Computation rules for `SpecF`. -/

theorem SpecF.ret {Q : α → M.State → Prop} {Div : Prop}
    {X : ITree E α → M.State → Prop} {value : α} {s : M.State} :
    SpecF M Q Div X (.ret value) s = Q value s := by
  simp only [SpecF, ITree.cases.ret]

theorem SpecF.div {Q : α → M.State → Prop} {Div : Prop}
    {X : ITree E α → M.State → Prop} {s : M.State} :
    SpecF M Q Div X (ITree.div : ITree E α) s = Div := by
  simp only [SpecF, ITree.cases.div]

/-- The event case, which hands the obligation straight to the machine. -/
theorem SpecF.vis {Q : α → M.State → Prop} {Div : Prop}
    {X : ITree E α → M.State → Prop} {event : E.I} {k : E.O event → ITree E α}
    {s : M.State} :
    SpecF M Q Div X (.vis event k) s =
      M.handle event s fun answer s' => X (k answer) s' := by
  simp only [SpecF, ITree.cases.vis]

/-- `SpecF` is monotone in its postcondition, divergence case, and tail. -/
theorem SpecF.mono {Q Q' : α → M.State → Prop} {Div Div' : Prop}
    {X X' : ITree E α → M.State → Prop}
    (hQ : ∀ value s, Q value s → Q' value s) (hDiv : Div → Div')
    (hX : ∀ m s, X m s → X' m s) {m : ITree E α} {s : M.State}
    (hLayer : SpecF M Q Div X m s) : SpecF M Q' Div' X' m s := by
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
      exact M.handle_mono fun answer s' => hX (k answer) s'

/-- The common case of `SpecF.mono`: only the rest of the run is weakened. -/
theorem SpecF.mono_tail {Q : α → M.State → Prop} {Div : Prop}
    {X X' : ITree E α → M.State → Prop} (hX : ∀ m s, X m s → X' m s)
    {m : ITree E α} {s : M.State} (hLayer : SpecF M Q Div X m s) :
    SpecF M Q Div X' m s :=
  hLayer.mono (fun _ _ => id) id hX

/-! ## The two judgments -/

/-- Total correctness as the least fixed point of `SpecF Q False`. -/
def TotalSpec (M : StateMachine E) (Q : α → M.State → Prop) (m : ITree E α)
    (s : M.State) : Prop :=
  ∀ X : ITree E α → M.State → Prop,
    (∀ m' s', SpecF M Q False X m' s' → X m' s') → X m s

/-- Partial correctness as the greatest fixed point of `SpecF Q True`. -/
def PartialSpec (M : StateMachine E) (Q : α → M.State → Prop) (m : ITree E α)
    (s : M.State) : Prop :=
  ∃ X : ITree E α → M.State → Prop,
    (∀ m' s', X m' s' → SpecF M Q True X m' s') ∧ X m s

/-! ### The constructors and destructors of `TotalSpec` -/

/-- Induction on a total-correctness derivation. -/
theorem TotalSpec.induction {Q : α → M.State → Prop}
    {P : ITree E α → M.State → Prop}
    (hRet : ∀ value s, Q value s → P (.ret value) s)
    (hVis : ∀ (event : E.I) (k : E.O event → ITree E α) (s : M.State),
      M.handle event s (fun answer s' => P (k answer) s') → P (.vis event k) s)
    {m : ITree E α} {s : M.State} (hSpec : TotalSpec M Q m s) : P m s := by
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

/-- Total correctness is a pre-fixed point: one layer of it is it.  This is the
two constructors at once, and the exact counterpart of `PartialSpec.intro`. -/
theorem TotalSpec.intro {Q : α → M.State → Prop} {m : ITree E α} {s : M.State}
    (hLayer : SpecF M Q False (TotalSpec M Q) m s) : TotalSpec M Q m s :=
  fun X hClosed => hClosed m s (hLayer.mono_tail fun _ _ hSpec => hSpec X hClosed)

/-- And it is a fixed point: it survives one event.  Every destructor below is
this rule read in one of the three cases of `SpecF`, and it is the counterpart of
`PartialSpec.step`. -/
theorem TotalSpec.step {Q : α → M.State → Prop} {m : ITree E α} {s : M.State}
    (hSpec : TotalSpec M Q m s) : SpecF M Q False (TotalSpec M Q) m s :=
  hSpec.induction
    (P := SpecF M Q False (TotalSpec M Q))
    (fun _ _ hPost => by simpa only [SpecF.ret] using hPost)
    fun _ _ _ hHandle => by
      simpa only [SpecF.vis] using
        M.handle_mono (fun _ _ hLayer => TotalSpec.intro hLayer) hHandle

theorem TotalSpec.ret {Q : α → M.State → Prop} {value : α} {s : M.State}
    (hPost : Q value s) : TotalSpec M Q (.ret value) s :=
  intro (by simpa only [SpecF.ret] using hPost)

theorem TotalSpec.vis {Q : α → M.State → Prop} {event : E.I}
    {k : E.O event → ITree E α} {s : M.State}
    (hHandle : M.handle event s fun answer s' => TotalSpec M Q (k answer) s') :
    TotalSpec M Q (.vis event k) s :=
  intro (by simpa only [SpecF.vis] using hHandle)

theorem TotalSpec.ret_post {Q : α → M.State → Prop} {value : α} {s : M.State}
    (hSpec : TotalSpec M Q (.ret value) s) : Q value s := by
  simpa only [SpecF.ret] using hSpec.step

/-- `TotalSpec.ret`/`TotalSpec.ret_post` as one rewrite. -/
@[simp]
theorem TotalSpec.ret_iff {Q : α → M.State → Prop} {value : α} {s : M.State} :
    TotalSpec M Q (.ret value) s ↔ Q value s :=
  ⟨TotalSpec.ret_post, TotalSpec.ret⟩

/-- Divergence is never totally correct.  This is the case `PartialSpec`
deliberately keeps. -/
theorem TotalSpec.div_false {Q : α → M.State → Prop} {s : M.State}
    (hSpec : TotalSpec M Q (ITree.div : ITree E α) s) : False := by
  simpa only [SpecF.div] using hSpec.step

/-- The event destructor: the machine answers the event here, and total
correctness continues in the state it answers with.  An event the machine cannot
answer is not totally correct, since there is nothing to destructure. -/
theorem TotalSpec.vis_view {Q : α → M.State → Prop} {event : E.I}
    {k : E.O event → ITree E α} {s : M.State}
    (hSpec : TotalSpec M Q (.vis event k) s) :
    M.handle event s fun answer s' => TotalSpec M Q (k answer) s' := by
  simpa only [SpecF.vis] using hSpec.step

/-! ### The constructors and destructors of `PartialSpec`

The same for the greatest fixed point, where `PartialSpec.coinduction` takes the
place `TotalSpec.induction` has above. -/

/-- The introduction rule: a relation closed under one event proves partial
correctness of every configuration it holds of.  This is what a loop invariant
is applied to. -/
theorem PartialSpec.coinduction {Q : α → M.State → Prop}
    (X : ITree E α → M.State → Prop)
    (hClosed : ∀ m' s', X m' s' → SpecF M Q True X m' s') {m : ITree E α}
    {s : M.State} (hX : X m s) : PartialSpec M Q m s :=
  ⟨X, hClosed, hX⟩

/-- Partial correctness is a post-fixed point: it survives one event. -/
theorem PartialSpec.step {Q : α → M.State → Prop} {m : ITree E α} {s : M.State}
    (hSpec : PartialSpec M Q m s) : SpecF M Q True (PartialSpec M Q) m s := by
  obtain ⟨X, hClosed, hX⟩ := hSpec
  exact (hClosed m s hX).mono_tail fun m' s' hX' => ⟨X, hClosed, hX'⟩

/-- And it is a fixed point: one layer of it is it. -/
theorem PartialSpec.intro {Q : α → M.State → Prop} {m : ITree E α} {s : M.State}
    (hLayer : SpecF M Q True (PartialSpec M Q) m s) : PartialSpec M Q m s := by
  refine coinduction
    (fun m' s' => PartialSpec M Q m' s' ∨ (m' = m ∧ s' = s)) ?_ (Or.inr ⟨rfl, rfl⟩)
  rintro m' s' (hSpec | ⟨rfl, rfl⟩)
  · exact hSpec.step.mono_tail fun _ _ => Or.inl
  · exact hLayer.mono_tail fun _ _ => Or.inl

theorem PartialSpec.ret {Q : α → M.State → Prop} {value : α} {s : M.State}
    (hPost : Q value s) : PartialSpec M Q (.ret value) s :=
  intro (by simpa only [SpecF.ret] using hPost)

/-- Divergence owes nothing.  This is the constructor `TotalSpec` deliberately
does not have. -/
@[simp]
theorem PartialSpec.div {Q : α → M.State → Prop} {s : M.State} :
    PartialSpec M Q (ITree.div : ITree E α) s :=
  intro (by simp only [SpecF.div])

theorem PartialSpec.vis {Q : α → M.State → Prop} {event : E.I}
    {k : E.O event → ITree E α} {s : M.State}
    (hHandle : M.handle event s fun answer s' => PartialSpec M Q (k answer) s') :
    PartialSpec M Q (.vis event k) s :=
  intro (by simpa only [SpecF.vis] using hHandle)

theorem PartialSpec.ret_post {Q : α → M.State → Prop} {value : α} {s : M.State}
    (hSpec : PartialSpec M Q (.ret value) s) : Q value s := by
  simpa only [SpecF.ret] using hSpec.step

/-- `PartialSpec.ret`/`PartialSpec.ret_post` as one rewrite. -/
@[simp]
theorem PartialSpec.ret_iff {Q : α → M.State → Prop} {value : α} {s : M.State} :
    PartialSpec M Q (.ret value) s ↔ Q value s :=
  ⟨PartialSpec.ret_post, PartialSpec.ret⟩

/-- The event destructor; the counterpart of `TotalSpec.vis_view`. -/
theorem PartialSpec.vis_view {Q : α → M.State → Prop} {event : E.I}
    {k : E.O event → ITree E α} {s : M.State}
    (hSpec : PartialSpec M Q (.vis event k) s) :
    M.handle event s fun answer s' => PartialSpec M Q (k answer) s' := by
  simpa only [SpecF.vis] using hSpec.step

/-! ## What the two judgments say of each other -/

/-- Total correctness is partial correctness. -/
theorem TotalSpec.toPartial {Q : α → M.State → Prop} {m : ITree E α}
    {s : M.State} (hSpec : TotalSpec M Q m s) : PartialSpec M Q m s :=
  hSpec.induction (P := PartialSpec M Q) (fun _ _ hPost => .ret hPost)
    fun _ _ _ hHandle => .vis hHandle

/-! ## Structural rules -/

theorem TotalSpec.mono {Q Q' : α → M.State → Prop} {m : ITree E α} {s : M.State}
    (hSpec : TotalSpec M Q m s) (hQ : ∀ value s, Q value s → Q' value s) :
    TotalSpec M Q' m s :=
  hSpec.induction (P := TotalSpec M Q')
    (fun value s' hPost => .ret (hQ value s' hPost)) fun _ _ _ hHandle => .vis hHandle

theorem PartialSpec.mono {Q Q' : α → M.State → Prop} {m : ITree E α} {s : M.State}
    (hSpec : PartialSpec M Q m s) (hQ : ∀ value s, Q value s → Q' value s) :
    PartialSpec M Q' m s :=
  coinduction (PartialSpec M Q)
    (fun _ _ hSpec' => hSpec'.step.mono hQ id fun _ _ => id) hSpec

theorem TotalSpec.bind {Q₁ : α → M.State → Prop} {Q₂ : β → M.State → Prop}
    {m : ITree E α} {next : α → ITree E β} {s : M.State}
    (hFirst : TotalSpec M Q₁ m s)
    (hNext : ∀ value s', Q₁ value s' → TotalSpec M Q₂ (next value) s') :
    TotalSpec M Q₂ (ITree.bind m next) s :=
  hFirst.induction (P := fun t u => TotalSpec M Q₂ (ITree.bind t next) u)
    (fun value s' hPost => by
      simpa only [itree_ret_bind] using hNext value s' hPost)
    fun _ _ _ hHandle => by
      rw [itree_vis_bind]
      exact .vis hHandle

theorem PartialSpec.bind {Q₁ : α → M.State → Prop} {Q₂ : β → M.State → Prop}
    {m : ITree E α} {next : α → ITree E β} {s : M.State}
    (hFirst : PartialSpec M Q₁ m s)
    (hNext : ∀ value s', Q₁ value s' → PartialSpec M Q₂ (next value) s') :
    PartialSpec M Q₂ (ITree.bind m next) s := by
  refine coinduction
    (fun t s' => (∃ m', t = ITree.bind m' next ∧ PartialSpec M Q₁ m' s') ∨
      PartialSpec M Q₂ t s')
    ?_ (Or.inl ⟨m, rfl, hFirst⟩)
  rintro t s' (⟨m', rfl, hSpec⟩ | hSpec)
  · revert hSpec
    cases m' using ITree.cases with
    | ret value =>
        simp only [ITree.pure_eq_ret, itree_ret_bind]
        intro hSpec
        exact ((hNext value s' hSpec.ret_post).step).mono_tail fun _ _ => Or.inr
    | div => simp only [itree_div_bind, SpecF.div, implies_true]
    | vis event k =>
        simp only [itree_vis_bind, SpecF.vis]
        intro hSpec
        exact M.handle_mono (fun _ _ hNext' => Or.inl ⟨_, rfl, hNext'⟩) hSpec.vis_view
  · exact hSpec.step.mono_tail fun _ _ => Or.inr

/-- Total correctness is monotone in the interaction-tree approximation order:
what a program does, a program that does more does too. -/
theorem TotalSpec.mono_le {Q : α → M.State → Prop} {m m' : ITree E α}
    (hLe : m ⊑ m') {s : M.State} (hSpec : TotalSpec M Q m s) :
    TotalSpec M Q m' s := by
  refine hSpec.induction
    (P := fun t u => ∀ t', t ⊑ t' → TotalSpec M Q t' u) ?_ ?_ m' hLe
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
      exact .vis (M.handle_mono (fun answer _ hNext => hNext _ (hLe'' answer)) hHandle)

/-- Partial correctness is anti-monotone in the tree approximation order. -/
theorem PartialSpec.mono_le {Q : α → M.State → Prop} {m m' : ITree E α}
    (hLe : m ⊑ m') {s : M.State} (hSpec : PartialSpec M Q m' s) :
    PartialSpec M Q m s := by
  refine coinduction (fun t s' => ∃ t', t ⊑ t' ∧ PartialSpec M Q t' s') ?_
    ⟨m', hLe, hSpec⟩
  rintro t s' ⟨t', hLe', hSpec'⟩
  rw [ITree.le_unfold] at hLe'
  obtain rfl | ⟨value, rfl, rfl⟩ | ⟨event, k, k', rfl, rfl, hCont⟩ := hLe'
  · simp only [SpecF.div]
  · simpa only [SpecF.ret] using hSpec'.ret_post
  · simp only [SpecF.vis]
    exact M.handle_mono (fun answer _ hNext => ⟨_, hCont answer, hNext⟩)
      hSpec'.vis_view

/-! ## Partial correctness at a limit -/

/-- Partial correctness on a conjunctive machine is admissible. -/
theorem PartialSpec.admissible (hConj : M.Conjunctive) (Q : α → M.State → Prop)
    (s : M.State) :
    Lean.Order.admissible (fun m : ITree E α => PartialSpec M Q m s) := by
  intro c hc hAll
  refine coinduction
    (fun t u => ∃ c' : ITree E α → Prop, ∃ hc' : chain c',
      (∀ x, c' x → PartialSpec M Q x u) ∧ t = CCPO.csup hc')
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
      -- One transition answers every approximation's demand.
      obtain ⟨k₀, hMem₀⟩ := ITree.csup_vis_mem hc' hEq
      have hChildren :
          M.handle event u fun answer u' =>
            ∀ k' : { k' : E.O event → ITree E α // c' (ITree.vis event k') },
              PartialSpec M Q (k'.val answer) u' :=
        hConj.handle_forall ⟨k₀, hMem₀⟩ fun k' => (hAll' _ k'.property).vis_view
      -- Limit children are suprema of approximation children.
      obtain rfl : k = fun o => CCPO.csup (ITree.visChain_chain hc' event o) := by
        rw [ITree.csup_vis hc' hMem₀] at hEq
        obtain ⟨-, hCont⟩ := vis_inj hEq.symm
        exact eq_of_heq hCont
      refine M.handle_mono (fun answer u' hChild => ?_) hChildren
      exact ⟨ITree.visChain c' event answer, ITree.visChain_chain hc' event answer,
        by rintro _ ⟨k', hMem', rfl⟩; exact hChild ⟨k', hMem'⟩, rfl⟩

/-! ## Adequacy -/

/-- Total correctness is execution to a return satisfying the postcondition. -/
theorem TotalSpec.exec_iff {Q : α → M.State → Prop} {m : ITree E α} {s : M.State} :
    TotalSpec M Q m s ↔
      Exec M m s fun t u => ∃ value, t = ITree.ret value ∧ Q value u := by
  constructor
  · intro hSpec
    exact hSpec.induction
      (P := fun t u => Exec M t u fun t' u' => ∃ value, t' = ITree.ret value ∧ Q value u')
      (fun value s' hPost => Exec.stop ⟨value, rfl, hPost⟩)
      fun _ _ _ hHandle => Exec.event hHandle
  · intro hExec
    refine hExec.induction (P := fun t u => TotalSpec M Q t u) ?_
      fun _ _ _ hHandle => TotalSpec.vis hHandle
    rintro m' s' ⟨value, rfl, hPost⟩
    exact TotalSpec.ret hPost

/-- A total specification on a resolving machine yields a terminating run. -/
theorem TotalSpec.evaluates (hResolves : M.Resolves) {Q : α → M.State → Prop}
    {m : ITree E α} {s : M.State} (hSpec : TotalSpec M Q m s) :
    ∃ value s', M.Evaluates m s value s' ∧ Q value s' := by
  obtain ⟨m', s', hRuns, value, rfl, hPost⟩ :=
    Exec.exists_stop hResolves (TotalSpec.exec_iff.mp hSpec)
  exact ⟨value, s', hRuns, hPost⟩

/-- Partial correctness is preserved by every run of the machine: it is a
property of a configuration, not of the program it started from. -/
theorem PartialSpec.runs (hConj : M.Conjunctive) (hFeasible : M.Feasible)
    {Q : α → M.State → Prop}
    {m m' : ITree E α} {s s' : M.State} (hSpec : PartialSpec M Q m s)
    (hRuns : M.Runs m s m' s') : PartialSpec M Q m' s' := by
  refine hRuns.induction
    (P := fun t u => PartialSpec M Q t u → PartialSpec M Q m' s')
    (fun t u hStop hSpec' => by
      obtain ⟨rfl, rfl⟩ := hStop
      exact hSpec')
    (fun event k u hHandle hSpec' => ?_) hSpec
  -- One feasible transition meets both demands.
  obtain ⟨answer, u', hPreserves, hChild⟩ :=
    hFeasible _ _ _ (hConj.handle_and hHandle hSpec'.vis_view)
  exact hPreserves hChild

/-- A run of a partially correct program that stops establishes the
postcondition. -/
theorem PartialSpec.evaluates (hConj : M.Conjunctive) (hFeasible : M.Feasible)
    {Q : α → M.State → Prop}
    {m : ITree E α} {s : M.State} {value : α} {s' : M.State}
    (hSpec : PartialSpec M Q m s) (hEval : M.Evaluates m s value s') :
    Q value s' :=
  (hSpec.runs hConj hFeasible hEval).ret_post

end Aeneas.Data.Coinductive

namespace Aeneas.Data.Coinductive.StateTest

inductive StateEvent : Type 1 where
  | get
  | put (value : Nat)
  | fail
  | choose (α : Type)

@[reducible]
def StateEvent.output : StateEvent → Type 1
  | .get => ULift Nat
  | .put _ => ULift Unit
  | .fail => ULift Unit
  | .choose α => ULift α

@[reducible]
def StateEffect : Effect where
  I := StateEvent
  O := StateEvent.output

@[reducible]
def machine : StateMachine StateEffect where
  State := Nat
  handle event state C :=
    match event with
    | .get => C ⟨state⟩ state
    | .put value => C ⟨()⟩ value
    | .fail => False
    | .choose α => Nonempty α ∧ ∀ answer, C ⟨answer⟩ state
  handle_mono := by
    rintro event state C C' hC hHandle
    cases event
    · exact hC _ _ hHandle
    · exact hC _ _ hHandle
    · exact hHandle.elim
    · exact ⟨hHandle.1, fun answer => hC _ _ (hHandle.2 answer)⟩

theorem machine_conjunctive : machine.Conjunctive := by
  rintro event state Demands ⟨C₀, hC₀⟩ hAll
  cases event
  · exact fun C hC => hAll C hC
  · exact fun C hC => hAll C hC
  · exact (hAll C₀ hC₀).elim
  · exact ⟨(hAll C₀ hC₀).1, fun answer C hC => (hAll C hC).2 answer⟩

theorem machine_feasible : machine.Feasible := by
  rintro event state C hHandle
  cases event
  · exact ⟨⟨state⟩, state, hHandle⟩
  · rename_i value
    exact ⟨⟨()⟩, value, hHandle⟩
  · exact hHandle.elim
  · obtain ⟨⟨answer⟩, hAll⟩ := hHandle
    exact ⟨⟨answer⟩, state, hAll answer⟩

theorem not_machine_resolves : ¬ machine.Resolves := by
  intro hResolves
  obtain ⟨answer, state', -, hHandle⟩ :=
    hResolves (.choose Bool) 0 (fun _ _ => True) ⟨⟨true⟩, fun _ => trivial⟩
  have hTrue := (hHandle.2 true).1
  have hFalse := (hHandle.2 false).1
  have hEq := hTrue.trans hFalse.symm
  simp only [ULift.up.injEq] at hEq
  exact Bool.noConfusion hEq

def spec (m : ITree StateEffect α) (p : α → Nat → Prop) (state : Nat) : Prop :=
  TotalSpec machine p m state

def dspec (m : ITree StateEffect α) (p : α → Nat → Prop) (state : Nat) : Prop :=
  PartialSpec machine p m state

example (Q : Nat → Nat → Prop) :
    Lean.Order.admissible fun computation : ITree StateEffect Nat =>
      dspec computation Q 0 :=
  PartialSpec.admissible machine_conjunctive Q 0

def get : ITree StateEffect Nat :=
  .vis .get fun value => .ret value.down

def put (value : Nat) : ITree StateEffect Unit :=
  .vis (.put value) fun result => .ret result.down

def fail : ITree StateEffect Unit :=
  .vis .fail fun result => .ret result.down

def choose (α : Type) : ITree StateEffect α :=
  .vis (.choose α) fun result => .ret result.down

def increment : ITree StateEffect Nat :=
  do
    let value ← get
    let _ ← put (value + 1)
    return value

def failure : ITree StateEffect Unit :=
  do
    let _ ← fail
    return ()

def flip : ITree StateEffect Nat :=
  do
    let answer ← choose Bool
    return if answer then 0 else 1

theorem increment_spec (state : Nat) :
    spec increment (fun value state' => value = state ∧ state' = state + 1)
      state := by
  simp [spec, increment, get, put, Bind.bind]
  apply TotalSpec.vis
  apply TotalSpec.vis
  exact TotalSpec.ret ⟨rfl, rfl⟩

example (state : Nat) :
    ∃ value state',
      machine.Evaluates increment state value state' ∧
      value = state ∧ state' = state + 1 := by
  refine ⟨state, state + 1, ?_, rfl, rfl⟩
  simp [increment, get, put, Bind.bind]
  apply StateMachine.Evaluates.event
  apply StateMachine.Evaluates.event
  exact StateMachine.Evaluates.ret state (state + 1)

example (state : Nat) :
    spec increment (fun value state' => value = state ∧ state' = state + 1)
      state :=
  increment_spec state

example (state : Nat) :
    dspec increment (fun value state' => value = state ∧ state' = state + 1)
      state :=
  TotalSpec.toPartial (increment_spec state)

example (state : Nat) :
    spec flip (fun value state' => (value = 0 ∨ value = 1) ∧ state' = state)
      state := by
  simp [spec, flip, choose, Bind.bind]
  apply TotalSpec.vis
  change Nonempty Bool ∧ ∀ answer : Bool,
    TotalSpec machine
      (fun value state' => (value = 0 ∨ value = 1) ∧ state' = state)
      (.ret (if answer then 0 else 1)) state
  constructor
  · exact ⟨true⟩
  · intro answer
    apply TotalSpec.ret
    cases answer
    · simp
    · simp

example (state : Nat) :
    dspec flip (fun value state' => (value = 0 ∨ value = 1) ∧ state' = state)
      state :=
  TotalSpec.toPartial (show
    spec flip (fun value state' => (value = 0 ∨ value = 1) ∧ state' = state)
      state by
    simp [spec, flip, choose, Bind.bind]
    apply TotalSpec.vis
    change Nonempty Bool ∧ ∀ answer : Bool,
      TotalSpec machine
        (fun value state' => (value = 0 ∨ value = 1) ∧ state' = state)
        (.ret (if answer then 0 else 1)) state
    constructor
    · exact ⟨true⟩
    · intro answer
      apply TotalSpec.ret
      cases answer
      · simp
      · simp)

example {Q : Nat → Nat → Prop} {m m' : ITree StateEffect Nat}
    {state state' : Nat} (hSpec : dspec m Q state)
    (hRuns : machine.Runs m state m' state') :
    dspec m' Q state' :=
  hSpec.runs machine_conjunctive machine_feasible hRuns

example (state : Nat) (Q : Unit → Nat → Prop) :
    ¬ spec failure Q state := by
  intro hSpec
  simp [spec, failure, fail, Bind.bind] at hSpec
  exact hSpec.vis_view

example (state : Nat) (Q : Unit → Nat → Prop) :
    ¬ dspec failure Q state := by
  intro hSpec
  simp [dspec, failure, fail, Bind.bind] at hSpec
  exact hSpec.vis_view

end Aeneas.Data.Coinductive.StateTest
