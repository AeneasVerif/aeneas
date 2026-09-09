import Aeneas.Data.Coinductive.ITree

/-!
# Interaction trees and the state machines that run them

State machines assign transitions to interaction-tree events.
`Exec` is their finite multi-step execution relation.
Based on the POPL 2025 paper *Program Logics à la Carte*.
-/

namespace Aeneas.Data.Coinductive

universe u v w x

variable {E : Effect.{v}} {α β γ : Type x}

/-! ## State machines -/

/-- A state machine with continuation-passing event transitions. -/
structure StateMachine (E : Effect.{v}) where
  /-- The states the machine runs on. -/
  State : Type u
  /-- `handle e s C` holds when the machine can answer the event `e` in the
  state `s` by a transition whose result and successor state satisfy `C`. -/
  handle : (event : E.I) → State → (E.O event → State → Prop) → Prop
  /-- Answering an event with a stronger outcome answers it with a weaker one
  (`sehandler_mono` in the paper). -/
  handle_mono :
    ∀ {event : E.I} {s : State} {C C' : E.O event → State → Prop},
      (∀ answer s', C answer s' → C' answer s') →
      handle event s C → handle event s C'

namespace StateMachine

/-- Build a state machine from a transition relation. -/
def ofStep (σ : Type u) (Step : (event : E.I) → σ → E.O event → σ → Prop) :
    StateMachine E where
  State := σ
  handle event s C := ∃ answer s', Step event s answer s' ∧ C answer s'
  handle_mono := by
    rintro event s C C' hC ⟨answer, s', hStep, hOutcome⟩
    exact ⟨answer, s', hStep, hC answer s' hOutcome⟩

/-- Every handled demand is witnessed by one concrete transition. -/
def Resolves (M : StateMachine E) : Prop :=
  ∀ (event : E.I) (s : M.State) (C : E.O event → M.State → Prop),
    M.handle event s C →
    ∃ answer s', C answer s' ∧ M.handle event s fun a u => a = answer ∧ u = s'

theorem ofStep_resolves (σ : Type u)
    (Step : (event : E.I) → σ → E.O event → σ → Prop) :
    (ofStep σ Step).Resolves := by
  rintro event s C ⟨answer, s', hStep, hOutcome⟩
  exact ⟨answer, s', hOutcome, answer, s', hStep, rfl, rfl⟩

/-- Every handled demand has an answer and successor state. -/
def Feasible (M : StateMachine E) : Prop :=
  ∀ (event : E.I) (s : M.State) (C : E.O event → M.State → Prop),
    M.handle event s C → ∃ answer s', C answer s'

/-- One transition can satisfy every demand in a nonempty family.
This excludes genuine angelic choice. -/
def Conjunctive (M : StateMachine E) : Prop :=
  ∀ {event : E.I} {s : M.State}
    (Demands : (E.O event → M.State → Prop) → Prop), (∃ C, Demands C) →
    (∀ C, Demands C → M.handle event s C) →
    M.handle event s fun answer s' => ∀ C, Demands C → C answer s'

theorem ofStep_conjunctive (σ : Type u)
    (Step : (event : E.I) → σ → E.O event → σ → Prop)
    (hFunctional : ∀ (event : E.I) (s : σ) (answer₁ : E.O event) (s₁ : σ)
      (answer₂ : E.O event) (s₂ : σ),
      Step event s answer₁ s₁ → Step event s answer₂ s₂ → answer₁ = answer₂ ∧ s₁ = s₂) :
    (ofStep σ Step).Conjunctive := by
  rintro event s Demands ⟨C₀, hC₀⟩ hAll
  obtain ⟨answer, s', hStep, -⟩ := hAll C₀ hC₀
  refine ⟨answer, s', hStep, fun C hC => ?_⟩
  obtain ⟨answer', s'', hStep', hOutcome⟩ := hAll C hC
  obtain ⟨rfl, rfl⟩ := hFunctional event s answer' s'' answer s' hStep' hStep
  exact hOutcome

variable {M : StateMachine E}

theorem Resolves.feasible (hResolves : M.Resolves) : M.Feasible := by
  intro event s C hHandle
  obtain ⟨answer, s', hOutcome, -⟩ := hResolves event s C hHandle
  exact ⟨answer, s', hOutcome⟩

/-- `Conjunctive` at a family rather than a set: one transition answers a whole
inhabited family of demands at once. -/
theorem Conjunctive.handle_forall (hConj : M.Conjunctive) {ι : Sort w} (i₀ : ι)
    {event : E.I} {s : M.State} {C : ι → E.O event → M.State → Prop}
    (hHandle : ∀ i, M.handle event s (C i)) :
    M.handle event s fun answer s' => ∀ i, C i answer s' := by
  refine M.handle_mono (fun _ _ hAll i => hAll (C i) ⟨i, rfl⟩)
    (hConj (fun X => ∃ i, X = C i) ⟨C i₀, i₀, rfl⟩ ?_)
  rintro X ⟨i, rfl⟩
  exact hHandle i

/-- `Conjunctive` at two demands. -/
theorem Conjunctive.handle_and (hConj : M.Conjunctive) {event : E.I} {s : M.State}
    {C C' : E.O event → M.State → Prop} (hHandle : M.handle event s C)
    (hHandle' : M.handle event s C') :
    M.handle event s fun answer s' => C answer s' ∧ C' answer s' := by
  refine M.handle_mono (fun _ _ hBoth => ⟨hBoth true, hBoth false⟩)
    (hConj.handle_forall (ι := Bool) (C := fun b => bif b then C else C') true ?_)
  rintro (_ | _) <;> assumption

end StateMachine

/-! ## The multi-step relation -/

/-- One execution layer: stop, or handle one visible event. -/
def ExecF (M : StateMachine.{u,v} E)
    (C X : ITree E α → M.State → Prop) (m : ITree E α) (s : M.State) : Prop :=
  C m s ∨
    match m.unfold with
    | .vis event k => M.handle event s fun answer s' => X (k answer) s'
    | _ => False

/-- Finite execution from `(m, s)` to a configuration satisfying `C`. -/
def Exec (M : StateMachine E) (m : ITree E α) (s : M.State)
    (C : ITree E α → M.State → Prop) : Prop :=
  ∀ X : ITree E α → M.State → Prop,
    (∀ m' s', ExecF M C X m' s' → X m' s') → X m s

namespace Exec

variable {M : StateMachine E} {C C' P : ITree E α → M.State → Prop}

/-- An execution may stop where it stands (`ExecStop`). -/
theorem stop {m : ITree E α} {s : M.State} (hC : C m s) : Exec M m s C :=
  fun _ hClosed => hClosed m s (Or.inl hC)

/-- An execution may take one transition of the machine (`ExecVis`). -/
theorem event {event : E.I} {k : E.O event → ITree E α} {s : M.State}
    (hHandle : M.handle event s fun answer s' => Exec M (k answer) s' C) :
    Exec M (.vis event k) s C := by
  intro X hClosed
  refine hClosed _ s (Or.inr ?_)
  simp only [unfold_vis]
  exact M.handle_mono (fun answer s' hExec => hExec X hClosed) hHandle

/-- The induction principle of `Exec`: a property that holds wherever an
execution may stop and is preserved by one transition of the machine holds of
every configuration an execution starts from. -/
theorem induction {m : ITree E α} {s : M.State} (hExec : Exec M m s C)
    (hStop : ∀ m' s', C m' s' → P m' s')
    (hEvent : ∀ (event : E.I) (k : E.O event → ITree E α) (s' : M.State),
      M.handle event s' (fun answer u => P (k answer) u) → P (.vis event k) s') :
    P m s := by
  refine hExec P fun m' s' hStep => ?_
  rcases hStep with hC | hStep
  · exact hStop m' s' hC
  · revert hStep
    cases m' with
    | ret value => simp only [ITree.pure_eq_ret, unfold_ret, false_implies]
    | div => simp only [unfold_tau, false_implies]
    | vis event k =>
        simp only [unfold_vis]
        exact hEvent event k s'

theorem mono {m : ITree E α} {s : M.State} (hExec : Exec M m s C)
    (hC : ∀ m' s', C m' s' → C' m' s') : Exec M m s C' :=
  hExec.induction (fun m' s' hStop => stop (hC m' s' hStop)) fun _ _ _ => event

/-- Executions compose: `exec_dup` of the paper. -/
theorem dup {m : ITree E α} {s : M.State}
    (hExec : Exec M m s fun m' s' => Exec M m' s' C) : Exec M m s C :=
  hExec.induction (fun _ _ hStop => hStop) fun _ _ _ => event

/-- Running `m >>= next` amounts to running `m` and continuing with `next`;
`exec_bind_post` of the paper. -/
theorem bind_post {m : ITree E α} {s : M.State} {next : α → ITree E γ}
    {C : ITree E γ → M.State → Prop}
    (hExec : Exec M m s fun m' s' => C (m' >>= next) s') :
    Exec M (m >>= next) s C :=
  hExec.induction (P := fun m' s' => Exec M (m' >>= next) s' C)
    (fun _ _ hStop => stop hStop)
    fun ev k s' hHandle => by
      simpa only [vis_bind] using
        event (M := M) (event := ev) (k := fun answer => k answer >>= next) hHandle

/-- `exec_bind` of the paper. -/
theorem bind {m : ITree E α} {s : M.State} {next : α → ITree E γ}
    {C : ITree E γ → M.State → Prop}
    (hExec : Exec M m s fun m' s' => Exec M (m' >>= next) s' C) :
    Exec M (m >>= next) s C :=
  dup (bind_post hExec)

end Exec

/-! ## Reachability and evaluation -/

namespace StateMachine

/-- `M.Runs m s m' s'`: the machine `M` takes the configuration `(m, s)` to the
configuration `(m', s')`. -/
def Runs (M : StateMachine E) (m : ITree E α) (s : M.State) (m' : ITree E α)
    (s' : M.State) : Prop :=
  Exec M m s fun t u => t = m' ∧ u = s'

/-- `M.Evaluates m s value s'`: the program `m`, run by the machine `M` from the
state `s`, returns `value` and leaves the state `s'`. -/
def Evaluates (M : StateMachine E) (m : ITree E α) (s : M.State) (value : α)
    (s' : M.State) : Prop :=
  M.Runs m s (.ret value) s'

variable {M : StateMachine E}

theorem Runs.refl (m : ITree E α) (s : M.State) : M.Runs m s m s :=
  Exec.stop ⟨rfl, rfl⟩

theorem Evaluates.ret (value : α) (s : M.State) :
    M.Evaluates (.ret value) s value s :=
  Runs.refl _ _

/-- An evaluation that begins with one transition of the machine. -/
theorem Evaluates.event {event : E.I} {k : E.O event → ITree E α}
    {s s' : M.State} {value : α}
    (hHandle :
      M.handle event s fun answer u => M.Evaluates (k answer) u value s') :
    M.Evaluates (.vis event k) s value s' :=
  Exec.event hHandle

/-- An evaluation that begins with one transition of a machine given by a
transition relation. -/
theorem Evaluates.step {σ : Type u}
    {Step : (event : E.I) → σ → E.O event → σ → Prop}
    {event : E.I} {k : E.O event → ITree E α} {s s₁ s₂ : σ}
    {answer : E.O event} {value : α}
    (hStep : Step event s answer s₁)
    (hNext : (ofStep σ Step).Evaluates (k answer) s₁ value s₂) :
    (ofStep σ Step).Evaluates (.vis event k) s value s₂ :=
  Exec.event (M := ofStep σ Step) ⟨answer, s₁, hStep, hNext⟩

theorem Evaluates.bind {m : ITree E α} {next : α → ITree E γ}
    {s s₁ s₂ : M.State} {value : α} {result : γ}
    (hFirst : M.Evaluates m s value s₁)
    (hNext : M.Evaluates (next value) s₁ result s₂) :
    M.Evaluates (m >>= next) s result s₂ :=
  Exec.bind (Exec.mono hFirst fun m' s' hStop => by
    obtain ⟨rfl, rfl⟩ := hStop
    rw [show (ITree.ret value : ITree E α) >>= next = next value from
      itree_ret_bind value next]
    exact hNext)

end StateMachine

namespace Exec

/-- A resolving machine realizes an `Exec` witness as an actual run. -/
theorem exists_stop {M : StateMachine E} (hResolves : M.Resolves)
    {m : ITree E α} {s : M.State} {C : ITree E α → M.State → Prop}
    (hExec : Exec M m s C) :
    ∃ m' s', M.Runs m s m' s' ∧ C m' s' := by
  refine hExec.induction (P := fun m s => ∃ m' s', M.Runs m s m' s' ∧ C m' s')
    (fun m' s' hStop => ⟨m', s', StateMachine.Runs.refl _ _, hStop⟩)
    fun ev k s' hHandle => ?_
  obtain ⟨answer, s₁, hNext, hSingle⟩ := hResolves ev s' _ hHandle
  obtain ⟨m', s₂, hRuns, hC⟩ := hNext
  refine ⟨m', s₂, event ?_, hC⟩
  refine M.handle_mono (fun a u hOutcome => ?_) hSingle
  obtain ⟨rfl, rfl⟩ := hOutcome
  exact hRuns

end Exec

end Aeneas.Data.Coinductive
