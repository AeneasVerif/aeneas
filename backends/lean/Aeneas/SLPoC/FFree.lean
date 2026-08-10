/-!
# The freer monad and the state machines that run it

`FFree E` is the freer monad over the event signature `E`: a program is a tree
of events, each followed by a continuation.  It fixes no meaning for the events
— that is the job of a **state machine** for `E`, defined in the second half of
this file following *Program Logics à la Carte* (Vistrup, Sammler and Jung,
POPL 2025, §5 "Angelic Choice and State Machine Adequacy"): a single-step
relation saying how the machine answers one event, and nothing else.  The
traversal of the program — which is the same for every signature — is factored
out into the multi-step relation `Exec` defined once and for all here.

The correspondence with the Coq development of the paper (`src/exec.v`) is:

| Here | Paper |
|---|---|
| `StateMachine` | `seHandler`, the single-step relation |
| `StateMachine.handle` | `sehandle` |
| `StateMachine.handle_mono` | `sehandler_mono` |
| `Exec` | `exec`, the multi-step relation |
| `Exec.stop`, `Exec.event` | the variants `ExecStop`, `ExecVis` of `execF` |
| `Exec.dup`, `Exec.bind` | `exec_dup`, `exec_bind` |

There is no counterpart of the variant `ExecTau`: `FFree` is inductive and has
no silent step, so `Exec` is an ordinary structural recursion instead of the
paper's coinductive fixed point.

A machine is *angelic*: `M.handle e s C` holds when **some** transition of `M`
answers `e` in the state `s` with a result and a successor state satisfying `C`
— see `StateMachine.ofStep`, which builds a machine from a transition relation.
Accordingly `Exec M m s C` states that `m` *has* an execution from `s` stopping
in a configuration satisfying `C`, which is what a program logic for `FFree` is
adequate against (`Exec.exists_stop`).
-/

namespace Aeneas.SLPoC

/-! ## The freer monad -/

inductive FFree (E : Type → Type 1) (α : Type) : Type 1 where
  | ok (value : α)
  | event {β : Type} (e : E β) (next : β → FFree E α)

namespace FFree

def bind {E : Type → Type 1} {α β : Type} (m : FFree E α)
    (next : α → FFree E β) : FFree E β :=
  match m with
  | .ok value => next value
  | .event e k =>
    .event e fun result => bind (k result) next

instance (E : Type → Type 1) : Monad (FFree E) where
  pure := .ok
  bind := bind

instance (E : Type → Type 1) : LawfulMonad (FFree E) :=
  LawfulMonad.mk' (FFree E)
    (id_map := by
      intro α m
      induction m
      · rfl
      · rename_i β event next ih
        simp only [Functor.map, bind]
        apply congrArg (FFree.event event)
        funext value
        exact ih value)
    (pure_bind := by intros; rfl)
    (bind_assoc := by
      intro α β γ m next₁ next₂
      induction m
      · rfl
      · rename_i δ event next ih
        apply congrArg (FFree.event event)
        funext value
        exact ih value)

def trigger {E : Type → Type 1} {α : Type} (e : E α) : FFree E α :=
  .event e .ok

end FFree

/-! ## State machines -/

universe u

variable {E : Type → Type 1} {α β γ : Type}

/-- A state machine for the event signature `E`: the single-step relation of
*Program Logics à la Carte*, where it is called `seHandler`.

The transitions are given in continuation-passing style rather than as a plain
relation, so that a machine may constrain the answer to an event by an arbitrary
predicate on the outcome — for instance, by requiring the pointer an allocation
returns to be fresh. -/
structure StateMachine (E : Type → Type 1) where
  /-- The states the machine runs on. -/
  State : Type u
  /-- `handle e s C` holds when the machine can answer the event `e` in the
  state `s` by a transition whose result and successor state satisfy `C`. -/
  handle : {β : Type} → E β → State → (β → State → Prop) → Prop
  /-- Answering an event with a stronger outcome answers it with a weaker one
  (`sehandler_mono` in the paper). -/
  handle_mono : ∀ {β : Type} {e : E β} {s : State} {C C' : β → State → Prop},
    (∀ result s', C result s' → C' result s') → handle e s C → handle e s C'

namespace StateMachine

/-- The machine on states `σ` whose transitions are the quadruples of `Step`:
`Step e s result s'` says that the event `e` may be answered in the state `s`
with `result`, leaving the state `s'`.

Every machine of an operational semantics arises this way; `handle` is more
general only in that it also accommodates the angelic and demonic choice
operators of the paper. -/
def ofStep (σ : Type u) (Step : {β : Type} → E β → σ → β → σ → Prop) :
    StateMachine E where
  State := σ
  handle e s C := ∃ result s', Step e s result s' ∧ C result s'
  handle_mono := by
    rintro β e s C C' hC ⟨result, s', hStep, hOutcome⟩
    exact ⟨result, s', hStep, hC result s' hOutcome⟩

/-- The handler *resolves* its transitions: whenever it answers an event with an
outcome satisfying `C`, one single transition already does.  This is what makes
`Exec M m s C` mean that `m` has a concrete execution stopping in `C`
(`Exec.exists_stop`); every machine built by `ofStep` resolves. -/
def Resolves (M : StateMachine E) : Prop :=
  ∀ {β : Type} (e : E β) (s : M.State) (C : β → M.State → Prop),
    M.handle e s C →
    ∃ result s', C result s' ∧ M.handle e s fun r u => r = result ∧ u = s'

theorem ofStep_resolves (σ : Type u)
    (Step : {β : Type} → E β → σ → β → σ → Prop) :
    (ofStep σ Step).Resolves := by
  rintro β e s C ⟨result, s', hStep, hOutcome⟩
  exact ⟨result, s', hOutcome, result, s', hStep, rfl, rfl⟩

end StateMachine

/-! ## The multi-step relation -/

/-- The multi-step relation `exec` of *Program Logics à la Carte*:
`Exec M m s C` holds when the program `m`, run by the machine `M` from the
state `s`, has an execution that stops in a configuration satisfying `C`.

An execution may stop at any point — that is the variant `ExecStop` of the
paper, and the left disjunct below — which is what makes `Exec` compose
(`Exec.dup`, `Exec.bind`). -/
def Exec (M : StateMachine E) :
    FFree E α → M.State → (FFree E α → M.State → Prop) → Prop
  | .ok value, s, C => C (.ok value) s
  | .event e next, s, C =>
      C (.event e next) s ∨
        M.handle e s fun result s' => Exec M (next result) s' C

namespace Exec

variable {M : StateMachine E} {C C' : FFree E α → M.State → Prop}

/-- An execution may stop where it stands (`ExecStop`). -/
theorem stop {m : FFree E α} {s : M.State} (hC : C m s) : Exec M m s C := by
  cases m with
  | ok value => exact hC
  | event e next => exact Or.inl hC

/-- An execution may take one transition of the machine (`ExecVis`). -/
theorem event {e : E β} {next : β → FFree E α} {s : M.State}
    (hHandle : M.handle e s fun result s' => Exec M (next result) s' C) :
    Exec M (.event e next) s C :=
  Or.inr hHandle

theorem mono {m : FFree E α} {s : M.State} (hExec : Exec M m s C)
    (hC : ∀ m' s', C m' s' → C' m' s') : Exec M m s C' := by
  revert s
  induction m with
  | ok value =>
      intro s hExec
      exact hC _ _ hExec
  | event e next ih =>
      intro s hExec
      exact hExec.imp (hC _ _) fun hHandle =>
        M.handle_mono (fun result s' hNext => ih result hNext) hHandle

/-- Executions compose: `exec_dup` of the paper. -/
theorem dup {m : FFree E α} {s : M.State}
    (hExec : Exec M m s fun m' s' => Exec M m' s' C) : Exec M m s C := by
  revert s
  induction m with
  | ok value =>
      intro s hExec
      exact hExec
  | event e next ih =>
      intro s hExec
      exact hExec.elim id fun hHandle =>
        Or.inr (M.handle_mono (fun result s' hNext => ih result hNext) hHandle)

/-- Running `m >>= next` amounts to running `m` and continuing with `next`;
`exec_bind_post` of the paper. -/
theorem bind_post {m : FFree E α} {s : M.State} {next : α → FFree E γ}
    {C : FFree E γ → M.State → Prop}
    (hExec : Exec M m s fun m' s' => C (m' >>= next) s') :
    Exec M (m >>= next) s C := by
  revert s
  induction m with
  | ok value =>
      intro s hExec
      exact stop hExec
  | event e k ih =>
      intro s hExec
      exact hExec.imp id fun hHandle =>
        M.handle_mono (fun result s' hNext => ih result hNext) hHandle

/-- `exec_bind` of the paper. -/
theorem bind {m : FFree E α} {s : M.State} {next : α → FFree E γ}
    {C : FFree E γ → M.State → Prop}
    (hExec : Exec M m s fun m' s' => Exec M (m' >>= next) s' C) :
    Exec M (m >>= next) s C :=
  dup (bind_post hExec)

end Exec

/-! ## Reachability and evaluation -/

namespace StateMachine

/-- `M.Runs m s m' s'`: the machine `M` takes the configuration `(m, s)` to the
configuration `(m', s')`. -/
def Runs (M : StateMachine E) (m : FFree E α) (s : M.State) (m' : FFree E α)
    (s' : M.State) : Prop :=
  Exec M m s fun t u => t = m' ∧ u = s'

/-- `M.Evaluates m s value s'`: the program `m`, run by the machine `M` from the
state `s`, returns `value` and leaves the state `s'`. -/
def Evaluates (M : StateMachine E) (m : FFree E α) (s : M.State) (value : α)
    (s' : M.State) : Prop :=
  M.Runs m s (.ok value) s'

variable {M : StateMachine E}

theorem Runs.refl (m : FFree E α) (s : M.State) : M.Runs m s m s :=
  Exec.stop ⟨rfl, rfl⟩

theorem Evaluates.ok (value : α) (s : M.State) :
    M.Evaluates (.ok value) s value s :=
  Runs.refl _ _

theorem Evaluates.pure (value : α) (s : M.State) :
    M.Evaluates (Pure.pure value) s value s :=
  Evaluates.ok value s

/-- An evaluation that begins with one transition of the machine. -/
theorem Evaluates.event {e : E β} {next : β → FFree E α} {s s' : M.State}
    {value : α}
    (hHandle :
      M.handle e s fun result u => M.Evaluates (next result) u value s') :
    M.Evaluates (.event e next) s value s' :=
  Exec.event hHandle

/-- An evaluation that begins with one transition of a machine given by a
transition relation. -/
theorem Evaluates.step {σ : Type u} {Step : {β : Type} → E β → σ → β → σ → Prop}
    {e : E β} {next : β → FFree E α} {s s₁ s₂ : σ} {result : β} {value : α}
    (hStep : Step e s result s₁)
    (hNext : (ofStep σ Step).Evaluates (next result) s₁ value s₂) :
    (ofStep σ Step).Evaluates (.event e next) s value s₂ :=
  Exec.event (M := ofStep σ Step) ⟨result, s₁, hStep, hNext⟩

theorem Evaluates.bind {m : FFree E α} {next : α → FFree E γ}
    {s s₁ s₂ : M.State} {value : α} {result : γ}
    (hFirst : M.Evaluates m s value s₁)
    (hNext : M.Evaluates (next value) s₁ result s₂) :
    M.Evaluates (m >>= next) s result s₂ :=
  Exec.bind (Exec.mono hFirst fun m' s' hStop => by
    obtain ⟨rfl, rfl⟩ := hStop
    exact hNext)

end StateMachine

namespace Exec

/-- An execution of a machine that resolves its transitions can be realised: it
is an actual run of the program to a configuration satisfying `C`.

This is what justifies reading `Exec M m s C` as "`m` has an execution stopping
in `C`", and it is how the adequacy of a program logic stated in terms of `Exec`
is turned into a statement about a concrete evaluation. -/
theorem exists_stop {M : StateMachine E} (hResolves : M.Resolves)
    {m : FFree E α} {s : M.State} {C : FFree E α → M.State → Prop}
    (hExec : Exec M m s C) :
    ∃ m' s', M.Runs m s m' s' ∧ C m' s' := by
  revert s
  induction m with
  | ok value =>
      intro s hExec
      exact ⟨.ok value, s, StateMachine.Runs.refl _ _, hExec⟩
  | event e next ih =>
      intro s hExec
      rcases hExec with hStop | hHandle
      · exact ⟨.event e next, s, StateMachine.Runs.refl _ _, hStop⟩
      · obtain ⟨result, s₁, hNext, hSingle⟩ := hResolves e s _ hHandle
        obtain ⟨m', s₂, hRuns, hC⟩ := ih result hNext
        refine ⟨m', s₂, event ?_, hC⟩
        refine M.handle_mono (fun r u hOutcome => ?_) hSingle
        obtain ⟨rfl, rfl⟩ := hOutcome
        exact hRuns

end Exec

end Aeneas.SLPoC
