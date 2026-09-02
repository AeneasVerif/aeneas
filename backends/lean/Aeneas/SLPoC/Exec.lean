import Aeneas.Data.Coinductive.ITree

/-!
# Interaction trees and the state machines that run them

A program is an **interaction tree** `ITree E α` over the event signature `E`
(`Aeneas.Data.Coinductive.ITree`): a possibly infinite tree of events, each
followed by a continuation.  It fixes no meaning for the events — that is the
job of a **state machine** for `E`, defined in the second half of this file
following *Program Logics à la Carte* (Vistrup, Sammler and Jung, POPL 2025, §5
"Angelic Choice and State Machine Adequacy"): a single-step relation saying how
the machine answers one event, and nothing else.  The traversal of the program —
which is the same for every signature — is factored out into the multi-step
relation `Exec` defined once and for all here.

The correspondence with the Coq development of the paper (`src/exec.v`) is:

| Here | Paper |
|---|---|
| `StateMachine` | `seHandler`, the single-step relation |
| `StateMachine.handle` | `sehandle` |
| `StateMachine.handle_mono` | `sehandler_mono` |
| `Exec` | `exec`, the multi-step relation |
| `Exec.stop`, `Exec.event` | the variants `ExecStop`, `ExecVis` of `execF` |
| `Exec.dup`, `Exec.bind` | `exec_dup`, `exec_bind` |

There is no counterpart of the variant `ExecTau`.  An interaction tree is
coinductive, so `Exec` can no longer be an ordinary structural recursion; it is
instead the **least** fixed point of the one-step unfolding `ExecF`, written
impredicatively as the intersection of the pre-fixed points of `ExecF`.  Least,
not greatest: an execution is a *finite* sequence of transitions, which is what
a total-correctness program logic must be adequate against.  The bottom element
`ITree.div` of the tree order — the tree of an unproductive recursion, where the
paper has an infinite stream of taus — accordingly offers no transition at all,
and `Exec M .div s C` holds only by stopping where it stands.

A machine is *angelic*: `M.handle e s C` holds when **some** transition of `M`
answers `e` in the state `s` with a result and a successor state satisfying `C`
— see `StateMachine.ofStep`, which builds a machine from a transition relation.
Accordingly `Exec M m s C` states that `m` *has* an execution from `s` stopping
in a configuration satisfying `C`, which is what a program logic for `ITree` is
adequate against (`Exec.exists_stop`).
-/

namespace Aeneas.SLPoC

open Aeneas.Data.Coinductive

universe u v w

variable {E : Effect.{v}} {α β γ : Type}

/-! ## State machines -/

/-- A state machine for the event signature `E`: the single-step relation of
*Program Logics à la Carte*, where it is called `seHandler`.

The transitions are given in continuation-passing style rather than as a plain
relation, so that a machine may constrain the answer to an event by an arbitrary
predicate on the outcome — for instance, by requiring the pointer an allocation
returns to be fresh. -/
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

/-- The machine on states `σ` whose transitions are the quadruples of `Step`:
`Step e s answer s'` says that the event `e` may be answered in the state `s`
with `answer`, leaving the state `s'`.

Every machine of an operational semantics arises this way; `handle` is more
general only in that it also accommodates the angelic and demonic choice
operators of the paper. -/
def ofStep (σ : Type u) (Step : (event : E.I) → σ → E.O event → σ → Prop) :
    StateMachine E where
  State := σ
  handle event s C := ∃ answer s', Step event s answer s' ∧ C answer s'
  handle_mono := by
    rintro event s C C' hC ⟨answer, s', hStep, hOutcome⟩
    exact ⟨answer, s', hStep, hC answer s' hOutcome⟩

/-- The handler *resolves* its transitions: whenever it answers an event with an
outcome satisfying `C`, one single transition already does.  This is what makes
`Exec M m s C` mean that `m` has a concrete execution stopping in `C`
(`Exec.exists_stop`); every machine built by `ofStep` resolves. -/
def Resolves (M : StateMachine E) : Prop :=
  ∀ (event : E.I) (s : M.State) (C : E.O event → M.State → Prop),
    M.handle event s C →
    ∃ answer s', C answer s' ∧ M.handle event s fun a u => a = answer ∧ u = s'

theorem ofStep_resolves (σ : Type u)
    (Step : (event : E.I) → σ → E.O event → σ → Prop) :
    (ofStep σ Step).Resolves := by
  rintro event s C ⟨answer, s', hStep, hOutcome⟩
  exact ⟨answer, s', hOutcome, answer, s', hStep, rfl, rfl⟩

end StateMachine

/-! ## The multi-step relation -/

/-- One step of `Exec`: either the execution stops where it stands — that is the
variant `ExecStop` of the paper — or the tree is a `vis` node whose event the
machine answers, the execution continuing in `X`.

A `ret` node has nothing left to do, and the divergent tree `ITree.div` never
does anything, so neither of them offers a transition. -/
def ExecF (M : StateMachine.{u,v} E)
    (C X : ITree E α → M.State → Prop) (m : ITree E α) (s : M.State) : Prop :=
  C m s ∨
    match m.unfold with
    | .vis event k => M.handle event s fun answer s' => X (k answer) s'
    | _ => False

/-- The multi-step relation `exec` of *Program Logics à la Carte*:
`Exec M m s C` holds when the program `m`, run by the machine `M` from the
state `s`, has an execution — a *finite* sequence of transitions — that stops in
a configuration satisfying `C`.

It is the least fixed point of `ExecF`, spelled out as the intersection of the
pre-fixed points of `ExecF`: `Exec M m s C` holds when every property closed
under `ExecF` holds of the configuration `(m, s)`.  Instantiating that
definition with the property `Exec M · · C` itself gives the introduction rules
`Exec.stop` and `Exec.event`, and instantiating it with an arbitrary property
gives the induction principle `Exec.induction`, which is how every lemma below
is proved.

An execution may stop at any point, which is what makes `Exec` compose
(`Exec.dup`, `Exec.bind`). -/
def Exec (M : StateMachine E) (m : ITree E α) (s : M.State)
    (C : ITree E α → M.State → Prop) : Prop :=
  ∀ X : ITree E α → M.State → Prop,
    (∀ m' s', ExecF M C X m' s' → X m' s') → X m s

namespace Exec

variable {M : StateMachine E} {C C' P : ITree E α → M.State → Prop}

theorem execF_mono {X X' : ITree E α → M.State → Prop}
    (hX : ∀ m' s', X m' s' → X' m' s') {m : ITree E α} {s : M.State}
    (hExec : ExecF M C X m s) : ExecF M C X' m s := by
  refine hExec.imp id ?_
  cases m with
  | ret value => simp only [unfold_pure, imp_self]
  | div => simp only [unfold_tau, imp_self]
  | vis event k =>
      simp only [unfold_vis]
      exact M.handle_mono fun answer s' => hX (k answer) s'

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
    | ret value => simp only [unfold_pure, false_implies]
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

theorem Evaluates.pure (value : α) (s : M.State) :
    M.Evaluates (Pure.pure value) s value s :=
  Evaluates.ret value s

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

/-- An execution of a machine that resolves its transitions can be realised: it
is an actual run of the program to a configuration satisfying `C`.

This is what justifies reading `Exec M m s C` as "`m` has an execution stopping
in `C`", and it is how the adequacy of a program logic stated in terms of `Exec`
is turned into a statement about a concrete evaluation. -/
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

end Aeneas.SLPoC
