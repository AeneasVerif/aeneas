import Aeneas.SLPoC.ST

/-!
# The machine of `Result`: operational semantics and certified interpreter

`Aeneas.Std.Primitives` defines `Result`, the interaction-tree monad over heap
events, and `Aeneas.SLPoC.ST` builds the correctness judgments and the ispecs
over it *denotationally*.  This file supplies the operational counterpart, in
three layers:

* the **runs** of that machine: `Aeneas.SLPoC.ST` gives heap events their
  meaning as the handler of a state machine (in the style of "Program Logics à
  la Carte") in order to state the judgments; here we take that machine's
  multi-step relation `Reaches` and big-step relation `Evaluates`;
* the **adequacy** of the judgments for that machine: a `PartialSpec`-proved
  program reaches only configurations whose next event is defined, and every
  run of it that stops satisfies the postcondition — which is what makes
  partial correctness mean what it should;
* the **certified interpreter**: a `TotalSpec` proof is a termination proof, so
  it can be recursed on to actually run the program. `exec` reads the returned
  value and final heap off that recursion, and `exec_post`/`exec_evaluates`
  certify them, so `#guard` on `execClosed` checks a verified program against
  its specification by running it.

Partial correctness buys nothing in the last layer: `PartialSpec` admits
divergence, so there is no recursion to terminate.
-/

namespace Aeneas.SepLogic

open Aeneas.Data
open Aeneas.Data.Coinductive
open Aeneas.Std (Error Heap Result RustEffect)

universe u

section ResultImplementation

unseal Result
set_option allowUnsafeReducibility true in
attribute [local reducible] Result Result.ok Result.vis Result.div Aeneas.Std.bind

/-! ## Handler properties required by operational adequacy -/

/-- The handler resolves its transitions: the one way it answers a heap event
answers it with one definite outcome. -/
theorem handler_resolves : handler.Resolves := by
  intro event h C hHandle
  cases event with
  | guardedModify EventResult pre modify => exact ⟨_, _, hHandle.2, hHandle.1, rfl, rfl⟩
  | fail error => exact hHandle.elim

/-- The handler is feasible: no heap event is a miracle. -/
theorem handler_feasible : handler.Feasible :=
  handler_resolves.feasible

/-! ## Runs of the machine

The handler of `Result` — `handler`, which says how one heap event is
answered on one heap — is defined in `Aeneas.SLPoC.ST`, where the correctness
judgments need it; what is added here are its runs. -/

/-- Big-step relation -/
def Evaluates (m : Result α) (h : Heap) (value : α) (h' : Heap) : Prop :=
  handler.Evaluates m h value h'

/-- `Reaches m h m' h'`: the machine of `Result` takes the configuration `(m, h)` to
the configuration `(m', h')`. -/
def Reaches (m : Result α) (h : Heap) (m' : Result α) (h' : Heap) : Prop :=
  handler.Runs m h m' h'

/-! ### Adequacy of `PartialSpec`

Partial correctness is closed under the transitions of the machine above, which
is what makes it mean what it should: every configuration a proved program
reaches performs a defined event, and every run that stops satisfies the
postcondition.

Both halves are the generic adequacy proved in `Aeneas.SLPoC.StateMachine` —
`PartialSpec.runs` and `PartialSpec.evaluates` — at the machine of `Result`,
which is conjunctive and feasible (`handler_conjunctive`,
`handler_feasible`); `Reaches` and
`Evaluates` are that machine's `Runs` and `Evaluates`, so those two apply as
they stand and only the third statement below is specific to heap events. -/

private theorem ispec_total {P : IPre} {m : Result α} {Q : IPost α}
    (hSpec : ispec P m Q) {h : Heap} (hPre : P h) :
    TotalSpec handler (fun value h' => Q value h') m h := by
  have hRaw := hSpec emp h ((sep_emp_r P).mpr h hPre)
  exact hRaw.mono fun value => sep_elim_right (Q value) emp

private theorem dispec_partial {P : IPre} {m : Result α} {Q : IPost α}
    (hSpec : dispec P m Q) {h : Heap} (hPre : P h) :
    PartialSpec handler (fun value h' => Q value h') m h := by
  have hRaw := hSpec emp h ((sep_emp_r P).mpr h hPre)
  exact hRaw.mono fun value => sep_elim_right (Q value) emp

/-- Every heap event a proved program reaches is defined on the heap it is
reached with; a proved program cannot reach failure. Partial correctness permits
divergence, not stuckness. This is the one thing the generic theory cannot say,
`pre` being what the `guardedModify` case of the handler demands. -/
private theorem partialSpec_pre_of_reaches {Q : α → Heap → Prop}
    {m : Result α} {h : Heap}
    {EventResult : Type} {pre : Heap → Prop}
    {modify : (h : Heap) → pre h → EventResult × Heap}
    {k : RustEffect.Output (RustEffect.Input.guardedModify EventResult pre modify) → Result α}
    {h' : Heap}
    (hSpec : PartialSpec handler Q m h)
    (hReaches :
      Reaches m h (.vis (RustEffect.Input.guardedModify EventResult pre modify) k) h') :
    pre h' :=
  (PartialSpec.runs handler_conjunctive handler_feasible
    hSpec hReaches).vis_view.choose

/-- What a partial ispec says of a run that stops. -/
theorem dispec_evaluates {P : IPre} {m : Result α} {Q : IPost α}
    (hTriple : dispec P m Q) {h : Heap} (hPre : P h) {value : α} {h' : Heap}
    (hEval : Evaluates m h value h') : Q value h' :=
  PartialSpec.evaluates handler_conjunctive handler_feasible
    (Q := fun value h' => Q value h') (dispec_partial hTriple hPre) hEval

/-- What a partial ispec says of a run that does not: every event it reaches is
defined. -/
theorem dispec_pre_of_reaches {P : IPre} {m : Result α} {Q : IPost α}
    (hTriple : dispec P m Q) {h : Heap} (hPre : P h)
    {EventResult : Type} {pre : Heap → Prop}
    {modify : (h : Heap) → pre h → EventResult × Heap}
    {k : RustEffect.Output (RustEffect.Input.guardedModify EventResult pre modify) → Result α}
    {h' : Heap}
    (hReaches :
      Reaches m h (.vis (RustEffect.Input.guardedModify EventResult pre modify) k) h') :
    pre h' :=
  partialSpec_pre_of_reaches (dispec_partial hTriple hPre) hReaches

/-! ## Certified execution -/

/-- What running `m` from `h` produces: the returned value and final heap,
together with the postcondition they satisfy and the evaluation that reaches
them. -/
def Outcome {α : Type u} (m : Result α) (Q : IPost α) (h : Heap) : Type (max u 1) :=
  { outcome : α × Heap //
      Q outcome.1 outcome.2 ∧ Evaluates m h outcome.1 outcome.2 }

/-- A tree is what its unfolding says it is. -/
theorem eq_of_unfold {m : Result α} {shape : ITreeF RustEffect α (Result α)}
    (hm : m.unfold = shape) : m = ITree.fold shape := by
  rw [← hm, ITree.unfold_fold]

theorem eq_ret_of_unfold {m : Result α} {value : α} (hm : m.unfold = .ret value) :
    m = ITree.ret value :=
  eq_of_unfold hm

theorem eq_vis_of_unfold {m : Result α} {event : RustEffect.Input}
    {k : RustEffect.Output event → Result α} (hm : m.unfold = .vis event k) :
    m = ITree.vis event k :=
  eq_of_unfold hm

/-- At a `vis` node total correctness supplies exactly what the handler demands
of the event: the guard of a heap event together with total correctness of the
continuation on the heap it produces, and `False` at failure. -/
private theorem totalSpec_unfold_vis {m : Result α} {event : RustEffect.Input}
    {k : RustEffect.Output event → Result α} {Q : IPost α} {h : Heap}
    (hm : m.unfold = .vis event k)
    (hSpec : TotalSpec handler (fun value h' => Q value h') m h) :
    handler.handle event h fun answer h' =>
      TotalSpec handler (fun value h'' => Q value h'') (k answer) h' := by
  rw [eq_vis_of_unfold hm] at hSpec
  exact hSpec.vis_view

private theorem totalSpec_unfold_fail_false {m : Result α} {error : Error}
    {k : RustEffect.Output (RustEffect.Input.fail error) → Result α}
    {Q : IPost α} {h : Heap}
    (hm : m.unfold = .vis (RustEffect.Input.fail error) k)
    (hSpec : TotalSpec handler (fun value h' => Q value h') m h) : False :=
  totalSpec_unfold_vis hm hSpec

/-- Run `m` from `h`. The total-correctness proof supplies the guard of each
heap event and rules out failure, so nothing has to be decided: the guard of a
heap event of `Result` is an arbitrary proposition, and a read through a dangling
or mistyped pointer is stuck rather than erroneous. Proofs are erased at run
time, so this computes.

An interaction tree is coinductive, so this is a partial fixed point rather than
a structural recursion, and it must answer something on a tree with no `ret` in
sight: `runOpt_spec` shows that `none` is unreachable under total correctness,
because `TotalSpec` puts `False` in the divergence case of its layer. -/
private def runOpt (m : Result α) (h : Heap) (Q : IPost α)
    (hSpec : TotalSpec handler (fun value h' => Q value h') m h) :
    Option (α × Heap) :=
  match hm : m.unfold with
  | .ret value => some (value, h)
  | .div => none
  | .vis (RustEffect.Input.guardedModify _ _ modify) k =>
      let hNext := totalSpec_unfold_vis hm hSpec
      runOpt (k (.up (modify h hNext.choose).1))
        (modify h hNext.choose).2 Q hNext.choose_spec
  | .vis (RustEffect.Input.fail _error) _k =>
      False.elim (totalSpec_unfold_fail_false hm hSpec)
partial_fixpoint

/-- The interpreter answers, its answer satisfies the postcondition, and it is
reached by an evaluation of the machine of `Aeneas.SepLogic.ST`. -/
private theorem runOpt_spec (Q : IPost α) (m : Result α) (h : Heap)
    (hSpec : TotalSpec handler (fun value h' => Q value h') m h) :
    ∃ outcome : α × Heap, runOpt m h Q hSpec = some outcome ∧
      Q outcome.1 outcome.2 ∧ Evaluates m h outcome.1 outcome.2 := by
  refine hSpec.induction
    (P := fun t u => ∀ hSpec' :
        TotalSpec handler (fun value h' => Q value h') t u,
      ∃ outcome : α × Heap,
      runOpt t u Q hSpec' = some outcome ∧
        Q outcome.1 outcome.2 ∧ Evaluates t u outcome.1 outcome.2) ?_ ?_ hSpec
  · intro value h' hPost hSpec'
    rw [runOpt.eq_def]
    exact ⟨(_, _), rfl, hPost, Handler.Evaluates.pure _ _⟩
  · intro event k h' hHandle
    cases event with
    | fail error => exact hHandle.elim
    | guardedModify EventResult pre modify =>
    obtain ⟨hPre, ih⟩ := hHandle
    intro hSpec'
    rw [runOpt.eq_def]
    split
    · rename_i value hm
      simp only [unfold_vis] at hm
      cases hm
    · rename_i hm
      simp only [unfold_vis] at hm
      cases hm
    · rename_i event k hm
      simp only [unfold_vis] at hm
      cases hm
      obtain ⟨outcome, hRun, hPost, hEvaluates⟩ := ih _
      refine ⟨outcome, ?_, hPost, ?_⟩
      · simpa using hRun
      · refine Handler.Evaluates.event (M := handler) ?_
        exact ⟨hPre, hEvaluates⟩
    · rename_i error k hm
      simp only [unfold_vis] at hm
      cases hm

private theorem runOpt_isSome (Q : IPost α) (m : Result α) (h : Heap)
    (hSpec : TotalSpec handler (fun value h' => Q value h') m h) :
    (runOpt m h Q hSpec).isSome := by
  obtain ⟨outcome, hRun, -⟩ := runOpt_spec Q m h hSpec
  rw [hRun]
  rfl

private theorem runOpt_get_spec (Q : IPost α) (m : Result α) (h : Heap)
    (hSpec : TotalSpec handler (fun value h' => Q value h') m h) :
    Q ((runOpt m h Q hSpec).get (runOpt_isSome Q m h hSpec)).1
        ((runOpt m h Q hSpec).get (runOpt_isSome Q m h hSpec)).2 ∧
      Evaluates m h ((runOpt m h Q hSpec).get (runOpt_isSome Q m h hSpec)).1
        ((runOpt m h Q hSpec).get (runOpt_isSome Q m h hSpec)).2 := by
  obtain ⟨outcome, hRun, hPost, hEvaluates⟩ := runOpt_spec Q m h hSpec
  have hGet : (runOpt m h Q hSpec).get (runOpt_isSome Q m h hSpec) = outcome :=
    Option.some.inj (by
      rw [Option.some_get]
      exact hRun)
  rw [hGet]
  exact ⟨hPost, hEvaluates⟩

/-- Run `m` from `h`, certified: the value and heap come with the postcondition
they satisfy and with the evaluation that reaches them. -/
private def run (m : Result α) (h : Heap) (Q : IPost α)
    (hSpec : TotalSpec handler (fun value h' => Q value h') m h) :
    Outcome m Q h :=
  ⟨(runOpt m h Q hSpec).get (runOpt_isSome Q m h hSpec),
    runOpt_get_spec Q m h hSpec⟩

/-- The value and heap produced by `run`. -/
private def exec (m : Result α) (h : Heap) (Q : IPost α)
    (hSpec : TotalSpec handler (fun value h' => Q value h') m h) :
    α × Heap :=
  (run m h Q hSpec).val

private theorem exec_post (m : Result α) (h : Heap) (Q : IPost α)
    (hSpec : TotalSpec handler (fun value h' => Q value h') m h) :
    Q (exec m h Q hSpec).1 (exec m h Q hSpec).2 :=
  (run m h Q hSpec).property.1

private theorem exec_evaluates (m : Result α) (h : Heap) (Q : IPost α)
    (hSpec : TotalSpec handler (fun value h' => Q value h') m h) :
    Evaluates m h (exec m h Q hSpec).1 (exec m h Q hSpec).2 :=
  (run m h Q hSpec).property.2

/-! ## Executing a specified program -/

/-- Run a program from a heap satisfying the precondition of a proved ispec. -/
def runISpec {P : IPre} {Q : IPost α} (m : Result α) (h : Heap)
    (hSpec : ispec P m Q) (hPre : P h) : Outcome m Q h :=
  run m h Q (ispec_total hSpec hPre)

/-- The value and heap produced by a specified program. -/
def execISpec {P : IPre} {Q : IPost α} (m : Result α) (h : Heap)
    (hSpec : ispec P m Q) (hPre : P h) : α × Heap :=
  (runISpec m h hSpec hPre).val

theorem execISpec_post {P : IPre} {Q : IPost α} (m : Result α) (h : Heap)
    (hSpec : ispec P m Q) (hPre : P h) :
    Q (execISpec m h hSpec hPre).1 (execISpec m h hSpec hPre).2 :=
  (runISpec m h hSpec hPre).property.1

theorem execISpec_evaluates {P : IPre} {Q : IPost α} (m : Result α) (h : Heap)
    (hSpec : ispec P m Q) (hPre : P h) :
    Evaluates m h (execISpec m h hSpec hPre).1
      (execISpec m h hSpec hPre).2 :=
  (runISpec m h hSpec hPre).property.2

/-- Run a program proved from `emp` on the empty heap. -/
def execClosed {Q : IPost α} (m : Result α) (hSpec : ispec emp m Q) : α × Heap :=
  execISpec m Heap.empty hSpec trivial

theorem execClosed_post {Q : IPost α} (m : Result α) (hSpec : ispec emp m Q) :
    Q (execClosed m hSpec).1 (execClosed m hSpec).2 :=
  execISpec_post m Heap.empty hSpec trivial

theorem execClosed_evaluates {Q : IPost α} (m : Result α)
    (hSpec : ispec emp m Q) :
    Evaluates m Heap.empty (execClosed m hSpec).1 (execClosed m hSpec).2 :=
  execISpec_evaluates m Heap.empty hSpec trivial

end ResultImplementation

end Aeneas.SepLogic
