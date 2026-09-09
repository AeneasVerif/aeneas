import Aeneas.SLPoC.ST

/-!
# The machine of `Result`: operational semantics and certified interpreter

`Aeneas.Std.Primitives` defines `Result`, the interaction-tree monad over heap
events, and `Aeneas.SLPoC.ST` builds the correctness judgments and the triples
over it *denotationally*.  This file supplies the operational counterpart, in
three layers:

* the **runs** of that machine: `Aeneas.SLPoC.ST` gives heap events their
  meaning as the handler of a state machine (in the style of "Program Logics à
  la Carte") in order to state the judgments; here we take that machine's
  multi-step relation `Reaches` and big-step relation `Evaluates`;
* the **adequacy** of the judgments for that machine: a `dspec`-proved program
  reaches only configurations whose next event is defined, and every run of it
  that stops satisfies the postcondition — which is what makes partial
  correctness mean what it should;
* the **certified interpreter**: a `spec` proof is a termination proof, so it
  can be recursed on to actually run the program.  `exec` reads the returned
  value and final heap off that recursion, and `exec_post`/`exec_evaluates`
  certify them, so `#guard` on `execClosed` checks a verified program against
  its specification by running it.

Partial correctness buys nothing in the last layer: `dspec` admits divergence,
so there is no recursion to terminate.
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

/-! ## Runs of the machine

The machine of `Result` — `RustEffect.machine`, whose handler `EventSpec` says
how one heap event is answered on one heap — is defined in `Aeneas.SLPoC.ST`,
where the correctness judgments need it; what is added here are its runs. -/

/-- Big-step relation -/
def Evaluates (m : Result α) (h : Heap) (value : α) (h' : Heap) : Prop :=
  RustEffect.machine.Evaluates m h value h'

/-- `Reaches m h m' h'`: the machine of `Result` takes the configuration `(m, h)` to
the configuration `(m', h')`. -/
def Reaches (m : Result α) (h : Heap) (m' : Result α) (h' : Heap) : Prop :=
  RustEffect.machine.Runs m h m' h'

/-! ### Adequacy of `dspec`

Partial correctness is closed under the transitions of the machine above, which
is what makes it mean what it should: every configuration a proved program
reaches performs a defined event, and every run that stops satisfies the
postcondition.

Both halves are the generic adequacy of `Aeneas.Data.Coinductive.Spec` —
`PartialSpec.runs` and `PartialSpec.evaluates` — at the machine of `Result`,
which is conjunctive and feasible (`RustEffect.machine_conjunctive`,
`RustEffect.machine_feasible`); `Reaches` and
`Evaluates` are that machine's `Runs` and `Evaluates`, so those two apply as
they stand and only the third statement below is specific to heap events. -/

/-- Every heap event a proved program reaches is defined on the heap it is
reached with; a proved program cannot reach failure. Partial correctness permits
divergence, not stuckness.  This is the one thing the generic theory cannot
say, `pre` being what `EventSpec` demands of a heap event. -/
theorem dspec_pre_of_reaches {Q : α → Heap → Prop} {m : Result α} {h : Heap}
    {EventResult : Type} {pre : Heap → Prop}
    {modify : (h : Heap) → pre h → EventResult × Heap}
    {k : RustEffect.Output (RustEffect.Input.guardedModify EventResult pre modify) → Result α}
    {h' : Heap}
    (hSpec : PartialSpec RustEffect.machine Q m h)
    (hReaches :
      Reaches m h (.vis (RustEffect.Input.guardedModify EventResult pre modify) k) h') :
    pre h' :=
  (PartialSpec.runs RustEffect.machine_conjunctive RustEffect.machine_feasible
    hSpec hReaches).vis_view.choose

/-- What a partial triple says of a run that stops. -/
theorem dtriple_evaluates {P : IPre} {m : Result α} {Q : IPost α}
    (hTriple : dtriple P m Q) {h : Heap} (hPre : P h) {value : α} {h' : Heap}
    (hEval : Evaluates m h value h') : Q value h' :=
  PartialSpec.evaluates RustEffect.machine_conjunctive RustEffect.machine_feasible
    (Q := fun value h' => Q value h') (dtriple_apply hTriple hPre) hEval

/-- What a partial triple says of a run that does not: every event it reaches is
defined. -/
theorem dtriple_pre_of_reaches {P : IPre} {m : Result α} {Q : IPost α}
    (hTriple : dtriple P m Q) {h : Heap} (hPre : P h)
    {EventResult : Type} {pre : Heap → Prop}
    {modify : (h : Heap) → pre h → EventResult × Heap}
    {k : RustEffect.Output (RustEffect.Input.guardedModify EventResult pre modify) → Result α}
    {h' : Heap}
    (hReaches :
      Reaches m h (.vis (RustEffect.Input.guardedModify EventResult pre modify) k) h') :
    pre h' :=
  dspec_pre_of_reaches (dtriple_apply hTriple hPre) hReaches

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

/-- At a `vis` node total correctness supplies exactly what `EventSpec` demands
of the event: the guard of a heap event together with total correctness of the
continuation on the heap it produces, and `False` at failure. -/
theorem spec_unfold_vis {m : Result α} {event : RustEffect.Input}
    {k : RustEffect.Output event → Result α} {Q : IPost α} {h : Heap}
    (hm : m.unfold = .vis event k) (hSpec : spec m Q h) :
    EventSpec event h fun answer h' => spec (k answer) Q h' := by
  rw [eq_vis_of_unfold hm] at hSpec
  exact hSpec.vis_view

theorem spec_unfold_fail_false {m : Result α} {error : Error}
    {k : RustEffect.Output (RustEffect.Input.fail error) → Result α}
    {Q : IPost α} {h : Heap}
    (hm : m.unfold = .vis (RustEffect.Input.fail error) k)
    (hSpec : spec m Q h) : False :=
  spec_unfold_vis hm hSpec

/-- Run `m` from `h`. The total-correctness proof supplies the guard of each
heap event and rules out failure, so nothing has to be decided: the guard of a
heap event of `Result` is an arbitrary proposition, and a read through a dangling
or mistyped pointer is stuck rather than erroneous. Proofs are erased at run
time, so this computes.

An interaction tree is coinductive, so this is a partial fixed point rather than
a structural recursion, and it must answer something on a tree with no `ret` in
sight: `runOpt_spec` shows that `none` is unreachable under total correctness,
because `TotalSpec` puts `False` in the divergence case of its layer. -/
def runOpt (m : Result α) (h : Heap) (Q : IPost α) (hSpec : spec m Q h) :
    Option (α × Heap) :=
  match hm : m.unfold with
  | .ret value => some (value, h)
  | .div => none
  | .vis (RustEffect.Input.guardedModify _ _ modify) k =>
      let hNext := spec_unfold_vis hm hSpec
      runOpt (k (.up (modify h hNext.choose).1))
        (modify h hNext.choose).2 Q hNext.choose_spec
  | .vis (RustEffect.Input.fail _error) _k =>
      False.elim (spec_unfold_fail_false hm hSpec)
partial_fixpoint

/-- The interpreter answers, its answer satisfies the postcondition, and it is
reached by an evaluation of the machine of `Aeneas.SepLogic.ST`. -/
theorem runOpt_spec (Q : IPost α) (m : Result α) (h : Heap) (hSpec : spec m Q h) :
    ∃ outcome : α × Heap, runOpt m h Q hSpec = some outcome ∧
      Q outcome.1 outcome.2 ∧ Evaluates m h outcome.1 outcome.2 := by
  refine hSpec.induction
    (P := fun t u => ∀ hSpec' : spec t Q u, ∃ outcome : α × Heap,
      runOpt t u Q hSpec' = some outcome ∧
        Q outcome.1 outcome.2 ∧ Evaluates t u outcome.1 outcome.2) ?_ ?_ hSpec
  · intro value h' hPost hSpec'
    rw [runOpt.eq_def]
    exact ⟨(_, _), rfl, hPost, StateMachine.Evaluates.pure _ _⟩
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
      · refine StateMachine.Evaluates.event (M := RustEffect.machine) ?_
        exact ⟨hPre, hEvaluates⟩
    · rename_i error k hm
      simp only [unfold_vis] at hm
      cases hm

theorem runOpt_isSome (Q : IPost α) (m : Result α) (h : Heap)
    (hSpec : spec m Q h) : (runOpt m h Q hSpec).isSome := by
  obtain ⟨outcome, hRun, -⟩ := runOpt_spec Q m h hSpec
  rw [hRun]
  rfl

theorem runOpt_get_spec (Q : IPost α) (m : Result α) (h : Heap)
    (hSpec : spec m Q h) :
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
def run (m : Result α) (h : Heap) (Q : IPost α) (hSpec : spec m Q h) :
    Outcome m Q h :=
  ⟨(runOpt m h Q hSpec).get (runOpt_isSome Q m h hSpec),
    runOpt_get_spec Q m h hSpec⟩

/-- The value and heap produced by `run`. -/
def exec (m : Result α) (h : Heap) (Q : IPost α) (hSpec : spec m Q h) : α × Heap :=
  (run m h Q hSpec).val

theorem exec_post (m : Result α) (h : Heap) (Q : IPost α) (hSpec : spec m Q h) :
    Q (exec m h Q hSpec).1 (exec m h Q hSpec).2 :=
  (run m h Q hSpec).property.1

theorem exec_evaluates (m : Result α) (h : Heap) (Q : IPost α)
    (hSpec : spec m Q h) :
    Evaluates m h (exec m h Q hSpec).1 (exec m h Q hSpec).2 :=
  (run m h Q hSpec).property.2

/-! ## Executing a specified program -/

/-- Run a program from a heap satisfying the precondition of a proved triple. -/
def runTriple {P : IPre} {Q : IPost α} (m : Result α) (h : Heap)
    (hTriple : triple P m Q) (hPre : P h) : Outcome m Q h :=
  run m h Q (triple_apply hTriple hPre)

/-- The value and heap produced by a specified program. -/
def execTriple {P : IPre} {Q : IPost α} (m : Result α) (h : Heap)
    (hTriple : triple P m Q) (hPre : P h) : α × Heap :=
  (runTriple m h hTriple hPre).val

theorem execTriple_post {P : IPre} {Q : IPost α} (m : Result α) (h : Heap)
    (hTriple : triple P m Q) (hPre : P h) :
    Q (execTriple m h hTriple hPre).1 (execTriple m h hTriple hPre).2 :=
  (runTriple m h hTriple hPre).property.1

theorem execTriple_evaluates {P : IPre} {Q : IPost α} (m : Result α) (h : Heap)
    (hTriple : triple P m Q) (hPre : P h) :
    Evaluates m h (execTriple m h hTriple hPre).1
      (execTriple m h hTriple hPre).2 :=
  (runTriple m h hTriple hPre).property.2

/-- Run a program proved from `emp` on the empty heap. -/
def execClosed {Q : IPost α} (m : Result α) (hTriple : triple emp m Q) : α × Heap :=
  execTriple m Heap.empty hTriple trivial

theorem execClosed_post {Q : IPost α} (m : Result α) (hTriple : triple emp m Q) :
    Q (execClosed m hTriple).1 (execClosed m hTriple).2 :=
  execTriple_post m Heap.empty hTriple trivial

theorem execClosed_evaluates {Q : IPost α} (m : Result α)
    (hTriple : triple emp m Q) :
    Evaluates m Heap.empty (execClosed m hTriple).1 (execClosed m hTriple).2 :=
  execTriple_evaluates m Heap.empty hTriple trivial

end ResultImplementation

end Aeneas.SepLogic
