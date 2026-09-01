import Aeneas.SLPoC.ST

/-!
# Executing a program the logic has proved

`Aeneas.SLPoC.ST` gives `St` two semantics that describe an execution without
performing one: the transition relation `StEvents.Step`, lifted to the big-step
`Evaluates`, and the denotation `theta` into the weakest-precondition monad.
This file adds the third: an interpreter that *runs* a program.

`St` cannot be interpreted unconditionally: the guard of an event is an
arbitrary proposition about the current heap.

The program logic supplies exactly what is missing.  `run` therefore takes the
weakest precondition as an argument and obtains the guard proof from it.
Proofs are erased at run time, so `run` computes; what it computes with is the
guarantee that a verified program never gets stuck.

The interpreter is *certified*: it returns the postcondition and the evaluation
that produced its answer alongside the answer, so nothing has to be re-proved
about it afterwards.
-/

namespace Aeneas.SLPoC

open scoped SepLogic

variable {α : Type}

/-- What running `m` from `h` produces: the returned value and the final heap,
together with the postcondition they satisfy and the evaluation that reaches
them.  Both components of the proof live in `Prop` and are erased, so an
`Outcome` computes to a plain pair. -/
def Outcome (m : St α) (Q : SLPost α) (h : Heap) : Type 1 :=
  { outcome : α × Heap //
      Q outcome.1 outcome.2 ∧ Evaluates m h outcome.1 outcome.2 }

/-- Run `m` on the heap `h`, given a proof that its weakest precondition holds
there.

The proof is what makes the function total: it supplies the guard of every
event. -/
def run : (m : St α) → (h : Heap) → (Q : SLPost α) → theta m Q h → Outcome m Q h
  | .ok value, h, _, hWp =>
      ⟨(value, h), hWp,
        StateMachine.Evaluates.ok (M := StEvents.machine) value h⟩
  | .event event next, h, Q, hWp =>
      /- The denotation of an event is the denotation of the event followed by
         that of the continuation; spelling it out is what lets the elimination
         lemmas of `Aeneas.SLPoC.ST` apply. -/
      have hEvent : theta_ev event (fun result => theta (next result) Q) h := hWp
      match event, hEvent with
      | .GuardedModify _ modify, hWp =>
          let hPre := (theta_ev_elim hWp).choose
          let result := (modify h hPre).1
          let modified := (modify h hPre).2
          let outcome :=
            run (next result) modified Q (theta_ev_elim hWp).choose_spec
          ⟨outcome.val, outcome.property.1,
            StateMachine.Evaluates.step (.guardedModify hPre) outcome.property.2⟩

/-- The value and the heap `run` produces. -/
def exec (m : St α) (h : Heap) (Q : SLPost α) (hWp : theta m Q h) : α × Heap :=
  (run m h Q hWp).val

theorem exec_post (m : St α) (h : Heap) (Q : SLPost α) (hWp : theta m Q h) :
    Q (exec m h Q hWp).1 (exec m h Q hWp).2 :=
  (run m h Q hWp).property.1

/-- The interpreter agrees with the transition relation: what it computes is an
execution of the machine of `Aeneas.SLPoC.ST`. -/
theorem exec_evaluates (m : St α) (h : Heap) (Q : SLPost α) (hWp : theta m Q h) :
    Evaluates m h (exec m h Q hWp).1 (exec m h Q hWp).2 :=
  (run m h Q hWp).property.2

/-! ## Running a specified program

A triple is exactly the permission to run: give it a heap satisfying the
precondition and the program returns, having established the postcondition. -/

/-- Run a program from a heap satisfying the precondition of a triple it has
been proved to satisfy. -/
def runTriple {P : SLPre} {Q : SLPost α} (m : St α) (h : Heap)
    (hTriple : triple P m Q) (hPre : P h) : Outcome m Q h :=
  run m h Q ((triple_iff P m Q).mp hTriple h hPre)

/-- The value and the heap a specified program produces. -/
def execTriple {P : SLPre} {Q : SLPost α} (m : St α) (h : Heap)
    (hTriple : triple P m Q) (hPre : P h) : α × Heap :=
  (runTriple m h hTriple hPre).val

theorem execTriple_post {P : SLPre} {Q : SLPost α} (m : St α) (h : Heap)
    (hTriple : triple P m Q) (hPre : P h) :
    Q (execTriple m h hTriple hPre).1 (execTriple m h hTriple hPre).2 :=
  (runTriple m h hTriple hPre).property.1

theorem execTriple_evaluates {P : SLPre} {Q : SLPost α} (m : St α) (h : Heap)
    (hTriple : triple P m Q) (hPre : P h) :
    Evaluates m h (execTriple m h hTriple hPre).1
      (execTriple m h hTriple hPre).2 :=
  (runTriple m h hTriple hPre).property.2

/-- A program proved from `emp` runs on the empty heap.  Being affine, the logic
lets its precondition be met by *any* heap; the empty one is the one a whole
program starts from. -/
def execClosed {Q : SLPost α} (m : St α) (hTriple : triple emp m Q) : α × Heap :=
  execTriple m empty hTriple trivial

theorem execClosed_post {Q : SLPost α} (m : St α) (hTriple : triple emp m Q) :
    Q (execClosed m hTriple).1 (execClosed m hTriple).2 :=
  execTriple_post m empty hTriple trivial

theorem execClosed_evaluates {Q : SLPost α} (m : St α)
    (hTriple : triple emp m Q) :
    Evaluates m empty (execClosed m hTriple).1 (execClosed m hTriple).2 :=
  execTriple_evaluates m empty hTriple trivial

end Aeneas.SLPoC
