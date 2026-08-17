import Aeneas.SLPoC.ST

/-!
# Executing a program the logic has proved

`Aeneas.SLPoC.ST` gives `St` two semantics that describe an execution without
performing one: the transition relation `StEvents.Step`, lifted to the big-step
`Evaluates`, and the denotation `theta` into the weakest-precondition monad.
This file adds the third: an interpreter that *runs* a program.

`St` cannot be interpreted unconditionally.  A heap cell stores its own Lean
type (`HeapCell = Σ α : Type, α`), so `Ptr.contains h p` — "the cell `p` points
at exists and holds an `α`" — is not decidable, and a read through a dangling or
mistyped pointer is stuck rather than erroneous.

The program logic supplies exactly what is missing.  `run` therefore takes the
weakest precondition as an argument and reads the witnesses it needs off it:
`theta_ev_read_contains` and friends turn `theta m Q h` into the very
`Ptr.contains` proofs `Ptr.read`, `Ptr.update` and `Ptr.free` ask for, and
`Ptr.freshPtr` makes allocation deterministic.  Proofs are erased at run time,
so `run` computes; what it computes with is the guarantee that a verified
program never gets stuck.

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

The proof is what makes the function total: it is consulted for the ownership
witnesses of every read, write and deallocation, and for nothing else. -/
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
      | .AllocPtr value, hWp =>
          let pointer := Ptr.freshPtr _ h
          let allocated := Ptr.freshHeap h value
          let hFresh := Ptr.fresh_freshPtr value h
          let outcome :=
            run (next pointer) allocated Q (theta_ev_alloc_elim hWp hFresh)
          ⟨outcome.val, outcome.property.1,
            StateMachine.Evaluates.step (.alloc hFresh) outcome.property.2⟩
      | .ReadPtr pointer, hWp =>
          let hContains := theta_ev_read_contains hWp
          let outcome :=
            run (next (Ptr.read pointer h hContains)) h Q
              (theta_ev_read_post hWp hContains)
          ⟨outcome.val, outcome.property.1,
            StateMachine.Evaluates.step (.read hContains) outcome.property.2⟩
      | .UpdatePtr pointer value, hWp =>
          let hContains := theta_ev_update_contains hWp
          let outcome :=
            run (next ()) (Ptr.update pointer value h hContains) Q
              (theta_ev_update_post hWp hContains)
          ⟨outcome.val, outcome.property.1,
            StateMachine.Evaluates.step (.update hContains) outcome.property.2⟩
      | .FreePtr pointer, hWp =>
          let hContains := theta_ev_free_contains hWp
          let outcome :=
            run (next ()) (Ptr.free pointer h hContains) Q
              (theta_ev_free_post hWp hContains)
          ⟨outcome.val, outcome.property.1,
            StateMachine.Evaluates.step (.free hContains) outcome.property.2⟩

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
