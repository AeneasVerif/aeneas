import Aeneas.SLPoC.MutableData.Ptr
import Aeneas.SLPoC.Tests.Examples.Basic

/-!
# Running verified programs

`Aeneas.SLPoC.ST` turns a proved triple into an execution.  These are the tests
that it really executes, that what it computes agrees with what the triple
predicts, and that the proof it carries is available without running anything.
-/

namespace Aeneas.SLPoC


/-! ## A closed program -/

def roundTrip : St Nat := do
  let p ← alloc (1 : Nat)
  let value ← read p
  update p (value + 41)
  let result ← read p
  free p
  pure result

theorem roundTrip.spec : (roundTrip) ⦃⇓ result => result = 42⦄ := by
  unfold roundTrip
  step*

-- The interpreter runs it.
#guard (execClosed roundTrip roundTrip.spec).1 = 42

/-- Its answer needs no execution: it *is* the postcondition of the triple. -/
example : (execClosed roundTrip roundTrip.spec).1 = 42 :=
  execClosed_post roundTrip roundTrip.spec

/-- And the execution the interpreter performs is one of the machine of
`Aeneas.SLPoC.ST`. -/
example :
    Evaluates roundTrip empty (execClosed roundTrip roundTrip.spec).1
      (execClosed roundTrip roundTrip.spec).2 :=
  execClosed_evaluates roundTrip roundTrip.spec

/-- What running a closed program shows and the affine logic cannot: this run
leaks nothing.  A triple only says what its postcondition owns, so the empty
final heap is a fact about the execution, not about the specification. -/
example : (execClosed roundTrip roundTrip.spec).2.size = 0 := by
  native_decide

def leaky : St Unit := do
  let _ ← alloc (1 : Nat)
  pure ()

theorem leaky.spec : ⦃ emp ⦄ leaky ⦃⇓ emp⦄ := by
  unfold leaky
  step*

/-- The same specification, and a cell left behind: affinity is exactly the gap
between the two semantics. -/
example : (execClosed leaky leaky.spec).2.size = 1 := by
  native_decide

/-! ## A program run on a heap it does not own entirely

`runTriple` needs the precondition to hold of the initial heap.  Being affine,
an assertion is satisfied by any heap that *extends* the cells it describes, so
the same triple runs the program on a larger heap — the frame is simply carried
along. -/

private def source : Ptr Nat := ⟨0, 0⟩
private def spare : Ptr Nat := ⟨1, 0⟩

/-- The heap of the single allocation `q` is interior to, holding `value`. -/
private def cell (q : Ptr Nat) (value : Nat) : Heap :=
  singleton q.baseRef (q.frag [value])

/-- Composing cells is what `∪` does, so it has to decide whether two carrier
types agree and does not compute; on disjoint addresses `disjointUnion` agrees
with it and does. -/
private def initial : Heap :=
  (cell source 1).disjointUnion (cell spare 7)

private theorem source_ne_spare : source.baseRef ≠ spare.baseRef :=
  fun hEq => Nat.succ_ne_zero 0 hEq.symm

private theorem initial_disjoint :
    PartialCommMonoid.Compatible (cell source 1) (cell spare 7) :=
  disjoint_singleton source_ne_spare

private theorem initial_eq : initial = cell source 1 ∪ cell spare 7 := by
  apply Heap.disjointUnion_eq_union
  intro a hMem hMem'
  have hSource : a = 0 := by
    by_contra hNe
    simp [Heap.mem_iff, cell, Ref.addr, Ptr.baseRef, source, hNe] at hMem
  have hSpare : a = 1 := by
    by_contra hNe
    simp [Heap.mem_iff, cell, Ref.addr, Ptr.baseRef, spare, hNe] at hMem'
  exact Nat.noConfusion (hSource.symm.trans hSpare)

private theorem initial_pre : (source ↦ 1) initial := by
  rw [initial_eq]
  exact Heap.Sub.union_left initial_disjoint

-- The frame is carried along: the run leaves both cells behind.
#guard
  (execTriple (Examples.incr_ptr source) initial
    (Examples.incr_ptr.spec source 1) initial_pre).2.size = 2

/-- And the owned cell was incremented, by the postcondition of the triple. -/
example :
    (source ↦ 1 + 1)
      (execTriple (Examples.incr_ptr source) initial
        (Examples.incr_ptr.spec source 1) initial_pre).2 :=
  execTriple_post (Examples.incr_ptr source) initial
    (Examples.incr_ptr.spec source 1) initial_pre

end Aeneas.SLPoC
