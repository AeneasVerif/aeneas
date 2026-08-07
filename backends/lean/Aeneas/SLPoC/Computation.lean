import Aeneas.SLPoC.FFree
import Aeneas.SLPoC.Heap

namespace Aeneas.SLPoC

inductive StEvents : Type → Type 1 where
  | Alloc {α : Type} (value : α) : StEvents (ref α)
  | Read {α : Type} (r : ref α) : StEvents α
  | Update {α : Type} (r : ref α) (value : α) : StEvents Unit
  | Free {α : Type} (r : ref α) : StEvents Unit

abbrev St := FFree StEvents

instance St.instLawfulMonad : LawfulMonad St :=
  inferInstanceAs (LawfulMonad (FFree StEvents))

namespace State

def alloc {α : Type} (value : α) : St (ref α) :=
  FFree.trigger (.Alloc value)

def read {α : Type} (r : ref α) : St α :=
  FFree.trigger (.Read r)

def update {α : Type} (r : ref α) (value : α) : St Unit :=
  FFree.trigger (.Update r value)

def free {α : Type} (r : ref α) : St Unit :=
  FFree.trigger (.Free r)

namespace Runner

abbrev Witness := Σ α : Type, ref α

def closedByAllocations (witnesses : Set Witness) : St α → Prop
  | .ok _ => True
  | .event e next =>
    match e with
    | .Alloc value =>
      ∀ r, closedByAllocations (Set.insert ⟨_, r⟩ witnesses) (next r)
    | .Read r =>
      ⟨_, r⟩ ∈ witnesses ∧ ∀ value, closedByAllocations witnesses (next value)
    | .Update r _ =>
      ⟨_, r⟩ ∈ witnesses ∧ closedByAllocations witnesses (next ())
    | .Free r =>
      ⟨_, r⟩ ∈ witnesses ∧
        closedByAllocations
          (fun witness =>
            witness ∈ witnesses ∧
              match witness with
              | ⟨_, current⟩ => ¬ Aeneas.SLPoC.refEq current r)
          (next ())

def Witness.holds (witness : Witness) (h : Heap) : Prop :=
  match witness with
  | ⟨_, r⟩ => Aeneas.SLPoC.contains h r

structure HeapWithWitnesses where
  heap : Heap
  witnesses : Set Witness
  holds : ∀ witness, witness ∈ witnesses → witness.holds heap

def runWithWitnesses : (m : St α) →
    (state : HeapWithWitnesses) →
    closedByAllocations state.witnesses m →
    Option (α × HeapWithWitnesses)
  | .ok value, state, _ => pure (value, state)
  | .event (.Alloc value) next, state, hBefore =>
    let allocation := Aeneas.SLPoC.alloc value state.heap
    let r := allocation.1
    let h := allocation.2
    let witness : Witness := ⟨_, r⟩
    let nextState : HeapWithWitnesses := {
      heap := h
      witnesses := Set.insert witness state.witnesses
      holds := by
        intro current hCurrent
        rcases hCurrent with hEq | hOld
        · subst current
          exact Aeneas.SLPoC.contains_alloc_self value state.heap
        · exact Aeneas.SLPoC.contains_alloc_of_contains value
            (state.holds current hOld)
    }
    runWithWitnesses (next r) nextState (hBefore r)
  | .event (.Read r) next, state, hBefore =>
    have hContains : Aeneas.SLPoC.contains state.heap r :=
      state.holds ⟨_, r⟩ hBefore.left
    match Aeneas.SLPoC.read? r state.heap hContains with
    | none => none
    | some value =>
      runWithWitnesses (next value) state (hBefore.right value)
  | .event (.Update r value) next, state, hBefore =>
    have hContains : Aeneas.SLPoC.contains state.heap r :=
      state.holds ⟨_, r⟩ hBefore.left
    match hUpdate : Aeneas.SLPoC.update? r value state.heap with
    | some h =>
      let nextState : HeapWithWitnesses := {
        heap := h
        witnesses := state.witnesses
        holds := by
          intro current hCurrent
          rcases current with ⟨γ, current⟩
          exact Aeneas.SLPoC.contains_update?_of_eq_some r value state.heap
            hContains (state.holds ⟨γ, current⟩ hCurrent) hUpdate
      }
      runWithWitnesses (next ()) nextState hBefore.right
    | none => none
  | .event (.Free r) next, state, hBefore =>
    have hContains : Aeneas.SLPoC.contains state.heap r :=
      state.holds ⟨_, r⟩ hBefore.left
    match hFree : Aeneas.SLPoC.free? r state.heap with
    | some h =>
      let nextState : HeapWithWitnesses := {
        heap := h
        witnesses := fun witness =>
          witness ∈ state.witnesses ∧
            match witness with
            | ⟨_, current⟩ => ¬ Aeneas.SLPoC.refEq current r
        holds := by
          intro current hCurrent
          rcases current with ⟨γ, current⟩
          exact Aeneas.SLPoC.contains_free?_of_eq_some_of_refEq_ne
            r state.heap hContains
            (state.holds ⟨γ, current⟩ hCurrent.left)
            hCurrent.right hFree
      }
      runWithWitnesses (next ()) nextState hBefore.right
    | none => none

def run (m : St α) (h : Heap) (allocations : Set Witness)
    (hAllocations : ∀ witness, witness ∈ allocations → witness.holds h)
    (hClosed : closedByAllocations allocations m) :
    Option (α × Heap) :=
  let initial : HeapWithWitnesses := {
    heap := h
    witnesses := allocations
    holds := hAllocations
  }
  do
    let (value, state) ← runWithWitnesses m initial hClosed
    pure (value, state.heap)

end Runner

end State

end Aeneas.SLPoC
