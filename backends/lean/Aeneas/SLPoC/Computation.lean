import Aeneas.SLPoC.FFree
import Aeneas.SLPoC.Heap

namespace Aeneas.SLPoC

inductive StEvents : Type → Type 1 where
  | Alloc {α : Type} (value : α) : StEvents (ref α)
  | Read {α : Type} (r : ref α) : StEvents α
  | Update {α : Type} (r : ref α) (value : α) : StEvents Unit
  | Free {α : Type} (r : ref α) : StEvents Unit

abbrev St := FFree StEvents

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
  | .ok _ | .fail _ | .div => True
  | .event e next =>
    match e with
    | .Alloc value =>
      ∀ r, closedByAllocations (Set.insert ⟨_, r⟩ witnesses) (next r)
    | .Read r =>
      ⟨_, r⟩ ∈ witnesses ∧ ∀ value, closedByAllocations witnesses (next value)
    | .Update r _ =>
      ⟨_, r⟩ ∈ witnesses ∧ closedByAllocations witnesses (next ())
    | .Free r =>
      ⟨_, r⟩ ∈ witnesses ∧ closedByAllocations witnesses (next ())

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
    Std.Result (α × HeapWithWitnesses)
  | .ok value, state, _ => .ok (value, state)
  | .fail error, _, _ => .fail error
  | .div, _, _ => .div
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
    | none => .fail .undef
    | some value =>
      runWithWitnesses (next value) state (hBefore.right value)
  | .event (.Update r value) next, state, hBefore =>
    have hContains : Aeneas.SLPoC.contains state.heap r :=
      state.holds ⟨_, r⟩ hBefore.left
    match hLookup : state.heap.lookup r.loc with
    | none => .fail .undef
    | some ⟨β, freed, oldValue⟩ =>
      if hFreed : freed then
        .fail .undef
      else
        have hType : β = _ := by
          simpa [Aeneas.SLPoC.contains, hLookup] using hContains
        have hLive : Aeneas.SLPoC.live state.heap r := by
          simp [Aeneas.SLPoC.live, hLookup, hFreed, hType]
        let h := Aeneas.SLPoC.update r value state.heap hLive
        let nextState : HeapWithWitnesses := {
          heap := h
          witnesses := state.witnesses
          holds := by
            intro current hCurrent
            rcases current with ⟨γ, current⟩
            exact Aeneas.SLPoC.contains_update r value state.heap hLive
              (state.holds ⟨γ, current⟩ hCurrent)
        }
        runWithWitnesses (next ()) nextState hBefore.right
  | .event (.Free r) next, state, hBefore =>
    have hContains : Aeneas.SLPoC.contains state.heap r :=
      state.holds ⟨_, r⟩ hBefore.left
    match hLookup : state.heap.lookup r.loc with
    | none => .fail .undef
    | some ⟨β, freed, value⟩ =>
      if hFreed : freed then
        .fail .undef
      else
        have hType : β = _ := by
          simpa [Aeneas.SLPoC.contains, hLookup] using hContains
        have hLive : Aeneas.SLPoC.live state.heap r := by
          simp [Aeneas.SLPoC.live, hLookup, hFreed, hType]
        let h := Aeneas.SLPoC.free r state.heap hLive
        let nextState : HeapWithWitnesses := {
          heap := h
          witnesses := state.witnesses
          holds := by
            intro current hCurrent
            rcases current with ⟨γ, current⟩
            exact Aeneas.SLPoC.contains_free r state.heap hLive
              (state.holds ⟨γ, current⟩ hCurrent)
        }
        runWithWitnesses (next ()) nextState hBefore.right

def run (m : St α) (h : Heap) (allocations : Set Witness)
    (hAllocations : ∀ witness, witness ∈ allocations → witness.holds h)
    (hClosed : closedByAllocations allocations m) :
    Std.Result (α × Heap) :=
  let initial : HeapWithWitnesses := {
    heap := h
    witnesses := allocations
    holds := hAllocations
  }
  match runWithWitnesses m initial hClosed with
  | .ok (value, state) => .ok (value, state.heap)
  | .fail error => .fail error
  | .div => .div

end Runner

end State

end Aeneas.SLPoC
