import Mathlib.Data.Finmap

namespace Aeneas.SLPoC

/- A location is a fresh allocation identifier that behaves like a monotonic
   counter, not a concrete address in machine memory. -/
abbrev Loc := Nat

/- Cells store their Lean type, whether they have been freed, and their value.
   Keeping freed cells records invalid locations without reusing them. -/
abbrev Cell := Σ α : Type, Bool × α

abbrev Heap := Finmap fun _ : Loc => Cell

def empty : Heap := ∅

def heapEq (h₁ h₂ : Heap) : Prop :=
  ∀ location, h₁.lookup location = h₂.lookup location

def ref (_ : Type) := Loc

def ref.loc {α : Type} (r : ref α) : Loc := r

def refEq {α: Type} (r₁ : ref α) (r₂ : ref α) : Prop :=
  r₁.loc = r₂.loc

def live {α : Type} (h : Heap) (r : ref α) : Prop :=
  match h.lookup r.loc with
  | none => False
  | some ⟨β, freed, _⟩ => freed = false ∧ β = α

def contains {α : Type} (h : Heap) (r : ref α) : Prop :=
  match h.lookup r.loc with
  | none => False
  | some ⟨β, _, _⟩ => β = α

def alloc {α : Type} (value : α) (h : Heap) : ref α × Heap :=
  let location := h.keys.sup id + 1
  (location, h.insert location ⟨α, false, value⟩)

def read {α : Type} (r : ref α) (h : Heap)
    (hLive : live h r) : α :=
  match hlookup : h.lookup r.loc with
  | none => by simp [live, hlookup] at hLive
  | some ⟨β, freed, value⟩ => by
      have hCell : freed = false ∧ β = α := by
        simpa [live, hlookup] using hLive
      have htype : β = α := by
        exact hCell.right
      exact htype ▸ value

def update {α : Type} (r : ref α) (value : α) (h : Heap)
    (_ : live h r) : Heap :=
  h.insert r.loc ⟨α, false, value⟩

def free {α : Type} (r : ref α) (h : Heap)
    (hLive : live h r) : Heap :=
  match hlookup : h.lookup r.loc with
  | none => by simp [live, hlookup] at hLive
  | some ⟨β, _, value⟩ => h.insert r.loc ⟨β, true, value⟩

def read? {α : Type} (r : ref α) (h : Heap)
    (hContains : contains h r) : Option α :=
  match hlookup : h.lookup r.loc with
  | none => by simp [contains, hlookup] at hContains
  | some ⟨β, freed, value⟩ =>
    if freed then
      none
    else
      have hType : β = α := by
        simpa [contains, hlookup] using hContains
      some (hType ▸ value)

def update? {α : Type} (r : ref α) (value : α)
    (h : Heap) : Option Heap :=
  match h.lookup r.loc with
  | none => none
  | some ⟨_, freed, _⟩ =>
    if freed then none else some (h.insert r.loc ⟨α, false, value⟩)

def free? {α : Type} (r : ref α) (h : Heap) : Option Heap :=
  match h.lookup r.loc with
  | none => none
  | some ⟨β, freed, value⟩ =>
    if freed then none else some (h.insert r.loc ⟨β, true, value⟩)

end Aeneas.SLPoC
