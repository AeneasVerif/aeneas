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

def refEq {α β : Type} (r₁ : ref α) (r₂ : ref β) : Prop :=
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

theorem contains_refEq {α β : Type} {h : Heap}
    {r₁ : ref α} {r₂ : ref β} (hLoc : refEq r₁ r₂)
    (h₁ : contains h r₁) (h₂ : contains h r₂) : α = β := by
  unfold refEq at hLoc
  unfold contains at h₁ h₂
  rw [hLoc] at h₁
  cases hLookup : h.lookup r₂.loc with
  | none => simp [hLookup] at h₂
  | some cell =>
    rcases cell with ⟨γ, freed, value⟩
    simp [hLookup] at h₁ h₂
    exact h₁.symm.trans h₂

theorem contains_of_live {α : Type} {h : Heap} {r : ref α}
    (hLive : live h r) : contains h r := by
  unfold live at hLive
  unfold contains
  split at hLive
  · contradiction
  · exact hLive.right

theorem contains_alloc_self {α : Type} (value : α) (h : Heap) :
    contains (alloc value h).2 (alloc value h).1 := by
  simp [alloc, contains, ref.loc]

theorem contains_alloc_of_contains {α β : Type} (value : β) {h : Heap}
    {r : ref α} (hContains : contains h r) :
    contains (alloc value h).2 r := by
  have hMemHeap : r.loc ∈ h := by
    have hContains' := hContains
    unfold contains at hContains'
    cases hLookup : h.lookup r.loc with
    | none => simp [hLookup] at hContains'
    | some cell => exact Finmap.mem_of_lookup_eq_some hLookup
  have hMem : r.loc ∈ h.keys := Finmap.mem_keys.mpr hMemHeap
  have hLe : r.loc ≤ h.keys.sup id := Finset.le_sup hMem
  have hNe : r.loc ≠ h.keys.sup id + 1 := by grind
  unfold alloc
  dsimp
  unfold contains
  rw [Finmap.lookup_insert_of_ne _ hNe]
  exact hContains

theorem contains_update {α β : Type} (r : ref α) (value : α) (h : Heap)
    (hLive : live h r) {r' : ref β} (hContains : contains h r') :
    contains (update r value h hLive) r' := by
  unfold update
  have hContainsR := contains_of_live hLive
  by_cases hEq : refEq r' r
  · have hType : β = α := contains_refEq hEq hContains hContainsR
    unfold refEq at hEq
    unfold contains
    rw [hEq, Finmap.lookup_insert]
    exact hType.symm
  · unfold refEq at hEq
    unfold contains
    rw [Finmap.lookup_insert_of_ne _ hEq]
    exact hContains

theorem contains_free {α β : Type} (r : ref α) (h : Heap)
    (hLive : live h r) {r' : ref β} (hContains : contains h r') :
    contains (free r h hLive) r' := by
  unfold free
  split
  · contradiction
  · rename_i γ freed value hLookup
    have hCell : freed = false ∧ γ = α := by
      simpa [live, hLookup] using hLive
    have hType : γ = α := hCell.right
    subst γ
    have hContainsR : contains h r := by simp [contains, hLookup]
    by_cases hEq : refEq r' r
    · have hTypes : β = α := contains_refEq hEq hContains hContainsR
      unfold refEq at hEq
      unfold contains
      rw [hEq, Finmap.lookup_insert]
      exact hTypes.symm
    · unfold refEq at hEq
      unfold contains
      rw [Finmap.lookup_insert_of_ne _ hEq]
      exact hContains

end Aeneas.SLPoC
