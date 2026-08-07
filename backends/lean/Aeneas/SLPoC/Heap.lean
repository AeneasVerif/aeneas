import Mathlib.Data.Finmap

namespace Aeneas.SLPoC

/- An allocation identifier is fresh and behaves like a monotonic
   counter, not a concrete address in machine memory. -/
abbrev AllocId := Nat

/- Cells store their Lean type, whether they have been freed, and their value.
   Keeping freed cells records invalid locations without reusing them. -/
abbrev Cell := Σ α : Type, Bool × α

abbrev Heap := Finmap fun _ : AllocId => Cell

def empty : Heap := ∅

def heapEq (h₁ h₂ : Heap) : Prop :=
  ∀ allocationId, h₁.lookup allocationId = h₂.lookup allocationId

def ref (_ : Type) := AllocId

private def ref.allocId {α : Type} (r : ref α) : AllocId := r

def singleton {α : Type} (r : ref α) (value : α) : Heap :=
  Finmap.singleton r.allocId ⟨α, false, value⟩

-- TODO: refEq should take only an alpha
def unallocated {α : Type} (h : Heap) (r : ref α) : Prop :=
  r.allocId ∉ h

def fresh {α : Type} (h : Heap) (r : ref α) (value : α)
    (h' : Heap) : Prop :=
  unallocated h r ∧ h' = h.insert r.allocId ⟨α, false, value⟩

-- TODO: refEq should take only an alpha
def refEq {α β : Type} (r₁ : ref α) (r₂ : ref β) : Prop :=
  r₁.allocId = r₂.allocId

def live {α : Type} (h : Heap) (r : ref α) : Prop :=
  match h.lookup r.allocId with
  | none => False
  | some ⟨β, freed, _⟩ => freed = false ∧ β = α

def contains {α : Type} (h : Heap) (r : ref α) : Prop :=
  match h.lookup r.allocId with
  | none => False
  | some ⟨β, _, _⟩ => β = α

def alloc {α : Type} (value : α) (h : Heap) : ref α × Heap :=
  let allocationId := h.keys.sup id + 1
  (allocationId, h.insert allocationId ⟨α, false, value⟩)

def read {α : Type} (r : ref α) (h : Heap)
    (hLive : live h r) : α :=
  match hlookup : h.lookup r.allocId with
  | none => by simp [live, hlookup] at hLive
  | some ⟨β, freed, value⟩ => by
      have hCell : freed = false ∧ β = α := by
        simpa [live, hlookup] using hLive
      have htype : β = α := by
        exact hCell.right
      exact htype ▸ value

def update {α : Type} (r : ref α) (value : α) (h : Heap)
    (_ : live h r) : Heap :=
  h.insert r.allocId ⟨α, false, value⟩

def free {α : Type} (r : ref α) (h : Heap)
    (hLive : live h r) : Heap :=
  match hlookup : h.lookup r.allocId with
  | none => by simp [live, hlookup] at hLive
  | some ⟨β, _, value⟩ => h.insert r.allocId ⟨β, true, value⟩

def read? {α : Type} (r : ref α) (h : Heap)
    (hContains : contains h r) : Option α :=
  match hlookup : h.lookup r.allocId with
  | none => by simp [contains, hlookup] at hContains
  | some ⟨β, freed, value⟩ =>
    match freed with
    | true => none
    | false =>
      have hType : β = α := by
        simpa [contains, hlookup] using hContains
      some (hType ▸ value)

def update? {α : Type} (r : ref α) (value : α)
    (h : Heap) : Option Heap :=
  match h.lookup r.allocId with
  | none => none
  | some ⟨_, freed, _⟩ =>
    match freed with
    | true => none
    | false => some (h.insert r.allocId ⟨α, false, value⟩)

def free? {α : Type} (r : ref α) (h : Heap) : Option Heap :=
  match h.lookup r.allocId with
  | none => none
  | some ⟨β, freed, value⟩ =>
    match freed with
    | true => none
    | false => some (h.insert r.allocId ⟨β, true, value⟩)

theorem contains_refEq {α β : Type} {h : Heap}
    {r₁ : ref α} {r₂ : ref β} (hLoc : refEq r₁ r₂)
    (h₁ : contains h r₁) (h₂ : contains h r₂) : α = β := by
  unfold refEq at hLoc
  unfold contains at h₁ h₂
  rw [hLoc] at h₁
  cases hLookup : h.lookup r₂.allocId with
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
  simp [alloc, contains, ref.allocId]

theorem contains_alloc_of_contains {α β : Type} (value : β) {h : Heap}
    {r : ref α} (hContains : contains h r) :
    contains (alloc value h).2 r := by
  have hMemHeap : r.allocId ∈ h := by
    have hContains' := hContains
    unfold contains at hContains'
    cases hLookup : h.lookup r.allocId with
    | none => simp [hLookup] at hContains'
    | some cell => exact Finmap.mem_of_lookup_eq_some hLookup
  have hMem : r.allocId ∈ h.keys := Finmap.mem_keys.mpr hMemHeap
  have hLe : r.allocId ≤ h.keys.sup id := Finset.le_sup hMem
  have hNe : r.allocId ≠ h.keys.sup id + 1 := by grind
  unfold alloc
  dsimp
  unfold contains
  simp only [ref.allocId] at hNe ⊢
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

theorem contains_update?_of_eq_some {α β : Type} (r : ref α)
    (value : α) (h : Heap) {h' : Heap} {r' : ref β}
    (hContainsR : contains h r) (hContains : contains h r')
    (hUpdate : update? r value h = some h') :
    contains h' r' := by
  unfold update? at hUpdate
  cases hLookup : h.lookup r.allocId with
  | none => simp [hLookup] at hUpdate
  | some cell =>
      rcases cell with ⟨γ, freed, oldValue⟩
      cases freed
      · simp [hLookup] at hUpdate
        subst h'
        have hLive : live h r := by
          simp [live, hLookup]
          simpa [contains, hLookup] using hContainsR
        exact contains_update r value h hLive hContains
      · simp [hLookup] at hUpdate

theorem contains_free?_of_eq_some {α β : Type} (r : ref α)
    (h : Heap) {h' : Heap} {r' : ref β}
    (hContainsR : contains h r) (hContains : contains h r')
    (hFree : free? r h = some h') :
    contains h' r' := by
  unfold free? at hFree
  cases hLookup : h.lookup r.allocId with
  | none => simp [hLookup] at hFree
  | some cell =>
      rcases cell with ⟨γ, freed, value⟩
      cases freed
      · simp [hLookup] at hFree
        subst h'
        have hLive : live h r := by
          simp [live, hLookup]
          simpa [contains, hLookup] using hContainsR
        have hFreeEq :
            free r h hLive = h.insert r.allocId ⟨γ, true, value⟩ := by
          unfold free
          split
          · rename_i hLookup'
            rw [hLookup] at hLookup'
            contradiction
          · rename_i δ freed' value' hLookup'
            have hCells :
                (⟨γ, false, value⟩ : Cell) =
                  ⟨δ, freed', value'⟩ := by
              apply Option.some.inj
              exact hLookup.symm.trans hLookup'
            cases hCells
            rfl
        rw [← hFreeEq]
        exact contains_free r h hLive hContains
      · simp [hLookup] at hFree


theorem live_union_left {α : Type} {h₁ h₂ : Heap} {r : ref α}
    (hLive : live h₁ r) : live (h₁ ∪ h₂) r := by
  have hMem : r.allocId ∈ h₁ := by
    unfold live at hLive
    split at hLive
    · contradiction
    · rename_i cell hLookup
      exact Finmap.mem_of_lookup_eq_some hLookup
  unfold live at hLive ⊢
  rw [Finmap.lookup_union_left hMem]
  exact hLive

theorem read_union_left {α : Type} {h₁ h₂ : Heap} {r : ref α}
    (hLive : live h₁ r) :
    read r (h₁ ∪ h₂) (live_union_left hLive) = read r h₁ hLive := by
  have hMem : r.allocId ∈ h₁ := by
    unfold live at hLive
    split at hLive
    · contradiction
    · rename_i cell hLookup
      exact Finmap.mem_of_lookup_eq_some hLookup
  unfold read
  split
  · rename_i hLookup
    have hLiveUnion := live_union_left (h₂ := h₂) hLive
    simp [live, hLookup] at hLiveUnion
  · rename_i β freed value hLookup
    split
    · rename_i hLookup₁
      simp [live, hLookup₁] at hLive
    · rename_i β₁ freed₁ value₁ hLookup₁
      have hCells :
          (⟨β, freed, value⟩ : Cell) = ⟨β₁, freed₁, value₁⟩ := by
        apply Option.some.inj
        exact hLookup.symm.trans
          ((Finmap.lookup_union_left hMem).trans hLookup₁)
      cases hCells
      rfl

theorem update_union_left {α : Type} {h₁ h₂ : Heap}
    (r : ref α) (value : α) (hLive : live h₁ r) :
    update r value (h₁ ∪ h₂) (live_union_left hLive) =
      update r value h₁ hLive ∪ h₂ := by
  exact Finmap.insert_union

theorem fresh_frame {α : Type} {r : ref α} {value : α}
    {h₁ h₂ h : Heap} (hDisjoint : Finmap.Disjoint h₁ h₂)
    (hFresh : fresh (h₁ ∪ h₂) r value h) :
    ∃ h₁',
      fresh h₁ r value h₁' ∧
      Finmap.Disjoint h₁' h₂ ∧
      h = h₁' ∪ h₂ := by
  rcases hFresh with ⟨hUnallocated, rfl⟩
  have hUnallocated₁ : unallocated h₁ r := by
    intro hMem
    exact hUnallocated (Finmap.mem_union.mpr (Or.inl hMem))
  have hUnallocated₂ : unallocated h₂ r := by
    intro hMem
    exact hUnallocated (Finmap.mem_union.mpr (Or.inr hMem))
  let h₁' := h₁.insert r.allocId ⟨α, false, value⟩
  refine ⟨h₁', ⟨hUnallocated₁, rfl⟩, ?_, ?_⟩
  · intro allocationId hMem₁ hMem₂
    dsimp [h₁'] at hMem₁
    rw [Finmap.mem_insert] at hMem₁
    rcases hMem₁ with hEq | hMem₁
    · exact hUnallocated₂ (hEq ▸ hMem₂)
    · exact hDisjoint allocationId hMem₁ hMem₂
  · exact Finmap.insert_union

theorem disjoint_update_left {α : Type} {r : ref α} {value : α}
    {h₁ h₂ : Heap} (hDisjoint : Finmap.Disjoint h₁ h₂)
    (hLive : live h₁ r) :
    Finmap.Disjoint (update r value h₁ hLive) h₂ := by
  have hUnallocated : unallocated h₂ r := by
    intro hMem₂
    unfold live at hLive
    split at hLive
    · contradiction
    · rename_i cell hLookup
      exact hDisjoint r.allocId
        (Finmap.mem_of_lookup_eq_some hLookup) hMem₂
  intro allocationId hMem₁ hMem₂
  unfold update at hMem₁
  rw [Finmap.mem_insert] at hMem₁
  rcases hMem₁ with hEq | hMem₁
  · exact hUnallocated (hEq ▸ hMem₂)
  · exact hDisjoint allocationId hMem₁ hMem₂

theorem disjoint_free_left {α : Type} {r : ref α}
    {h₁ h₂ : Heap} (hDisjoint : Finmap.Disjoint h₁ h₂)
    (hLive : live h₁ r) :
    Finmap.Disjoint (free r h₁ hLive) h₂ := by
  have hUnallocated : unallocated h₂ r := by
    intro hMem₂
    unfold live at hLive
    split at hLive
    · contradiction
    · rename_i cell hLookup
      exact hDisjoint r.allocId
        (Finmap.mem_of_lookup_eq_some hLookup) hMem₂
  unfold free
  split
  · contradiction
  · intro allocationId hMem₁ hMem₂
    rw [Finmap.mem_insert] at hMem₁
    rcases hMem₁ with hEq | hMem₁
    · exact hUnallocated (hEq ▸ hMem₂)
    · exact hDisjoint allocationId hMem₁ hMem₂

theorem free_union_left {α : Type} {h₁ h₂ : Heap}
    (r : ref α) (hLive : live h₁ r) :
    free r (h₁ ∪ h₂) (live_union_left hLive) =
      free r h₁ hLive ∪ h₂ := by
  have hMem : r.allocId ∈ h₁ := by
    unfold live at hLive
    split at hLive
    · contradiction
    · rename_i cell hLookup
      exact Finmap.mem_of_lookup_eq_some hLookup
  unfold free
  split
  · rename_i hLookup
    have hLiveUnion := live_union_left (h₂ := h₂) hLive
    simp [live, hLookup] at hLiveUnion
  · rename_i β freed value hLookup
    split
    · rename_i hLookup₁
      simp [live, hLookup₁] at hLive
    · rename_i β₁ freed₁ value₁ hLookup₁
      have hCells :
          (⟨β, freed, value⟩ : Cell) = ⟨β₁, freed₁, value₁⟩ := by
        apply Option.some.inj
        exact hLookup.symm.trans
          ((Finmap.lookup_union_left hMem).trans hLookup₁)
      cases hCells
      exact Finmap.insert_union

end Aeneas.SLPoC
