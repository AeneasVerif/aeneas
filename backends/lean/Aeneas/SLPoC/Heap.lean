import Mathlib.Data.Finmap

namespace Aeneas.SLPoC

/- An allocation identifier is fresh and behaves like a monotonic
   counter, not a concrete address in machine memory. -/
abbrev AllocId := Nat

/- Heap entries store their Lean type and value. -/
abbrev HeapCell := Σ α : Type, α -- TODO: make it a list

abbrev Heap := Finmap fun _ : AllocId => HeapCell

def empty : Heap := ∅

def Ref (_ : Type) := AllocId

/-- Allocation identifiers are natural numbers, so references are inhabited. -/
instance instInhabitedRef {α : Type} : Inhabited (Ref α) := ⟨(0 : AllocId)⟩

private def Ref.allocId {α : Type} (r : Ref α) : AllocId := r

def singleton {α : Type} (r : Ref α) (value : α) : Heap :=
  Finmap.singleton r.allocId ⟨α, value⟩

def unallocated {α : Type} (h : Heap) (r : Ref α) : Prop :=
  r.allocId ∉ h

def fresh {α : Type} (h : Heap) (r : Ref α) (value : α)
    (h' : Heap) : Prop :=
  unallocated h r ∧ h' = h.insert r.allocId ⟨α, value⟩

def contains {α : Type} (h : Heap) (r : Ref α) : Prop :=
  match h.lookup r.allocId with
  | none => False
  | some ⟨β, _⟩ => β = α

/-- The allocation identifier this heap will hand out next: one past every
identifier it uses.  Allocation is deterministic, which is what lets a program
be *run* and not only related to its outcomes. -/
def freshRef (α : Type) (h : Heap) : Ref α :=
  h.keys.sup id + 1

/-- The heap `freshRef` allocates into. -/
def freshHeap {α : Type} (h : Heap) (value : α) : Heap :=
  h.insert (freshRef α h).allocId ⟨α, value⟩

theorem fresh_freshRef {α : Type} (value : α) (h : Heap) :
    fresh h (freshRef α h) value (freshHeap h value) := by
  refine ⟨?_, rfl⟩
  intro hMem
  have hMemKeys : h.keys.sup id + 1 ∈ h.keys :=
    Finmap.mem_keys.mpr hMem
  have hLe : h.keys.sup id + 1 ≤ h.keys.sup id :=
    Finset.le_sup (f := fun x : Nat => x) hMemKeys
  exact Nat.not_succ_le_self _ hLe

theorem exists_fresh {α : Type} (value : α) (h : Heap) :
    ∃ r h', fresh h r value h' :=
  ⟨freshRef α h, freshHeap h value, fresh_freshRef value h⟩

/-! ## Sub-heaps

The assertions of `Aeneas.SLPoC.WP` are *affine*: they own the cells they
describe and say nothing about the rest of the heap.  Semantically that means
they are closed under the extension order below, the way Iris's `uPred` is
monotone in its resource. -/

/-- `Heap.Sub h h'`: `h'` is `h` extended with cells that `h` does not own. -/
def Heap.Sub (h h' : Heap) : Prop :=
  ∃ rest, Finmap.Disjoint h rest ∧ h' = h ∪ rest

namespace Heap.Sub

@[refl]
theorem refl (h : Heap) : Heap.Sub h h :=
  ⟨∅, Finmap.Disjoint.symm _ _ (Finmap.disjoint_empty h), Finmap.union_empty.symm⟩

theorem trans {h₁ h₂ h₃ : Heap} (hSub₁₂ : Heap.Sub h₁ h₂)
    (hSub₂₃ : Heap.Sub h₂ h₃) : Heap.Sub h₁ h₃ := by
  obtain ⟨rest₁, hDisjoint₁, rfl⟩ := hSub₁₂
  obtain ⟨rest₂, hDisjoint₂, rfl⟩ := hSub₂₃
  obtain ⟨hDisjoint₁₂, hDisjoint₂₂⟩ :=
    (Finmap.disjoint_union_left h₁ rest₁ rest₂).mp hDisjoint₂
  exact ⟨rest₁ ∪ rest₂,
    (Finmap.disjoint_union_right h₁ rest₁ rest₂).mpr ⟨hDisjoint₁, hDisjoint₁₂⟩,
    Finmap.union_assoc⟩

theorem of_empty (h : Heap) : Heap.Sub empty h :=
  ⟨h, Finmap.disjoint_empty h, Finmap.empty_union.symm⟩

theorem union_left {h₁ h₂ : Heap} (hDisjoint : Finmap.Disjoint h₁ h₂) :
    Heap.Sub h₁ (h₁ ∪ h₂) :=
  ⟨h₂, hDisjoint, rfl⟩

theorem union_right {h₁ h₂ : Heap} (hDisjoint : Finmap.Disjoint h₁ h₂) :
    Heap.Sub h₂ (h₁ ∪ h₂) :=
  ⟨h₁, Finmap.Disjoint.symm _ _ hDisjoint,
    Finmap.union_comm_of_disjoint hDisjoint⟩

/-- An extension of a split heap splits the same way, the extra cells going to
the right-hand side. -/
theorem split {h₁ h₂ h' : Heap} (hDisjoint : Finmap.Disjoint h₁ h₂)
    (hSub : Heap.Sub (h₁ ∪ h₂) h') :
    ∃ h₂', Finmap.Disjoint h₁ h₂' ∧ h' = h₁ ∪ h₂' ∧ Heap.Sub h₂ h₂' := by
  obtain ⟨rest, hDisjointRest, rfl⟩ := hSub
  obtain ⟨hDisjoint₁, hDisjoint₂⟩ :=
    (Finmap.disjoint_union_left h₁ h₂ rest).mp hDisjointRest
  exact ⟨h₂ ∪ rest,
    (Finmap.disjoint_union_right h₁ h₂ rest).mpr ⟨hDisjoint, hDisjoint₁⟩,
    Finmap.union_assoc, ⟨rest, hDisjoint₂, rfl⟩⟩

/-- A heap disjoint from an extension is disjoint from the heap extended. -/
theorem disjoint_of_sub {h h' frame : Heap} (hSub : Heap.Sub h h')
    (hDisjoint : Finmap.Disjoint h' frame) : Finmap.Disjoint h frame := by
  obtain ⟨rest, _, rfl⟩ := hSub
  exact ((Finmap.disjoint_union_left h rest frame).mp hDisjoint).left

/-- Extending on one side of a union extends the union. -/
theorem union_mono_left {h h' frame : Heap} (hSub : Heap.Sub h h')
    (hDisjoint : Finmap.Disjoint h' frame) :
    Heap.Sub (h ∪ frame) (h' ∪ frame) := by
  obtain ⟨rest, hDisjointRest, rfl⟩ := hSub
  obtain ⟨_, hDisjointFrame⟩ :=
    (Finmap.disjoint_union_left h rest frame).mp hDisjoint
  refine ⟨rest, ?_, ?_⟩
  · exact (Finmap.disjoint_union_left h frame rest).mpr
      ⟨hDisjointRest, Finmap.Disjoint.symm _ _ hDisjointFrame⟩
  · rw [Finmap.union_assoc, Finmap.union_assoc,
      Finmap.union_comm_of_disjoint (Finmap.Disjoint.symm _ _ hDisjointFrame)]

end Heap.Sub

namespace Heap

def read {α : Type} (r : Ref α) (h : Heap)
    (hContains : contains h r) : α :=
  match hlookup : h.lookup r.allocId with
  | none => by simp [contains, hlookup] at hContains
  | some ⟨β, value⟩ => by
      have htype : β = α := by
        simpa [contains, hlookup] using hContains
      exact htype ▸ value

def update {α : Type} (r : Ref α) (value : α) (h : Heap)
    (_ : contains h r) : Heap :=
  h.insert r.allocId ⟨α, value⟩

def free {α : Type} (r : Ref α) (h : Heap)
    (_ : contains h r) : Heap :=
  h.erase r.allocId

end Heap

/-- A heap that contains a cell has its allocation identifier as a key. -/
theorem mem_of_contains {α : Type} {h : Heap} {r : Ref α}
    (hContains : contains h r) : r.allocId ∈ h := by
  unfold contains at hContains
  split at hContains
  · contradiction
  · rename_i cell hLookup
    exact Finmap.mem_of_lookup_eq_some hLookup

/-- Two heaps that both contain the cell `r` are not disjoint. -/
theorem disjoint_contains_false {α : Type} {h₁ h₂ : Heap} {r : Ref α}
    (hDisjoint : Finmap.Disjoint h₁ h₂) (hContains₁ : contains h₁ r)
    (hContains₂ : contains h₂ r) : False :=
  hDisjoint r.allocId (mem_of_contains hContains₁) (mem_of_contains hContains₂)

theorem contains_union_left {α : Type} {h₁ h₂ : Heap} {r : Ref α}
    (hContains : contains h₁ r) : contains (h₁ ∪ h₂) r := by
  have hMem : r.allocId ∈ h₁ := mem_of_contains hContains
  unfold contains at hContains ⊢
  rw [Finmap.lookup_union_left hMem]
  exact hContains

theorem read_union_left {α : Type} {h₁ h₂ : Heap} {r : Ref α}
    (hContains : contains h₁ r) :
    Heap.read r (h₁ ∪ h₂) (contains_union_left hContains) =
      Heap.read r h₁ hContains := by
  have hMem : r.allocId ∈ h₁ := by
    unfold contains at hContains
    split at hContains
    · contradiction
    · rename_i cell hLookup
      exact Finmap.mem_of_lookup_eq_some hLookup
  unfold Heap.read
  split
  · rename_i hLookup
    have hContainsUnion := contains_union_left (h₂ := h₂) hContains
    simp [contains, hLookup] at hContainsUnion
  · rename_i β value hLookup
    split
    · rename_i hLookup₁
      simp [contains, hLookup₁] at hContains
    · rename_i β₁ value₁ hLookup₁
      have hCells :
          (⟨β, value⟩ : HeapCell) = ⟨β₁, value₁⟩ := by
        apply Option.some.inj
        exact hLookup.symm.trans
          ((Finmap.lookup_union_left hMem).trans hLookup₁)
      cases hCells
      rfl

theorem update_union_left {α : Type} {h₁ h₂ : Heap}
    (r : Ref α) (value : α) (hContains : contains h₁ r) :
    Heap.update r value (h₁ ∪ h₂) (contains_union_left hContains) =
      Heap.update r value h₁ hContains ∪ h₂ := by
  exact Finmap.insert_union

theorem fresh_frame {α : Type} {r : Ref α} {value : α}
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
  let h₁' := h₁.insert r.allocId ⟨α, value⟩
  refine ⟨h₁', ⟨hUnallocated₁, rfl⟩, ?_, ?_⟩
  · intro allocationId hMem₁ hMem₂
    dsimp [h₁'] at hMem₁
    rw [Finmap.mem_insert] at hMem₁
    rcases hMem₁ with hEq | hMem₁
    · exact hUnallocated₂ (hEq ▸ hMem₂)
    · exact hDisjoint allocationId hMem₁ hMem₂
  · exact Finmap.insert_union

theorem disjoint_update_left {α : Type} {r : Ref α} {value : α}
    {h₁ h₂ : Heap} (hDisjoint : Finmap.Disjoint h₁ h₂)
    (hContains : contains h₁ r) :
    Finmap.Disjoint (Heap.update r value h₁ hContains) h₂ := by
  have hUnallocated : unallocated h₂ r := by
    intro hMem₂
    unfold contains at hContains
    split at hContains
    · contradiction
    · rename_i cell hLookup
      exact hDisjoint r.allocId
        (Finmap.mem_of_lookup_eq_some hLookup) hMem₂
  intro allocationId hMem₁ hMem₂
  unfold Heap.update at hMem₁
  rw [Finmap.mem_insert] at hMem₁
  rcases hMem₁ with hEq | hMem₁
  · exact hUnallocated (hEq ▸ hMem₂)
  · exact hDisjoint allocationId hMem₁ hMem₂

theorem disjoint_free_left {α : Type} {r : Ref α}
    {h₁ h₂ : Heap} (hDisjoint : Finmap.Disjoint h₁ h₂)
    (hContains : contains h₁ r) :
    Finmap.Disjoint (Heap.free r h₁ hContains) h₂ := by
  intro allocationId hMem₁ hMem₂
  exact hDisjoint allocationId (Finmap.mem_erase.mp hMem₁).right hMem₂

theorem free_union_left {α : Type} {h₁ h₂ : Heap}
    (r : Ref α) (hDisjoint : Finmap.Disjoint h₁ h₂)
    (hContains : contains h₁ r) :
    Heap.free r (h₁ ∪ h₂) (contains_union_left hContains) =
      Heap.free r h₁ hContains ∪ h₂ := by
  have hMem : r.allocId ∈ h₁ := by
    unfold contains at hContains
    split at hContains
    · contradiction
    · rename_i cell hLookup
      exact Finmap.mem_of_lookup_eq_some hLookup
  have hNotMem : r.allocId ∉ h₂ :=
    fun hMem₂ => hDisjoint r.allocId hMem hMem₂
  unfold Heap.free
  apply Finmap.ext_lookup
  intro allocationId
  by_cases hEq : allocationId = r.allocId
  · subst allocationId
    rw [Finmap.lookup_erase, Finmap.lookup_union_right
      Finmap.notMem_erase_self]
    exact Finmap.lookup_eq_none.mpr hNotMem |>.symm
  · rw [Finmap.lookup_erase_ne hEq]
    by_cases hMem₁ : allocationId ∈ h₁
    · rw [Finmap.lookup_union_left hMem₁,
        Finmap.lookup_union_left (Finmap.mem_erase.mpr ⟨hEq, hMem₁⟩),
        Finmap.lookup_erase_ne hEq]
    · rw [Finmap.lookup_union_right hMem₁,
        Finmap.lookup_union_right
          (fun hMem => hMem₁ (Finmap.mem_erase.mp hMem).right)]

theorem fresh_empty_eq_singleton {α : Type} {r : Ref α} {value : α}
    {h : Heap} (hFresh : fresh empty r value h) :
    h = singleton r value := by
  rcases hFresh with ⟨_, rfl⟩
  apply Finmap.ext_lookup
  intro allocationId
  by_cases hEq : allocationId = r.allocId
  · subst allocationId
    simp [empty, singleton]
  · rw [Finmap.lookup_insert_of_ne _ hEq]
    symm
    apply Finmap.lookup_eq_none.mpr
    change allocationId ∉
      Finmap.singleton r.allocId ⟨α, value⟩
    rwa [Finmap.mem_singleton]

/-- Two cells at different references are disjoint. -/
theorem disjoint_singleton {α : Type} {r s : Ref α} {value₁ value₂ : α}
    (hNe : r ≠ s) :
    Finmap.Disjoint (singleton r value₁) (singleton s value₂) := by
  intro allocationId hMem₁ hMem₂
  rw [singleton, Finmap.mem_singleton] at hMem₁
  rw [singleton, Finmap.mem_singleton] at hMem₂
  exact hNe (hMem₁.symm.trans hMem₂)

theorem contains_singleton {α : Type} (r : Ref α) (value : α) :
    contains (singleton r value) r := by
  simp [contains, singleton]

theorem read_singleton {α : Type} (r : Ref α) (value : α)
    (hContains : contains (singleton r value) r) :
    Heap.read r (singleton r value) hContains = value := by
  unfold Heap.read
  split
  · rename_i hLookup
    unfold singleton at hLookup
    rw [Finmap.lookup_singleton_eq] at hLookup
    contradiction
  · rename_i β stored hLookup
    unfold singleton at hLookup
    rw [Finmap.lookup_singleton_eq] at hLookup
    cases hLookup
    rfl

theorem update_singleton {α : Type} (r : Ref α)
    (oldValue newValue : α)
    (hContains : contains (singleton r oldValue) r) :
    Heap.update r newValue (singleton r oldValue) hContains =
      singleton r newValue := by
  simp [Heap.update, singleton]

theorem free_singleton {α : Type} (r : Ref α) (value : α)
    (hContains : contains (singleton r value) r) :
    Heap.free r (singleton r value) hContains = empty := by
  unfold Heap.free
  apply Finmap.ext_lookup
  intro allocationId
  by_cases hEq : allocationId = r.allocId
  · subst allocationId
    simp [empty]
  · rw [Finmap.lookup_erase_ne hEq]
    simp only [empty, Finmap.lookup_empty]
    apply Finmap.lookup_eq_none.mpr
    simpa [singleton, Finmap.mem_singleton] using hEq

end Aeneas.SLPoC
