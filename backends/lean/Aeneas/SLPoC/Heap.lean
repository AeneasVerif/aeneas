module

import Mathlib.Data.Finmap
public import Aeneas.SLPoC.PCM

public section

namespace Aeneas.SLPoC

/- An allocation identifier is fresh and behaves like a monotonic
   counter, not a concrete address in machine memory. -/
abbrev AllocId := Nat

/- Heap entries store their Lean type and value. -/
abbrev HeapCell := Σ α : Type, α -- TODO: make it a list

private abbrev HeapImpl := Finmap fun _ : AllocId => HeapCell

/-- A finite collection of dynamically typed heap cells. -/
structure Heap where
  private mk ::
  private impl : HeapImpl

private instance : Coe Heap HeapImpl := ⟨Heap.impl⟩
private instance : Coe HeapImpl Heap := ⟨Heap.mk⟩

private def Heap.lookup (h : Heap) (allocationId : AllocId) :
    Option HeapCell :=
  h.impl.lookup allocationId

private def Heap.insert (h : Heap) (allocationId : AllocId)
    (cell : HeapCell) : Heap :=
  ⟨h.impl.insert allocationId cell⟩

private def Heap.erase (h : Heap) (allocationId : AllocId) : Heap :=
  ⟨h.impl.erase allocationId⟩

private def Heap.keys (h : Heap) :=
  h.impl.keys

private theorem Heap.ext_impl {h₁ h₂ : Heap}
    (hEq : h₁.impl = h₂.impl) : h₁ = h₂ := by
  cases h₁
  cases h₂
  cases hEq
  rfl

def empty : Heap := ⟨∅⟩

instance Heap.instEmptyCollection : EmptyCollection Heap := ⟨empty⟩

def Heap.union (h₁ h₂ : Heap) : Heap := ⟨h₁.impl ∪ h₂.impl⟩

instance Heap.instUnion : Union Heap := ⟨Heap.union⟩

def Heap.mem (allocationId : AllocId) (h : Heap) : Prop :=
  allocationId ∈ h.impl

instance Heap.instMembership : Membership AllocId Heap :=
  ⟨fun h allocationId => Heap.mem allocationId h⟩

/-- The number of allocated cells. -/
def Heap.size (h : Heap) : Nat :=
  h.impl.keys.card

def Heap.compatible (h₁ h₂ : Heap) : Prop :=
  Finmap.Disjoint h₁.impl h₂.impl

private theorem Heap.mem_union {allocationId : AllocId} {h₁ h₂ : Heap} :
    allocationId ∈ h₁ ∪ h₂ ↔ allocationId ∈ h₁ ∨ allocationId ∈ h₂ :=
  Finmap.mem_union

private theorem Heap.lookup_union_left {allocationId : AllocId}
    {h₁ h₂ : Heap} (hMem : allocationId ∈ h₁) :
    (h₁ ∪ h₂).lookup allocationId = h₁.lookup allocationId :=
  Finmap.lookup_union_left hMem

private theorem Heap.mem_insert {allocationId insertedId : AllocId}
    {cell : HeapCell} {h : Heap} :
    allocationId ∈ h.insert insertedId cell ↔
      allocationId = insertedId ∨ allocationId ∈ h :=
  Finmap.mem_insert

private theorem Heap.mem_erase {allocationId erasedId : AllocId} {h : Heap} :
    allocationId ∈ h.erase erasedId ↔
      allocationId ≠ erasedId ∧ allocationId ∈ h :=
  Finmap.mem_erase

private theorem Heap.insert_union {allocationId : AllocId}
    {cell : HeapCell} {h₁ h₂ : Heap} :
    (h₁ ∪ h₂).insert allocationId cell =
      h₁.insert allocationId cell ∪ h₂ := by
  apply Heap.ext_impl
  exact Finmap.insert_union

@[simp]
theorem Heap.empty_union (h : Heap) : empty ∪ h = h := by
  apply Heap.ext_impl
  exact Finmap.empty_union

@[simp]
theorem Heap.union_empty (h : Heap) : h ∪ empty = h := by
  apply Heap.ext_impl
  exact Finmap.union_empty

/-- Heaps form a PCM under disjoint union. -/
instance Heap.instPartialCommMonoid : PartialCommMonoid Heap where
  Compatible := Heap.compatible
  compatible_comm hCompatible := by
    exact Finmap.Disjoint.symm _ _ hCompatible
  compatible_empty_left h := by
    exact Finmap.disjoint_empty h.impl
  compatible_assoc a b c := by
    change
      Finmap.Disjoint a.impl b.impl ∧
          Finmap.Disjoint (a.impl ∪ b.impl) c.impl ↔
        Finmap.Disjoint b.impl c.impl ∧
          Finmap.Disjoint a.impl (b.impl ∪ c.impl)
    rw [Finmap.disjoint_union_left, Finmap.disjoint_union_right]
    constructor
    · rintro ⟨hab, hac, hbc⟩
      exact ⟨hbc, hab, hac⟩
    · rintro ⟨hbc, hab, hac⟩
      exact ⟨hab, hac, hbc⟩
  union_assoc _ _ := by
    apply Heap.ext_impl
    exact Finmap.union_assoc
  empty_union _ := by
    apply Heap.ext_impl
    exact Finmap.empty_union
  union_empty _ := by
    apply Heap.ext_impl
    exact Finmap.union_empty
  union_comm_of_compatible hCompatible := by
    apply Heap.ext_impl
    exact Finmap.union_comm_of_disjoint hCompatible

@[expose]
def Ref (_ : Type) := AllocId

/-- Allocation identifiers are natural numbers, so references are inhabited. -/
instance instInhabitedRef {α : Type} : Inhabited (Ref α) := ⟨(0 : AllocId)⟩

@[expose]
def Ref.allocId {α : Type} (r : Ref α) : AllocId := r

def singleton {α : Type} (r : Ref α) (value : α) : Heap :=
  ⟨Finmap.singleton r.allocId ⟨α, value⟩⟩

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
  ∃ rest, PartialCommMonoid.Compatible h rest ∧ h' = h ∪ rest

namespace Heap.Sub

@[refl]
theorem refl (h : Heap) : Heap.Sub h h :=
  ⟨∅,
    PartialCommMonoid.compatible_comm
      (PartialCommMonoid.compatible_empty_left h),
    (PartialCommMonoid.union_empty h).symm⟩

theorem trans {h₁ h₂ h₃ : Heap} (hSub₁₂ : Heap.Sub h₁ h₂)
    (hSub₂₃ : Heap.Sub h₂ h₃) : Heap.Sub h₁ h₃ := by
  obtain ⟨rest₁, hCompatible₁, rfl⟩ := hSub₁₂
  obtain ⟨rest₂, hCompatible₂, rfl⟩ := hSub₂₃
  have ⟨_, hCompatible⟩ :=
    (PartialCommMonoid.compatible_assoc h₁ rest₁ rest₂).mp
      ⟨hCompatible₁, hCompatible₂⟩
  exact ⟨rest₁ ∪ rest₂, hCompatible,
    PartialCommMonoid.union_assoc hCompatible₁ hCompatible₂⟩

theorem of_empty (h : Heap) : Heap.Sub empty h :=
  ⟨h, PartialCommMonoid.compatible_empty_left h,
    (PartialCommMonoid.empty_union h).symm⟩

theorem union_left {h₁ h₂ : Heap}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂) :
    Heap.Sub h₁ (h₁ ∪ h₂) :=
  ⟨h₂, hCompatible, rfl⟩

theorem union_right {h₁ h₂ : Heap}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂) :
    Heap.Sub h₂ (h₁ ∪ h₂) :=
  ⟨h₁, PartialCommMonoid.compatible_comm hCompatible,
    PartialCommMonoid.union_comm_of_compatible hCompatible⟩

/-- An extension of a split heap splits the same way, the extra cells going to
the right-hand side. -/
theorem split {h₁ h₂ h' : Heap}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂)
    (hSub : Heap.Sub (h₁ ∪ h₂) h') :
    ∃ h₂', PartialCommMonoid.Compatible h₁ h₂' ∧
      h' = h₁ ∪ h₂' ∧ Heap.Sub h₂ h₂' := by
  obtain ⟨rest, hCompatibleRest, rfl⟩ := hSub
  have ⟨hCompatible₂, hCompatible₁⟩ :=
    (PartialCommMonoid.compatible_assoc h₁ h₂ rest).mp
      ⟨hCompatible, hCompatibleRest⟩
  exact ⟨h₂ ∪ rest, hCompatible₁,
    PartialCommMonoid.union_assoc hCompatible hCompatibleRest,
    ⟨rest, hCompatible₂, rfl⟩⟩

/-- A heap disjoint from an extension is disjoint from the heap extended. -/
theorem disjoint_of_sub {h h' frame : Heap} (hSub : Heap.Sub h h')
    (hCompatible : PartialCommMonoid.Compatible h' frame) :
    PartialCommMonoid.Compatible h frame := by
  obtain ⟨rest, hCompatibleRest, rfl⟩ := hSub
  have ⟨hRestFrame, hRestFrame'⟩ :=
    (PartialCommMonoid.compatible_assoc h rest frame).mp
      ⟨hCompatibleRest, hCompatible⟩
  have ⟨hFrame, _⟩ :=
    (PartialCommMonoid.compatible_assoc rest frame h).mp
      ⟨hRestFrame,
        PartialCommMonoid.compatible_comm hRestFrame'⟩
  exact PartialCommMonoid.compatible_comm hFrame

/-- Extending on one side of a union extends the union. -/
theorem union_mono_left {h h' frame : Heap} (hSub : Heap.Sub h h')
    (hCompatible : PartialCommMonoid.Compatible h' frame) :
    Heap.Sub (h ∪ frame) (h' ∪ frame) := by
  obtain ⟨rest, hCompatibleRest, rfl⟩ := hSub
  have ⟨hRestFrame, hRestFrame'⟩ :=
    (PartialCommMonoid.compatible_assoc h rest frame).mp
      ⟨hCompatibleRest, hCompatible⟩
  have hFrameRest := PartialCommMonoid.compatible_comm hRestFrame
  have hFrameRest' :
      PartialCommMonoid.Compatible h (frame ∪ rest) := by
    rw [← PartialCommMonoid.union_comm_of_compatible hRestFrame]
    exact hRestFrame'
  have ⟨hCompatibleFrame, hCompatibleCombined⟩ :=
    (PartialCommMonoid.compatible_assoc h frame rest).mpr
      ⟨hFrameRest, hFrameRest'⟩
  refine ⟨rest, hCompatibleCombined, ?_⟩
  calc
    (h ∪ rest) ∪ frame = h ∪ (rest ∪ frame) :=
      PartialCommMonoid.union_assoc hCompatibleRest hCompatible
    _ = h ∪ (frame ∪ rest) := congrArg (h ∪ ·)
      (PartialCommMonoid.union_comm_of_compatible hRestFrame)
    _ = (h ∪ frame) ∪ rest :=
      (PartialCommMonoid.union_assoc
        hCompatibleFrame hCompatibleCombined).symm

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
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂)
    (hContains₁ : contains h₁ r)
    (hContains₂ : contains h₂ r) : False :=
  hCompatible r.allocId (mem_of_contains hContains₁)
    (mem_of_contains hContains₂)

theorem contains_union_left {α : Type} {h₁ h₂ : Heap} {r : Ref α}
    (hContains : contains h₁ r) : contains (h₁ ∪ h₂) r := by
  have hMem : r.allocId ∈ h₁ := mem_of_contains hContains
  unfold contains at hContains ⊢
  rw [Heap.lookup_union_left hMem]
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
  exact Heap.insert_union

theorem fresh_frame {α : Type} {r : Ref α} {value : α}
    {h₁ h₂ h : Heap}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂)
    (hFresh : fresh (h₁ ∪ h₂) r value h) :
    ∃ h₁',
      fresh h₁ r value h₁' ∧
      PartialCommMonoid.Compatible h₁' h₂ ∧
      h = h₁' ∪ h₂ := by
  rcases hFresh with ⟨hUnallocated, rfl⟩
  have hUnallocated₁ : unallocated h₁ r := by
    intro hMem
    exact hUnallocated (Heap.mem_union.mpr (Or.inl hMem))
  have hUnallocated₂ : unallocated h₂ r := by
    intro hMem
    exact hUnallocated (Heap.mem_union.mpr (Or.inr hMem))
  let h₁' := h₁.insert r.allocId ⟨α, value⟩
  refine ⟨h₁', ⟨hUnallocated₁, rfl⟩, ?_, ?_⟩
  · intro allocationId hMem₁ hMem₂
    dsimp [h₁'] at hMem₁
    change allocationId ∈ h₁.insert r.allocId ⟨α, value⟩ at hMem₁
    rw [Heap.mem_insert] at hMem₁
    rcases hMem₁ with hEq | hMem₁
    · exact hUnallocated₂ (hEq ▸ hMem₂)
    · exact hCompatible allocationId hMem₁ hMem₂
  · exact Heap.insert_union

theorem disjoint_update_left {α : Type} {r : Ref α} {value : α}
    {h₁ h₂ : Heap}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂)
    (hContains : contains h₁ r) :
    PartialCommMonoid.Compatible
      (Heap.update r value h₁ hContains) h₂ := by
  have hUnallocated : unallocated h₂ r := by
    intro hMem₂
    unfold contains at hContains
    split at hContains
    · contradiction
    · rename_i cell hLookup
      exact hCompatible r.allocId
        (Finmap.mem_of_lookup_eq_some hLookup) hMem₂
  intro allocationId hMem₁ hMem₂
  change allocationId ∈ h₁.insert r.allocId ⟨α, value⟩ at hMem₁
  rw [Heap.mem_insert] at hMem₁
  rcases hMem₁ with hEq | hMem₁
  · exact hUnallocated (hEq ▸ hMem₂)
  · exact hCompatible allocationId hMem₁ hMem₂

theorem disjoint_free_left {α : Type} {r : Ref α}
    {h₁ h₂ : Heap}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂)
    (hContains : contains h₁ r) :
    PartialCommMonoid.Compatible (Heap.free r h₁ hContains) h₂ := by
  intro allocationId hMem₁ hMem₂
  change allocationId ∈ h₁.erase r.allocId at hMem₁
  exact hCompatible allocationId (Heap.mem_erase.mp hMem₁).right hMem₂

theorem free_union_left {α : Type} {h₁ h₂ : Heap}
    (r : Ref α) (hCompatible : PartialCommMonoid.Compatible h₁ h₂)
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
    fun hMem₂ => hCompatible r.allocId hMem hMem₂
  unfold Heap.free
  apply Heap.ext_impl
  apply Finmap.ext_lookup
  intro allocationId
  change
    Finmap.lookup allocationId (h₁.impl ∪ h₂.impl |>.erase r.allocId) =
      Finmap.lookup allocationId (h₁.impl.erase r.allocId ∪ h₂.impl)
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
  apply Heap.ext_impl
  apply Finmap.ext_lookup
  intro allocationId
  change
    Finmap.lookup allocationId
        ((∅ : HeapImpl).insert r.allocId ⟨α, value⟩) =
      Finmap.lookup allocationId
        (Finmap.singleton r.allocId ⟨α, value⟩ : HeapImpl)
  by_cases hEq : allocationId = r.allocId
  · subst allocationId
    simp
  · rw [Finmap.lookup_insert_of_ne _ hEq]
    symm
    apply Finmap.lookup_eq_none.mpr
    rwa [Finmap.mem_singleton]

/-- Two cells at different references are disjoint. -/
theorem disjoint_singleton {α : Type} {r s : Ref α} {value₁ value₂ : α}
    (hNe : r ≠ s) :
    PartialCommMonoid.Compatible
      (singleton r value₁) (singleton s value₂) := by
  intro allocationId hMem₁ hMem₂
  change allocationId ∈
    (Finmap.singleton r.allocId ⟨α, value₁⟩ : HeapImpl) at hMem₁
  change allocationId ∈
    (Finmap.singleton s.allocId ⟨α, value₂⟩ : HeapImpl) at hMem₂
  rw [Finmap.mem_singleton] at hMem₁
  rw [Finmap.mem_singleton] at hMem₂
  exact hNe (hMem₁.symm.trans hMem₂)

theorem contains_singleton {α : Type} (r : Ref α) (value : α) :
    contains (singleton r value) r := by
  simp [contains, singleton, Heap.lookup]

theorem read_singleton {α : Type} (r : Ref α) (value : α)
    (hContains : contains (singleton r value) r) :
    Heap.read r (singleton r value) hContains = value := by
  unfold Heap.read
  split
  · rename_i hLookup
    change
      Finmap.lookup r.allocId
          (Finmap.singleton r.allocId ⟨α, value⟩ : HeapImpl) =
        none at hLookup
    rw [Finmap.lookup_singleton_eq] at hLookup
    contradiction
  · rename_i β stored hLookup
    change
      Finmap.lookup r.allocId
          (Finmap.singleton r.allocId ⟨α, value⟩ : HeapImpl) =
        some (⟨β, stored⟩ : HeapCell) at hLookup
    rw [Finmap.lookup_singleton_eq] at hLookup
    cases hLookup
    rfl

theorem update_singleton {α : Type} (r : Ref α)
    (oldValue newValue : α)
    (hContains : contains (singleton r oldValue) r) :
    Heap.update r newValue (singleton r oldValue) hContains =
      singleton r newValue := by
  apply Heap.ext_impl
  simp [Heap.update, singleton, Heap.insert]

theorem free_singleton {α : Type} (r : Ref α) (value : α)
    (hContains : contains (singleton r value) r) :
    Heap.free r (singleton r value) hContains = empty := by
  unfold Heap.free
  apply Heap.ext_impl
  apply Finmap.ext_lookup
  intro allocationId
  change
    Finmap.lookup allocationId
        ((Finmap.singleton r.allocId ⟨α, value⟩ : HeapImpl).erase
          r.allocId) =
      Finmap.lookup allocationId (∅ : HeapImpl)
  by_cases hEq : allocationId = r.allocId
  · subst allocationId
    simp
  · rw [Finmap.lookup_erase_ne hEq]
    simp only [Finmap.lookup_empty]
    apply Finmap.lookup_eq_none.mpr
    simpa [singleton, Finmap.mem_singleton] using hEq

end Aeneas.SLPoC
