module
import Aeneas.Std.HeapLemmas

/-! Heap tests: allocation ids are never reused, `dealloc` only accepts a whole block of the right
kind, once, and freed blocks can never be used again. -/

namespace Aeneas.Std.HeapTests

open Heap

-- The start of the first allocation in the empty heap.
local notation "p₀" => (RawPtr.mk (freshAllocId ∅) 0 : MutRawPtr Nat)

/-- A fresh heap allocation can be deallocated, but only once. -/
example (value : Nat) :
    ∃ hDealloc : CanDealloc (alloc [value] .heap ∅).2 p₀ 1 .heap,
      ¬ CanDealloc ((alloc [value] .heap ∅).2.dealloc p₀ 1 .heap hDealloc).2 p₀ 1 .heap :=
  ⟨(canDealloc_alloc_iff ∅ [value] 1 .heap .heap).mpr ⟨rfl, rfl⟩, not_canDealloc_dealloc _ rfl⟩

/-- A two-cell allocation is deallocated whole. -/
example (a b : Nat) : CanDealloc (alloc [a, b] .heap ∅).2 p₀ 2 .heap :=
  (canDealloc_alloc_iff ∅ [a, b] 2 .heap .heap).mpr ⟨rfl, rfl⟩

/-- An empty allocation can also be deallocated only once. -/
example :
    ∃ hDealloc : CanDealloc (alloc ([] : List Nat) .heap ∅).2 p₀ 0 .heap,
      ¬ CanDealloc ((alloc ([] : List Nat) .heap ∅).2.dealloc p₀ 0 .heap hDealloc).2 p₀ 0 .heap :=
  ⟨(canDealloc_alloc_iff ∅ ([] : List Nat) 0 .heap .heap).mpr ⟨rfl, rfl⟩,
    not_canDealloc_dealloc _ rfl⟩

/-- Allocating after a deallocation gets a new id, and the freed block stays dead. -/
example {α : Type} (h : Heap) (q : MutRawPtr Nat) (kind : AllocKind)
    (hDealloc : CanDealloc h q 1 kind) (value : α) :
    freshAllocId (h.dealloc q 1 kind hDealloc).2 ≠ q.allocId ∧
      ¬ IsLive ((h.dealloc q 1 kind hDealloc).2.alloc [value] .view).2 q := by
  have hMem := mem_dealloc hDealloc
  refine ⟨fun hEq => notMem_freshAllocId hEq.symm hMem, fun hLive => ?_⟩
  exact not_isLive_dealloc hDealloc rfl ((isLive_alloc_of_mem hMem).mp hLive)

/-- An empty allocation reserves its id, and its pointer stays dead after the next allocation. -/
example {α β : Type} (h : Heap) (value : β) :
    freshAllocId (h.alloc ([] : List α) .view).2 ≠ freshAllocId h ∧
      ¬ IsLive ((h.alloc ([] : List α) .view).2.alloc [value] .view).2
        (⟨freshAllocId h, 0⟩ : MutRawPtr α) := by
  have hMem := mem_alloc (kind := .view) h ([] : List α)
  refine ⟨fun hEq => notMem_freshAllocId hEq.symm hMem, fun hLive => ?_⟩
  exact not_isLive_alloc_of_le (values := ([] : List α)) (kind := .view) (i := 0) (by simp)
    ((isLive_alloc_of_mem hMem).mp hLive)

/-- A view (e.g. a copy behind a reference) cannot be deallocated through the allocator. -/
example (value : Nat) : ¬ CanDealloc (alloc [value] .view ∅).2 p₀ 1 .heap :=
  fun hDealloc => nomatch ((canDealloc_alloc_iff ∅ [value] 1 .view .heap).mp hDealloc).1

/-- Conversely, memory from the global allocator cannot be released as a view. -/
example (value : Nat) : ¬ CanDealloc (alloc [value] .heap ∅).2 p₀ 1 .view :=
  fun hDealloc => nomatch ((canDealloc_alloc_iff ∅ [value] 1 .heap .view).mp hDealloc).1

/-- `endBorrow` never applies to a freed block. -/
example (h : Heap) (q : MutRawPtr Nat) (kind : AllocKind) (hDealloc : CanDealloc h q 1 kind) :
    ¬ IsBorrowed (h.dealloc q 1 kind hDealloc).2 q :=
  not_isBorrowed_dealloc hDealloc rfl

/-- While a cell is borrowed, its block cannot be deallocated. -/
example (h : Heap) (q : MutRawPtr Nat) (hValid : IsValid h q) (kind : AllocKind) :
    ¬ CanDealloc (h.borrow q hValid).2 q 1 kind :=
  fun hDealloc => not_isLive_borrow hValid (by simpa using isLive_of_canDealloc hDealloc one_pos)

/-- An interior pointer cannot be deallocated. -/
example (a b : Nat) : ¬ CanDealloc (alloc [a, b] .heap ∅).2 (RawPtr.shift p₀ 1) 1 .heap :=
  fun hDealloc => by simpa using offset_eq_zero_of_canDealloc hDealloc

/-- A size smaller than the block's is rejected. -/
example (a b : Nat) : ¬ CanDealloc (alloc [a, b] .heap ∅).2 p₀ 1 .heap :=
  fun hDealloc => nomatch ((canDealloc_alloc_iff ∅ [a, b] 1 .heap .heap).mp hDealloc).2

/-- A size larger than the block's is rejected. -/
example (value : Nat) : ¬ CanDealloc (alloc [value] .heap ∅).2 p₀ 2 .heap :=
  fun hDealloc => nomatch ((canDealloc_alloc_iff ∅ [value] 2 .heap .heap).mp hDealloc).2

/-! Reasoning about new cells from outside the heap module: `alloc_eq` exposes how `alloc` builds
its result, and `Subheap.singleton_allocation` splits a fresh block into one cell per value. -/

/-- A shifted pointer moves within its allocation. -/
example (q : MutRawPtr Nat) : (q.shift 1).shift 2 = q.shift 3 := by
  simp [RawPtr.shift_shift]

/-- The second cell of a fresh allocation holds the second value. -/
example (h : Heap) (a b : Nat) :
    ∃ hValid : IsValid (h.alloc [a, b] .heap).2 (⟨freshAllocId h, 1⟩ : MutRawPtr Nat),
      ((h.alloc [a, b] .heap).2.read _ hValid).1 = b := by
  have hSub : Subheap (singleton (⟨freshAllocId h, 1⟩ : MutRawPtr Nat) b .heap 2)
      (h.alloc [a, b] .heap).2 := by
    rw [alloc_eq]
    exact (Subheap.singleton_allocation (freshAllocId h) [a, b] .heap (i := 1) (by simp)).trans
      (Subheap.union_left (compatible_freshAllocId _ _ _))
  exact ⟨hSub.isValid (isValid_singleton _ b .heap (by simp)), read_of_subheap hSub (by simp) _⟩

/-- Allocation frames the existing heap: a cell already there keeps its value. -/
example (h : Heap) (q : MutRawPtr Nat) (value : Nat) (kind : AllocKind) (len : Nat)
    (hOffset : q.offset < len) (hCell : Subheap (singleton q value kind len) h)
    (values : List Nat) :
    ∃ hValid : IsValid (h.alloc values .heap).2 q,
      ((h.alloc values .heap).2.read q hValid).1 = value := by
  have hSub : Subheap (singleton q value kind len) (h.alloc values .heap).2 := by
    rw [alloc_eq]
    exact hCell.trans (Subheap.union_right (compatible_freshAllocId _ _ _))
  exact ⟨hSub.isValid (isValid_singleton q value kind hOffset), read_of_subheap hSub hOffset _⟩

end Aeneas.Std.HeapTests
