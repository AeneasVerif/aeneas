module
import Aeneas.Std.HeapLemmas

/-! Heap tests: allocation ids are never reused, `dealloc` only accepts a whole allocation of the
right kind, once, and `freed` slots can never be used again. -/

namespace Aeneas.Std.HeapTests

open Heap

/-- A fresh freeable allocation can be deallocated, but only once. -/
example (value : Nat) :
    ∃ hDealloc : CanDealloc (alloc [value] true ∅).2 (freshLoc ∅) 1 true,
      ¬ CanDealloc ((alloc [value] true ∅).2.dealloc (freshLoc ∅) 1 true hDealloc).2 (freshLoc ∅) 1
        true :=
  ⟨canDealloc_iff.mpr ⟨freshLoc_offset ∅, fun _ hi => isLive_alloc hi,
    (isEndMarker_alloc_end_iff ∅ [value] true true).mpr rfl⟩,
   fun hAgain => not_isEndMarker_dealloc _ (canDealloc_iff.mp hAgain).2.2⟩

/-- A two-slot allocation is deallocated whole. -/
example (a b : Nat) : CanDealloc (alloc [a, b] true ∅).2 (freshLoc ∅) 2 true :=
  canDealloc_iff.mpr ⟨freshLoc_offset ∅, fun _ hi => isLive_alloc hi,
    (isEndMarker_alloc_end_iff ∅ [a, b] true true).mpr rfl⟩

/-- An empty allocation can also be deallocated only once. -/
example :
    ∃ hDealloc : CanDealloc (alloc ([] : List Nat) true ∅).2 (freshLoc ∅) 0 true,
      ¬ CanDealloc ((alloc ([] : List Nat) true ∅).2.dealloc (freshLoc ∅) 0 true hDealloc).2
        (freshLoc ∅) 0 true :=
  ⟨canDealloc_iff.mpr ⟨freshLoc_offset ∅, fun _ hi => absurd hi (Nat.not_lt_zero _),
    (isEndMarker_alloc_end_iff ∅ ([] : List Nat) true true).mpr rfl⟩,
   fun hAgain => not_isEndMarker_dealloc _ (canDealloc_iff.mp hAgain).2.2⟩

/-- Allocating after a deallocation gets a new id, and the deallocated slot stays dead. -/
example {α : Type} (h : Heap) (l : Loc) (freeable : Bool) (hDealloc : CanDealloc h l 1 freeable)
    (value : α) :
    (freshLoc (h.dealloc l 1 freeable hDealloc).2).allocId ≠ l.allocId ∧
      ¬ IsLive ((h.dealloc l 1 freeable hDealloc).2.alloc [value] false).2 l := by
  have hMem : l ∈ (h.dealloc l 1 freeable hDealloc).2 := by
    simpa using mem_dealloc hDealloc (Nat.zero_le 1)
  refine ⟨fun hEq => notMem_freshAllocId (by simpa using hEq.symm) hMem, fun hLive => ?_⟩
  exact not_isLive_dealloc hDealloc (Nat.zero_le 1)
    (by simpa using (isLive_alloc_of_mem hMem).mp hLive)

/-- An empty allocation reserves its id, and its pointer stays dead after the next allocation. -/
example {α β : Type} (h : Heap) (value : β) :
    (freshLoc (h.alloc ([] : List α) false).2).allocId ≠ (freshLoc h).allocId ∧
      ¬ IsLive ((h.alloc ([] : List α) false).2.alloc [value] false).2 (freshLoc h) := by
  have hMem : freshLoc h ∈ (h.alloc ([] : List α) false).2 := by
    simpa using mem_alloc_end (freeable := false) h ([] : List α)
  refine ⟨fun hEq => notMem_freshAllocId (by simpa using hEq.symm) hMem, fun hLive => ?_⟩
  exact not_isLive_alloc_end (freeable := false) h ([] : List α)
    (by simpa using (isLive_alloc_of_mem hMem).mp hLive)

/-- An allocation not from the global allocator (e.g. a copy behind a reference) cannot be
deallocated through the allocator. -/
example (value : Nat) : ¬ CanDealloc (alloc [value] false ∅).2 (freshLoc ∅) 1 true :=
  fun hDealloc => by
    simpa using
      (isEndMarker_alloc_end_iff ∅ [value] false true).mp (canDealloc_iff.mp hDealloc).2.2

/-- Conversely, memory from the global allocator cannot be released as a view. -/
example (value : Nat) : ¬ CanDealloc (alloc [value] true ∅).2 (freshLoc ∅) 1 false :=
  fun hDealloc => by
    simpa using
      (isEndMarker_alloc_end_iff ∅ [value] true false).mp (canDealloc_iff.mp hDealloc).2.2

/-- `endBorrow` never applies to a deallocated slot. -/
example (h : Heap) (l : Loc) (freeable : Bool) (hDealloc : CanDealloc h l 1 freeable) :
    ¬ IsBorrowed (h.dealloc l 1 freeable hDealloc).2 l := by
  simpa using not_isBorrowed_dealloc hDealloc (Nat.zero_le 1)

/-- While a slot is borrowed, its allocation cannot be deallocated. -/
example (h : Heap) (q : MutRawPtr Nat) (hValid : IsValid h q) (freeable : Bool) :
    ¬ CanDealloc (h.borrow q hValid).2 q.loc 1 freeable :=
  fun hDealloc =>
    not_isLive_borrow hValid (by simpa using (canDealloc_iff.mp hDealloc).2.1 0 one_pos)

/-- An interior pointer cannot be deallocated. -/
example (a b : Nat) : ¬ CanDealloc (alloc [a, b] true ∅).2 ((freshLoc ∅).shift 1) 1 true :=
  fun hDealloc => by simpa using (canDealloc_iff.mp hDealloc).1

/-- A size smaller than the allocation's is rejected. -/
example (a b : Nat) : ¬ CanDealloc (alloc [a, b] true ∅).2 (freshLoc ∅) 1 true :=
  fun hDealloc =>
    not_isLive_of_isEndMarker (canDealloc_iff.mp hDealloc).2.2 (isLive_alloc (i := 1) (by simp))

/-- A size larger than the allocation's is rejected. -/
example (value : Nat) : ¬ CanDealloc (alloc [value] true ∅).2 (freshLoc ∅) 2 true :=
  fun hDealloc => by
    exact not_isLive_alloc_end (h := ∅) [value] ((canDealloc_iff.mp hDealloc).2.1 1 (by omega))

/-! Reasoning about new cells from outside the heap module: `alloc_eq` and `allocation_eq` expose
how `alloc` builds its result, and `RawPtr.loc_shift` says where a shifted pointer points. -/

/-- A shifted pointer moves within its allocation. -/
example (q : MutRawPtr Nat) : ((q.shift 1).shift 2).loc = q.loc.shift 3 := by
  simp [Loc.shift_shift]

/-- The second cell of a fresh allocation is reachable through a pointer shifted from its start,
and holds the second value. -/
example (h : Heap) (a b : Nat) :
    ∃ hValid : IsValid (h.alloc [a, b] true).2 ((⟨freshLoc h⟩ : MutRawPtr Nat).shift 1),
      ((h.alloc [a, b] true).2.read _ hValid).1 = b := by
  have hq : (⟨freshLoc h⟩ : MutRawPtr Nat).shift 1 = ⟨(freshLoc h).shift 1⟩ :=
    RawPtr.ext (by simp)
  have hCells : Subheap (singleton ((⟨freshLoc h⟩ : MutRawPtr Nat).shift 1) b)
      (array (freshLoc h) [a, b]) := by
    have hCompatible := compatible_array_append (freshLoc h) [a] [b]
    rw [hq, show [a, b] = [a] ++ [b] from rfl, array_append]
    simpa using Subheap.union_right hCompatible
  have hSub : Subheap (singleton ((⟨freshLoc h⟩ : MutRawPtr Nat).shift 1) b)
      (h.alloc [a, b] true).2 := by
    rw [alloc_eq, allocation_eq]
    refine hCells.trans ((Subheap.union_left ?_).trans (Subheap.union_left ?_))
    · exact compatible_array_endMarker _ _ _
    · rw [← allocation_eq]
      exact compatible_freshLoc _ _ _
  exact ⟨hSub.isValid (isValid_singleton _ b), read_of_subheap hSub _⟩

/-- Allocation frames the existing heap: a cell already there keeps its value. -/
example (h : Heap) (q : MutRawPtr Nat) (value : Nat) (hCell : Subheap (singleton q value) h)
    (values : List Nat) :
    ∃ hValid : IsValid (h.alloc values true).2 q,
      ((h.alloc values true).2.read q hValid).1 = value := by
  have hSub : Subheap (singleton q value) (h.alloc values true).2 := by
    rw [alloc_eq]
    exact hCell.trans (Subheap.union_right (compatible_freshLoc _ _ _))
  exact ⟨hSub.isValid (isValid_singleton q value), read_of_subheap hSub _⟩

end Aeneas.Std.HeapTests
