module
import Aeneas.Std.HeapLemmas

/-! Heap tests: allocation ids are never reused, and `dealloc` only accepts a whole freeable
allocation, once. -/

namespace Aeneas.Std.HeapTests

open Heap

/-- A fresh freeable allocation can be deallocated, but only once. -/
example (value : Nat) :
    ∃ hDealloc : CanDealloc (alloc ∅ [value] true) (freshLoc ∅) 1,
      ¬ CanDealloc ((alloc ∅ [value] true).dealloc (freshLoc ∅) 1 hDealloc) (freshLoc ∅) 1 :=
  ⟨canDealloc_iff.mpr ⟨freshLoc_offset ∅, fun _ hi => isLive_alloc hi,
    (isFreeableEnd_alloc_end_iff ∅ [value] true).mpr rfl⟩,
   fun hAgain => not_isFreeableEnd_dealloc _ (canDealloc_iff.mp hAgain).2.2⟩

/-- A two-slot allocation is deallocated whole. -/
example (a b : Nat) : CanDealloc (alloc ∅ [a, b] true) (freshLoc ∅) 2 :=
  canDealloc_iff.mpr ⟨freshLoc_offset ∅, fun _ hi => isLive_alloc hi,
    (isFreeableEnd_alloc_end_iff ∅ [a, b] true).mpr rfl⟩

/-- An empty allocation can also be deallocated only once. -/
example :
    ∃ hDealloc : CanDealloc (alloc ∅ ([] : List Nat) true) (freshLoc ∅) 0,
      ¬ CanDealloc ((alloc ∅ ([] : List Nat) true).dealloc (freshLoc ∅) 0 hDealloc)
        (freshLoc ∅) 0 :=
  ⟨canDealloc_iff.mpr ⟨freshLoc_offset ∅, fun _ hi => absurd hi (Nat.not_lt_zero _),
    (isFreeableEnd_alloc_end_iff ∅ ([] : List Nat) true).mpr rfl⟩,
   fun hAgain => not_isFreeableEnd_dealloc _ (canDealloc_iff.mp hAgain).2.2⟩

/-- Allocating after a deallocation gets a new id, and the deallocated slot stays dead. -/
example {α : Type} (h : Heap) (l : Loc) (hDealloc : CanDealloc h l 1) (value : α) :
    (freshLoc (h.dealloc l 1 hDealloc)).allocId ≠ l.allocId ∧
      ¬ IsLive (alloc (h.dealloc l 1 hDealloc) [value] false) l := by
  have hMem : l ∈ h.dealloc l 1 hDealloc := by
    simpa using mem_dealloc hDealloc (Nat.zero_le 1)
  refine ⟨fun hEq => notMem_freshAllocId (by simpa using hEq.symm) hMem, fun hLive => ?_⟩
  exact not_isLive_dealloc hDealloc (Nat.zero_le 1)
    (by simpa using (isLive_alloc_of_mem hMem).mp hLive)

/-- An empty allocation reserves its id, and its pointer stays dead after the next allocation. -/
example {α β : Type} (h : Heap) (value : β) :
    (freshLoc (alloc h ([] : List α) false)).allocId ≠ (freshLoc h).allocId ∧
      ¬ IsLive (alloc (alloc h ([] : List α) false) [value] false) (freshLoc h) := by
  have hMem : freshLoc h ∈ alloc h ([] : List α) false := by
    simpa using mem_alloc_end (freeable := false) h ([] : List α)
  refine ⟨fun hEq => notMem_freshAllocId (by simpa using hEq.symm) hMem, fun hLive => ?_⟩
  exact not_isLive_alloc_end (freeable := false) h ([] : List α)
    (by simpa using (isLive_alloc_of_mem hMem).mp hLive)

/-- An allocation not from the global allocator (e.g. a copy behind a reference) cannot be
deallocated. -/
example (value : Nat) : ¬ CanDealloc (alloc ∅ [value] false) (freshLoc ∅) 1 :=
  fun hDealloc => by
    simpa using (isFreeableEnd_alloc_end_iff ∅ [value] false).mp (canDealloc_iff.mp hDealloc).2.2

/-- An interior pointer cannot be deallocated. -/
example (a b : Nat) : ¬ CanDealloc (alloc ∅ [a, b] true) ((freshLoc ∅).shift 1) 1 :=
  fun hDealloc => by simpa using (canDealloc_iff.mp hDealloc).1

/-- A size smaller than the allocation's is rejected. -/
example (a b : Nat) : ¬ CanDealloc (alloc ∅ [a, b] true) (freshLoc ∅) 1 :=
  fun hDealloc =>
    not_isLive_of_isFreeableEnd (canDealloc_iff.mp hDealloc).2.2 (isLive_alloc (i := 1) (by simp))

/-- A size larger than the allocation's is rejected. -/
example (value : Nat) : ¬ CanDealloc (alloc ∅ [value] true) (freshLoc ∅) 2 :=
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
    ∃ hValid : IsValid (alloc h [a, b] true) ((⟨freshLoc h⟩ : MutRawPtr Nat).shift 1),
      (alloc h [a, b] true).read _ hValid = b := by
  have hq : (⟨freshLoc h⟩ : MutRawPtr Nat).shift 1 = ⟨(freshLoc h).shift 1⟩ :=
    RawPtr.ext (by simp)
  have hCells : Subheap (singleton ((⟨freshLoc h⟩ : MutRawPtr Nat).shift 1) b)
      (array (freshLoc h) [a, b]) := by
    have hCompatible := compatible_array_append (freshLoc h) [a] [b]
    rw [hq, show [a, b] = [a] ++ [b] from rfl, array_append]
    simpa using Subheap.union_right hCompatible
  have hSub : Subheap (singleton ((⟨freshLoc h⟩ : MutRawPtr Nat).shift 1) b)
      (alloc h [a, b] true) := by
    rw [alloc_eq, allocation_eq]
    refine hCells.trans ((Subheap.union_left ?_).trans (Subheap.union_left ?_))
    · exact compatible_array_endMarker _ _ _
    · rw [← allocation_eq]
      exact compatible_freshLoc _ _ _
  exact ⟨hSub.isValid (isValid_singleton _ b), read_of_subheap hSub _⟩

/-- Allocation frames the existing heap: a cell already there keeps its value. -/
example (h : Heap) (q : MutRawPtr Nat) (value : Nat) (hCell : Subheap (singleton q value) h)
    (values : List Nat) :
    ∃ hValid : IsValid (alloc h values true) q, (alloc h values true).read q hValid = value := by
  have hSub : Subheap (singleton q value) (alloc h values true) := by
    rw [alloc_eq]
    exact hCell.trans (Subheap.union_right (compatible_freshLoc _ _ _))
  exact ⟨hSub.isValid (isValid_singleton q value), read_of_subheap hSub _⟩

end Aeneas.Std.HeapTests
