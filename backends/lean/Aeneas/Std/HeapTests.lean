module
import Aeneas.Std.HeapLemmas

/-! Heap tests: allocation ids are never reused, `dealloc` only accepts a whole allocation of the
right kind, once, and `freed` slots can never be used again. -/

namespace Aeneas.Std.HeapTests

open Heap

-- The start of the first allocation in the empty heap (alignment `1`).
local notation "p₀" => (RawPtr.mk (freshLoc ∅ 1) : MutRawPtr Nat)

/-- A fresh global allocation can be deallocated, but only once. -/
example (value : Nat) :
    ∃ hDealloc : CanDealloc (alloc 1 [some value] .global ∅).2 p₀ 1 .global,
      ¬ CanDealloc ((alloc 1 [some value] .global ∅).2.dealloc p₀ 1 .global hDealloc).2 p₀ 1
        .global :=
  ⟨canDealloc_iff.mpr ⟨freshLoc_offset ∅ 1, fun _ hi => isLive_alloc hi,
    (isEndMarker_alloc_end_iff ∅ 1 [some value] .global .global).mpr rfl⟩,
   fun hAgain => not_isEndMarker_dealloc _ (canDealloc_iff.mp hAgain).2.2⟩

/-- A two-slot allocation is deallocated whole. -/
example (a b : Nat) : CanDealloc (alloc 1 [some a, some b] .global ∅).2 p₀ 2 .global :=
  canDealloc_iff.mpr ⟨freshLoc_offset ∅ 1, fun _ hi => isLive_alloc hi,
    (isEndMarker_alloc_end_iff ∅ 1 [some a, some b] .global .global).mpr rfl⟩

/-- An empty allocation can also be deallocated only once. -/
example :
    ∃ hDealloc : CanDealloc (alloc 1 ([] : List (Option Nat)) .global ∅).2 p₀ 0 .global,
      ¬ CanDealloc ((alloc 1 ([] : List (Option Nat)) .global ∅).2.dealloc p₀ 0 .global
        hDealloc).2 p₀ 0 .global :=
  ⟨canDealloc_iff.mpr ⟨freshLoc_offset ∅ 1, fun _ hi => absurd hi (Nat.not_lt_zero _),
    (isEndMarker_alloc_end_iff ∅ 1 ([] : List (Option Nat)) .global .global).mpr rfl⟩,
   fun hAgain => not_isEndMarker_dealloc _ (canDealloc_iff.mp hAgain).2.2⟩

/-- Allocating after a deallocation gets a new id, and the deallocated slot stays dead. -/
example {α : Type} (h : Heap) (q : MutRawPtr Nat) (kind : AllocKind)
    (hDealloc : CanDealloc h q 1 kind) (value : Option α) :
    (freshLoc (h.dealloc q 1 kind hDealloc).2 1).allocId ≠ q.loc.allocId ∧
      ¬ IsLive ((h.dealloc q 1 kind hDealloc).2.alloc 1 [value] .view).2 q.loc := by
  have hMem : q.loc ∈ (h.dealloc q 1 kind hDealloc).2 := by
    simpa using mem_dealloc hDealloc (Nat.zero_le 1)
  refine ⟨fun hEq => notMem_freshAllocId (by simpa using hEq.symm) hMem, fun hLive => ?_⟩
  exact not_isLive_dealloc hDealloc (Nat.zero_le 1)
    (by simpa using (isLive_alloc_of_mem hMem).mp hLive)

/-- An empty allocation reserves its id, and its pointer stays dead after the next allocation. -/
example {α β : Type} (h : Heap) (value : Option β) :
    (freshLoc (h.alloc 1 ([] : List (Option α)) .view).2 1).allocId ≠ (freshLoc h 1).allocId ∧
      ¬ IsLive ((h.alloc 1 ([] : List (Option α)) .view).2.alloc 1 [value] .view).2
        (freshLoc h 1) := by
  have hMem : freshLoc h 1 ∈ (h.alloc 1 ([] : List (Option α)) .view).2 := by
    simpa using mem_alloc_end (kind := .view) h 1 ([] : List (Option α))
  refine ⟨fun hEq => notMem_freshAllocId (by simpa using hEq.symm) hMem, fun hLive => ?_⟩
  exact not_isLive_alloc_end (kind := .view) h 1 ([] : List (Option α))
    (by simpa using (isLive_alloc_of_mem hMem).mp hLive)

/-- An allocation not from the global allocator (e.g. a copy behind a reference) cannot be
deallocated through the allocator. -/
example (value : Nat) : ¬ CanDealloc (alloc 1 [some value] .view ∅).2 p₀ 1 .global :=
  fun hDealloc => by
    simpa using (isEndMarker_alloc_end_iff ∅ 1 [some value] .view .global).mp
      (canDealloc_iff.mp hDealloc).2.2

/-- Conversely, memory from the global allocator cannot be released as a view. -/
example (value : Nat) : ¬ CanDealloc (alloc 1 [some value] .global ∅).2 p₀ 1 .view :=
  fun hDealloc => by
    simpa using (isEndMarker_alloc_end_iff ∅ 1 [some value] .global .view).mp
      (canDealloc_iff.mp hDealloc).2.2

/-- `endBorrow` never applies to a deallocated slot. -/
example (h : Heap) (q : MutRawPtr Nat) (kind : AllocKind) (hDealloc : CanDealloc h q 1 kind) :
    ¬ IsBorrowed (h.dealloc q 1 kind hDealloc).2 q.loc := by
  simpa using not_isBorrowed_dealloc hDealloc (Nat.zero_le 1)

/-- While a slot is borrowed, its allocation cannot be deallocated. -/
example (h : Heap) (q : MutRawPtr Nat) (hValid : IsValid h q) (kind : AllocKind) :
    ¬ CanDealloc (h.borrow q hValid).2 q 1 kind :=
  fun hDealloc =>
    not_isLive_borrow hValid (by simpa using (canDealloc_iff.mp hDealloc).2.1 0 one_pos)

/-- An interior pointer cannot be deallocated. -/
example (a b : Nat) :
    ¬ CanDealloc (alloc 1 [some a, some b] .global ∅).2 (RawPtr.shiftCells p₀ 1) 1 .global :=
  fun hDealloc => by simpa using (canDealloc_iff.mp hDealloc).1

/-- A size smaller than the allocation's is rejected. -/
example (a b : Nat) : ¬ CanDealloc (alloc 1 [some a, some b] .global ∅).2 p₀ 1 .global :=
  fun hDealloc =>
    not_isLive_of_isEndMarker (canDealloc_iff.mp hDealloc).2.2 (isLive_alloc (i := 1) (by simp))

/-- A size larger than the allocation's is rejected. -/
example (value : Nat) : ¬ CanDealloc (alloc 1 [some value] .global ∅).2 p₀ 2 .global :=
  fun hDealloc => by
    exact not_isLive_alloc_end (h := ∅) 1 [some value]
      ((canDealloc_iff.mp hDealloc).2.1 1 (by omega))

/-- Fresh allocations are aligned, and never in the null allocation `0`. -/
example (h : Heap) : 8 ∣ (freshLoc h 8).allocId ∧ (freshLoc h 8).allocId ≠ 0 :=
  ⟨by simpa using dvd_freshAllocId h 8, by simpa using freshAllocId_ne_zero h 8⟩

/-! Reasoning about new cells from outside the heap module: `alloc_eq` and `allocation_eq` expose
how `alloc` builds its result, and `RawPtr.loc_shiftCells` says where a shifted pointer points. -/

/-- A shifted pointer moves within its allocation. -/
example (q : MutRawPtr Nat) : ((q.shiftCells 1).shiftCells 2).loc = q.loc.shift 3 := by
  simp [Loc.shift_shift]

/-- The second cell of a fresh allocation is reachable through a pointer shifted from its start,
and holds the second value. -/
example (h : Heap) (a b : Option Nat) :
    ∃ hValid : IsValid (h.alloc 1 [a, b] .global).2
        ((⟨freshLoc h 1⟩ : MutRawPtr Nat).shiftCells 1),
      ((h.alloc 1 [a, b] .global).2.read _ hValid).1 = b := by
  have hq : (⟨freshLoc h 1⟩ : MutRawPtr Nat).shiftCells 1 = ⟨(freshLoc h 1).shift 1⟩ :=
    RawPtr.ext (by simp)
  have hCells : Subheap (cell ((⟨freshLoc h 1⟩ : MutRawPtr Nat).shiftCells 1) b)
      (array (freshLoc h 1) [a, b]) := by
    have hCompatible := compatible_array_append (freshLoc h 1) [a] [b]
    rw [hq, show [a, b] = [a] ++ [b] from rfl, array_append]
    simpa using Subheap.union_right hCompatible
  have hSub : Subheap (cell ((⟨freshLoc h 1⟩ : MutRawPtr Nat).shiftCells 1) b)
      (h.alloc 1 [a, b] .global).2 := by
    rw [alloc_eq, allocation_eq]
    refine hCells.trans ((Subheap.union_left ?_).trans (Subheap.union_left ?_))
    · exact compatible_array_endMarker _ _ _
    · rw [← allocation_eq]
      exact compatible_freshLoc _ _ _ _
  exact ⟨hSub.isValid (isValid_cell _ b), read_of_subheap hSub _⟩

/-- Allocation frames the existing heap: a cell already there keeps its content. -/
example (h : Heap) (q : MutRawPtr Nat) (value : Option Nat) (hCell : Subheap (cell q value) h)
    (values : List (Option Nat)) :
    ∃ hValid : IsValid (h.alloc 1 values .global).2 q,
      ((h.alloc 1 values .global).2.read q hValid).1 = value := by
  have hSub : Subheap (cell q value) (h.alloc 1 values .global).2 := by
    rw [alloc_eq]
    exact hCell.trans (Subheap.union_right (compatible_freshLoc _ _ _ _))
  exact ⟨hSub.isValid (isValid_cell q value), read_of_subheap hSub _⟩

/-- Writing initializes a cell: an uninitialized cell reads back the written value. -/
example (q : MutRawPtr Nat) (value : Nat) (hValid : IsValid (cell q none) q) :
    ∃ hValid' : IsValid ((cell q none).write q (some value) hValid).2 q,
      (((cell q none).write q (some value) hValid).2.read q hValid').1 = some value := by
  rw [write_cell]
  exact ⟨isValid_cell q _, by rw [read_cell]⟩

end Aeneas.Std.HeapTests
