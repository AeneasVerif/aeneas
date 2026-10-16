module
import Aeneas.Std.HeapLemmas

/-! Heap tests: allocation ids are never reused, `dealloc` only accepts a whole allocation of the
right kind, once, and `freed` slots can never be used again. -/

namespace Aeneas.Std.HeapTests

open Heap

-- The start of the first allocation in the empty heap.
local notation "p₀" => (RawPtr.mk (freshLoc ∅) : MutRawPtr Nat)

/-- A fresh global allocation can be deallocated, but only once. -/
example (value : Nat) :
    ∃ hDealloc : CanDealloc (alloc [some value] .global ∅).2 p₀ 1 .global,
      ¬ CanDealloc ((alloc [some value] .global ∅).2.dealloc p₀ 1 .global hDealloc).2 p₀ 1
        .global :=
  ⟨canDealloc_iff.mpr ⟨freshLoc_offset ∅, fun _ hi => isLive_alloc hi,
    (isEndMarker_alloc_end_iff ∅ [some value] .global .global).mpr rfl⟩,
   fun hAgain => not_isEndMarker_dealloc _ (canDealloc_iff.mp hAgain).2.2⟩

/-- A two-slot allocation is deallocated whole. -/
example (a b : Nat) : CanDealloc (alloc [some a, some b] .global ∅).2 p₀ 2 .global :=
  canDealloc_iff.mpr ⟨freshLoc_offset ∅, fun _ hi => isLive_alloc hi,
    (isEndMarker_alloc_end_iff ∅ [some a, some b] .global .global).mpr rfl⟩

/-- An empty allocation can also be deallocated only once. -/
example :
    ∃ hDealloc : CanDealloc (alloc ([] : List (Option Nat)) .global ∅).2 p₀ 0 .global,
      ¬ CanDealloc ((alloc ([] : List (Option Nat)) .global ∅).2.dealloc p₀ 0 .global
        hDealloc).2 p₀ 0 .global :=
  ⟨canDealloc_iff.mpr ⟨freshLoc_offset ∅, fun _ hi => absurd hi (Nat.not_lt_zero _),
    (isEndMarker_alloc_end_iff ∅ ([] : List (Option Nat)) .global .global).mpr rfl⟩,
   fun hAgain => not_isEndMarker_dealloc _ (canDealloc_iff.mp hAgain).2.2⟩

/-- Allocating after a deallocation gets a new id, and the deallocated slot stays dead. -/
example {α : Type} (h : Heap) (q : MutRawPtr Nat) (kind : AllocKind)
    (hDealloc : CanDealloc h q 1 kind) (value : Option α) :
    (freshLoc (h.dealloc q 1 kind hDealloc).2).allocId ≠ q.loc.allocId ∧
      ¬ IsLive ((h.dealloc q 1 kind hDealloc).2.alloc [value] .view).2 q.loc := by
  have hMem : q.loc ∈ (h.dealloc q 1 kind hDealloc).2 := by
    simpa using mem_dealloc hDealloc (Nat.zero_le 1)
  refine ⟨fun hEq => notMem_freshAllocId (by simpa using hEq.symm) hMem, fun hLive => ?_⟩
  exact not_isLive_dealloc hDealloc (Nat.zero_le 1)
    (by simpa using (isLive_alloc_of_mem hMem).mp hLive)

/-- An empty allocation reserves its id, and its pointer stays dead after the next allocation. -/
example {α β : Type} (h : Heap) (value : Option β) :
    (freshLoc (h.alloc ([] : List (Option α)) .view).2).allocId ≠ (freshLoc h).allocId ∧
      ¬ IsLive ((h.alloc ([] : List (Option α)) .view).2.alloc [value] .view).2 (freshLoc h) := by
  have hMem : freshLoc h ∈ (h.alloc ([] : List (Option α)) .view).2 := by
    simpa using mem_alloc_end (kind := .view) h ([] : List (Option α))
  refine ⟨fun hEq => notMem_freshAllocId (by simpa using hEq.symm) hMem, fun hLive => ?_⟩
  exact not_isLive_alloc_end (kind := .view) h ([] : List (Option α))
    (by simpa using (isLive_alloc_of_mem hMem).mp hLive)

/-- An allocation not from the global allocator (e.g. a copy behind a reference) cannot be
deallocated through the allocator. -/
example (value : Nat) : ¬ CanDealloc (alloc [some value] .view ∅).2 p₀ 1 .global :=
  fun hDealloc => by
    simpa using (isEndMarker_alloc_end_iff ∅ [some value] .view .global).mp
      (canDealloc_iff.mp hDealloc).2.2

/-- Conversely, memory from the global allocator cannot be released as a view. -/
example (value : Nat) : ¬ CanDealloc (alloc [some value] .global ∅).2 p₀ 1 .view :=
  fun hDealloc => by
    simpa using (isEndMarker_alloc_end_iff ∅ [some value] .global .view).mp
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
    ¬ CanDealloc (alloc [some a, some b] .global ∅).2 (RawPtr.shift p₀ 1) 1 .global :=
  fun hDealloc => by simpa using (canDealloc_iff.mp hDealloc).1

/-- A size smaller than the allocation's is rejected. -/
example (a b : Nat) : ¬ CanDealloc (alloc [some a, some b] .global ∅).2 p₀ 1 .global :=
  fun hDealloc =>
    not_isLive_of_isEndMarker (canDealloc_iff.mp hDealloc).2.2 (isLive_alloc (i := 1) (by simp))

/-- A size larger than the allocation's is rejected. -/
example (value : Nat) : ¬ CanDealloc (alloc [some value] .global ∅).2 p₀ 2 .global :=
  fun hDealloc => by
    exact not_isLive_alloc_end (h := ∅) [some value]
      ((canDealloc_iff.mp hDealloc).2.1 1 (by omega))

/-! Reasoning about new cells from outside the heap module: `alloc_eq` and `allocation_eq` expose
how `alloc` builds its result, and `RawPtr.loc_shift` says where a shifted pointer points. -/

/-- A shifted pointer moves within its allocation. -/
example (q : MutRawPtr Nat) : ((q.shift 1).shift 2).loc = q.loc.shift 3 := by
  simp [Loc.shift_shift]

/-- The second cell of a fresh allocation is reachable through a pointer shifted from its start,
and holds the second value. -/
example (h : Heap) (a b : Option Nat) :
    ∃ hValid : IsValid (h.alloc [a, b] .global).2 ((⟨freshLoc h⟩ : MutRawPtr Nat).shift 1),
      ((h.alloc [a, b] .global).2.read _ hValid).1 = b := by
  have hq : (⟨freshLoc h⟩ : MutRawPtr Nat).shift 1 = ⟨(freshLoc h).shift 1⟩ :=
    RawPtr.ext (by simp)
  have hCells : Subheap (cell ((⟨freshLoc h⟩ : MutRawPtr Nat).shift 1) b)
      (array (freshLoc h) [a, b]) := by
    have hCompatible := compatible_array_append (freshLoc h) [a] [b]
    rw [hq, show [a, b] = [a] ++ [b] from rfl, array_append]
    simpa using Subheap.union_right hCompatible
  have hSub : Subheap (cell ((⟨freshLoc h⟩ : MutRawPtr Nat).shift 1) b)
      (h.alloc [a, b] .global).2 := by
    rw [alloc_eq, allocation_eq]
    refine hCells.trans ((Subheap.union_left ?_).trans (Subheap.union_left ?_))
    · exact compatible_array_endMarker _ _ _
    · rw [← allocation_eq]
      exact compatible_freshLoc _ _ _
  exact ⟨hSub.isValid (isValid_cell _ b), read_of_subheap hSub _⟩

/-- Allocation frames the existing heap: a cell already there keeps its content. -/
example (h : Heap) (q : MutRawPtr Nat) (value : Option Nat) (hCell : Subheap (cell q value) h)
    (values : List (Option Nat)) :
    ∃ hValid : IsValid (h.alloc values .global).2 q,
      ((h.alloc values .global).2.read q hValid).1 = value := by
  have hSub : Subheap (cell q value) (h.alloc values .global).2 := by
    rw [alloc_eq]
    exact hCell.trans (Subheap.union_right (compatible_freshLoc _ _ _))
  exact ⟨hSub.isValid (isValid_cell q value), read_of_subheap hSub _⟩

/-- Writing initializes a cell: an uninitialized cell reads back the written value. -/
example (q : MutRawPtr Nat) (value : Nat) (hValid : IsValid (cell q none) q) :
    ∃ hValid' : IsValid ((cell q none).write q (some value) hValid).2 q,
      (((cell q none).write q (some value) hValid).2.read q hValid').1 = some value := by
  rw [write_cell]
  exact ⟨isValid_cell q _, by rw [read_cell]⟩

end Aeneas.Std.HeapTests
