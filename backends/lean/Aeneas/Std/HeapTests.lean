module
import Aeneas.Std.HeapLemmas

/-! Heap tests: allocation ids are never reused, and `dealloc` only accepts a whole owned
allocation, once. -/

namespace Aeneas.Std.HeapTests

open Heap

/-- A fresh owned allocation can be deallocated, but only once. -/
example (value : Nat) :
    ∃ hDealloc : canDealloc (freshHeap ∅ [value] true) (freshLoc ∅) 1,
      ¬ canDealloc ((freshHeap ∅ [value] true).dealloc (freshLoc ∅) 1 hDealloc) (freshLoc ∅) 1 :=
  ⟨⟨rfl, fun _ hi => isLive_freshHeap hi,
    (isOwnedEnd_freshHeap_end_iff ∅ [value] true).mpr rfl⟩,
   fun hAgain => not_isOwnedEnd_dealloc _ hAgain.2.2⟩

/-- A two-slot allocation is deallocated whole. -/
example (a b : Nat) : canDealloc (freshHeap ∅ [a, b] true) (freshLoc ∅) 2 :=
  ⟨rfl, fun _ hi => isLive_freshHeap hi,
    (isOwnedEnd_freshHeap_end_iff ∅ [a, b] true).mpr rfl⟩

/-- An empty allocation can also be deallocated only once. -/
example :
    ∃ hDealloc : canDealloc (freshHeap ∅ ([] : List Nat) true) (freshLoc ∅) 0,
      ¬ canDealloc ((freshHeap ∅ ([] : List Nat) true).dealloc (freshLoc ∅) 0 hDealloc)
        (freshLoc ∅) 0 :=
  ⟨⟨rfl, fun _ hi => absurd hi (Nat.not_lt_zero _),
    (isOwnedEnd_freshHeap_end_iff ∅ ([] : List Nat) true).mpr rfl⟩,
   fun hAgain => not_isOwnedEnd_dealloc _ hAgain.2.2⟩

/-- Allocating after a deallocation gets a new id, and the deallocated slot stays dead. -/
example {α : Type} (h : Heap) (l : Loc) (hDealloc : canDealloc h l 1) (value : α) :
    (freshLoc (h.dealloc l 1 hDealloc)).allocId ≠ l.allocId ∧
      ¬ isLive (freshHeap (h.dealloc l 1 hDealloc) [value] false) l :=
  ⟨fun hEq => not_mem_freshBase hEq.symm (mem_dealloc hDealloc (Nat.zero_le 1)),
    fun hLive => not_isLive_dealloc hDealloc (Nat.zero_le 1)
      ((isLive_freshHeap_of_mem (mem_dealloc hDealloc (Nat.zero_le 1))).mp hLive)⟩

/-- An empty allocation reserves its id, and its pointer stays dead after the next allocation. -/
example {α β : Type} (h : Heap) (value : β) :
    (freshLoc (freshHeap h ([] : List α) false)).allocId ≠ (freshLoc h).allocId ∧
      ¬ isLive (freshHeap (freshHeap h ([] : List α) false) [value] false) (freshLoc h) :=
  ⟨fun hEq => not_mem_freshBase hEq.symm (mem_freshHeap_end (owned := false) h ([] : List α)),
    fun hLive => not_isLive_freshHeap_end (owned := false) h ([] : List α)
      ((isLive_freshHeap_of_mem (mem_freshHeap_end _ _)).mp hLive)⟩

/-- An allocation that is not owned (e.g. a copy behind a reference) cannot be deallocated. -/
example (value : Nat) : ¬ canDealloc (freshHeap ∅ [value] false) (freshLoc ∅) 1 :=
  fun hDealloc => by
    simpa using (isOwnedEnd_freshHeap_end_iff ∅ [value] false).mp hDealloc.2.2

/-- An interior pointer cannot be deallocated. -/
example (a b : Nat) : ¬ canDealloc (freshHeap ∅ [a, b] true) ((freshLoc ∅).add 1) 1 :=
  fun hDealloc => by simpa using hDealloc.1

/-- A size smaller than the allocation's is rejected. -/
example (a b : Nat) : ¬ canDealloc (freshHeap ∅ [a, b] true) (freshLoc ∅) 1 :=
  fun hDealloc =>
    not_isLive_of_isOwnedEnd hDealloc.2.2 (isLive_freshHeap (i := 1) (by simp))

/-- A size larger than the allocation's is rejected. -/
example (value : Nat) : ¬ canDealloc (freshHeap ∅ [value] true) (freshLoc ∅) 2 :=
  fun hDealloc => by
    exact not_isLive_freshHeap_end (h := ∅) [value] (hDealloc.2.1 1 (by omega))

end Aeneas.Std.HeapTests
