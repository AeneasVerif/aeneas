import Aeneas.SLPoC.Heap

/-!
# The Rust view of the heap

A translated Rust program manipulates *pointers*, not the allocation
identifiers of `Aeneas.SLPoC.Heap`.  This file introduces `Ptr α`, the pointer
to a value of type `α` such a program uses, together with the heap operations
it supports — allocation, read, write and deallocation — and the lemmas the
program logic of `Aeneas.SLPoC.ST` needs about them.

`Ptr α` is for now a definitional alias of `Ref α`, so a pointer *is* an
allocation identifier and every operation below is a renaming of its
counterpart in `Heap.lean`.  The point of the indirection is that the program
logic of `Aeneas.SLPoC.ST` is written against `Ptr` only: other Rust memory
notions (`Box`, `&mut`, …) can be added, and the representation of a pointer
refined, without touching it.
-/

namespace Aeneas.SLPoC

/-- A Rust pointer to a value of type `α`. -/
def Ptr (α : Type) := Ref α

/-- Pointers are inhabited, which is what makes the `unwrap`s of a translated
Rust program expressible as `Option.get!`. -/
instance instInhabitedPtr {α : Type} : Inhabited (Ptr α) :=
  inferInstanceAs (Inhabited (Ref α))

namespace Ptr

variable {α : Type}

/-! ## Operations -/

/-- The heap made of the single cell `p`, holding `value`. -/
def singleton (p : Ptr α) (value : α) : Heap :=
  _root_.Aeneas.SLPoC.singleton p value

/-- `p` points to no cell of `h`. -/
def unallocated (h : Heap) (p : Ptr α) : Prop :=
  _root_.Aeneas.SLPoC.unallocated h p

/-- `h'` is `h` extended with a cell holding `value`, freshly allocated at
`p`. -/
def fresh (h : Heap) (p : Ptr α) (value : α) (h' : Heap) : Prop :=
  _root_.Aeneas.SLPoC.fresh h p value h'

/-- `h` has a cell at `p`, and it holds a value of type `α`. -/
def contains (h : Heap) (p : Ptr α) : Prop :=
  _root_.Aeneas.SLPoC.contains h p

/-- Read the value `p` points at. -/
def read (p : Ptr α) (h : Heap) (hContains : contains h p) : α :=
  Heap.read p h hContains

/-- Write `value` through `p`. -/
def update (p : Ptr α) (value : α) (h : Heap)
    (hContains : contains h p) : Heap :=
  Heap.update p value h hContains

/-- Deallocate the cell `p` points at. -/
def free (p : Ptr α) (h : Heap) (hContains : contains h p) : Heap :=
  Heap.free p h hContains

/-! ## Allocation -/

/-- The pointer the next allocation returns.  Allocation is deterministic, so a
program can be run and not only related to its outcomes. -/
def freshPtr (α : Type) (h : Heap) : Ptr α :=
  _root_.Aeneas.SLPoC.freshRef α h

/-- The heap `freshPtr` allocates into. -/
def freshHeap {α : Type} (h : Heap) (value : α) : Heap :=
  _root_.Aeneas.SLPoC.freshHeap h value

theorem fresh_freshPtr (value : α) (h : Heap) :
    fresh h (freshPtr α h) value (freshHeap h value) :=
  _root_.Aeneas.SLPoC.fresh_freshRef value h

theorem exists_fresh (value : α) (h : Heap) :
    ∃ p h', fresh h p value h' :=
  _root_.Aeneas.SLPoC.exists_fresh value h

/-! ## How the operations interact with the union of two heaps

These are the lemmas that make the frame rule provable: an operation performed
on a sub-heap can equally be performed on the whole heap, and leaves the other
part of it untouched. -/

theorem contains_union_left {h₁ h₂ : Heap} {p : Ptr α}
    (hContains : contains h₁ p) : contains (h₁ ∪ h₂) p :=
  _root_.Aeneas.SLPoC.contains_union_left hContains

/-- A heap that extends the cell `p` contains it: this is what an affine
points-to assertion gives, the cells it does not describe being unconstrained. -/
theorem contains_of_sub {p : Ptr α} {value : α} {h : Heap}
    (hSub : Heap.Sub (singleton p value) h) : contains h p := by
  obtain ⟨rest, _, rfl⟩ := hSub
  exact contains_union_left (contains_singleton p value)

/-- Two disjoint heaps cannot both own the cell `p`. -/
theorem disjoint_contains_false {h₁ h₂ : Heap} {p : Ptr α}
    (hDisjoint : Finmap.Disjoint h₁ h₂) (hContains₁ : contains h₁ p)
    (hContains₂ : contains h₂ p) : False :=
  _root_.Aeneas.SLPoC.disjoint_contains_false hDisjoint hContains₁ hContains₂

theorem read_union_left {h₁ h₂ : Heap} {p : Ptr α}
    (hContains : contains h₁ p) :
    read p (h₁ ∪ h₂) (contains_union_left hContains) =
      read p h₁ hContains :=
  _root_.Aeneas.SLPoC.read_union_left hContains

theorem update_union_left {h₁ h₂ : Heap} (p : Ptr α) (value : α)
    (hContains : contains h₁ p) :
    update p value (h₁ ∪ h₂) (contains_union_left hContains) =
      update p value h₁ hContains ∪ h₂ :=
  _root_.Aeneas.SLPoC.update_union_left p value hContains

theorem free_union_left {h₁ h₂ : Heap} (p : Ptr α)
    (hDisjoint : Finmap.Disjoint h₁ h₂) (hContains : contains h₁ p) :
    free p (h₁ ∪ h₂) (contains_union_left hContains) =
      free p h₁ hContains ∪ h₂ :=
  _root_.Aeneas.SLPoC.free_union_left p hDisjoint hContains

theorem fresh_frame {p : Ptr α} {value : α} {h₁ h₂ h : Heap}
    (hDisjoint : Finmap.Disjoint h₁ h₂)
    (hFresh : fresh (h₁ ∪ h₂) p value h) :
    ∃ h₁',
      fresh h₁ p value h₁' ∧
      Finmap.Disjoint h₁' h₂ ∧
      h = h₁' ∪ h₂ :=
  _root_.Aeneas.SLPoC.fresh_frame hDisjoint hFresh

theorem disjoint_update_left {p : Ptr α} {value : α} {h₁ h₂ : Heap}
    (hDisjoint : Finmap.Disjoint h₁ h₂) (hContains : contains h₁ p) :
    Finmap.Disjoint (update p value h₁ hContains) h₂ :=
  _root_.Aeneas.SLPoC.disjoint_update_left hDisjoint hContains

theorem disjoint_free_left {p : Ptr α} {h₁ h₂ : Heap}
    (hDisjoint : Finmap.Disjoint h₁ h₂) (hContains : contains h₁ p) :
    Finmap.Disjoint (free p h₁ hContains) h₂ :=
  _root_.Aeneas.SLPoC.disjoint_free_left hDisjoint hContains

/-! ## The operations on the heap of a single cell

These describe the effect of each operation on exactly the resources its
specification owns, which is what the specifications in `ST.lean` are proved
from. -/

theorem fresh_empty_eq_singleton {p : Ptr α} {value : α} {h : Heap}
    (hFresh : fresh empty p value h) : h = singleton p value :=
  _root_.Aeneas.SLPoC.fresh_empty_eq_singleton hFresh

theorem fresh_eq_singleton_union {p : Ptr α} {value : α} {h h' : Heap}
    (hFresh : fresh h p value h') :
    Finmap.Disjoint (singleton p value) h ∧ h' = singleton p value ∪ h := by
  have hUnion : empty ∪ h = h := by simp [empty]
  have hDisjointEmpty : Finmap.Disjoint empty h := Finmap.disjoint_empty h
  have hFreshUnion : fresh (empty ∪ h) p value h' := by rw [hUnion]; exact hFresh
  obtain ⟨h₁, hFresh₁, hDisjoint, rfl⟩ := fresh_frame hDisjointEmpty hFreshUnion
  obtain rfl := fresh_empty_eq_singleton hFresh₁
  exact ⟨hDisjoint, rfl⟩

theorem contains_singleton (p : Ptr α) (value : α) :
    contains (singleton p value) p :=
  _root_.Aeneas.SLPoC.contains_singleton p value

/-- Two cells at different pointers are disjoint. -/
theorem disjoint_singleton {p q : Ptr α} {value₁ value₂ : α} (hNe : p ≠ q) :
    Finmap.Disjoint (singleton p value₁) (singleton q value₂) :=
  _root_.Aeneas.SLPoC.disjoint_singleton hNe

theorem read_singleton (p : Ptr α) (value : α)
    (hContains : contains (singleton p value) p) :
    read p (singleton p value) hContains = value :=
  _root_.Aeneas.SLPoC.read_singleton p value hContains

theorem update_singleton (p : Ptr α) (oldValue newValue : α)
    (hContains : contains (singleton p oldValue) p) :
    update p newValue (singleton p oldValue) hContains =
      singleton p newValue :=
  _root_.Aeneas.SLPoC.update_singleton p oldValue newValue hContains

theorem free_singleton (p : Ptr α) (value : α)
    (hContains : contains (singleton p value) p) :
    free p (singleton p value) hContains = empty :=
  _root_.Aeneas.SLPoC.free_singleton p value hContains

end Ptr

end Aeneas.SLPoC
