module

public import Mathlib.Data.Finmap

/-! Block-based heap: finite map from (allocation id, offset) to typed cells `Σ α, α` or dead slots.
Supports interior pointers, stored pointers, provenance by allocation id. Freed slots and the end
marker of each allocation stay in the map as dead slots, so allocation ids are never reused. Not
supported: uninitialized memory, byte-level representation/type punning, pointer-integer casts,
allocation bounds (interior free undetected), higher-order store, permissions. -/

public section

namespace Aeneas.Std

abbrev AllocId := Nat

abbrev Loc := AllocId × Nat

abbrev HeapCell := Σ α : Type, α

/-- A slot is live (`some cell`) or dead (`none`): freed, or the end marker of an allocation.
Dead slots are never readable, but keep their allocation id reserved. -/
abbrev HeapImpl := Finmap fun _ : Loc => Option HeapCell

structure Heap where
  private mk ::
  private impl : HeapImpl

@[expose]
def Loc.add (l : Loc) (i : Nat) : Loc := (l.1, l.2 + i)

namespace Heap

/-- The live cell at `address`; `none` if the slot is missing or dead. -/
private def lookup (h : Heap) (address : Loc) :
    Option HeapCell :=
  (h.impl.lookup address).join

private def insert (h : Heap) (address : Loc)
    (cell : Option HeapCell) : Heap :=
  ⟨h.impl.insert address cell⟩

private def keys (h : Heap) :=
  h.impl.keys

def empty : Heap := ⟨∅⟩

instance instEmptyCollection : EmptyCollection Heap := ⟨empty⟩

def union (h₁ h₂ : Heap) : Heap := ⟨h₁.impl ∪ h₂.impl⟩

instance instUnion : Union Heap := ⟨Heap.union⟩

def mem (address : Loc) (h : Heap) : Prop :=
  address ∈ h.impl

instance instMembership : Membership Loc Heap :=
  ⟨fun h address => Heap.mem address h⟩

def compatible (h₁ h₂ : Heap) : Prop :=
  Finmap.Disjoint h₁.impl h₂.impl

def singleton {α : Type} (l : Loc) (value : α) : Heap :=
  ⟨Finmap.singleton l (some ⟨α, value⟩)⟩

/-- A dead slot at `l`. -/
def endMarker (l : Loc) : Heap := ⟨Finmap.singleton l none⟩

/-- The definedness guard of operations on `l`: `h` holds a value of type `α` at `l`. -/
def contains (h : Heap) (α : Type) (l : Loc) : Prop :=
  match h.lookup l with
  | none => False
  | some ⟨β, _⟩ => β = α

@[expose]
def rangeHeap {α : Type} (l : Loc) : List α → Heap
  | [] => empty
  | value :: rest => singleton l value ∪ rangeHeap (l.add 1) rest

/-- `values` stored from `l` on, followed by a dead end marker: it reserves the allocation id even
when `values` is empty. -/
@[expose] def allocation {α : Type} (l : Loc) (values : List α) : Heap :=
  rangeHeap l values ∪ endMarker (l.add values.length)

/-- The next allocation identifier, past every one in the heap: allocation is deterministic. Since
freed slots and end markers stay in the heap as dead slots, an identifier is never handed out
twice. -/
def freshBase (h : Heap) : AllocId :=
  (h.keys.image Prod.fst).sup id + 1

@[expose] def freshLoc (h : Heap) : Loc := (freshBase h, 0)

@[expose] def freshHeap {α : Type} (h : Heap) (values : List α) : Heap :=
  allocation (freshLoc h) values ∪ h

/-- `h'` is `h` extended with cells that `h` does not own. -/
@[expose] def Sub (h h' : Heap) : Prop :=
  ∃ rest, Heap.compatible h rest ∧ h' = h ∪ rest

def read {α : Type} (l : Loc) (h : Heap)
    (hContains : contains h α l) : α :=
  match hlookup : h.lookup l with
  | none => by simp [contains, hlookup] at hContains
  | some ⟨β, value⟩ => by
      have htype : β = α := by
        simpa [contains, hlookup] using hContains
      exact htype ▸ value

def update {α : Type} (l : Loc) (value : α) (h : Heap)
    (_ : contains h α l) : Heap :=
  h.insert l (some ⟨α, value⟩)

/-- Kills the slot at `l`: it stays in the heap as a dead slot. -/
def free {α : Type} (l : Loc) (h : Heap)
    (_ : contains h α l) : Heap :=
  h.insert l none

end Heap

end Aeneas.Std
