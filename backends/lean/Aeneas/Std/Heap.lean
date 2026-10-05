module

public import Mathlib.Data.Finmap

public section

namespace Aeneas.Std

abbrev AllocId := Nat

abbrev Loc := AllocId × Nat

abbrev HeapCell := Σ α : Type, α

abbrev HeapImpl := Finmap fun _ : Loc => HeapCell

structure Heap where
  private mk ::
  private impl : HeapImpl

@[expose]
def Ref (_ : Type) := Loc

namespace Ref

instance instInhabited {α : Type} : Inhabited (Ref α) := ⟨((0 : AllocId), 0)⟩

instance instDecidableEq {α : Type} : DecidableEq (Ref α) :=
  inferInstanceAs (DecidableEq Loc)

@[expose]
def addr {α : Type} (r : Ref α) : Loc := r

@[expose]
def base {α : Type} (r : Ref α) : AllocId := r.addr.1

@[expose]
def offset {α : Type} (r : Ref α) : Nat := r.addr.2

@[expose]
def add {α : Type} (r : Ref α) (i : Nat) : Ref α := (r.base, r.offset + i)

end Ref

namespace Heap

private def lookup (h : Heap) (address : Loc) :
    Option HeapCell :=
  h.impl.lookup address

private def insert (h : Heap) (address : Loc)
    (cell : HeapCell) : Heap :=
  ⟨h.impl.insert address cell⟩

private def erase (h : Heap) (address : Loc) : Heap :=
  ⟨h.impl.erase address⟩

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

def singleton {α : Type} (r : Ref α) (value : α) : Heap :=
  ⟨Finmap.singleton r.addr ⟨α, value⟩⟩

/-- The definedness guard of operations on `r`: `h` holds a value of type `α` at `r`. -/
def contains {α : Type} (h : Heap) (r : Ref α) : Prop :=
  match h.lookup r.addr with
  | none => False
  | some ⟨β, _⟩ => β = α

@[expose]
def rangeHeap {α : Type} (r : Ref α) : List α → Heap
  | [] => empty
  | value :: rest => singleton r value ∪ rangeHeap (r.add 1) rest

/-- The next allocation identifier, past every one in use: allocation is deterministic. -/
def freshBase (h : Heap) : AllocId :=
  (h.keys.image Prod.fst).sup id + 1

def freshRef (α : Type) (h : Heap) : Ref α := (freshBase h, 0)

@[expose] def freshHeap {α : Type} (h : Heap) (values : List α) : Heap :=
  rangeHeap (freshRef α h) values ∪ h

/-- `h'` is `h` extended with cells that `h` does not own. -/
@[expose] def Sub (h h' : Heap) : Prop :=
  ∃ rest, Heap.compatible h rest ∧ h' = h ∪ rest

def read {α : Type} (r : Ref α) (h : Heap)
    (hContains : contains h r) : α :=
  match hlookup : h.lookup r.addr with
  | none => by simp [contains, hlookup] at hContains
  | some ⟨β, value⟩ => by
      have htype : β = α := by
        simpa [contains, hlookup] using hContains
      exact htype ▸ value

def update {α : Type} (r : Ref α) (value : α) (h : Heap)
    (_ : contains h r) : Heap :=
  h.insert r.addr ⟨α, value⟩

def free {α : Type} (r : Ref α) (h : Heap)
    (_ : contains h r) : Heap :=
  h.erase r.addr

end Heap

end Aeneas.Std
