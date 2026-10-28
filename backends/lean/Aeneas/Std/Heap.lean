module

public import Aeneas.Std.Heap.Model
public import Aeneas.Std.Heap.Axioms.Representation

@[expose] public section

namespace Aeneas.Std

universe u

/-- Fixed abstract representation at the effect boundary; operations remain parametric.
`State.{0}` stores translated `Type` values with a representation in `Type 1`. -/
abbrev State := Heap layout.{u}.Repr

namespace State

noncomputable abbrev empty : State.{u} := Heap.empty
abbrev Inv (s : State.{u}) := Heap.Inv s

noncomputable def newBlock (values : List ty) (ownAllocation : Bool) :=
  Heap.newBlock layout values ownAllocation

noncomputable def alloc (values : List ty) := newBlock values true
noncomputable def newView (values : List ty) := newBlock values false
noncomputable def allocUninitialized (ty : Type u) (count : Nat) :
    State.{u} → RawPtr ty → State.{u} → Prop :=
  Heap.alloc layout count
noncomputable def add (p : RawPtr ty) (count : Nat) := Heap.add layout p count
noncomputable def read (p : RawPtr ty) := Heap.read layout p
noncomputable def write (p : RawPtr ty) (value : ty) := Heap.write layout p value
noncomputable def borrowRange (p : RawPtr ty) (count : Nat) :=
  Heap.borrowRange layout p count
noncomputable def endBorrowRange (p : RawPtr ty) (values : List ty) :=
  Heap.endBorrowRange layout p values
noncomputable def shareRange (p : RawPtr ty) (count : Nat) :=
  Heap.shareRange layout p count
noncomputable def endShareRange (p : RawPtr ty) (values : List ty) :=
  Heap.endShareRange layout p values
noncomputable def newSharedView (values : List ty) := Heap.newSharedView layout values
noncomputable def dealloc (p : RawPtr ty) (count : Nat) :=
  Heap.freeBlock layout p count true
noncomputable def removeView (p : RawPtr ty) (count : Nat) :=
  Heap.freeBlock layout p count false
noncomputable def endSharedView (p : RawPtr ty) (original : List ty) :=
  Heap.endSharedView layout p original

end State
end Aeneas.Std
