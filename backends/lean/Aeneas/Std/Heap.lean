module

public import Aeneas.Std.Heap.Model

@[expose] public section

namespace Aeneas.Std

universe u

/-- The effect boundary uses the same block declarations as the heap operations.
`State.{0}` stores translated `Type` values with a representation in `Type 1`. -/
abbrev State := Heap Std.Block.{u}

namespace State

noncomputable abbrev empty : State.{u} := Heap.empty
abbrev Inv (s : State.{u}) := Heap.Inv s

noncomputable def newBlock (values : List ty) (ownAllocation : Bool) :=
  Heap.newBlock values ownAllocation

noncomputable def alloc (values : List ty) := newBlock values true
noncomputable def newExposure (values : List ty) := newBlock values false
noncomputable def allocUninitialized (ty : Type u) (count : Nat) :
    State.{u} → RawPtr ty → State.{u} → Prop :=
  Heap.alloc count
noncomputable def offset (p : RawPtr ty) (count : Int) := Heap.offset p count
noncomputable def read (p : RawPtr ty) := Heap.read p
noncomputable def write (p : RawPtr ty) (value : ty) := Heap.write p value
noncomputable def borrowRange (p : RawPtr ty) (count : Nat) :=
  Heap.borrowRange p count
noncomputable def endBorrowRange (p : RawPtr ty) (values : List ty) :=
  Heap.endBorrowRange p values
noncomputable def shareRange (p : RawPtr ty) (count : Nat) :=
  Heap.shareRange p count
noncomputable def endShareRange (p : RawPtr ty) (values : List ty) :=
  Heap.endShareRange p values
noncomputable def newSharedExposure (values : List ty) := Heap.newSharedExposure values
noncomputable def dealloc (p : RawPtr ty) (count : Nat) :=
  Heap.freeBlock p count true
noncomputable def removeExposure (p : RawPtr ty) (count : Nat) :=
  Heap.freeBlock p count false
noncomputable def endSharedExposure (p : RawPtr ty) (original : List ty) :=
  Heap.endSharedExposure p original

end State
end Aeneas.Std
