module

public import Aeneas.Std.Heap.Model

/-! Relational adapters for Rust's effect boundary. The heap itself is executable.
Encodings are nondeterministic witnesses justified by the explicit representation. -/

@[expose] public section

namespace Aeneas.Std

abbrev State := Heap

namespace State

abbrev empty := Heap.empty
abbrev Inv (s : State) : Prop := Heap.Inv s

def newBlock (repr : Repr ty) (values : List ty) (own : Bool)
    (s₀ : State) (p : RawPtr ty) (s₁ : State) : Prop :=
  ∃ data : List (Vector U8 repr.size),
    data.map repr.decode = values.map some ∧ Heap.newBlock repr data own s₀ = some (p, s₁)

def alloc (repr : Repr ty) (values : List ty) := newBlock repr values true
def newExposure (repr : Repr ty) (values : List ty) := newBlock repr values false

def allocUninitialized (repr : Repr ty) (count : Nat)
    (s₀ : State) (p : RawPtr ty) (s₁ : State) : Prop :=
  Heap.alloc repr count s₀ = some (p, s₁)

def offset (repr : Repr ty) (p : RawPtr ty) (count : Int)
    (s₀ : State) (result : RawPtr ty) (s₁ : State) : Prop :=
  Heap.offset repr p count s₀ = some result ∧ s₁ = s₀

def read (repr : Repr ty) (p : RawPtr ty)
    (s₀ : State) (value : ty) (s₁ : State) : Prop :=
  Heap.read repr p s₀ = some value ∧ s₁ = s₀

def readRange (repr : Repr ty) (p : RawPtr ty) (count : Nat)
    (s₀ : State) (values : List ty) (s₁ : State) : Prop :=
  Heap.readRange repr p count s₀ = some values ∧ s₁ = s₀

def write (repr : Repr ty) (p : RawPtr ty) (value : ty)
    (s₀ : State) (_ : Unit) (s₁ : State) : Prop :=
  ∃ data : Vector U8 repr.size, ∃ decoded : repr.decode data = some value,
    Heap.write repr p value data decoded s₀ = some s₁

/-- Rust's safe-borrow boundary reads the values before transferring their permissions. -/
def borrowRange (repr : Repr ty) (p : RawPtr ty) (count : Nat)
    (s₀ : State) (values : List ty) (s₁ : State) : Prop :=
  Heap.readRange repr p count s₀ = some values ∧ Heap.borrowRange repr p count s₀ = some s₁

def endBorrowRange (repr : Repr ty) (p : RawPtr ty) (values : List ty)
    (s₀ : State) (_ : Unit) (s₁ : State) : Prop :=
  ∃ data : List (Vector U8 repr.size),
    data.map repr.decode = values.map some ∧ Heap.endBorrowRange repr p data s₀ = some s₁

def shareRange (repr : Repr ty) (p : RawPtr ty) (count : Nat)
    (s₀ : State) (values : List ty) (s₁ : State) : Prop :=
  Heap.readRange repr p count s₀ = some values ∧ Heap.shareRange repr p count s₀ = some s₁

def endShareRange (repr : Repr ty) (p : RawPtr ty) (values : List ty)
    (s₀ : State) (_ : Unit) (s₁ : State) : Prop :=
  Heap.readRange repr p values.length s₀ = some values ∧
    Heap.endShareRange repr p values.length s₀ = some s₁

def newSharedExposure (repr : Repr ty) (values : List ty)
    (s₀ : State) (p : RawPtr ty) (s₁ : State) : Prop :=
  ∃ data : List (Vector U8 repr.size),
    data.map repr.decode = values.map some ∧ Heap.newSharedExposure repr data s₀ = some (p, s₁)

def dealloc (repr : Repr ty) (p : RawPtr ty) (count : Nat)
    (s₀ : State) (_ : Unit) (s₁ : State) : Prop :=
  Heap.freeBlock repr p count true s₀ = some s₁

def removeExposure (repr : Repr ty) (p : RawPtr ty) (count : Nat)
    (s₀ : State) (_ : Unit) (s₁ : State) : Prop :=
  Heap.freeBlock repr p count false s₀ = some s₁

def endSharedExposure (repr : Repr ty) (p : RawPtr ty) (values : List ty)
    (s₀ : State) (_ : Unit) (s₁ : State) : Prop :=
  Heap.readRange repr p values.length s₀ = some values ∧
    Heap.endSharedExposure repr p values.length s₀ = some s₁

end State
end Aeneas.Std
