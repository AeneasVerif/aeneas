module

public import Aeneas.Std.Heap.Model

/-! Joint placement/encoding relations for the checked Rust effect boundary.
Enabledness requires compatibility with the unknown implicit safe heap, not just `Inv`. -/

@[expose] public section

namespace Aeneas.Std

abbrev State := Heap

namespace State

abbrev empty := Heap.empty
abbrev Inv (s : State) : Prop := Heap.Inv s

/-- Exposure does not perform a typed write. Pointer metadata not supplied by
the value must already be justified by a readable explicit byte at this address. -/
def exposes (repr : Repr ty) (s : State) (address : Nat) (value : ty)
    (bytes : Vector Byte repr.size) : Prop :=
  repr.decode bytes = some value ∧
    ∀ i : Fin repr.size,
      (match bytes[i.val] with
      | .pointer p lane =>
          repr.Carries value p ∨
            ∃ id blk index depth,
              s.allocations id = some blk ∧ s.live blk = true ∧
              blk.bptr.val + index = address + i.val ∧
              blk.repr[index]? = some (.shared depth (.pointer p lane))
      | _ => True)

def exposesList (repr : Repr ty) (s : State) (address : Nat) :
    List ty → List (Vector Byte repr.size) → Prop
  | [], [] => True
  | value :: values, bytes :: data =>
      exposes repr s address value bytes ∧
        exposesList repr s (address + repr.size) values data
  | _, _ => False

def newBlock (repr : Repr ty) (values : List ty) (own : Bool)
    (s₀ : State) (p : RawPtr ty) (s₁ : State) : Prop :=
  ∃ data : List (Vector Byte repr.size), ∃ bptr root,
    (if own then repr.encodeList values data else exposesList repr s₀ bptr.val values data) ∧
    Heap.newBlock repr data own bptr root s₀ = some (p, s₁)

def alloc (repr : Repr ty) (values : List ty) := newBlock repr values true
def newExposure (repr : Repr ty) (values : List ty) := newBlock repr values false

def allocUninitialized (repr : Repr ty) (count : Nat)
    (s₀ : State) (p : RawPtr ty) (s₁ : State) : Prop :=
  ∃ bptr, Heap.alloc repr count bptr s₀ = some (p, s₁)

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
  ∃ data : Vector Byte repr.size, ∃ encoded : repr.encode value data,
    Heap.write repr p value data encoded s₀ = some s₁

/-- Until backward continuations track untouched representation, mutable safe
loans are restricted to representations admissible for their returned values.
Numerical reads across pointer lanes remain supported, but such loans fail. -/
def mutableValues (repr : Repr ty) (p : RawPtr ty) (values : List ty) (s : State) : Prop :=
    ∃ blk, s.allocations p.provenance = some blk ∧
      ∀ (i : Nat) (hi : i < values.length),
        ∃ bytes : Vector Byte repr.size,
        ∃ hb : p.offsetFrom blk.bptr + i * repr.size + repr.size ≤ blk.repr.length,
          Repr.readBytes repr.size
            (repr.select blk.bytes (p.offsetFrom blk.bptr + i * repr.size) hb) =
              some bytes ∧ repr.encode values[i] bytes

def borrowRange (repr : Repr ty) (p : RawPtr ty) (count : Nat)
    (s₀ : State) (values : List ty) (s₁ : State) : Prop :=
  Heap.readRange repr p count s₀ = some values ∧ mutableValues repr p values s₀ ∧
    Heap.borrowRange repr p count s₀ = some s₁

def endBorrowRange (repr : Repr ty) (p : RawPtr ty) (values : List ty)
    (s₀ : State) (_ : Unit) (s₁ : State) : Prop :=
  ∃ data : List (Vector Byte repr.size),
    repr.encodeList values data ∧ Heap.endBorrowRange repr p data s₀ = some s₁

def shareRange (repr : Repr ty) (p : RawPtr ty) (count : Nat)
    (s₀ : State) (values : List ty) (s₁ : State) : Prop :=
  Heap.readRange repr p count s₀ = some values ∧ Heap.shareRange repr p count s₀ = some s₁

def endShareRange (repr : Repr ty) (p : RawPtr ty) (values : List ty)
    (s₀ : State) (_ : Unit) (s₁ : State) : Prop :=
  Heap.readRange repr p values.length s₀ = some values ∧
    Heap.endShareRange repr p values.length s₀ = some s₁

def newSharedExposure (repr : Repr ty) (values : List ty)
    (s₀ : State) (p : RawPtr ty) (s₁ : State) : Prop :=
  ∃ data : List (Vector Byte repr.size), ∃ bptr root,
    exposesList repr s₀ bptr.val values data ∧
    Heap.newSharedExposure repr data bptr root s₀ = some (p, s₁)

def dealloc (repr : Repr ty) (p : RawPtr ty) (count : Nat)
    (s₀ : State) (_ : Unit) (s₁ : State) : Prop :=
  Heap.dealloc repr p count s₀ = some s₁

def returnOwned (repr : Repr ty) (p : RawPtr ty) (count : Nat)
    (s₀ : State) (_ : Unit) (s₁ : State) : Prop :=
  Heap.returnOwned repr p count s₀ = some s₁

def removeExposure (repr : Repr ty) (p : RawPtr ty) (count : Nat)
    (s₀ : State) (_ : Unit) (s₁ : State) : Prop :=
  Heap.endExposureAt repr p count 0 s₀ = some s₁

def endSharedExposure (repr : Repr ty) (p : RawPtr ty) (values : List ty)
    (s₀ : State) (_ : Unit) (s₁ : State) : Prop :=
  Heap.readRange repr p values.length s₀ = some values ∧
    Heap.endSharedExposure repr p values.length s₀ = some s₁

end State
end Aeneas.Std
