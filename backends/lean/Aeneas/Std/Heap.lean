module

public import Mathlib.Data.Finmap

/-! Block-based heap: finite map from (allocation id, offset) to typed cells `Σ α, α` or dead slots.
Supports interior pointers, stored pointers, provenance by allocation id. Deallocated slots and the
end marker of each allocation stay in the map as dead slots, so allocation ids are never reused. The
end marker also records whether the allocation comes from the global allocator
(`Alloc/Alloc.lean`): only those can be deallocated, and only whole. Not supported: uninitialized
memory, byte-level representation/type punning, pointer-integer casts, higher-order store,
permissions, the byte-level allocator API (`std::alloc::alloc`, `Layout`). -/

public section

namespace Aeneas.Std

abbrev AllocId := Nat

/-- A heap location: an allocation id, and a slot offset into that allocation. A pair rather than a
structure: tests evaluate concrete heaps, and `Prod`'s decidable equality reduces cheaply there. -/
abbrev Loc := AllocId × Nat

abbrev Loc.allocId (l : Loc) : AllocId := l.1

abbrev Loc.offset (l : Loc) : Nat := l.2

abbrev HeapCell := Σ α : Type, α

/-- A heap slot: a value, or a dead slot that keeps its allocation id reserved. -/
inductive Slot where
  | live (cell : HeapCell)
  /-- A dead slot. At the end of an allocation, `owned` says whether it comes from the global
  allocator, so that it may be deallocated. -/
  | dead (owned : Bool)

/-! Why the dead slot and its flag. From
```rust
pub fn boxed() -> u32 {
    let p = Box::into_raw(Box::new(1u32));
    unsafe { *Box::from_raw(p) }
}

pub fn borrowed() -> u32 {
    let mut x = 1u32;
    let p = core::ptr::from_mut(&mut x);
    unsafe { *Box::from_raw(p) } // UB: frees the local `x`
}
```
Aeneas extracts
```lean
def boxed : Result Std.U32 := do
  let p ← alloc.boxed.Box.into_raw 1#u32
  alloc.boxed.Box.from_raw p

def borrowed : Result Std.U32 := do
  let (p, _) ← core.ptr.from_mut 1#u32
  alloc.boxed.Box.from_raw p
```
Both `into_raw` and `from_mut` create an allocation holding `1` at offset `0`, followed by a dead
slot. The dead slot keeps the allocation id reserved, even once the value is freed or when there is
no value at all, so a pointer into this allocation never reaches a later one. Its flag tells the two
programs apart: `into_raw` allocates with `Global.allocate`, which writes `dead true`, and
`from_mut` writes `dead false`, since `p` only borrows `x`. `from_raw` frees with
`Global.deallocate`, which requires `dead true` after the value and turns it into `dead false`:
`boxed` runs, while `borrowed`, or freeing `p` twice, is rejected. -/

def Slot.cell? : Slot → Option HeapCell
  | .live cell => some cell
  | .dead _ => none

abbrev HeapImpl := Finmap fun _ : Loc => Slot

structure Heap where
  private mk ::
  private impl : HeapImpl

@[expose]
def Loc.add (l : Loc) (i : Nat) : Loc := (l.allocId, l.offset + i)

inductive Mutability where
| Mut | Const

/-- A Rust raw pointer: a heap location. `T` is a phantom parameter, universe-polymorphic like the
    other type parameters (only the heap cells a pointer reads or writes need to live in `Type`).
    A structure rather than `Loc` itself, so that `T` and `M` stay part of the type. The heap
    operations that read or write a typed cell take a pointer: its `T` is the cell's type. -/
@[ext]
structure RawPtr (T : Type _) (M : Mutability) where
  addr : Loc
  deriving Inhabited, DecidableEq

abbrev MutRawPtr (T : Type _) := RawPtr T .Mut
abbrev ConstRawPtr (T : Type _) := RawPtr T .Const

open Lean PrettyPrinter Delaborator SubExpr in
@[app_delab RawPtr]
meta def delabRawPtr : Delab := do
  let e ← getExpr
  guard (e.isAppOfArity ``RawPtr 2)
  let name ← match e.appArg! with
    | .const ``Mutability.Mut _ => pure ``MutRawPtr
    | .const ``Mutability.Const _ => pure ``ConstRawPtr
    | _ => failure
  let t ← withNaryArg 0 delab
  `($(mkIdent (← unresolveNameGlobal name)) $t)

namespace RawPtr

/-- `q` moved `i` slots forward, for specifications. Programs use `add`. -/
@[expose] def shift (q : RawPtr T M) (i : Nat) : RawPtr T M :=
  ⟨q.addr.add i⟩

end RawPtr

namespace Heap

/-- The live cell at `address`; `none` if the slot is missing or dead. -/
private def lookup (h : Heap) (address : Loc) :
    Option HeapCell :=
  (h.impl.lookup address).bind Slot.cell?

private def insert (h : Heap) (address : Loc)
    (cell : Slot) : Heap :=
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

def singleton (q : RawPtr α M) (value : α) : Heap :=
  ⟨Finmap.singleton q.addr (.live ⟨α, value⟩)⟩

/-- The end marker of an allocation at `l`: `owned` if the allocation may be deallocated. -/
def endMarker (l : Loc) (owned : Bool) : Heap :=
  ⟨Finmap.singleton l (.dead owned)⟩

/-- The definedness guard of operations through `q`: `h` holds a value of `q`'s type at `q`. -/
def contains (h : Heap) (q : RawPtr α M) : Prop :=
  match h.lookup q.addr with
  | none => False
  | some ⟨β, _⟩ => β = α

/-- The slot at `l` holds a value, of any type. -/
def isLive (h : Heap) (l : Loc) : Prop :=
  (h.lookup l).isSome

/-- The slot at `l` is the end marker of an allocation that may be deallocated. -/
def isOwnedEnd (h : Heap) (l : Loc) : Prop :=
  h.impl.lookup l = some (.dead true)

/-- `values` stored from `l` on. The cells are written through a `MutRawPtr`; any mutability gives
the same heap. -/
@[expose]
def rangeHeap (l : Loc) : List α → Heap
  | [] => empty
  | value :: rest => singleton (⟨l⟩ : MutRawPtr α) value ∪ rangeHeap (l.add 1) rest

/-- `values` stored from `l` on, followed by a dead end marker: it reserves the allocation id even
when `values` is empty. -/
@[expose] def allocation (l : Loc) (values : List α) (owned : Bool) : Heap :=
  rangeHeap l values ∪ endMarker (l.add values.length) owned

/-- The next allocation identifier, past every one in the heap: allocation is deterministic. Since
freed slots and end markers stay in the heap as dead slots, an identifier is never handed out
twice. -/
def freshBase (h : Heap) : AllocId :=
  (h.keys.image Loc.allocId).sup id + 1

@[expose] def freshLoc (h : Heap) : Loc := (freshBase h, 0)

@[expose] def freshHeap (h : Heap) (values : List α) (owned : Bool) : Heap :=
  allocation (freshLoc h) values owned ∪ h

/-- `h'` is `h` extended with cells that `h` does not own. -/
@[expose] def Sub (h h' : Heap) : Prop :=
  ∃ rest, Heap.compatible h rest ∧ h' = h ∪ rest

def read (h : Heap) (q : RawPtr α M)
    (hContains : contains h q) : α :=
  match hlookup : h.lookup q.addr with
  | none => by simp [contains, hlookup] at hContains
  | some ⟨β, value⟩ => by
      have htype : β = α := by
        simpa [contains, hlookup] using hContains
      exact htype ▸ value

def update (h : Heap) (q : RawPtr α M) (value : α)
    (_ : contains h q) : Heap :=
  h.insert q.addr (.live ⟨α, value⟩)

/-- The guard of `dealloc l n`: `l` starts an owned allocation of exactly `n` live slots. Anything
else is undefined behaviour in Rust: memory that the global allocator did not return (e.g. a local
behind a reference), a pointer into the middle of an allocation, the wrong size, or memory already
deallocated. See the safety section of
[`GlobalAlloc::dealloc`](https://doc.rust-lang.org/std/alloc/trait.GlobalAlloc.html#tymethod.dealloc).
-/
@[expose] def canDealloc (h : Heap) (l : Loc) (n : Nat) : Prop :=
  l.offset = 0 ∧ (∀ i < n, isLive h (l.add i)) ∧ isOwnedEnd h (l.add n)

/-- `n` dead slots from `l` on, none of them owned. -/
def deadRange (l : Loc) : Nat → Heap
  | 0 => empty
  | n + 1 => ⟨Finmap.singleton l (.dead false)⟩ ∪ deadRange (l.add 1) n

/-- Deallocates the `n` slots at `l` and the end marker after them. They stay in the heap as dead
slots: the allocation id stays reserved, and the allocation cannot be deallocated again. -/
def dealloc (h : Heap) (l : Loc) (n : Nat) (_ : canDealloc h l n) : Heap :=
  deadRange l (n + 1) ∪ h

end Heap

end Aeneas.Std
