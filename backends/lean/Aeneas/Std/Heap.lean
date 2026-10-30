module

public import Lean

/-! The memory model for raw pointers, inspired by RefinedRust (Caesium), but with typed cells
instead of bytes.

A `Heap` is a fragment of the memory, made of two partial maps:
- `cells` maps each location (allocation id + offset) to a `Cell`, which holds a value together with
  its type (Caesium's `heap_cell`, without bytes);
- `allocs` maps each allocation id to its `Allocation` (Caesium's `allocation` + `alloc_alive`):
  owning this entry is the right to deallocate the block.

Fragments combine with `∪` when they are `Disjoint` (no location and no allocation id in common).
The whole memory is a `State`: a heap plus the counter `next` from which fresh allocation ids are
taken. Deallocation removes the entries of the block, and since `next` only grows, allocation ids
are never reused.

Supports interior pointers, stored pointers, provenance by allocation id, uninitialized cells.
Not supported: byte-level representation/type punning, pointer-integer casts, higher-order store,
the byte-level allocator API (`std::alloc::alloc`, `Layout`). -/

@[expose] public section

namespace Aeneas.Std

abbrev AllocId := Nat

inductive AllocKind where
  /-- Allocated by the global allocator -/
  | heap
  /-- A raw-pointer view of a place that Aeneas translates to a plain value.
  Such views cannot be deallocated through the allocator. -/
  | view
  deriving DecidableEq

/-- The address of a cell: an allocation id and an offset, counted in cells (not in bytes). -/
@[ext]
structure Loc where
  allocId : AllocId
  offset : Nat
  deriving DecidableEq, Inhabited

/-- The content of a memory cell. Every cell carries the type of its value. -/
inductive Cell : Type (v + 1) where
  /-- We own the cell; `none` means uninitialized -/
  | owned (ty : Type v) (value : Option ty)
  /-- The value was moved out by `borrow` (converting a raw pointer to a borrow): we hold the
  exclusive right to give it back with `endBorrow` -/
  | borrowed

/-- An allocation block. Owning it is the right to deallocate the block. -/
structure Allocation where
  /-- The allocation kind determines whether we're allowed to free the block through the allocator -/
  kind : AllocKind
  /-- The number of cells of the block -/
  len : Nat
  deriving DecidableEq

/-- A fragment of the memory. -/
@[ext]
structure Heap : Type (v + 1) where
  cells : Loc → Option Cell.{v}
  allocs : AllocId → Option Allocation

/-- The whole memory: the heap, together with the counter used to generate fresh allocation ids.
The counter is not part of the fragments: it can't be split. -/
structure State : Type (v + 1) where
  heap : Heap.{v}
  /-- The next fresh allocation id -/
  next : AllocId

/-! Three examples of how the memory model is used. In the comments, the heap after each line,
starting from the empty heap: `a ↦ kind[len]` is the `Allocation` of block `a`, and
`(a, i) ↦ cell` is the cell at offset `i` of block `a`.

**`Box` into and from raw pointers.** In Aeneas' model, `Box::new(0u32)` returns `0`, which gets
allocated in memory by `into_raw`. Rust's `Box::new` uses the global allocator, so the block has
kind `.heap`, and it can be freed by `from_raw`:
```rust
let p = Box::into_raw(Box::new(0u32));
// 0 ↦ heap[1], (0, 0) ↦ owned 0
let x = unsafe { *Box::from_raw(p) };
// The box returned by `from_raw` is dropped at the end of the statement, which frees the block.
// The model reads 0 and frees at once:
// (empty)
```
```lean
let p ← alloc.boxed.Box.into_raw 0#u32 -- State.alloc [0#u32]
let x ← alloc.boxed.Box.from_raw p     -- RawPtr.read p, then State.dealloc p 1
```

**Raw pointer to a place.** Aeneas translates the local `x` to a plain value, without an address.
Taking a raw pointer to it creates a *view*: a block of kind `.view`, holding a copy of `x`. When the
borrow of `x` ends, the back function of `from_mut` reads the value back and removes the view:
```rust
let mut x = 0u32;
let p = core::ptr::from_mut(&mut x);
// 0 ↦ view[1], (0, 0) ↦ owned 0
unsafe { *p = 1 };
// 0 ↦ view[1], (0, 0) ↦ owned 1
assert!(x == 1);
// The borrow of `x` ends before the assertion, so the view is removed:
// (empty)
```
```lean
let x := 0#u32
let (p, end_p) ← core.ptr.from_mut x -- State.newView [x]
MutRawPtr.write p 1#u32
let x ← end_p                        -- RawPtr.read p, then State.removeView p 1
massert (x = 1#u32)
```

**From a raw pointer to a borrow.** Converting a raw pointer to a borrow moves the value of the
cell out (`borrow`): the cell is `borrowed`, so that every access to it through a raw pointer fails
while the borrow is live. When the borrow ends, `endBorrow` gives the final value back:
```rust
let mut x = 0u32;
let p = core::ptr::from_mut(&mut x);
// 0 ↦ view[1], (0, 0) ↦ owned 0
unsafe { *p = 1 };
// 0 ↦ view[1], (0, 0) ↦ owned 1
let p1 = unsafe { &mut *p };
// 0 ↦ view[1], (0, 0) ↦ borrowed
*p1 = 2;
// The borrow `p1` ends here:
// 0 ↦ view[1], (0, 0) ↦ owned 2
assert!(x == 2);
// (empty)
```
```lean
let x := 0#u32
let (p, end_p) ← core.ptr.from_mut x -- State.newView [x]
MutRawPtr.write p 1#u32
let p1 ← RawPtr.borrow p             -- State.borrow p
let p1 := 2#u32
RawPtr.endBorrow p p1                -- State.endBorrow p p1
let x ← end_p                        -- RawPtr.read p, then State.removeView p 1
massert (x = 2#u32)
```
-/

/-
The operations, and how they change the memory. A cell given away by `borrow` is `borrowed` until
`endBorrow` gives it back, at the same address. `dealloc` frees a whole `.heap` block, and
`removeView` a whole `.view` block, provided that no cell of the block is borrowed.

| Operation    | Effect                                        | Used by                                       |
|--------------|-----------------------------------------------|-----------------------------------------------|
| `alloc`      | fresh id ↦ heap[n], cells ↦ owned             | `Box::into_raw`                               |
| `newView`    | fresh id ↦ view[n], cells ↦ owned             | `from_mut`, `as_ptr`, `as_mut_ptr`            |
| `dealloc`    | removes a heap block and its (owned) cells    | `Box::from_raw`                               |
| `removeView` | removes a view block and its (owned) cells    | end of `from_mut`, `as_ptr`, `as_mut_ptr`     |
| `borrow`     | owned → borrowed                              | `from_raw_parts`, `from_raw_parts_mut`        |
| `endBorrow`  | borrowed → owned                              | end of `from_raw_parts`, `from_raw_parts_mut` |
-/

namespace Heap

def empty : Heap := ⟨fun _ => none, fun _ => none⟩

instance instEmptyCollection : EmptyCollection Heap := ⟨empty⟩

/-- Combines two fragments. It is meaningful when they are `Disjoint`; otherwise the left one
wins. -/
def union (h₁ h₂ : Heap) : Heap :=
  ⟨fun l => (h₁.cells l).or (h₂.cells l), fun a => (h₁.allocs a).or (h₂.allocs a)⟩

instance instUnion : Union Heap := ⟨Heap.union⟩

/-- Replaces the cell at `l`. -/
def setCell (h : Heap) (l : Loc) (c : Cell) : Heap :=
  { h with cells := fun l' => if l' = l then some c else h.cells l' }

/-- Two fragments are disjoint if they have no location and no allocation id in common. -/
def Disjoint (h₁ h₂ : Heap) : Prop :=
  (∀ l, h₁.cells l = none ∨ h₂.cells l = none) ∧ (∀ a, h₁.allocs a = none ∨ h₂.allocs a = none)

end Heap

inductive Mutability where
| Mut | Const

/-- `T` is universe-polymorphic so that pointers to values in higher universes
(`dyn Trait`, functions returning `Result`) elaborate. Only the cells a pointer reads or writes
need to live in the universe of the heap. -/
@[ext]
structure RawPtr (T : Type u) (M : Mutability) where
  allocId : AllocId
  offset : Nat
  deriving DecidableEq, Inhabited

abbrev MutRawPtr (T : Type u) := RawPtr T .Mut
abbrev ConstRawPtr (T : Type u) := RawPtr T .Const

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

/-- The location a pointer points to. -/
def loc (q : RawPtr T M) : Loc := ⟨q.allocId, q.offset⟩

def shift (q : RawPtr T M) (i : Nat) : RawPtr T M :=
  ⟨q.allocId, q.offset + i⟩

end RawPtr

namespace State

def empty : State := ⟨∅, 0⟩

/-- The cell of `q`. -/
def cell (s : State.{v}) (q : RawPtr T M) : Option Cell.{v} := s.heap.cells q.loc

/-- Replaces the cell at `l`. -/
def setCell (s : State) (l : Loc) (c : Cell) : State :=
  ⟨s.heap.setCell l c, s.next⟩

/-- Creates a fresh block of kind `kind` holding `values`, at the next allocation id: fresh memory
is mutable in Rust. -/
def allocBlock (values : List α) (kind : AllocKind) (s : State) : MutRawPtr α × State :=
  (⟨s.next, 0⟩,
    ⟨⟨fun l => if l.allocId = s.next ∧ l.offset < values.length
               then some (.owned α values[l.offset]?) else s.heap.cells l,
      fun a => if a = s.next then some ⟨kind, values.length⟩ else s.heap.allocs a⟩,
     s.next + 1⟩)

/-- Removes the allocation entry of block `a` and its first `n` cells. The id `a` is never reused,
because `next` doesn't change. -/
def removeBlock (a : AllocId) (n : Nat) (s : State) : State :=
  ⟨⟨fun l => if l.allocId = a ∧ l.offset < n then none else s.heap.cells l,
    fun b => if b = a then none else s.heap.allocs b⟩, s.next⟩

/-- The cell of `q` is owned (initialized or not). -/
def IsLive (s : State.{v}) (q : RawPtr T M) : Prop :=
  ∃ (ty : Type v) (value : Option ty), s.cell q = some (.owned ty value)

/-- `q.shift count` stays in bounds (`add`): the memory owns every cell it steps over. -/
def InBounds (s : State.{v}) (q : RawPtr T M) (count : Nat) : Prop :=
  ∀ i < count, IsLive s (q.shift i)

/-! The operations, as relations `op s x s'` between the initial state `s`, the result `x` and the
final state `s'`: these are the arguments of `Result.guardedModify`. An operation is undefined
behaviour in the states where it has no successor. -/

/-- Creates a fresh block. Use `alloc` or `newView`; the lemmas are stated on `newBlock` and apply
to both. -/
def newBlock (values : List α) (kind : AllocKind) : State.{v} → MutRawPtr α → State.{v} → Prop :=
  fun s p s' => (p, s') = s.allocBlock values kind

/-- Allocates `values` with the global allocator (`Box::into_raw`). -/
abbrev alloc (values : List α) : State.{v} → MutRawPtr α → State.{v} → Prop :=
  newBlock values .heap

/-- Creates a raw-pointer view of a place that holds `values` (`from_mut`, `as_ptr`,
`as_mut_ptr`). -/
abbrev newView (values : List α) : State.{v} → MutRawPtr α → State.{v} → Prop :=
  newBlock values .view

/-- Shifts `q` by `count` cells (`add`), which must stay in bounds. -/
def add (q : RawPtr T M) (count : Nat) : State.{v} → RawPtr T M → State.{v} → Prop :=
  fun s r s' => s.InBounds q count ∧ r = q.shift count ∧ s' = s

/-- Reads the value of `q`: the cell must be owned and hold an initialized value of type `α`. -/
def read (q : RawPtr α M) : State.{v} → α → State.{v} → Prop :=
  fun s x s' => s.cell q = some (.owned α (some x)) ∧ s' = s

/-- Writes `value` at `q`: the cell must be owned, of type `α`, and may be uninitialized. -/
def write (q : RawPtr α M) (value : α) : State.{v} → Unit → State.{v} → Prop :=
  fun s _ s' => (∃ old, s.cell q = some (.owned α old)) ∧
    s' = s.setCell q.loc (.owned α (some value))

/-- Moves the value of `q` out into a borrow (`from_raw_parts`): the cell is `borrowed` until
`endBorrow`, so every access through a raw pointer fails meanwhile. -/
def borrow (q : RawPtr α M) : State.{v} → α → State.{v} → Prop :=
  fun s x s' => s.cell q = some (.owned α (some x)) ∧ s' = s.setCell q.loc .borrowed

/-- Ends the borrow of `q`, giving `value` back. -/
def endBorrow (q : RawPtr α M) (value : α) : State.{v} → Unit → State.{v} → Prop :=
  fun s _ s' => s.cell q = some .borrowed ∧ s' = s.setCell q.loc (.owned α (some value))

/-- The condition of `dealloc` (kind `.heap`) and `removeView` (kind `.view`): `q` starts a block
of kind `kind`, of exactly `n` cells, all owned (none of them is borrowed). So `dealloc` fails on a
view, and `removeView` fails on memory from the global allocator. Anything else is undefined
behaviour in Rust as well: a pointer into the middle of an allocation, the wrong size, or memory
already deallocated. See the safety section of
[`Allocator::deallocate`](https://doc.rust-lang.org/std/alloc/trait.Allocator.html#tymethod.deallocate) -/
def CanDealloc (s : State) (q : RawPtr α M) (n : Nat) (kind : AllocKind) : Prop :=
  q.offset = 0 ∧ s.heap.allocs q.allocId = some ⟨kind, n⟩ ∧ ∀ i < n, IsLive s (q.shift i)

/-- Frees the block of `q`, of `n` cells. Use `dealloc` or `removeView`; the lemmas are stated on
`freeBlock` and apply to both. -/
def freeBlock (q : RawPtr α M) (n : Nat) (kind : AllocKind) : State.{v} → Unit → State.{v} → Prop :=
  fun s _ s' => s.CanDealloc q n kind ∧ s' = s.removeBlock q.allocId n

/-- Frees memory of the global allocator (`Box::from_raw`). -/
abbrev dealloc (q : RawPtr α M) (n : Nat) : State.{v} → Unit → State.{v} → Prop :=
  freeBlock q n .heap

/-- Removes a raw-pointer view (the end of `from_mut`, `as_ptr`, `as_mut_ptr`). -/
abbrev removeView (q : RawPtr α M) (n : Nat) : State.{v} → Unit → State.{v} → Prop :=
  freeBlock q n .view

end State

end Aeneas.Std
