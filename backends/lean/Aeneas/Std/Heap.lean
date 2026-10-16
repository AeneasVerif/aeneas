module

public import Mathlib.Data.Finmap

/-! Block-based heap: finite map from (allocation id, offset) to typed cells `Σ α, Option α`: a
cell holds a value of type `α`, or is uninitialized (`none`).
Supports interior pointers, stored pointers, uninitialized memory, provenance by allocation id.
Freed slots stay in the map so allocation ids are never reused. The end of
an allocation also records its `AllocKind`: whether it comes from the global allocator or is a
raw-pointer view. Each kind is deallocated only its own way, and only whole, otherwise UB.
The byte representation of integers, `bool` and arrays of them (byte cells) is described by
`Pointee` (see `Core/Ptr.lean`): a value is stored in several cells, and memory can be read at
another type with the same cells. Allocation ids tell the alignment of the allocations
(`freshAllocId`).
Not supported: byte layouts of structures and enums, the bytes of pointers,
pointer-integer casts, higher-order store, permissions, the byte-level allocator API
(`std::alloc::alloc`, `Layout`). -/

public section

namespace Aeneas.Std

abbrev AllocId := Nat

@[ext] structure Loc where
  allocId : AllocId
  offset : Nat
  deriving DecidableEq, Inhabited

private abbrev HeapCell := Σ α : Type, Option α

inductive AllocKind where
  /-- Allocated by the global allocator -/
  | global
  /-- A raw-pointer view of a place that Aeneas translates to a plain value -/
  | view
  deriving DecidableEq

private inductive Slot where
  | live (cell : HeapCell)
  -- one past the last value, with the kind of the allocation
  | endMarker (kind : AllocKind)
  | freed
  -- the value is held by a live borrow
  | borrowed

private def Slot.cell? : Slot → Option HeapCell
  | .live cell => some cell
  | _ => none

private abbrev HeapImpl := Finmap fun _ : Loc => Slot

structure Heap where
  private mk ::
  private impl : HeapImpl

/-! Two examples of how the slots in the Heap work. In the comments, the heap after each line,
starting from the empty heap; `a ↦ [ ... ]` is the allocation `a` with the slots at each offset.
```rust
pub fn boxed() -> u32 {
    // In Aeneas' model, `Box::new(1u32)` returns `1`, which gets allocated in memory
    // in `into_raw` by using the global allocator (because Rust's `Box::new` uses it),
    // thus the allocation is recorded in the Heap with marker `endMarker .global`.
    let p = Box::into_raw(Box::new(1u32));
    // 0 ↦ [ live 1 ; endMarker .global ]
    unsafe { *Box::from_raw(p) }
    // `from_raw` turns `p` into a new `Box` whose lifetime ends at the end of this statement,
    // so it is freed. Rust only lets a program free memory allocated by the global allocator,
    // which is what `endMarker .global` records. The model reads 1 and frees at once:
    // 0 ↦ [ freed ; freed ]
}

pub fn borrowed() -> u32 {
    let mut x = 1u32;
    let p = core::ptr::from_mut(&mut x);
    // 0 ↦ [ live 1 ; endMarker .view ]
    // `p` points to the local `x`, which the global allocator did not hand out,
    // so the marker is `endMarker .view`.
    unsafe { *Box::from_raw(p) }
    // `from_raw` turns `p` into a `Box`. Its lifetime ends at the end of this statement, so it is
    // freed, but this is UB because Rust only lets a program free memory that the
    // global allocator handed out. The `endMarker` helps us distinguish between the two examples.
}
```
See the safety section of
[`GlobalAlloc::dealloc`](https://doc.rust-lang.org/std/alloc/trait.GlobalAlloc.html#tymethod.dealloc).
-/

/-
The operations, and how they move slots between `live`, `borrowed` and `freed`. `freed` is final:
no operation leaves it, so deallocated memory can never be used again. `borrowed` always returns
to `live`, at the same address. An allocation is one `live` slot per cell (`live*`), initialized
or not, then an `endMarker` with its kind; `dealloc` frees all of it, end marker included, and
only for that kind. `write` initializes a live cell; reading an uninitialized cell is UB.

| Operation             | Allocation                          | Used by                                       |
|-----------------------|-------------------------------------|-----------------------------------------------|
| `alloc _ .global`     | fresh id → live*, endMarker .global | `Box::into_raw`, `Global::allocate`           |
| `alloc _ .view`       | fresh id → live*, endMarker .view   | `from_mut`, `as_ptr`, `as_mut_ptr`            |
| `dealloc _ _ .global` | live*, endMarker .global → freed*   | `Box::from_raw`, `Global::deallocate`         |
| `dealloc _ _ .view`   | live*, endMarker .view → freed*     | end of `from_mut`, `as_ptr`, `as_mut_ptr`     |
| `borrow`              | live → borrowed                     | `from_raw_parts`, `from_raw_parts_mut`        |
| `endBorrow`           | borrowed → live                     | end of `from_raw_parts`, `from_raw_parts_mut` |
-/

def Loc.shift (l : Loc) (i : Nat) : Loc := ⟨l.allocId, l.offset + i⟩

inductive Mutability where
| Mut | Const

/-- `T` is universe-polymorphic so that pointers to values in higher universes
(`dyn Trait`, functions returning `Result`) elaborate. Only the cells a pointer reads or writes
need to live in `Type`. -/
@[ext]
structure RawPtr (T : Type u) (M : Mutability) where
  loc : Loc
  deriving Inhabited

instance : DecidableEq (RawPtr T M) := fun q r =>
  decidable_of_iff (q.loc = r.loc) ⟨RawPtr.ext, congrArg RawPtr.loc⟩

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

/-- `q` moved `i` cells forward. Pointer arithmetic counts values (`RawPtr.shift`, which moves by
the number of cells of the pointee): this is for the cells themselves. -/
def shiftCells (q : RawPtr T M) (i : Nat) : RawPtr T M :=
  ⟨q.loc.shift i⟩

end RawPtr

namespace Heap

private def lookup (h : Heap) (l : Loc) : Option HeapCell :=
  (h.impl.lookup l).bind Slot.cell?

private def insert (h : Heap) (l : Loc) (slot : Slot) : Heap :=
  ⟨h.impl.insert l slot⟩

private def keys (h : Heap) := h.impl.keys

def empty : Heap := ⟨∅⟩

@[no_expose] instance instEmptyCollection : EmptyCollection Heap := ⟨empty⟩

def union (h₁ h₂ : Heap) : Heap := ⟨h₁.impl ∪ h₂.impl⟩

@[no_expose] instance instUnion : Union Heap := ⟨Heap.union⟩

def Mem (l : Loc) (h : Heap) : Prop := l ∈ h.impl

@[no_expose] instance instMembership : Membership Loc Heap :=
  ⟨fun h l => Heap.Mem l h⟩

def Compatible (h₁ h₂ : Heap) : Prop := Finmap.Disjoint h₁.impl h₂.impl

/-- A live cell at `q` holding `content`, uninitialized if `content = none`. -/
def cell (q : RawPtr α M) (content : Option α) : Heap :=
  ⟨Finmap.singleton q.loc (.live ⟨α, content⟩)⟩

def endMarker (l : Loc) (kind : AllocKind) : Heap :=
  ⟨Finmap.singleton l (.endMarker kind)⟩

def IsLive (h : Heap) (l : Loc) : Prop := (h.lookup l).isSome

/-- `l` is the end marker of an allocation -/
def IsEndMarker (h : Heap) (l : Loc) (kind : AllocKind) : Prop :=
  h.impl.lookup l = some (.endMarker kind)

/-- The cells holding `contents` from `l` on. -/
def array (l : Loc) : List (Option α) → Heap
  | [] => empty
  | content :: rest => cell (⟨l⟩ : MutRawPtr α) content ∪ array (l.shift 1) rest

def allocation (l : Loc) (contents : List (Option α)) (kind : AllocKind) : Heap :=
  array l contents ∪ endMarker (l.shift contents.length) kind

/-- The next allocation identifier, past every one in the heap: allocation is deterministic. Since
freed slots and end markers stay in the heap, an identifier is never handed out twice.

The identifier also tells how the allocation is aligned: it is an odd multiple of `align`
(`align` is a power of two, the alignment of the type of the values stored in the allocation), so
that the largest power of two dividing it is the alignment Rust guarantees for the allocation (see
`RawPtr.Aligned`). It is never `0`, the allocation of the null pointer. -/
def freshAllocId (h : Heap) (align : Nat) : AllocId :=
  max align 1 * (2 * ((h.keys.image Loc.allocId).sup id + 1) + 1)

def freshLoc (h : Heap) (align : Nat) : Loc := ⟨freshAllocId h align, 0⟩

/-- `h'` is `h` extended with cells that `h` does not own. -/
def Subheap (h h' : Heap) : Prop :=
  ∃ rest, Heap.Compatible h rest ∧ h' = h ∪ rest

/-- Creates a fresh allocation in the heap, aligned to `align`: fresh memory is mutable in Rust. -/
def alloc (align : Nat) (contents : List (Option α)) (kind : AllocKind) (h : Heap) :
    MutRawPtr α × Heap :=
  (⟨freshLoc h align⟩, allocation (freshLoc h align) contents kind ∪ h)

/-- `q` points to a live cell of type `α`, initialized or not. -/
def IsValid (h : Heap) (q : RawPtr α M) : Prop :=
  match h.lookup q.loc with
  | none => False
  | some ⟨β, _⟩ => β = α

/-- The content of the cell at `q`: `none` if it is uninitialized. -/
def read (q : RawPtr α M) (h : Heap) (hValid : IsValid h q) : Option α × Heap :=
  match hlookup : h.lookup q.loc with
  | none => by simp [IsValid, hlookup] at hValid
  | some ⟨β, content⟩ => by
     have htype : β = α := by
       simpa [IsValid, hlookup] using hValid
     exact (htype ▸ content, h)

def write (q : RawPtr α M) (content : Option α) (h : Heap) (_ : IsValid h q) : Unit × Heap :=
  ((), h.insert q.loc (.live ⟨α, content⟩))

/-- The guard of `dealloc q n kind`: `q` starts an allocation of exactly `n` live slots, whose end
marker records `kind`. So `Global.deallocate` (`.global`) fails on a view, and `endView` (`.view`)
fails on memory from the global allocator. Anything else is undefined behaviour in Rust as well:
a pointer into the middle of an allocation, the wrong size, or memory already deallocated. See the
safety section of
[`Allocator::deallocate`](https://doc.rust-lang.org/std/alloc/trait.Allocator.html#tymethod.deallocate) -/
def CanDealloc (h : Heap) (q : RawPtr α M) (n : Nat) (kind : AllocKind) : Prop :=
  q.loc.offset = 0 ∧ (∀ i < n, IsLive h (q.loc.shift i)) ∧ IsEndMarker h (q.loc.shift n) kind

/-- `n` freed slots from `l` on. -/
private def freedRange (l : Loc) : Nat → Heap
  | 0 => empty
  | n + 1 => ⟨Finmap.singleton l .freed⟩ ∪ freedRange (l.shift 1) n

-- Deallocates the `n` slots at `q` and the marker after them. They stay in the heap as freed slots.
def dealloc (q : RawPtr α M) (n : Nat) (kind : AllocKind) (h : Heap)
    (_ : CanDealloc h q n kind) : Unit × Heap :=
  ((), freedRange q.loc (n + 1) ∪ h)

/-- One borrowed slot at `l`. Owning it is the right to `endBorrow` it. -/
def borrowedSlot (l : Loc) : Heap :=
  ⟨Finmap.singleton l .borrowed⟩

def IsBorrowed (h : Heap) (l : Loc) : Prop :=
  h.impl.lookup l = some .borrowed

/-- One freed slot at `l`. Owning it records that `l` was deallocated. -/
def freedSlot (l : Loc) : Heap :=
  ⟨Finmap.singleton l .freed⟩

def IsFreed (h : Heap) (l : Loc) : Prop :=
  h.impl.lookup l = some .freed

/-- Moves the content of `q` out into a borrow (`from_raw_parts`): the slot holds no value until
`endBorrow`, so every access through a raw pointer fails meanwhile. -/
def borrow (q : RawPtr α M) (h : Heap) (hValid : IsValid h q) : Option α × Heap :=
  ((read q h hValid).1, h.insert q.loc .borrowed)

/-- Ends the borrow of `q`. -/
def endBorrow (q : RawPtr α M) (content : Option α) (h : Heap) (_ : IsBorrowed h q.loc) :
    Unit × Heap :=
  ((), h.insert q.loc (.live ⟨α, content⟩))

end Heap

end Aeneas.Std
