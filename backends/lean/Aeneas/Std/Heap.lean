module

public import Mathlib.Data.Finmap

/-! Block-based heap: a finite map from allocation ids to blocks. A block records how it was
allocated (`AllocKind`), the type of its values, and one `Cell` per value. A heap is also a fragment
of the memory: fragments combine (`∪`) cell by cell, so two fragments can own different cells of the
same block. Freed blocks stay in the map so allocation ids are never reused.
Supports interior pointers, stored pointers, provenance by allocation id.
Not supported: uninitialized memory, byte-level representation/type punning,
pointer-integer casts, higher-order store, the byte-level allocator API
(`std::alloc::alloc`, `Layout`). -/

public section

namespace Aeneas.Std

abbrev AllocId := Nat

inductive AllocKind where
  /-- Allocated by the global allocator -/
  | heap
  /-- A raw-pointer view of a place that Aeneas translates to a plain value.
  Such views cannot be deallocated through the allocator. -/
  | view
  deriving DecidableEq

inductive Cell (α : Type u) where
  /-- We own the value -/
  | owned (x : α)
  /-- Someone else owns it: useful for separation, but also when converting a raw pointer
  to a mutable borrow -/
  | notOwned

/-- An allocation block -/
structure Block : Type 1 where
  /-- The allocation kind determines whether we're allowed to manually free the block or not -/
  kind : AllocKind
  /-- The type of the allocated values -/
  ty : Type
  cells : List (Cell ty)

inductive BlockSlot : Type 1 where
  | live (block : Block)
  | freed

structure Heap where
  private mk ::
  private allocs : Finmap fun _ : AllocId => BlockSlot

/-! Two examples of how blocks work. In the comments, the heap after each line, starting from the
empty heap; `a ↦ live kind [ ... ]` is the allocation `a` with its cells.
```rust
pub fn boxed() -> u32 {
    // In Aeneas' model, `Box::new(1u32)` returns `1`, which gets allocated in memory
    // in `into_raw` by using the global allocator (because Rust's `Box::new` uses it),
    // thus the block is recorded in the Heap with kind `.heap`.
    let p = Box::into_raw(Box::new(1u32));
    // 0 ↦ live .heap [ owned 1 ]
    unsafe { *Box::from_raw(p) }
    // `from_raw` turns `p` into a new `Box` whose lifetime ends at the end of this statement,
    // so it is freed. Rust only lets a program free memory allocated by the global allocator,
    // which is what the kind `.heap` records. The model reads 1 and frees at once:
    // 0 ↦ freed
}

pub fn borrowed() -> u32 {
    let mut x = 1u32;
    let p = core::ptr::from_mut(&mut x);
    // 0 ↦ live .view [ owned 1 ]
    // `p` points to the local `x`, which the global allocator did not hand out,
    // so the kind is `.view`.
    unsafe { *Box::from_raw(p) }
    // `from_raw` turns `p` into a `Box`. Its lifetime ends at the end of this statement, so it is
    // freed, but this is UB because Rust only lets a program free memory that the
    // global allocator handed out. The kind helps us distinguish between the two examples.
}
```
See the safety section of
[`GlobalAlloc::dealloc`](https://doc.rust-lang.org/std/alloc/trait.GlobalAlloc.html#tymethod.dealloc).
-/

/-
The operations, and how they change blocks and cells. `freed` is final: no operation leaves it, so
deallocated memory can never be used again. A cell given away by `borrow` is `notOwned` until
`endBorrow` gives it back, at the same address. `dealloc` frees a whole block, and only for its kind.

| Operation           | Effect                                       | Used by                                       |
|---------------------|----------------------------------------------|-----------------------------------------------|
| `alloc _ .heap`     | fresh id → live .heap [owned*]               | `Box::into_raw`, `Global::allocate`           |
| `alloc _ .view`     | fresh id → live .view [owned*]               | `from_mut`, `as_ptr`, `as_mut_ptr`            |
| `dealloc _ _ .heap` | live .heap [owned*] → freed                  | `Box::from_raw`, `Global::deallocate`         |
| `dealloc _ _ .view` | live .view [owned*] → freed                  | end of `from_mut`, `as_ptr`, `as_mut_ptr`     |
| `borrow`            | owned → notOwned                             | `from_raw_parts`, `from_raw_parts_mut`        |
| `endBorrow`         | notOwned → owned                             | end of `from_raw_parts`, `from_raw_parts_mut` |
-/

namespace Cell

/-- Combines two fragments of a cell: the owned one wins. -/
def join : Cell α → Cell α → Cell α
  | .owned x, _ => .owned x
  | .notOwned, c => c

/-- Two fragments of a cell combine if at most one of them owns it. -/
def Compatible : Cell α → Cell α → Prop
  | .owned _, .owned _ => False
  | .owned _, .notOwned => True
  | .notOwned, _ => True

/-- Combines two fragments of the cells of a block, cell by cell. Lists of different lengths
give `c₁`. -/
def joinList (c₁ c₂ : List (Cell α)) : List (Cell α) :=
  if c₁.length = c₂.length then List.zipWith join c₁ c₂ else c₁

end Cell

namespace Block

open Classical in
/-- The cells of `b` as cells of type `t`, or none if `b` holds another type. Comparing the types
is not computable. -/
noncomputable def cellsAs (b : Block) (t : Type) : List (Cell t) :=
  if hTy : b.ty = t then hTy ▸ b.cells else []

/-- Two fragments of a block combine if they agree on the kind, the type and the number of
cells, and no cell is owned by both. -/
def Compatible (b₁ b₂ : Block) : Prop :=
  b₁.kind = b₂.kind ∧ b₂.ty = b₁.ty ∧ List.Forall₂ Cell.Compatible b₁.cells (b₂.cellsAs b₁.ty)

/-- Combines two fragments of a block cell by cell, keeping the header of `b₁`. A block of another
type adds nothing. -/
noncomputable def join (b₁ b₂ : Block) : Block :=
  ⟨b₁.kind, b₁.ty, Cell.joinList b₁.cells (b₂.cellsAs b₁.ty)⟩

end Block

namespace BlockSlot

/-- A `freed` block is exclusive: it combines with nothing. -/
def Compatible : BlockSlot → BlockSlot → Prop
  | .live b₁, .live b₂ => b₁.Compatible b₂
  | .live _, .freed => False
  | .freed, _ => False

noncomputable def join : BlockSlot → BlockSlot → BlockSlot
  | .live b₁, .live b₂ => .live (b₁.join b₂)
  | .live b₁, .freed => .live b₁
  | .freed, _ => .freed

end BlockSlot

private def OptCompatible : Option BlockSlot → Option BlockSlot → Prop
  | some s₁, some s₂ => s₁.Compatible s₂
  | some _, none => True
  | none, _ => True

inductive Mutability where
| Mut | Const

/-- `T` is universe-polymorphic so that pointers to values in higher universes
(`dyn Trait`, functions returning `Result`) elaborate. Only the cells a pointer reads or writes
need to live in `Type`. -/
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

def shift (q : RawPtr T M) (i : Nat) : RawPtr T M :=
  ⟨q.allocId, q.offset + i⟩

end RawPtr

namespace Heap

private def lookup (h : Heap) (a : AllocId) : Option BlockSlot := h.allocs.lookup a

private def insert (h : Heap) (a : AllocId) (slot : BlockSlot) : Heap :=
  ⟨h.allocs.insert a slot⟩

def empty : Heap := ⟨∅⟩

@[no_expose] instance instEmptyCollection : EmptyCollection Heap := ⟨empty⟩

/-- The slot of `a` in `h₁ ∪ h₂`, for `a` in `h₂`. -/
private noncomputable def joinAt (h₁ h₂ : Heap) (a : AllocId) : BlockSlot :=
  ((h₁.lookup a).merge BlockSlot.join (h₂.lookup a)).getD .freed

private noncomputable def insertJoin (h₁ h₂ : Heap) (a : AllocId)
    (m : Finmap fun _ : AllocId => BlockSlot) : Finmap fun _ : AllocId => BlockSlot :=
  m.insert a (joinAt h₁ h₂ a)

private theorem insertJoin_leftComm (h₁ h₂ : Heap) : LeftCommutative (insertJoin h₁ h₂) :=
  ⟨fun a₁ a₂ m => by
    by_cases hEq : a₁ = a₂
    · subst hEq; rfl
    · exact Finmap.insert_insert_of_ne m (Ne.symm hEq)⟩

/-- Combines two fragments block by block: the slots of `h₂` are joined into `h₁`. -/
noncomputable def union (h₁ h₂ : Heap) : Heap :=
  ⟨@Multiset.foldr _ _ (insertJoin h₁ h₂) (insertJoin_leftComm h₁ h₂) h₁.allocs h₂.allocs.keys.val⟩

@[no_expose] noncomputable instance instUnion : Union Heap := ⟨Heap.union⟩

def Mem (a : AllocId) (h : Heap) : Prop := a ∈ h.allocs

@[no_expose] instance instMembership : Membership AllocId Heap :=
  ⟨fun h a => Heap.Mem a h⟩

def Compatible (h₁ h₂ : Heap) : Prop := ∀ a, OptCompatible (h₁.lookup a) (h₂.lookup a)

/-- The value at `q`, if `h` owns it. It does not depend on the type of `q`. -/
private def cell? (h : Heap) (q : RawPtr T M) : Option (Σ α : Type, α) :=
  match h.lookup q.allocId with
  | some (.live b) =>
    match b.cells[q.offset]? with
    | some (.owned x) => some ⟨b.ty, x⟩
    | _ => none
  | _ => none

/-- The block of `q`, of kind `kind` and `len` cells, owning only the cell of `q` (none of them if
`len ≤ q.offset`). -/
def singleton (q : RawPtr α M) (value : α) (kind : AllocKind) (len : Nat) : Heap :=
  ⟨Finmap.singleton q.allocId
    (.live ⟨kind, α, (List.replicate len .notOwned).set q.offset (.owned value)⟩)⟩

/-- The block of `q`, of kind `kind` and `len` cells, owning none of them: what is left of
`singleton q _ kind len` after `borrow`. -/
def borrowedBlock (q : RawPtr α M) (kind : AllocKind) (len : Nat) : Heap :=
  ⟨Finmap.singleton q.allocId (.live ⟨kind, α, List.replicate len .notOwned⟩)⟩

/-- The block `a` holding `values`, all owned. -/
def allocation (a : AllocId) (values : List α) (kind : AllocKind) : Heap :=
  ⟨Finmap.singleton a (.live ⟨kind, α, values.map .owned⟩)⟩

def IsLive (h : Heap) (q : RawPtr T M) : Prop := (h.cell? q).isSome

def freshAllocId (h : Heap) : AllocId :=
  h.allocs.keys.sup id + 1

/-- `h'` is `h` extended with a compatible fragment. -/
def Subheap (h h' : Heap) : Prop :=
  ∃ rest, Heap.Compatible h rest ∧ h' = h ∪ rest

/-- Creates a fresh allocation in the heap: fresh memory is mutable in Rust. -/
def alloc (values : List α) (kind : AllocKind) (h : Heap) : MutRawPtr α × Heap :=
  (⟨freshAllocId h, 0⟩, h.insert (freshAllocId h) (.live ⟨kind, α, values.map .owned⟩))

def IsValid (h : Heap) (q : RawPtr α M) : Prop :=
  match h.cell? q with
  | none => False
  | some ⟨β, _⟩ => β = α

def read (q : RawPtr α M) (h : Heap) (hValid : IsValid h q) : α × Heap :=
  match hlookup : h.cell? q with
  | none => by simp [IsValid, hlookup] at hValid
  | some ⟨β, value⟩ => by
     have htype : β = α := by
       simpa [IsValid, hlookup] using hValid
     exact (htype ▸ value, h)

/-- `h` does not own the cell of `q`, whose block holds values of type `α`: `endBorrow` can give
it back. -/
def IsBorrowed (h : Heap) (q : RawPtr α M) : Prop :=
  match h.lookup q.allocId with
  | some (.live b) => b.ty = α ∧ b.cells[q.offset]? = some .notOwned
  | _ => False

/-- Owns `value` at `q`, given that the block of `q` holds values of type `α`. -/
private def setOwned (h : Heap) (q : RawPtr α M) (value : α)
    (hTy : ∀ b, h.lookup q.allocId = some (.live b) → b.ty = α) : Heap :=
  match hlookup : h.lookup q.allocId with
  | some (.live b) =>
    h.insert q.allocId
      (.live ⟨b.kind, b.ty, b.cells.set q.offset (.owned (cast (hTy b hlookup).symm value))⟩)
  | _ => h

private theorem ty_of_isValid {h : Heap} {q : RawPtr α M} (hValid : IsValid h q) :
    ∀ b, h.lookup q.allocId = some (.live b) → b.ty = α := by
  intro b hlookup
  unfold IsValid cell? at hValid
  simp only [hlookup] at hValid
  split at hValid
  · rename_i hCell; split at hCell <;> simp_all
  · rename_i hCell; split at hCell <;> simp_all

private theorem ty_of_isBorrowed {h : Heap} {q : RawPtr α M} (hBorrowed : IsBorrowed h q) :
    ∀ b, h.lookup q.allocId = some (.live b) → b.ty = α := by
  intro b hlookup
  unfold IsBorrowed at hBorrowed
  rw [hlookup] at hBorrowed
  exact hBorrowed.1

def write (q : RawPtr α M) (value : α) (h : Heap) (hValid : IsValid h q) : Unit × Heap :=
  ((), h.setOwned q value (ty_of_isValid hValid))

/-- The guard of `dealloc q n kind`: `q` starts a block of kind `kind`, of exactly `n` cells, all
owned. So `Global.deallocate` (`.heap`) fails on a view, and `endView` (`.view`) fails on memory
from the global allocator. Anything else is undefined behaviour in Rust as well: a pointer into the
middle of an allocation, the wrong size, or memory already deallocated. See the safety section of
[`Allocator::deallocate`](https://doc.rust-lang.org/std/alloc/trait.Allocator.html#tymethod.deallocate) -/
def CanDealloc (h : Heap) (q : RawPtr α M) (n : Nat) (kind : AllocKind) : Prop :=
  q.offset = 0 ∧
    match h.lookup q.allocId with
    | some (.live b) => b.kind = kind ∧ b.cells.length = n ∧ ∀ i < n, IsLive h (q.shift i)
    | _ => False

/-- Deallocates the block of `q`. It stays in the heap as `freed`. -/
def dealloc (q : RawPtr α M) (n : Nat) (kind : AllocKind) (h : Heap)
    (_ : CanDealloc h q n kind) : Unit × Heap :=
  ((), h.insert q.allocId .freed)

/-- Moves the value of `q` out into a borrow (`from_raw_parts`): the cell is not owned until
`endBorrow`, so every access through a raw pointer fails meanwhile. -/
def borrow (q : RawPtr α M) (h : Heap) (hValid : IsValid h q) : α × Heap :=
  ((read q h hValid).1,
    match h.lookup q.allocId with
    | some (.live b) =>
      h.insert q.allocId (.live ⟨b.kind, b.ty, b.cells.set q.offset .notOwned⟩)
    | _ => h)

/-- Ends the borrow of `q`. -/
def endBorrow (q : RawPtr α M) (value : α) (h : Heap) (hBorrowed : IsBorrowed h q) : Unit × Heap :=
  ((), h.setOwned q value (ty_of_isBorrowed hBorrowed))

end Heap

end Aeneas.Std
