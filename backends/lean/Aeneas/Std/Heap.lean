module

public import Mathlib.Data.Finmap

/-! Block-based heap: finite map from (allocation id, offset) to typed cells `Σ α, α`.
Supports interior pointers, stored pointers, provenance by allocation id.
Freed slots stay in the map so allocation ids are never reused. The end of
an allocation also records whether the allocation comes from the global allocator:
only those can be deallocated, and only whole, otherwise UB. Not supported: uninitialized
memory, byte-level representation/type punning, pointer-integer casts, higher-order store,
permissions, the byte-level allocator API (`std::alloc::alloc`, `Layout`). -/

public section

namespace Aeneas.Std

abbrev AllocId := Nat

structure Loc where
  allocId : AllocId
  offset : Nat
  deriving DecidableEq, Inhabited

private abbrev HeapCell := Σ α : Type, α

private inductive Slot where
  | live (cell : HeapCell)
  | freed
  -- one past the last value: `freeable` iff the allocation comes from the global allocator
  | endMarker (freeable : Bool)

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
    // thus the allocation is recorded in the Heap with marker `endMarker true`.
    let p = Box::into_raw(Box::new(1u32));
    // 0 ↦ [ live 1 ; endMarker true ]
    unsafe { *Box::from_raw(p) }
    // `from_raw` turns `p` into a new `Box` whose lifetime ends at the end of this statement,
    // so it is freed. Rust only lets a program free memory allocated by the global allocator,
    // which is what `endMarker true` records. The model reads 1 and frees at once:
    // 0 ↦ [ freed ; freed ]
}

pub fn borrowed() -> u32 {
    let mut x = 1u32;
    let p = core::ptr::from_mut(&mut x);
    // 0 ↦ [ live 1 ; endMarker false ]
    // `p` points to the local `x`, which the global allocator did not hand out,
    // so the marker is `endMarker false`.
    unsafe { *Box::from_raw(p) }
    // `from_raw` turns `p` into a `Box`. Its lifetime ends at the end of this statement, so it is
    // freed, but this is UB because Rust only lets a program free memory that the
    // global allocator handed out. The `endMarker` helps us distinguish between the two examples.
}
```
See the safety section of
[`GlobalAlloc::dealloc`](https://doc.rust-lang.org/std/alloc/trait.GlobalAlloc.html#tymethod.dealloc).
-/

def Loc.shift (l : Loc) (i : Nat) : Loc := ⟨l.allocId, l.offset + i⟩

inductive Mutability where
| Mut | Const

/-- `T` is a phantom parameter, universe-polymorphic so that pointers to values in higher universes
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

def shift (q : RawPtr T M) (i : Nat) : RawPtr T M :=
  ⟨q.loc.shift i⟩

end RawPtr

namespace Heap

private def lookup (h : Heap) (l : Loc) :
    Option HeapCell :=
  (h.impl.lookup l).bind Slot.cell?

private def insert (h : Heap) (l : Loc)
    (slot : Slot) : Heap :=
  ⟨h.impl.insert l slot⟩

private def keys (h : Heap) :=
  h.impl.keys

def empty : Heap := ⟨∅⟩

@[no_expose] instance instEmptyCollection : EmptyCollection Heap := ⟨empty⟩

def union (h₁ h₂ : Heap) : Heap := ⟨h₁.impl ∪ h₂.impl⟩

@[no_expose] instance instUnion : Union Heap := ⟨Heap.union⟩

def Mem (l : Loc) (h : Heap) : Prop :=
  l ∈ h.impl

@[no_expose] instance instMembership : Membership Loc Heap :=
  ⟨fun h l => Heap.Mem l h⟩

def Compatible (h₁ h₂ : Heap) : Prop :=
  Finmap.Disjoint h₁.impl h₂.impl

def singleton (q : RawPtr α M) (value : α) : Heap :=
  ⟨Finmap.singleton q.loc (.live ⟨α, value⟩)⟩

def endMarker (l : Loc) (freeable : Bool) : Heap :=
  ⟨Finmap.singleton l (.endMarker freeable)⟩

def IsValid (h : Heap) (q : RawPtr α M) : Prop :=
  match h.lookup q.loc with
  | none => False
  | some ⟨β, _⟩ => β = α

def IsLive (h : Heap) (l : Loc) : Prop :=
  (h.lookup l).isSome

def IsFreeableEnd (h : Heap) (l : Loc) : Prop :=
  h.impl.lookup l = some (.endMarker true)

def array (l : Loc) : List α → Heap
  | [] => empty
  | value :: rest => singleton (⟨l⟩ : MutRawPtr α) value ∪ array (l.shift 1) rest

def allocation (l : Loc) (values : List α) (freeable : Bool) : Heap :=
  array l values ∪ endMarker (l.shift values.length) freeable

def freshAllocId (h : Heap) : AllocId :=
  (h.keys.image Loc.allocId).sup id + 1

def freshLoc (h : Heap) : Loc := ⟨freshAllocId h, 0⟩

def alloc (h : Heap) (values : List α) (freeable : Bool) : Heap :=
  allocation (freshLoc h) values freeable ∪ h

/-- `h'` is `h` extended with cells that `h` does not own. -/
def Subheap (h h' : Heap) : Prop :=
  ∃ rest, Heap.Compatible h rest ∧ h' = h ∪ rest

def read (h : Heap) (q : RawPtr α M)
    (hValid : IsValid h q) : α :=
  match hlookup : h.lookup q.loc with
  | none => by simp [IsValid, hlookup] at hValid
  | some ⟨β, value⟩ => by
      have htype : β = α := by
        simpa [IsValid, hlookup] using hValid
      exact htype ▸ value

def write (h : Heap) (q : RawPtr α M) (value : α)
    (_ : IsValid h q) : Heap :=
  h.insert q.loc (.live ⟨α, value⟩)

/-- The guard of `dealloc l n`: `l` starts an allocation of the global allocator, of exactly `n`
live slots. Anything else is undefined behaviour in Rust: memory that the global allocator did not
allocate, a pointer into the middle of an allocation, the wrong
size, or memory already deallocated. See the safety section of
[`Allocator::deallocate`](https://doc.rust-lang.org/std/alloc/trait.Allocator.html#tymethod.deallocate),
which, unlike `GlobalAlloc::dealloc`, also allows zero-sized allocations (`n = 0`).
-/
def CanDealloc (h : Heap) (l : Loc) (n : Nat) : Prop :=
  l.offset = 0 ∧ (∀ i < n, IsLive h (l.shift i)) ∧ IsFreeableEnd h (l.shift n)

/-- `n` freed slots from `l` on. -/
private def freedRange (l : Loc) : Nat → Heap
  | 0 => empty
  | n + 1 => ⟨Finmap.singleton l .freed⟩ ∪ freedRange (l.shift 1) n

-- Deallocates the `n` slots at `l` and the marker after them. They stay in the heap as freed slots.
def dealloc (h : Heap) (l : Loc) (n : Nat) (_ : CanDealloc h l n) : Heap :=
  freedRange l (n + 1) ∪ h

end Heap

end Aeneas.Std
