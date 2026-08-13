import Aeneas.SLPoC.Step

/-!
# Verus mimalloc free-list kernel

This is a sequential SLPoC port of
`https://github.com/verus-lang/verified-memory-allocator/blob/main/verus-mimalloc/linked_list.rs`,
specifically the ownership transfer performed by `LL::insert_block` and
`LL::pop_block`.

The source splits one raw byte allocation at `size_of::<Node>()`: the first
machine word becomes a typed `Node`, while `PointsToRaw` continues to own the
padding and the `Mim::block` token records the block metadata.  SLPoC currently
has neither byte-addressed subranges nor provenance-aware pointer arithmetic.
The encoding below therefore uses two distinct typed heap cells:

* `Block.header` is the word in which the next pointer is written;
* `Block.padding` owns the resource-bearing remainder; and
* the repeated `BlockMeta` value ties that remainder to its ghost block
  descriptor.

`blockValid` records the source layout equation, but the model deliberately
does not claim that the two typed pointers are numerically adjacent.  A raw
header is represented honestly as an existentially hidden previous typed
value.  Thus insertion still transfers two separately framed cells into the
list, and pop returns both cells as whole-block ownership; only byte-level
uninitialization, provenance exposure, and address reconstruction are
abstracted.  The source additionally ties every block to an allocator
instance, heap ID, page key, fixed page/block configuration, and provenance;
`blockValid` does not model those global allocator invariants.  "Whole-block
ownership" below therefore means the complete two-cell resource of this typed
abstraction, not ownership of a contiguous raw allocation.  As in SLPoC
generally, permissions are specification resources: the executable pop returns
the block's header pointer, while its postcondition returns the padding
ownership and metadata.
-/

namespace Aeneas.SLPoC

open scoped SepLogic

/-! # Executable definitions -/

/-- The mimalloc node header.  The Rust source stores exactly this next pointer
in the first machine word of a free block. -/
structure FreeNode where
  next : Option (Ptr FreeNode)

/-- Ghost layout and identity data corresponding to the relevant fields of the
source `Mim::block` key. -/
structure BlockMeta where
  blockId : Nat
  pageId : Nat
  blockSize : Nat
  paddingSize : Nat

/-- Typed stand-in for the raw padding range and the resource carried by the
source block token. -/
structure PaddingCell (R : Type) where
  info : BlockMeta
  payload : R

/-- Typed descriptor of one allocation.  `padding` replaces the address
calculation `header + size_of::<Node>()`. -/
structure Block (R : Type) where
  header : Ptr FreeNode
  padding : Ptr (PaddingCell R)
  info : BlockMeta

/-- The executable part of `LL`; Verus' permission map is represented later by
the separation-logic assertion `freeListRep`. -/
structure FreeList where
  first : Option (Ptr FreeNode)

namespace FreeList

/-- The source fixes the node layout to one eight-byte machine word. -/
def headerSize : Nat := 8

/-- Executable insertion: write the old head into the block header and publish
that header as the new head. -/
def insertBlock (s : FreeList) (header : Ptr FreeNode) : St FreeList := do
  update header { next := s.first }
  pure { first := some header }

/-- Executable pop: read the first node, advance the head, and return the raw
block address.  Ghost ownership of the complete block is returned by the
specification below. -/
def popBlock (s : FreeList) : St (FreeList × Ptr FreeNode) := do
  let header := s.first.get!
  let node ← read header
  pure ({ first := node.next }, header)

/-! # Ghost state, specifications and proofs -/

variable {R : Type}

/-- The source-side requirement that the allocation divides into one node
header followed by the padding range. -/
def blockValid (b : Block R) : Prop :=
  b.info.blockSize = headerSize + b.info.paddingSize

/-- Contents owned at the typed padding pointer. -/
def paddingValue (b : Block R) (payload : R) : PaddingCell R :=
  { info := b.info, payload }

/-- Ownership of a complete raw block before insertion or after pop.

The hidden `oldNext` is the typed abstraction of arbitrary/uninitialized bytes
in the header range.  Both the header and padding cells are owned. -/
def blockOwn (b : Block R) (payload : R) : SLProp :=
  iprop(
    ⌜blockValid b⌝ ∗
    hexists fun oldNext : Option (Ptr FreeNode) =>
      iprop(
        b.header ↦ { next := oldNext } ∗
        b.padding ↦ paddingValue b payload))

/-- Ghost entries are ordered from the executable head toward the tail. -/
abbrev Entries (R : Type) := List (Block R × R)

/-- Header pointer of the first ghost entry. -/
def firstHeader : Entries R → Option (Ptr FreeNode)
  | [] => none
  | (b, _) :: _ => some b.header

/-- Ownership of every header and every padding/resource cell in a free list.
Each header contains the pointer of the following ghost entry. -/
def freeBlocks : Entries R → SLProp
  | [] => emp
  | (b, payload) :: rest =>
      iprop(
        ⌜blockValid b⌝ ∗
        b.header ↦ { next := firstHeader rest } ∗
        b.padding ↦ paddingValue b payload ∗
        freeBlocks rest)

/-- Full list representation: the concrete head agrees with the ghost list,
and the list owns both typed pieces of every block. -/
def freeListRep (s : FreeList) (entries : Entries R) : SLProp :=
  iprop(⌜s.first = firstHeader entries⌝ ∗ freeBlocks entries)

@[simp] theorem firstHeader_nil :
    firstHeader ([] : Entries R) = none := rfl

@[simp] theorem firstHeader_cons (b : Block R) (payload : R)
    (rest : Entries R) :
    firstHeader ((b, payload) :: rest) = some b.header := rfl

@[simp] theorem freeBlocks_nil :
    freeBlocks ([] : Entries R) = emp := rfl

@[sl_simps] theorem blockOwn_eq (b : Block R) (payload : R) :
    blockOwn b payload =
      iprop(
        ⌜blockValid b⌝ ∗
        hexists fun oldNext : Option (Ptr FreeNode) =>
          iprop(
            b.header ↦ { next := oldNext } ∗
            b.padding ↦ paddingValue b payload)) := rfl

@[sl_simps] theorem freeListRep_eq (s : FreeList) (entries : Entries R) :
    freeListRep s entries =
      iprop(⌜s.first = firstHeader entries⌝ ∗ freeBlocks entries) := rfl

@[simp] theorem freeBlocks_cons (b : Block R) (payload : R)
    (rest : Entries R) :
    freeBlocks ((b, payload) :: rest) =
      iprop(
        ⌜blockValid b⌝ ∗
        b.header ↦ { next := firstHeader rest } ∗
        b.padding ↦ paddingValue b payload ∗
        freeBlocks rest) := rfl

/-- Split the newly inserted block's two cells from the remainder of the free
list.  This is the typed counterpart of the source permission-map entry
`(PointsTo<Node>, PointsToRaw, Mim::block, IsExposed)`. -/
@[sl_simps] theorem freeListRep_cons (s : FreeList) (b : Block R)
    (payload : R) (rest : Entries R) :
    freeListRep s ((b, payload) :: rest) =
      iprop(
        ⌜s.first = some b.header⌝ ∗
        ⌜blockValid b⌝ ∗
        b.header ↦ { next := firstHeader rest } ∗
        b.padding ↦ paddingValue b payload ∗
        freeBlocks rest) := rfl

/-- Join a concrete initialized header and its separately framed padding back
into whole-block ownership. -/
theorem blockOwn_join (b : Block R) (payload : R)
    (next : Option (Ptr FreeNode)) (hvalid : blockValid b) :
    iprop(
      b.header ↦ { next := next } ∗
      b.padding ↦ paddingValue b payload) ⊢
    blockOwn b payload := by
  unfold blockOwn
  sl_frame

/-- Exact insertion specification.  It consumes whole-block ownership, writes
the current head into the header, and transfers both header and padding into a
new first list entry. -/
@[step]
theorem insertBlock.spec (s : FreeList) (entries : Entries R)
    (b : Block R) (payload : R) :
    ⦃ freeListRep s entries ∗ blockOwn b payload ⦄
      insertBlock s b.header
    ⦃⇓ s' => freeListRep s' ((b, payload) :: entries)⦄ := by
  unfold insertBlock freeListRep
  simp only [firstHeader_cons, freeBlocks_cons]
  rw [hstar_assoc_eq]
  sl_pull hfirst
  unfold blockOwn
  sl_pull oldNext
  rw [hfirst]
  sl_step*

/-- Exact pop specification.  It removes precisely the first ghost entry,
returns that entry's header pointer, preserves the rest of the list, and joins
the popped header and padding/resource cells into ownership of the whole raw
block. -/
@[step]
theorem popBlock.spec (s : FreeList) (b : Block R) (payload : R)
    (rest : Entries R) :
    ⦃ freeListRep s ((b, payload) :: rest) ⦄
      popBlock s
    ⦃⇓ (s', header) =>
      ⌜header = b.header⌝ ∗
      blockOwn b payload ∗
      freeListRep s' rest⦄ := by
  unfold popBlock
  sl_step*

end FreeList

end Aeneas.SLPoC
