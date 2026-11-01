# Concrete addresses and provenance for Aeneas (prototype)

This replaces the byte model inspired by
[AeneasVerif/aeneas#1433](https://github.com/AeneasVerif/aeneas/pull/1433).
It is a design experiment, not a refinement proof of Rust or an automatically
integrated extraction pipeline.

## The implicit safe heap

Safe Rust holds an **unknown implicit part of the heap**. An absent explicit
permission does not mean that the physical byte or allocation is absent.
Safe allocation, aliasing, and return authority are abstract boundary assumptions,
relying on what safe Rust promises; this model does not enumerate safe memory.

Exposure brings a compatible contribution into the explicit heap. Borrowing
returns permissions to safe Rust. Neither operation necessarily allocates or
deallocates physical storage. Numerical compatibility alone does not authorize
restoration or identify the safe place being exposed.

## Symbolic bytes and representations

`Repr.lean` defines:

```
RawPtr T = { base : Nat, byteOffset : Usize }
Byte     = uninit | data U8 | pointer (RawPtr Unit) Nat
Cell     = shared Nat Byte | borrowed
```

`base` is a ghost **view index**, not a numerical base pointer.
Pointer copies, casts, arithmetic, and coherent pointer loads preserve it.
`MutRawPtr` and `ConstRawPtr` are the same type: constness grants no permission.

`Byte.pointer p lane` carries the complete pointer payload and its byte position.
Eight little-endian lanes model a thin pointer on the current 64-bit target.
Coherent lanes recover the original index and offset, without minting a view or
granting pointee access. Lanes from different pointers cannot be combined just
because their numerical bytes match; copies of the same pointer can.

Numerical projection adds the retained base address and pointer offset, then
extracts the requested byte. Reading a lane as data does not mutate its metadata.
Writing ordinary data replaces metadata even when the numerical byte is unchanged.
`copyBytes` is an untyped, atomic, memmove-style operation: it preserves pointer
lanes and initialization state, rather than repeatedly decoding and writing `U8`.
Copying an uninitialized representation is not a typed read of its value.
`swapBytes` similarly exchanges two snapshots atomically, preserving symbolic
bytes even for self-swap. It accepts identical or disjoint physical ranges;
partial overlap is rejected.

`Repr T` explicitly supplies size, alignment, read interpretation (`decode`),
admissible writes (`encodes`), and pointer payloads contained in a value
(`pointers`). Completeness and encode/decode-back laws are proved fields.
`encodes_support` additionally requires every written pointer lane to come from
one of those payloads; padding cannot spontaneously introduce provenance.
Descriptors, including their payload lists, must be calibrated to Rust types.

Scalar decoding may observe pointer lanes numerically, but scalar encoding must
emit data bytes. Inverse decoding is **not** the encoding relation.
`Repr.u8` and `Repr.pointer` implement these two cases. Symbolic bytes can carry
unbounded ghost indices; this does not claim that finite machine bytes encode Nat.
No canonical encoder or representation axiom is introduced.

Non-writing safe-to-raw exposure is different from encoding a write.
`State.exposes` permits initialized symbolic bytes that decode to the safe
value, retaining pointer metadata supplied by that value or already justified
by a readable explicit contribution at the same address. This permits shared
U8 exposures of pointer fragments without allowing scalar writes to forge them.

Typed reads require readable, initialized cells across the entire footprint,
including padding. Single zero-sized accesses are rejected; empty ranges still
require a live, aligned, in-bounds position.

## Permissions and overlapping views

`shared 0` is exclusive raw write permission. Positive sharing depths preserve
read permission and record local outstanding shares; they are not fractions.

| Cell | Typed read | Write | Entire-view cleanup |
|---|---|---|---|
| `shared 0 (data/pointer)` | If decoding succeeds | Yes | With matching authority |
| `shared 0 uninit` | No | Yes | With matching authority |
| `shared (n + 1) (data/pointer)` | If decoding succeeds | No | No exclusive cleanup |
| `shared (n + 1) uninit` | No | No | No exclusive cleanup |
| `borrowed` | No | No | No |

At each numerical address, borrowed cells are raw-permission-neutral.
Two positive shared contributions are compatible exactly when their **symbolic
Byte payloads agree**: `shared 1 x` and `shared 2 x` are compatible.
A writer conflicts with every other non-borrowed contribution.
`uninit` is not a wildcard, and pointer metadata is not equivalent to equal
numerical data bytes. Missing permissions are interpreted as held implicitly
by safe Rust.

Authorization remains selected-view-specific. Pooling just total depths would
lose the distinction between `A.borrowed/B.shared0` and
`A.shared0/B.borrowed`. No second aggregate-permission store is needed.

A writer cannot coexist with another active raw observer, so writes do not
mirror bytes into every record. Borrowed ancestors have no readable payload;
matching backward continuations restore their updated values later.
The regression `nestedSlices` exercises `A[0,8)`, `B[1,7)`, and `C[2,6)`,
writes through C, and unwinds the views while preserving exterior bytes.
Only A owns the underlying allocation.

Independent shared exposures retire their baseline contribution at depth one.
They do **not** decrement it into a writer. Local nested shares decrement
separately; exclusive access cannot resume until conflicting views retire.

## Concrete heap and lifecycle

`Model.lean` stores one map `Nat → Option Block` and a fresh Nat counter.
Each record contains concrete `bptr : Usize`, root index, byte cells, ownership,
explicit activity, and physical root liveness. The root is its first record;
aliases reference it rather than needing another ID namespace or table.
Its byte extent bounds the modeled allocation; child views must fit inside it.
Different live roots have disjoint numerical extents, even while their
permissions are borrowed or held implicitly.

`Heap.Inv` requires no entries beyond the issued prefix, well-formed records,
consistent roots, valid symbolic pointer metadata, and pairwise compatibility
of active contributions. `check` computes the finite part of this invariant;
its straightforward enumeration is intended for small prototypes, not as an
optimized allocator.

Base addresses are nonnull; mathematical base-plus-length must fit Usize without
wrapping, including a representable one-past address. Access alignment is
divisibility of **bptr + offset**, not an independent alignment guarantee.
Arithmetic is deliberately view-bounded. `distance` recognizes a common root
across distinct views; equal numerical addresses alone do not prove provenance.
`ptrEq` compares numerical addresses, not ghost records.

Retirement keeps immutable address metadata but contributes no permissions.
Root death separately disables all views of that allocation.
Consequently a dangling pointer can still be stored, loaded, and numerically
observed. Reusing its address creates a new root; it cannot revive the old view.

`returnOwned` transfers a complete owned view to implicit safe Rust without
physical death. A subsequent `newBlock` can use that known inactive root,
preserving its address while issuing a fresh view index.
`dealloc` instead marks the root dead. Both require exact full-root coverage,
depth-zero cells, and no other active view of that root, including fully borrowed
aliases. Nonowning exposures retire through their matching return operation.
These are abstract ownership transitions, not checks of an allocator's original
layout or allocation-size/isize policy.

## Rust boundary, Boxes, and failure

`Std/Heap.lean` specifies transitions relationally. Placement, root relationship,
and admissible encoding are chosen **jointly**, subject to compatibility.
Rust wrappers in `Core/Ptr.lean` and `Alloc/Boxed.lean` use these relations
through `Result.checkedModify`. The demonic interpretation admits every
compatible witness; choosing an incompatible padding encoding first cannot
cause spurious intermediate failure.

If no successor exists, the checked boundary explicitly fails at the unchanged
input heap. Earlier operations are not rolled back.
Fresh Nat IDs cannot exhaust cumulatively. Nevertheless, `Box::into_raw` and
borrowed `to_raw` exposure can still fail if no compatible placement exists.
Failure-freedom requires **boundary feasibility**, not `Heap.Inv` alone.
This remaining model limitation is not a Rust precondition.

Safe `Box<T>` is still represented by pure `T`, without a place identity.
`into_raw` materializes an owned record; `from_raw` reads it and calls
`returnOwned`, not physical `dealloc`. Safe Rust retains ownership afterward.
The core supports re-exposure of a **known** root, but these functional wrappers
cannot connect repeated conversions of the same unmoved Box to that identity.
They may choose a different address. Retaining an old pointer's address does
not fix that address-history overapproximation.

Matching translated backward continuations are trusted to return the correct
range and value, once, after their children have returned. There is no dynamic
loan tree or consumable return ticket. A direct Lean call can prematurely
restore a parent while a child is borrowed; the regression explicitly
demonstrates that boundary. Cleanup nevertheless checks independently active
views in its pre-state. Compatibility is not a replacement for safe authority.

Mutable safe loans currently require the selected representation to be an
admissible encoding of each decoded value (`State.mutableValues`). Numerical
U8 reads of pointer lanes remain supported, but mutable U8 loans across those
lanes are conservatively rejected. A returned scalar value alone cannot
distinguish untouched memory from a same-value write; supporting that boundary
requires representation/write history in the matching backward continuation.

## Scope and checking

Plain-data-to-pointer recovery is rejected conservatively, not declared
universally undefined in Rust. Integer/exposed-provenance reconstruction,
provenance-free and null pointers, pointer tagging, wide/function pointers,
MaybeUninit/UnsafeCell semantics, and complete allocator fidelity are not
implemented. An unseen safe subslice cannot establish its entire physical
allocation extent: larger later exposures need an already identified root.
Automatic descriptor plumbing and safe-place identity tracking remain compiler
integration work.

`Provenance.lean` proves fresh-ID, immutable-address, admissible-encoding,
writer-exclusion, and allocation/update invariant laws with only Lean's standard
axioms. `Std/HeapTests.lean` checks nested slices, shared aliases and uninitialized
shares, pointer copying/overwriting, coherent lanes, dangling values and address
reuse, owning return/re-exposure, root/loan guards, joint choices, bounds,
alignment, and atomic initialization-preserving copy.

The separation primitives now distinguish **indexed resource disjointness**
from physical address disjointness. `Resource.Holds.overlapCompatible` derives
the exact physical Byte/permission compatibility from `Heap.Inv` for different
view resources at the same address. Cleanup records retain concrete base and
extent, but do not by themselves confer alias absence or safe return authority.

`Specs.lean` proves uniformly enabled typed reads and exact framed symbolic
updates/writes. `TripleAt` retains arbitrary matching frames and all permitted
successors while recording input-state compatibility obligations. In particular,
a write supplies a compatible initialized encoding witness; its postcondition
covers every State.write encoding, not just that witness. General restoration
and decrements cannot use the former unconditional mutation invariant law:
reintroducing a writer can conflict with another logically separated view.
Deriving operation-specific enabledness without the finite compatibility
obligation remains part of the higher-level proof migration.

`Allocation.lean` proves fresh-view creation and whole-view retirement with
arbitrary matching frames. `Borrowing.lean` proves exact selected-view borrow,
share, decrement, and restoration contracts, with explicit final compatibility.
`Access.lean` proves byte-wise read/write/cleanup denial. `Effects.lean` lifts
state-indexed contracts to the actual demonic checked effects. The regression
suite instantiates a checked write with a physically overlapping borrowed
ancestor frame and proves both frame retention and typed read-back.

The independent Astra prototype review identified and checked fixes for
non-writing pointer-fragment exposure, mutable representation-crossing loans,
and untyped swap. A subsequent read-only review of the migrated core framing,
write, and retirement contracts found no additional concrete defects.

From `backends/lean`:

```
lake build Aeneas.Std.HeapTests Aeneas.Std.Core.PtrOps \
  Aeneas.Std.Core.PtrMovement Aeneas.Std.Alloc.Boxed Aeneas.Std.Heap.Access
```

**Root-specific cleanup, range/restoration/pointer-operation contracts,
EffectSpecs, and extracted example proofs remain to be migrated.** The
Lemmas/Separation/Resources/Specs/Allocation/Borrowing/Access/Effects core
modules are migrated, but remaining old disjoint-index resources,
U8-only descriptors, alignment assumptions, and lifecycle contracts do not
establish the new model's claims. They remain present and in the unchanged
default build; the targeted command above is not a claim that that build passes.
No axioms, sorry definitions, or target exclusions conceal that migration work.
