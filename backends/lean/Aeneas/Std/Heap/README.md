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
RawPtr T = { provenance : Nat, address : Usize }
Byte     = uninit | data U8 | pointer (RawPtr Unit) Nat
Cell     = shared Nat Byte | borrowed
```

`provenance` is a ghost **view index**, not a numerical base pointer. `address` is the
complete concrete address, not an offset from that view.
Pointer copies, casts, arithmetic, and coherent pointer loads preserve it.
`MutRawPtr` and `ConstRawPtr` are the same type: constness grants no permission.

### Initialization and padding

There is one initialization mechanism: `Byte.uninit`. Fresh uninitialized
storage and uninitialized padding use that same constructor. Padding is
relative to a descriptor's decoder, not a separate byte kind. Size and alignment
alone do not determine it: four bytes can have alignment one and no padding;
the two-byte `padded` regression has alignment two and an ignored byte.

Permissions remain separate. A shared uninitialized byte can be overwritten
with exclusive depth-zero permission, or passed to a decoder that ignores it.
A borrowed cell is inaccessible even in an ignored position. `pointsTo` means
an admissible typed representation, not that every byte is initialized.
`write_uninitialized.spec` is a convenience specialization of `write_writable.spec`,
not a second initialization semantics. No padding mask or initializedness flag
is needed alongside the symbolic bytes.

### Pointer representations

`Byte.pointer p lane` carries the complete pointer payload and its byte position.
Eight little-endian lanes model a thin pointer on the current 64-bit target.
Coherent lanes recover the original index and address, without minting a view or
granting pointee access. Lanes from different pointers cannot be combined just
because their numerical bytes match; copies of the same pointer can.

Numerical projection extracts the requested byte directly from the pointer's
stored address. Reading a lane as data does not mutate its metadata.
Writing ordinary data replaces metadata even when the numerical byte is unchanged.
`copyBytes` is an untyped, atomic, memmove-style operation: it preserves pointer
lanes and initialization state, rather than repeatedly decoding and writing `U8`.
Copying an uninitialized representation is not a typed read of its value.
`swapBytes` similarly exchanges two snapshots atomically, preserving symbolic
bytes even for self-swap. It accepts identical or disjoint physical ranges;
partial overlap is rejected.

`Repr T` explicitly supplies size, alignment, read interpretation (`decode`),
and admissible writes (`encode`). Completeness (`encode_complete`) and
encode/decode-back laws are proved fields. `encode_valid` requires every written
pointer lane to have a valid lane index. This remains necessary for generic
write enabledness: decoding laws, including independence of ignored padding,
do not prevent an aggregate descriptor from encoding an out-of-range pointer
lane. The explicit pointer descriptor guarantees validity only for its own
encodings, not for arbitrary descriptors. Descriptors must be calibrated to Rust types; in particular,
scalar encodings must not introduce provenance in their padding.

`decode` receives only symbolic bytes; there is no address-map argument.
Pointer lanes already contain their concrete address, so integer observation
and coherent pointer decoding are heap-independent. A vector of optional
numerical bytes alone would discard the provenance metadata.
There is no separately supplied pointer list. `Repr.Carries value p` is derived
from `encode`: some admissible encoding of `value` contains a lane of `p`.
Exposure and write contracts use this derived predicate for provenance evidence;
it does not itself grant access to those pointers.

Scalar decoding may observe pointer lanes numerically, but scalar encoding must
emit data bytes. Inverse decoding is **not** the encoding relation.
`Repr.u8` and `Repr.pointer` implement these two cases. The explicit pointer
descriptor encode every lane, and its decoder succeeds exactly on that complete
encoding (`pointer_decode_iff`). It rejects a nonzero first lane, any missing,
duplicated, reordered or mismatched lane, and numerical data without metadata.
Symbolic bytes can carry
unbounded ghost indices; this does not claim that finite machine bytes encode Nat.
No canonical encoder or representation axiom is introduced.

Non-writing safe-to-raw exposure is different from encoding a write.
`State.exposes` permits symbolic bytes that decode to the safe
value, retaining pointer metadata supplied by that value or already justified
by a readable explicit contribution at the same address. This permits shared
U8 exposures of pointer fragments without allowing scalar writes to forge them.

Typed reads require readable permissions across the entire footprint, but pass
uninitialized symbolic bytes through to the decoder. The decoder rejects
uninitialized value-bearing bytes and may ignore uninitialized padding.
The descriptor's `decode_mono` law makes that independence mandatory: whenever
decoding succeeds, replacing any or all uninitialized positions by arbitrary
symbolic bytes must preserve success and the exact decoded value. Initialized
positions remain unchanged. `decode_set_uninit` specializes the law to one position.
Borrowed padding remains inaccessible. Admissible encodings may likewise contain
uninitialized padding if the descriptor's encode/decode law justifies it;
points-to and exposure do not impose an additional initialization condition.
This does not require every decodable representation to be an admissible write.
Single zero-sized accesses are rejected; empty ranges still require a live,
aligned, in-bounds position.

## Permissions and overlapping views

`shared 0` is exclusive raw write permission. Positive sharing depths preserve
read permission and record local outstanding shares; they are not fractions.

| Cell | Typed read | Write | Entire-view cleanup |
|---|---|---|---|
| `shared 0 (data/pointer)` | If decoding succeeds | Yes | With matching authority |
| `shared 0 uninit` | Only if ignored by decoding | Yes | With matching authority |
| `shared (n + 1) (data/pointer)` | If decoding succeeds | No | No exclusive cleanup |
| `shared (n + 1) uninit` | Only if ignored by decoding | No | No exclusive cleanup |
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

View base addresses are nonnull; mathematical base-plus-length must fit Usize without
wrapping, including a representable one-past address. Access alignment is
divisibility of the pointer's **stored address**, not an independent alignment
guarantee. Accesses first check that this address is at least the selected view's
base, then derive the local index by subtraction. A before-view address must not
silently become index zero through truncated subtraction.
Arithmetic checks source and target addresses against the selected view, including
one-past, and rejects overflow before constructing a new Usize.
`distance` recognizes a common root
across distinct views; equal numerical addresses alone do not prove provenance.
`ptrEq` compares numerical addresses, not ghost records.

Retirement keeps immutable view metadata but contributes no permissions.
Root death separately disables all views of that allocation.
Consequently a dangling pointer can still be stored, loaded, and numerically
observed directly from the pointer value. Numerical equality does not require
either view to be live or even present. Reusing an address creates a new root;
it cannot revive the old view, and numerical observation grants no access.

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

`Lemmas.lean` proves invariant preservation for layout-preserving, valid-payload,
permission-weakening updates, including writer payload replacement.
`Specs.lean` derives uniformly enabled writes internally from exclusive byte
resources, without asking clients to prove the resulting heap's `check`.
`write.spec` and `write_pointsTo.spec` cover pointer-free values.
`write_supported.spec` and `write_pointsTo_supported.spec` additionally retain
local supporting resources for pointer payload provenance. Every arbitrary
matching frame and every permitted encoding successor is preserved.

The current `SupportsValue` condition uses a live resource with the pointer's
view index; the concrete address is already machine-representable. It need not
give permission at the pointer's address; `supportsValue_pointer_alloc` obtains this
evidence from cleanup resources. This sufficient condition does not yet cover
writing a dangling pointer using only an existing pointer-slot resource, although
the raw transition supports such a write. Clients of the pointer-free contracts
need only the footprint and a positive representation size.

Low-level `writeAt.spec` retains the exact input-state/check interface.
Restoration to writer permission still uses state-specific checked contracts:
reintroducing a writer can conflict with another logically separated view.
Backward-continuation return authority has not yet been encoded as a separation
resource; borrowed-cell ownership alone is deliberately not treated as sufficient.

`Initialization.lean` now initializes arbitrary writable symbolic bytes, including
uninitialized and previously invalid values. Pointer initialization has a local
support-resource variant. `Ranges.lean` provides concrete-address splitting,
multi-element reads, mutable borrowing, sharing, and decrements that retain
positive sharing depth. Its grouping descriptor accepts symbolic bytes, including
ignored uninitialized padding, while enforcing lane bounds on encodings.
`modify_weaken.spec` encapsulates invariant preservation for these range updates.
The mutable range contract also establishes `State.mutableValues`; decoding alone
would not justify a representation-crossing mutable loan.
Returning the final share to depth zero is deliberately not inferred from a
positive-depth footprint: conflicting readers may still exist in other views.
`RangeRestoration.lean` preserves arbitrary frames and all encoding successors
for an enabled range return. Its explicitly state-specific contract requires a
compatible return witness; this is a low-level boundary, not the completed
backward-resource authority contract. Empty transfers preserve the heap.

`PointerOps.lean` provides uniform replacement, unaligned access, and atomic
snapshot-swap contracts. Swapping two exclusive footprints derives physical
disjointness from the invariant inside the library, including for different
views. Self-swap needs just one footprint. Neither variant decodes or re-encodes
the snapshots, so initialization and pointer lanes are preserved.

`Allocation.lean` proves fresh-view creation and whole-view retirement with
arbitrary matching frames. Retirement now derives invariant preservation without
a client-side final check. `RootReturn` records exact root coverage and alias
absence for the remaining state-specific owned-return contract; cleanup layout
resources alone do not supply this authority.
`Borrowing.lean` proves exact selected-view borrow,
share, decrement, and restoration contracts. Borrow and share now have uniform
resource-only enabling proofs, including points-to wrappers; decrement and
restoration still require explicit final compatibility.
`Access.lean` proves byte-wise read/write/cleanup denial. `Effects.lean` supplies
framing and composition for actual demonic checked effects. `EffectSpecs.lean`
provides read, write, supported pointer write, singleton borrow/share/return,
scaled pointer movement, allocation/exposure, and ownership-return contracts
for the Rust wrappers. Nonowning exposure produces `readable`, which promises
decoding without falsely requiring the observed bytes to encode a scalar write.
Baseline nonowning return is uniformly enabled by whole-view resources.
Allocation explicitly requires compatible placement feasibility and covers every
permitted successor. `RawPtr.borrowWithBack` now pairs a raw-to-safe borrow with
its effectful backward computation. Its scoped contract derives restoration
enabledness from the original exclusive footprint, covers every encoding
successor, and retains arbitrary original frames. `RawPtr.withBorrow` packages
a pure safe update followed by that matching backward call; `borrow_update_read`
proves raw read-back without client heap checks.

The callback guarantee currently applies at the forward operation's returned
state. It is not yet a resource protocol that can be threaded through nested
heap effects and raw re-exposures. General restoration still needs a
state-specific enabled-return witness, and owned return still needs
`RootReturn`; neither is presented as a completed backward-resource authority
design. The regression
suite instantiates a checked write with a physically overlapping borrowed
ancestor frame and proves both frame retention and typed read-back without a
client-side update/check witness. It also proves a generic padded write/read
sequence and a pointer-typed update retaining its target's cleanup resource,
using the actual Rust wrappers without explicit client heap-preservation goals.
Additional framed sharing/read, singleton read/borrow, padded initialization,
multi-element padded read/borrow, nested range-share, and swap/read compositions
exercise the effect contracts. Their client statements and scripts contain no heap checks
or pairwise-overlap proof obligations. Executable regressions cover
ignored uninitialized padding, rejected uninitialized values, padding exposure
and copying, and coherent pointer updates (including dangling-pointer storage).
The generic padding regression fills an ignored uninitialized byte with any
symbolic byte; a separate check rejects borrowed padding. Pointer regressions
independently corrupt each of the eight lanes with uninitialized bytes, plain
data, and incorrect lane numbers.

`PointerMovement.lean` now provides concrete-address byte movement and distance
contracts from cleanup resources and ordinary source/target bounds, with no
client-side invariant-preservation check. The address regressions reject
below-view positions before local-offset subtraction, reject wraparound and
out-of-view movement, and distinguish one-past arithmetic from typed access.

The independent Astra prototype review identified and checked fixes for
non-writing pointer-fragment exposure, mutable representation-crossing loans,
and untyped swap. A subsequent read-only review of the migrated core framing,
write, and retirement contracts found no additional concrete defects.
Before the concrete-address pointer refactor, an independent read-only review
of the padding changes and uniform write,
borrow, and share enabledness proofs found no significant issues. It confirmed
that return-authority resources, dangling-pointer support evidence, and the
remaining default-build/example migration still block a completion claim.
An independent read-only review of the subsequent concrete-address changes,
derived payload support, mandatory decoding-stability law, and complete-lane
pointer descriptor found no high-confidence introduced correctness defects.
It confirmed the same remaining authority and migration limitations.
An independent read-only review of the migrated effect contracts, allocation
and retirement helpers, readable exposures, and wrapper client proofs found no
significant issues.
An independent read-only review of the restored initialization, range,
range-return, atomic-swap, descriptor, and client proofs likewise found no
significant defects. It confirmed that ordinary client compositions have no
overlap/check/preservation obligations, while backward-return authority remains
an explicit limitation rather than an unconditional borrowed-cell rule.
An independent read-only review of the scoped backward-call contracts and
provenance-field rename found no significant issues.

For restored ordinary clients, the finer model adds descriptor calibration and
explicit concrete-base arguments, but not overlap/check/preservation subproofs.
Pointer-bearing writes additionally need provenance-support evidence.
Nested safe/raw scopes and allocation lifecycle proofs still require library
authority work; their current failures are not evidence of an unavoidable
client proof burden. No before/after proof-time benchmark has been performed.

From `backends/lean`:

```
lake build Aeneas.Std.HeapTests Aeneas.Std.Core.PtrOps \
  Aeneas.Std.Core.PtrMovement Aeneas.Std.Alloc.Boxed Aeneas.Std.Heap.Access \
  Aeneas.Std.Heap.PointerMovement Aeneas.Std.Heap.EffectSpecs
```

This command passes. The actual default backend `lake build` also
passes, without removing targets or adding axioms or sorry proofs.
That build does not validate every source file or the separate extracted-test
project.

The extracted `RawReadWriteRead` example now has restored framed proofs of both
corrected functions, directly alongside those functions, with exact standard-axiom
guards. From `tests/lean`, `lake build RawReadWriteRead` passes.
Its arbitrary-descriptor theorem requires the descriptor-calibration fact that
the scalar write cannot encode pointer payloads, in addition to positive size.
The little-endian word and pair descriptors in `RawBoxProofs` have also been
migrated and checked independently; that is not a successful build of its
remaining lifecycle proofs.

**Backward-resource restoration/cleanup authority and the rest of the extracted
example series remain migration work.** Nonempty range restoration has an honest
state-specific enabledness premise, not a resource-only backward contract.
An unconditional restoration contract from borrowed cells alone would be false
in the presence of arbitrary overlapping views.
No target was removed to obtain the passing build.
Bounded ID capacity is not placement feasibility,
and cleanup ownership is not absence of other live views.
The extracted RawBox/RawPointerOps/RawTransmute/RawValueCasts/DoublyLinked proof
series still fails to build against these new contracts.
The latest combined build fails first in `RawBoxProofs`, `RawBoxManual`, and
`DoublyLinked.RawProperties`. The external `borrow_four` wrapper now uses the
matching backward primitive, but its module depends on failing `RawBoxProofs`
and therefore has not been validated end-to-end.
