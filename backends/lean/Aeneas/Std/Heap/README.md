# Concrete addresses and provenance for Aeneas (prototype)

This replaces the byte model inspired by
[AeneasVerif/aeneas#1433](https://github.com/AeneasVerif/aeneas/pull/1433).
It is a design experiment, not a refinement proof of Rust or an automatically
integrated extraction pipeline.

## Assurance coverage

The following evidence is deliberately layered. Generic contracts are
kernel-checked and guarded against additional axioms; finite regression
theorems use `native_decide` and are not dependencies of those contracts.
Rust/Miri tests check valid executions of the companion fixtures, not a
refinement between Rust and this prototype.

| Milestone | Evidence | Boundary |
|---|---|---|
| Whole clients | `RawMemoryViews/ProvenanceScoped.lean` proves allocation, initialization, physical free, stack exposure, pointer-byte copy and both returns. `RawZmijMwe/Reuse.lean` proves two formatter calls with exact snapshots and statically sized final storage. | Handwritten models. Allocator outcome/placements are ghost parameters. Formatter address stability remains an explicit specialization/hypothesis. The first Rust slice must be copied before reborrowing. |
| Successful executions | `Execution.lean` defines `HeapWP.Runs` directly over `Result` effects; `Runs.post` links it to universal WP. Client witnesses execute the real formatter, full deallocation/copy wrapper, owning-cell destructor client and list constructor. | Finite witnesses establish existence, not success for every placement. The formatter witness is one call; repeated calls also have a universal contract and a separate seven-call heap trace. |
| Composable returns | `ScopedView.lean`: transitive `ClosedViews` and `RootReturn.after_closed_views` allow multiple fresh scopes and byte changes to old allocations. `HeapAssuranceTests.siblingScopes` exercises disjoint siblings, a shared child, an empty range and an unrelated write. | Return authority is a proved precondition, not implied by borrowed cells alone. Frame preservation and heap invariants are separate obligations. Raw operations do not dynamically authenticate a loan tree. |
| Representation boundaries | Genuine ignored padding and partial initialization/copy, all 256 Bool bytes, all 256 numeric padding replacements, ZST lifecycle, and pointer-lane corruption/loan rejection. | Single ZST accesses and mutable U8 loans across pointer lanes are valid Rust patterns but unsupported. Invalid Bool/value-byte reads are rejected; unsupported does not mean Rust UB. |
| Concrete ownership | `DoublyLinked/ConcreteLayout.lean` supplies a 24-byte, alignment-8 descriptor and `NodeLayout` proof. `RawMemoryViews/Ownership.lean` proves one destructor observation and physical reclamation with arbitrary frames. | Node calibration is 64-bit little-endian `repr(C)`, checked by Rust layout tests. Non-Copy/once-only ownership is enforced by the Rust API, not linear Lean types. Forget/abort paths do not promise cleanup. |

`HeapAssuranceTests` is part of the default backend build; the client root
modules import their new contracts and actual-computation witnesses. The paired
Rust cases are in `raw_memory_views.rs`, `raw_zmij_mwe.rs` and `doubly_linked/`.
See `tests/lean/EXTRACTION.md` for reproduction and correspondence assumptions.

### Supported, unsupported, and invalid are distinct

An uninitialized padding byte can be ignored by a typed decoder and copied as
raw storage, but cannot be read as a `u8`. Uninitialized value-bearing bytes
cannot be decoded. `no_exact_uninit_decoder` demonstrates why a decoder that
distinguishes uninitialized storage from its initialized replacement conflicts
with `decode_mono`; raw snapshots are the supported alternative.

The node codec leaves bytes 20--23 as genuine padding, not a hidden initialized
array element. Its canonical write encoding leaves them uninitialized; decoding
ignores them. Its initial null links use the existing symbolic pointer payload
`(provenance = 0, address = 0)`. First allocation issues record 0 before validating
its bytes, so this representation is constructively usable even from an empty
heap. Address-zero reads still fail. This is not a general provenance-free
pointer or integer-to-pointer conversion rule.

The mutable pointer-byte Rust regression separates a read-only use of `&mut u8`
from writing back the same numeric byte. Only the former subsequently
dereferences the original pointer. A pure returned U8 cannot distinguish those
histories, so the current mutable-loan boundary conservatively rejects both.

Nonempty duplicate returns, repeated exposure retirement, and parent cleanup
with a live child are rejected in the tested scenarios. This does **not** make
arbitrary low-level `endBorrow` calls safe: `HeapTests` retains a raw-operation
trace that prematurely restores a parent when a child is itself suspended.
This is not a counterexample to the scoped callback contracts: the child remains
an active view, so the parent's `RootReturn` authority is unavailable.
Empty-range returns carry no consumable byte permission and may be repeatable
no-ops. Client proofs must establish each callback's current-state preconditions;
they do not assume an additional unchecked stack discipline.

## The implicit safe heap

Safe Rust holds an **unknown implicit part of the heap**. An absent explicit
permission does not mean that the physical byte or allocation is absent.
Safe allocation, aliasing, and return authority are abstract boundary assumptions,
relying on what safe Rust promises; this model does not enumerate safe memory.

The separation assertion `empty h` means `h = ∅`: the computation's **owned
explicit footprint** is empty, not that the whole heap is empty. `HeapWP.Triple`
implicitly quantifies over arbitrary disjoint frames and preserves them.
Consequently, a safe wrapper that exposes and then retires its raw view can
have precondition `empty` and postcondition `result = expected ∧ empty h`,
without explicit heap, frame, or resource-matching parameters. `HeapWP.frame`
adds a caller's assertion to such a contract.

`Heap/Step.lean` registers `HeapWP.Triple` directly with the existing `step`
tactic. Heap contracts are not duplicated as pure specifications. Existing
pure `WP.spec` contracts can be lifted while preserving the owned fragment;
OOM keeps its accepted-abort semantics. `step with` selects a heap contract,
and `step*` also handles intervening pure arithmetic. Nontrivial separation
rearrangements and framing remain explicit rather than an implicit heap solver.

Reusable range and exposure support lives in the backend, not in `RawScale`:
`RangeAccess.lean` handles indexed reads and address bounds;
`RangeWrite.lean` focuses and reassembles single or paired ranges;
`SharedExposure.lean` handles singleton shared exposures;
`SliceExposure.lean` handles whole-slice allocation and matching returns,
including empty slices. Cleanup ownership establishes empty-view liveness.
Exclusive range exposure requires encoding calibration, just like its singleton
counterpart. The read-back and mutable-return contracts require positive element
size, but not positive element count. `Notation.lean` provides the scoped
heap-triple syntax.

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

`core.ptr.from_ref repr value` returns a raw pointer and a `Result Unit`
backward computation capturing that pointer and the original value. Executing
it checks the original value and retires the shared exposure.
`core.ptr.from_mut repr value` instead returns a pointer and a `Result T`
backward computation that reads the updated value and retires the exclusive
exposure. Translated callers execute the matching callbacks when the borrows
end; obtaining a callback alone does not run it.

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
one-past, and rejects overflow before constructing a new Usize. It requires the
allocation root to remain alive, but does not require the access view to remain
active: returning a temporary view removes access permissions, not the retained
allocation identity or bounds. Reads and writes still require active views.
`distance` recognizes a common root
across distinct views; equal numerical addresses alone do not prove provenance.
`ptrEq` compares numerical addresses, not ghost records.

Retirement keeps immutable view metadata but contributes no permissions.
Root death separately disables all views of that allocation.
Consequently a dangling pointer can still be stored, loaded, and numerically
observed directly from the pointer value. Numerical equality does not require
either view to be live or even present. Reusing an address creates a new root;
it cannot revive the old view, and numerical observation grants no access.

For nonempty views whose allocation roots are still alive, equal **start**
addresses imply overlapping storage, so `Heap.Inv.same_root_of_overlap` derives
common root identity. `HeapWP.offset_from_reexposed.spec` uses an explicit
start-address equality hypothesis to prove the exact byte distance from a
writer's end cursor to a newly exposed start, even after the writer's view
retires. This is not a general equal-address/provenance axiom: dead allocations
and equal one-past/start addresses of adjacent allocations do not qualify.
Independent safe-to-raw conversions still do not guarantee this start-address
equality; source-place tracking remains a separate translation boundary.

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
through `Result.allocatingModify` for allocation/exposure and
`Result.checkedModify` for accesses and returns. The demonic interpretation admits every
compatible witness; choosing an incompatible padding encoding first cannot
cause spurious intermediate failure.

The heap WP is universal: every permitted successor must satisfy the
continuation, without requiring that a placement exists. If allocation or
exposure has no successor, `allocatingModify` reports `Result.oom`
(`fail Error.oom`). Both ordinary `WP.spec` and `HeapWP.Spec` accept OOM as
an abort, without a return value or continuation. Thus `Box::into_raw` and
borrowed `to_raw` contracts no longer require placement-feasibility premises.
Fresh Nat IDs cannot exhaust cumulatively; finite addresses or compatibility
can still prevent placement. This abstract OOM allowance is not a claim that
Rust's pointer conversion invokes an allocator.

In contrast, disabled `checkedModify` operations produce `fail Error.undef`,
which the WP rejects. Reads, writes, borrowing, returns, and `Result.require`
still require their safety conditions. Panics and other errors remain rejected,
as does divergence by `WP.spec` and `HeapWP.Spec`; the separate partial
`WP.dspec` retains its existing divergence allowance. Failure preserves the
input heap of that operation, not earlier states: there is no rollback.

An accepted specification alone no longer implies successful-return existence
or the excluded-miracle law: OOM satisfies even a false success postcondition.
`WP.spec_exists` therefore requires an explicit no-OOM premise. Client proofs
can use `HeapWP.Spec.of_spec`, `Spec.bind`, and `Spec.pure` without
`unseal Result`; the implementation stays opaque. Use `bind_ok` for `Std.bind`,
or normalize typeclass bind with `bind_tc_eq` when refolding code.

Safe `Box<T>` is still represented by pure `T`, without a place identity.
`into_raw` materializes an owned record; `from_raw` reads it and calls
`returnOwned`, not physical `dealloc`. Safe Rust retains ownership afterward.
The core supports re-exposure of a **known** root, but these functional wrappers
cannot connect repeated conversions of the same unmoved Box to that identity.
They may choose a different address. Retaining an old pointer's address does
not fix that address-history overapproximation.

The low-level evaluator and the scoped proof interface have different roles.
Raw restoration checks borrowed cells and heap compatibility, not a dynamic
loan tree. It can restore a parent while a child view is itself borrowed.
Scoped contracts instead require current-state return authority: the
`RootReturn` rule excludes every other active view of that root, including
suspended ones. Captured-state callback contracts likewise cannot simply be
reused after intervening effects; their preservation must be proved.
The regression demonstrates evaluator permissiveness, not a failure of these
contracts. Rust-to-model correspondence must justify the generated callbacks;
capability-respecting client proofs do not need a separate stack-order axiom.

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

`SupportsValue` accepts provenance metadata from either a resource for the
referenced view or an existing stored pointer lane. The latter covers pointers
to retired views: copying a dangling pointer need not access its former target.
`write_local.spec` and `write_pointsTo_local.spec` use the complete local
footprint, including the overwritten value, without depending on an arbitrary
external frame. The linked-list examples derive this evidence from their own
nodes and stored links. Pointer-free clients need only the footprint and a
positive representation size.

Low-level `writeAt.spec` retains the exact input-state/check interface.
Restoration to writer permission still uses state-specific checked contracts:
reintroducing a writer can conflict with another logically separated view.
Matching forward/backward contracts capture authority at the exact
forward-produced state; borrowed-cell ownership alone is deliberately not
treated as sufficient. Lexical `RootTriple` scopes retain whole-root return
authority through byte operations and retirement, with their own frame rule.
An empty root scope gives an ordinary framed `Triple` via `RootTriple.toTriple`.

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
for range returns. `borrowRange_return.spec` captures the original exclusive
footprint and derives enabledness for every pointer-free replacement vector,
without a client-supplied compatible-return witness. The corresponding shared
return contract likewise captures the matching forward state. General
standalone restoration remains a low-level state-specific boundary.
Empty transfers preserve the heap.

`PointerOps.lean` provides uniform replacement, unaligned access, and atomic
snapshot-swap contracts. Swapping two exclusive footprints derives physical
disjointness from the invariant inside the library, including for different
views. Self-swap needs just one footprint. Neither variant decodes or re-encodes
the snapshots, so initialization and pointer lanes are preserved.

`Allocation.lean` proves fresh-view creation and whole-view retirement with
arbitrary matching frames. Retirement now derives invariant preservation without
a client-side final check. `RootReturn` records exact root coverage and alias absence.
Owned conversion produces it, and `RootTriple` carries it through the Box and
owning-list lifecycles; cleanup layout resources alone do not supply it.
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
For an exclusive exposure, `newBlock_exposure_carries` proves that external
readable views cannot supply extra pointer lanes: they would conflict with the
new writer. `allocExposure_encoded.spec` combines this fact with a static
descriptor calibration law to obtain an admissible representation, rather than
assuming every numerically readable value is writable. The array callback
example uses this distinction to recover all four updated bytes as a safe word.
Allocation covers every permitted successor and accepts OOM if none exists.
`RawPtr.borrowWithBack` now pairs a raw-to-safe borrow with
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
A subsequent independent read-only review of the restored Box, range, array,
pointer-support and full linked-list proofs found no significant issues. It
confirmed the remaining nested re-exposure protocol, pointer-free returned-value
restriction, concrete node-layout calibration and extraction-coverage limits
described here.

For ordinary clients, the finer model adds descriptor calibration and, for
interior views, concrete-base arguments, but not overlap/check/preservation
subproofs. Pointer-bearing writes additionally need local provenance evidence.
Linked-list helpers infer it from stored links; full-node assertions use the
node's address as the view base. `NodeLayout` is an explicit static calibration
of an arbitrary node descriptor, not a new layout axiom or a supplied concrete
Rust ABI descriptor. The safe list's `ListState` hides its node addresses,
length invariant and root return authority. Its API contracts specify complete
payload sequences for construction, push, pop, front/back, clear and drop.
All five raw insert/remove alias cases and the finite-chain proofs are retained.
No before/after proof-time benchmark has been performed.

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
The entire existing example series now passes, from `tests/lean`:

```
lake build RawBox RawBoxProofs RawBoxManual RawReadWriteRead RawTransmute \
  RawValueCasts RawTransmuteExternals RawPointerOps DoublyLinked
```

This includes Box lifecycles, matching borrowed/shared callbacks, range fill
and return, scalar casts, the complete array callback and safe owning lists.
Applicable exact axiom guards admit only the standard Lean logical axioms.
No targets, cases or functional postconditions were removed to obtain this build.
Actual zero-sized raw reads remain deliberately disabled.

**Remaining scope:** the newer heap-uninitialized, eight-u16/sixteen-u8,
pointer-as-integer and nested boxed-slice Rust scenarios are native tests in
`tests/src/raw_pointer_ops.rs`; their twelve-test suite passes. These four
additions are under `cfg(test)`, so they are not extracted Lean client proofs.
The heap-level `nestedSlices` regression covers shrinking views and restoration,
but is not a replacement for a framed theorem for the Rust safe/raw callback
chain. Matching callback contracts currently apply at the forward-produced
state; threading their authority through nested re-exposures and child
retirement still requires a general library protocol. Retired records remain in
the state, so returning a child does not literally restore the parent's saved
state. Neither unconditional borrowed-cell restoration nor another heap-check
premise in the client solves that missing abstraction.

No adapted fixture was overwritten by regeneration. An isolated extraction
attempt with the restored pinned Charon and rebuilt compiler produced LLBC for
the four newer scenarios, but Lean translation still failed: safe-place raw
borrowing is unsupported, and const/mut pointer reads clash under `RawPtr.read`.
The generated partial files are not proof coverage; see `tests/lean/EXTRACTION.md`.
Bounded ID capacity is not placement feasibility, and cleanup ownership is not
absence of other live views.
