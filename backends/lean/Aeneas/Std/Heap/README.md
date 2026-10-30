# Concrete byte memory for Aeneas (WIP)

An experiment based on
[AeneasVerif/aeneas#1433](https://github.com/AeneasVerif/aeneas/pull/1433).
It is a design-feedback model, not a refinement proof of Rust's operational
semantics or a completed extraction pipeline.

## Runtime core: two files

`Repr.lean` defines byte representations and permission updates. `Model.lean`
defines pointers, blocks, the heap, and executable heap operations. There is no
`Types.lean`, abstract `Block`, global representation lookup, or representation
axiom file.

### Representations and permissions (`Repr.lean`)

An explicit `Repr T` supplies `size`, `align`, partial `decode`, a proof that
alignment divides size, and completeness: every `T` has some decoding byte vector.
Alignment is a positive power of two. Size includes padding and is the array
stride; zero size is allowed. These parameters must be calibrated separately to
the Rust type and target.

There is no canonical encoder. Executable writes receive an encoding and a proof
that it decodes to the requested value. `Repr.choose repr value`, defined in
`Std/Primitives.lean`, is the monadic operation supplying both: its result is
`{ bytes : Vector U8 repr.size // repr.decode bytes = some value }`.
It changes no heap state. Its total-correctness contract is proved from
`repr.complete`; its demonic WP quantifies over **every** encoding satisfying
the decode-back equation, not just the witness used in `complete`.
`chooseList` does the same for a list of values using that descriptor.
Neither operation chooses the descriptor itself or introduces an axiom.
This does not assert a finite
encoding for arbitrary Lean types: supplying a representation is an obligation.
In particular, an infinite type such as `Nat` cannot have this representation.

The only permission-bearing cell type is
`Cell T = shared depth (Option T) | borrowed`. Actual storage contains `Cell U8`.

| Byte cell | Read | Raw write |
|---|---|---|
| `shared 0 (some byte)` | Yes | Yes |
| `shared (depth + 1) (some byte)` | Yes | No |
| `shared 0 none` | No | Yes |
| `shared (depth + 1) none` | No | No |
| `borrowed` | No | No |

`create` expands encoded cells into byte cells, preserving their permissions.
`select` and `update` take a byte offset `i` and operate on `[i, i + size)`.
`read` collects readable initialized bytes, then decodes them. Their sharing
depths need not agree. `write` checks every byte's write permission before
replacing the footprint. Invalid typed contents can therefore be overwritten.

`borrow`, `share`, and `endShare` change permissions, not typed values.
Borrowing can transfer uninitialized writable bytes. `endBorrow` restores
initialized encoded bytes. All updates preserve the surrounding bytes and length.
An empty footprint cannot authorize an observation or single-cell mutation:
these operations reject zero-sized representations.

There is no extra typed-validity metadata or automatic pointer invalidation.
Overlapping access is governed by the same byte permissions at every type.
Whether readable bytes decode as another type is determined by that type's
descriptor; neither decoding success nor failure is universally promised.
Padding must currently be initialized to read the whole footprint.
`MaybeUninit` and `UnsafeCell` are not modeled.

### Heap and pointers (`Model.lean`)

`RawPtr T` contains a bounded `Usize` base identifier and a bounded `Usize`
`byteOffset`, independent of `T` and its descriptor. The phantom type contributes
no runtime metadata. Offset one can therefore represent a misaligned `u32`
pointer without pretending it points to the second `u32`.
`MutRawPtr` and `ConstRawPtr` abbreviate the same type; changing constness does
not grant permissions.

`Block` stores a byte-cell list, a guaranteed base alignment, and an `owned` flag.
`Heap` stores one map from bases to optional blocks and the next fresh base.
Absence means no live allocation or exposure. Identifiers are never reused;
they are model identities, not physical addresses.

`alloc` creates uninitialized depth-zero bytes using `Repr.create`. `newBlock`
creates supplied encodings at depth zero; `newSharedExposure` starts at depth one.
The latter two also use `create`. Empty allocations still have an identity and
cleanup authority. Allocation checks byte length, counter capacity, and vacancy
of the next slot. The greatest base identifier is an exhausted-counter sentinel.
`Heap.Inv` requires every slot at or above the counter to be absent.

Access requires the requested alignment to divide both the block's guarantee
and the pointer's byte offset. Single and range reads, writes, and permission
transfers use these checks uniformly. `modify` commits a
length-preserving transformation only on success. Range operations transform
all selected footprints before committing once: failure exposes no partial update.
Empty ranges still require a live aligned base, an aligned offset, and an
in-bounds position. Element `i` of a range starts at `byteOffset + i * size`.

`freeBlock` requires byte offset zero, the matching owned flag, alignment, **exact**
byte coverage, and depth-zero permissions throughout. It cannot hide protected
trailing bytes through floor division. Shared-exposure cleanup instead requires
`owned = false` and depth one throughout.

`offset` takes an `Int` displacement in typed elements and computes
`byteOffset + displacement * size`. Both byte endpoints must lie in the live
block, including one-past, and the result must fit `Usize`. Movement before the
beginning is rejected, not truncated. Forming a pointer does not require
alignment or readable contents. Rust `add` and `offset` use this checked operation.

`RawPtr.cast U p` preserves the base and byte offset exactly. It needs no
descriptor and performs no access checks; casting back restores the original
pointer, even at nonzero or misaligned offsets. It changes no bytes or permissions
and assumes no equation between source and target decoders. This pure helper is
used by manual transmute examples and explicit external models, not inserted by
the compiler. The legacy `cast_scalar` wrapper still fails. Physical pointer equality, pointer-integer
conversions, and unaligned-access operations are not provided.

## Rust boundary and Boxes

`Std/Heap.lean` contains relational adapters around the executable operations;
`Core/Ptr.lean`, `Alloc/Boxed.lean`, and slice wrappers supply Rust-facing effects.
Descriptors are passed explicitly, not found through a typeclass or global map.
Write, Box allocation, raw exposure, and borrow restoration call `choose` or
`chooseList` internally before committing their executable heap operation.
Translated callers do not supply encoding bytes or decode-back proofs. The
explicit descriptor arguments in the current fixtures are still manual
adaptations; they are not emitted by the compiler.
Safe borrow boundaries read typed values before transferring byte permissions.

Heap wrappers use `Result.checkedModify`, a common failure boundary around their
relations. `State.checked` returns a successful answer exactly when the original
relation permits it; if no successor exists, its only answer is `none` at the
unchanged input heap. The continuation maps `none` to `.fail .undef`. Permission,
alignment, bounds, decoding, and allocation failures therefore explicitly fail
rather than leaving a disabled heap request. Earlier successful operations are
not rolled back. This is logical totalization, not an executable decision
procedure for arbitrary relations. Encoding choice remains on `guardedModify`,
with enabling established by completeness.

Safe `Box<T>` values remain represented by `T`. `Box.into_raw` creates a one-value
owned block. `Box.from_raw` reads and removes that entire allocation; it cannot
recover an independently owned Box from an interior field.

A raw exposure is different: it temporarily puts a safe place into explicit
storage with `owned = false`. Its matching backward computation reads the
updated value and removes the exposure. Removing it does not deallocate the
underlying Rust Box. Cleanup authority and byte access permissions are separate.

Restoration is privileged to the matching translated backward continuation.
The heap does not authenticate continuation identity, lifetime, or restoration
type. Arbitrary direct Lean calls to `endShare` or `endBorrow` are not authorized
Rust programs. `HeapTests.restoration_is_privileged` demonstrates this boundary.

## Proof files

| File | Responsibility |
|---|---|
| `Lemmas.lean` | Concrete traversal, byte selection/update, read-back, singleton-range bridges, disjoint access, map and invariant laws |
| `Separation.lean` | Byte/cleanup resources, matching, separation algebra, framed relational triples |
| `Resources.lean` | Byte fragments, encoded `pointsTo`, splitting, matching, and update framing |
| `Specs.lean` | Generic footprint-update rule and framed read/write contracts, including writing any chosen valid encoding |
| `Allocation.lean` | Capacity, freshness, allocation resources, frame preservation, exact cleanup |
| `Borrowing.lean` | Single-footprint byte and typed borrow/share/restoration, and checked movement contracts |
| `Access.lean` | Byte-based read/write/cleanup denial, including overlapping different types |
| `Effects.lean` | Total-correctness interpretation of actual `Result` effects, exact demonic choice contracts, and composition rules |
| `EffectSpecs.lean` | Rust read/write, singleton-range access/permission transfer, movement, Box and mutable-exposure allocation/cleanup contracts |

Cell resources claim individual byte positions and an alignment guarantee.
Typed `block` and `pointsTo` assertions additionally require the pointer offset
to satisfy the descriptor's alignment.
Compatibility is byte-disjointness, independent of the originating type.
Cleanup resources separately record exact byte length, alignment, and ownership.
Fragments can therefore frame differently typed, disjoint footprints at one base.
Shared cells are not duplicable resources.

Triples require an enabled transition and correctness of every successor,
preserving arbitrary matching disjoint frames. `HeapWP.Spec` interprets actual
`Result` computations using interaction-tree `DWP`; it rejects failure,
divergence, and disabled effects. Ordinary effect-free WP is unchanged.

**Finite allocation needs capacity.** Allocation contracts use `HeapWP.Spec` at
the actual input heap, with explicit counter/size bounds. An unconditional framed
allocation triple from `emp` would be false at an exhausted heap. Local access,
permission transfer, movement, and cleanup retain ordinary framed triples.

The concrete heap proof chain and integration proofs introduce no memory-model
axioms or `sorry`; the integration guards allow only `propext`,
`Classical.choice`, and `Quot.sound`. This proves properties of this model, not
its correspondence with Rust or the correctness of its compiler adaptations.

### Coverage boundaries

Range operations are executable and regression-tested, but their former
general range-level separation/effect contracts have not yet been ported.
`Borrowing.lean` proves single-footprint permission transfer; `EffectSpecs.lean`
lifts it to `borrow`, `endBorrow`, and singleton `readRange`, `borrowRange`,
`endBorrowRange`, `shareRange`, and `endShareRange`.
Do not treat a successful backend build as evidence of those missing contracts.

Integration proofs cover Box round-trip, stored pointers, corrected alias and
repeated-read examples, pair replacement, one-past pointer formation, and
manually adapted scalar and pair borrowed-Box examples.
Descriptors are explicit parameters, including a separate descriptor for stored
pointers; pointers are not assumed to fit in one word. The callback contract
accepts any subsequently written value and consumes the exposure resources.
The local borrowed conversion is named `to_raw`, not the consuming `into_raw`.
Each caller invokes the backward function before dereferencing the safe Box
again. The scalar and pair examples have matching Rust source in `raw_box.rs`;
their callback adaptations are handwritten, not compiler-generated.
`RawBoxProofs.lean` also supplies complete little-endian `u32` and paired-`u32`
descriptors and instantiates the round-trip, pair, and one-past proofs with them.
These are concrete model encodings, not a proof of Rust tuple layout or ABI.
A true zero-sized descriptor cannot satisfy a read-success theorem here.

`RawBoxManual.lean` additionally verifies model-API compositions, not Rust
translations: nested sharing with const-pointer range reads, exclusive
borrow/update/restoration, and their composition at the same pointer. Their
contracts preserve arbitrary matching frames and identify every returned value.

The transmute-specific design, pitfalls, bytemuck/zerocopy comparison, and
Rust-to-Lean example map are documented separately in [TRANSMUTE.md](TRANSMUTE.md).
The proved examples cover thin raw-pointer round trips, exact by-value
representation conversions, and the safe mutable word/byte-array view.
The document distinguishes model proofs from ABI calibration, handwritten
external models, and manual extraction adaptations.

`DoublyLinked/` provides separate raw and safe doubly-linked-list APIs:

| Layer | Rust | Lean implementation | Contracts |
|---|---|---|---|
| Raw intrusive sentinel ring | [raw.rs](../../../../../tests/src/doubly_linked/raw.rs) | [Raw.lean](../../../../../tests/lean/DoublyLinked/Raw.lean) | [RawProperties.lean](../../../../../tests/lean/DoublyLinked/RawProperties.lean), [ListProperties.lean](../../../../../tests/lean/DoublyLinked/ListProperties.lean) |
| Safe owning list | [safe.rs](../../../../../tests/src/doubly_linked/safe.rs) | [Safe.lean](../../../../../tests/lean/DoublyLinked/Safe.lean) | [Ownership.lean](../../../../../tests/lean/DoublyLinked/Ownership.lean), [SafeProperties.lean](../../../../../tests/lean/DoublyLinked/SafeProperties.lean) |

The [Rust entry point](../../../../../tests/src/doubly_linked.rs) includes both
APIs in one crate namespace, preserving the `crate::ext` extraction boundary.
[tests.rs](../../../../../tests/src/doubly_linked/tests.rs) keeps raw-ring tests
separate from the safe-only client test. `DoublyLinked/Funs.lean` is an import
aggregator for the two factored Lean APIs, not a second set of definitions.
Nodes store actual raw `prev` and
`next` pointers and a `u32` payload. Two opaque primitives perform whole-node
reads and writes; the link operations remain transparent Rust.
`RawProperties.lean` proves exact framed contracts for link setters, insertion
between distinct neighbours, insertion into an empty ring, unlinking between
distinct neighbours, removing the last node, and removing an already detached
node. The last two cases handle neighbour aliasing without assuming three
distinct allocations. `ListProperties.lean` defines ownership of every link and
payload in a finite ring and proves insertion at the sentinel implements list
cons; removal of the first node returns that exact pointer, leaves it detached,
and preserves the remaining sequence. Both contracts cover arbitrary finite
lengths and preserve arbitrary disjoint matching frames by the generic heap-WP
frame rule.

This list milestone has two explicit manual translation adaptations. The
generated recursive `Node` containing `RawPtr Node` is rejected by Lean's
positivity checker; its stored pointer phantom tags are erased to `Unit` and
restored in `Node.mk`/accessors, preserving both base and byte offset. The
constructor/accessor round trip is proved. Callers also thread an explicit
`Repr Node` through the external models. These contracts are parametric
in a positive-sized complete descriptor, including its stored-pointer encoding;
no concrete `Repr Node` is instantiated, and no Rust node ABI or pointer
representation is proved. The generated function file is also manually
factored into `Raw.lean` and `Safe.lean`; its bodies and control flow are
unchanged apart from the descriptor arguments. Re-extraction overwrites the
type repair and function aggregator, requiring both adaptations and factoring
to be replayed as documented in `tests/lean/EXTRACTION.md`.
Neither Charon nor the shared Aeneas compiler was
changed.

The same fixture now supplies a safe owning `LinkedList` with private root and
length fields. `new`, `len`, `is_empty`, `front`, `back`, `push_front`, `pop_front`,
`clear`, and `Drop` have proved contracts in `SafeProperties.lean`. Their public
state assertion includes the deterministic heap observation
`self.toList repr heap = some values`: push implements cons, pop returns
head/tail, front/back return the first/last payload, and clear produces `[]`.
`Ownership.lean` tracks cleanup authority for every payload node and the
sentinel as well as the exact ring and length. Pop reclaims its detached node;
total clear releases payload nodes, and Drop consumes the remaining sentinel
through the concrete Box model. Its public post preserves the external frame
and heap invariant, not an explicit whole-heap allocation-map difference.
Two additional opaque wrappers provide Box allocation and reclamation.
Heap-counter/descriptor-size capacity is explicit for allocation, as is checked
length capacity for push. No automatic lifetime analysis or Rust ABI refinement
is claimed; these are proofs about the documented adapted extraction.

The lower-level intrusive interface still accepts caller-provided stable
storage and unlinks without freeing it. `init.spec` covers initialized writable
storage, which the owning wrapper's allocator supplies; initializing arbitrary
uninitialized storage has no list-specific contract yet. Native tests check
both traversal directions, all 36 pairs of three-node insertion/removal orders,
detached-node idempotence, an untouched neighbouring canary, and a safe-only
sequence comparison including moves, clear/reuse, and nonempty destruction.
All four tests also pass with address/leak sanitization. Exact axiom guards
on the local/global ring contracts, all public safe contracts, and the heap
observation bridge allow only `propext`, `Classical.choice`, and `Quot.sound`.

## Checks

From `backends/lean`:

```sh
lake build Aeneas.Std.HeapTests
lake build
```

From the repository root, without re-extraction:

```sh
make verify-raw-box
make verify-doubly-linked
```

`HeapTests.lean` exercises lifecycle and cleanup, uninitialized borrow/restoration,
mixed sharing, cross-type byte protection, alignment, atomic range failure,
signed/one-past movement, finite allocation exhaustion, empty footprints, and the
privileged-restoration boundary.
It also checks that monadic choice preserves the heap and leaves an ignored
encoding byte genuinely unconstrained. Failure observations inspect the actual
read request: permission denial and invalid typed contents force its continuation
to `.fail .undef` and preserve the failed operation's input heap.
