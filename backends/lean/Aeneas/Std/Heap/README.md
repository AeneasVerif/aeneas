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
that it decodes to the requested value. Rust-facing relational adapters choose
any such encoding, justified by completeness. This does not assert a finite
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
`select` and `update` operate on footprint `[i * size, (i + 1) * size)`.
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

`RawPtr T` contains a bounded `Usize` base identifier and a bounded `Usize` index
counted in `T` entries. The phantom type contributes no runtime metadata.
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

Access requires the requested alignment to divide the block's guarantee. The
aligned stride then suffices for typed displacement. `modify` commits a
length-preserving transformation only on success. Range operations transform
all selected footprints before committing once: failure exposes no partial update.
Empty ranges still require a live aligned base and an in-bounds position.

`freeBlock` requires index zero, the matching owned flag, alignment, **exact**
byte coverage, and depth-zero permissions throughout. It cannot hide protected
trailing bytes through floor division. Shared-exposure cleanup instead requires
`owned = false` and depth one throughout.

`offset` takes an `Int` displacement. Both endpoints must lie in the typed extent,
including one-past, and the result must fit `Usize`. Movement before the beginning
is rejected, not truncated. Extent requires a live aligned base, but not readable
contents. Rust `add` and `offset` use this checked operation.

Physical pointer equality, pointer-integer conversions, usable cross-type cast
wrappers, unaligned access, and arbitrary byte-offset pointers are not provided.
Different descriptors can inspect a common base directly in model examples;
that alone does not implement Rust's cast API.

## Rust boundary and Boxes

`Std/Heap.lean` contains relational adapters around the executable operations;
`Core/Ptr.lean`, `Alloc/Boxed.lean`, and slice wrappers supply Rust-facing effects.
Descriptors are passed explicitly, not found through a typeclass or global map.
Safe borrow boundaries read typed values before transferring byte permissions.

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
| `Lemmas.lean` | Concrete traversal, byte selection/update, read-back, disjoint access, map and invariant laws |
| `Separation.lean` | Byte/cleanup resources, matching, separation algebra, framed relational triples |
| `Resources.lean` | Byte fragments, encoded `pointsTo`, splitting, matching, and update framing |
| `Specs.lean` | Generic footprint-update rule and framed read/write contracts |
| `Allocation.lean` | Capacity, freshness, allocation resources, frame preservation, exact cleanup |
| `Borrowing.lean` | Single-footprint borrow/share/restoration and checked movement contracts |
| `Access.lean` | Byte-based read/write/cleanup denial, including overlapping different types |
| `Effects.lean` | Total-correctness interpretation of actual `Result` effects and composition rules |
| `EffectSpecs.lean` | Rust read/write, movement, Box and mutable-exposure allocation/cleanup contracts |

Cell resources claim individual byte positions and an alignment guarantee.
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
`Borrowing.lean` currently proves single-footprint permission transfer.
Do not treat a successful backend build as evidence of those missing contracts.

Integration proofs cover Box round-trip, stored pointers, corrected alias and
repeated-read examples, and a handwritten borrowed-Box/callback prototype.
Descriptors are explicit parameters, including a separate descriptor for stored
pointers; pointers are not assumed to fit in one word. The callback contract
accepts any subsequently written value and consumes the exposure resources.
Pair and one-past fixtures type-check but do not yet have end-to-end proofs.
A true zero-sized descriptor cannot satisfy a read-success theorem here.

The fixture headers mark manual descriptor adaptations and repeated-read repairs.
The compiler was not changed or rerun; re-extraction would overwrite those edits.
See `tests/lean/EXTRACTION.md` for the recorded extraction provenance.

## Checks

From `backends/lean`:

```sh
lake build Aeneas.Std.HeapTests
lake build
```

From the repository root, without re-extraction:

```sh
make verify-raw-box
```

`HeapTests.lean` exercises lifecycle and cleanup, uninitialized borrow/restoration,
mixed sharing, cross-type byte protection, alignment, atomic range failure,
signed/one-past movement, finite allocation exhaustion, empty footprints, and the
privileged-restoration boundary.
