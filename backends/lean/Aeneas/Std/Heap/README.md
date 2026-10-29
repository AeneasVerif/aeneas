# Instrumented Byte Memory for Aeneas (WIP)

An experiment based on
[AeneasVerif/aeneas#1433](https://github.com/AeneasVerif/aeneas/pull/1433).
This is a design-feedback model, not a complete formalization of Rust memory.

## Core design

`Heap Block` maps fresh base identifiers to optional allocation entries.
Each entry contains instrumented storage, its guaranteed base alignment, and an
owned-allocation flag. Absence means there is no live allocation or exposure.
The `cells`, `alignment`, and `allocated` accessors are derived from this one map.
Cleanup authority is separate from permissions to access cells. Identifiers are
never reused; they are model identities, not physical addresses.

There is no `Layout` record. `Block` is abstract, and `Block.bytes` projects its
canonical instrumented bytes as `List (Cell U8)`. This is the same
`U8` used by extracted Rust code: `Scalar/Types.lean` defines the unsigned scalar
types without importing effectful operations. The model does not expose how
permissions or typed-validity flags are stored.

`RawPtr T` contains a base and a natural `index`, counted in `T` cells. Cell `i`
has byte footprint `[i * size T, (i + 1) * size T)`. Thus index
equality across types says nothing about overlap. The permission system is
independent of pointer constness: casting a shared pointer to mutable does not
authorize writes. `MutRawPtr` and `ConstRawPtr` currently abbreviate the same type.
`UnsafeCell` is not modeled.

The canonical bytes and typed observations use the same minimal cell type:
`shared depth (Option T) | borrowed`.

| Cell | Read | Raw write |
|---|---|---|
| `shared 0 (some value)` | Yes | Yes |
| `shared (depth + 1) (some value)` | Yes | No |
| `shared 0 none` | No | Yes |
| `shared (depth + 1) none` | No | No |
| `borrowed` | No | No |

There is no separate permission type or uninitialized constructor. Missing values
do not discard sharing depth. An exclusive borrow transfers the value to the
safe borrower; the raw representation retains no borrowed payload.
Sharing depths are neither ownership fractions nor counts of raw-pointer aliases.
Safe values remain valid Lean values of their translated types. `MaybeUninit`
and precise treatment of Rust padding are outside this model: currently a readable
typed cell requires initialized bytes throughout its footprint, including padding.

### Size and alignment

`Heap.repr T : Heap.Repr T` describes the type once. `Heap.size T` and
`Heap.align T` are derived from that description, not independently supplied maps.
`size T` corresponds to Rust's `size_of::<T>()`, including padding; it is the
array stride, not an unpadded payload length. `align T` corresponds to
`align_of::<T>()`. Its `Alignment` type guarantees a positive power of two, and
`size_aligned` requires that alignment to divide size. Zero size is permitted,
but zero alignment is not.

Allocation entries store a guaranteed base alignment, not an address. Access as
`T` requires that `align T` divide that guarantee. Since `index * size T` is a
multiple of `align T`, typed displacement adds no further alignment condition.
Allocation establishes the requested type's alignment; updates preserve it.
A differently typed interpretation must satisfy its own alignment requirement.
The guarantee is conservative: fortuitous stronger physical alignment is not
available to this model.

## Typed observations and local updates

`view T r i cell` is a partial, single-valued relation, not a whole-list decoder.
Every byte in a successful cell's footprint must agree with the cell's sharing
depth or borrowed state. Readable typed values require readable bytes.
Incompatible depths therefore make the view fail; no permission averaging
or conversion to a weaker permission is allowed. Even uniform byte permissions
need not make a typed value available: validity is also instrumented.

`decode T r i : Option (Cell T)` is derived from this relation. `none` is
observation failure, not a cell with a missing value or a borrowed cell. `Heap.observe`
includes base lookup and alignment; composing it with `Cell.read` is proved equivalent to
the actual relational raw-read operation.

`setCell T i cell r r'` relates representations differing by one typed-cell update.
Its `none` case is exactly `r' = r`. Likewise, `Heap.writeBack p none` leaves
the entire heap unchanged, including when the base is absent. Writing back a
failed observation cannot overwrite bytes.

For `some cell`, the target must be in bounds and has that cell afterward.
Byte length and all typed extents stay unchanged. Bytes and permissions outside
the footprint are preserved, as are all disjoint typed observations, including
their success or failure. Overlapping interpretations may become unavailable.
`Updates` composes these atomic operations; range operations do not decode and
re-encode an entire allocation. Empty range replacement is an exact no-op.

The former functional `encode`/whole-list `decode`, `ReadLaw`, `WriteLaw`, and
`taint` interface has been removed. There is deliberately no promise that an
unchanged integer update preserves every other typed interpretation.

### Type representations

`Heap.Repr T` describes a type's byte representation; it is not an allocation or
a stored byte block. Its fields are `size`, `alignment : Alignment`, `encode`,
partial `decode`, and `supports`. Size divisibility, encoding length, and the
round-trip law are separate declarations in `Axioms/Representation.lean`.
The namespace avoids shadowing Lean's `Repr` class.

`Block.Realizes T` is a separate client obligation: every initialized `T`
observation is supported by `Heap.repr T` and has its corresponding encoded bytes
in its footprint. The round-trip law then recovers that value from those bytes.
There are no size/alignment agreement conditions: both the block relations and
the byte-content claims use the same `Heap.repr T`.

`Heap.read.bytes` and `Heap.write.bytes` connect these obligations to the actual
heap primitives, not just an auxiliary observation. `HeapTests.byteRepr` and its
write example demonstrate this interface for a single byte, given that this is
the chosen `Heap.repr U8`.

The heap primitives manipulate abstract typed values without requiring their
finite encodings to round-trip. Concrete byte-content claims require `Realizes`;
it is not assumed automatically. No lossless finite encoding of every value of
an arbitrary Lean type is asserted. In particular, abstract allocation identifiers are unbounded, so stored
pointers are not given a universal injective finite-byte codec.

### Cross-type permissions and pointer validity

A raw write checks every byte in its footprint, even if decoding at the writing
type fails. Protected bytes reject even same-value writes. For zero-sized cells,
any available same-type cell must also be writable; an empty footprint does not
bypass that cell's permission.

Borrowing a positive-sized `T` cell makes every overlapping different-type view
unavailable, rather than exposing a borrowed marker at `U`. Consequently, an
overlapping `U` cannot end that borrow. Disjoint observations survive.
Nonempty zero-sized exclusive borrowing is deliberately deferred; empty borrows
are no-ops. Zero-sized allocation, reads, writes, and cleanup remain available.
Distinct same-type zero-sized indices are logical cells; a zero-sized footprint
at a different type is byte-disjoint and cannot alter those observations.

An update at a type different from `RawPtr U` invalidates every overlapping
`RawPtr U` view, even when byte contents happen to be identical. This conservative
rule needs no type classifier. Same-type pointer stores remain possible. Pointer
validity is not recoverable from bits alone. Reading pointer bytes as an integer
is underspecified: the block may expose an integer view without changing state,
or conservatively reject it. A write through that integer view cannot preserve
the overlapping pointer's validity.

Sizes and alignments are interface parameters, not inferred from arbitrary Lean types.
The concrete `U32`/`U8` and stored-pointer cross-type examples explicitly state
their size assumptions. The abstract `repr` declaration does not yet
calibrate those parameters for Rust types.

`Access.lean` proves byte-based read/write denial, byte-based cleanup denial,
disjoint observation preservation, mixed-permission decoding failure, wrong-type
borrow-restoration denial, and integer-to-pointer invalidation. The cleanup
contract requires complete byte coverage, not just the floor-divided typed extent;
otherwise a different type could hide protected trailing bytes.

## Allocation, Boxes, and pointer movement

`create` relates a typed cell list to an instrumented representation with exactly
that extent, byte length, and those initial observations. It does not choose a
base. `Heap.newCells` creates the fresh identity; `alloc` initializes its cells
as `shared 0 none`, while `newBlock` and `newSharedExposure` create initialized cells.
Zero-count allocation still creates a fresh base with cleanup authority.

A *raw exposure* places a safe value in temporary explicit storage, with cleanup
by the matching backward computation. Allocation cleanup authority instead allows
recovering an owned allocation or deallocating it. These are separate from cell
access permissions.

Safe `Box<T>` values remain represented by `T`. `Box.into_raw` exposes a one-cell
owned block; `Box.from_raw` reads and removes that entire block. This does not
assign physical identities to safe boxes or permit converting an interior field
into an independently owned box. Whole-block cleanup conservatively requires
available writable cells of a covering type; invalidated typed values may first
need to be initialized again.

Rust's `.add(usize)` and `.offset(isize)` use checked `Heap.offset`, whose
displacement is an `Int`. Both starting and resulting indices must lie within
the typed extent, including one-past-the-end. Extent is independent of typed
value availability but requires a live, suitably aligned base. Movement before
the beginning is rejected, not truncated.

Physical pointer equality, pointer-integer conversions, usable cross-type pointer
cast wrappers, unaligned access APIs, and arbitrary byte-offset pointers are not
provided. The block laws can describe differently typed footprints at one base;
that does not by itself implement Rust's casting API.

## Separation and effects

Fragments are sets of logical cell and cleanup resources observing a whole heap,
not physical fragments of `Block`. Typed ranges split and recombine. Cleanup
resources record allocation authority, alignment, exact extent, and complete byte coverage.
Resources at one base still must agree on their type and have distinct keys.
Simultaneously owning differently typed resources at one base is not supported
by this connector; the underlying block relations nevertheless have cross-type frame laws.

Relational triples require both an existing successor and correctness of every
successor, preserving arbitrary matching disjoint frames. Frame, bind,
consequence, pure, and resource-dropping rules are proved, along with primitive
allocation, access, borrowing, sharing, movement, and cleanup contracts.

`Effects.lean` interprets `Result` with the interaction-tree `DWP`. Guarded effects
require an existing successor and correctness for every successor. Failure,
divergence, and disabled effects are rejected. The ordinary effect-free WP is
unchanged. `HeapWP.Triple` and `EffectSpecs.lean` lift and compose the relational
contracts for actual Rust-model wrappers, without ordinary `step` automation.

## Trust boundary and examples

`Types.lean` defines cells, pointers, alignment, `Heap Block`, and `Heap.Repr T`.
`Axioms/Representation.lean` separately declares the abstract `Block`, `Heap.repr`,
byte projection, typed relations, and their required laws. `Model.lean` defines
the heap operations from these declarations. There is no bundled model argument
or second copy of the type metadata.

The former single `layout` assumption has been unpacked, not discharged: no
concrete block implementation or refinement proof to Rust's operational semantics
is supplied. Heap and separation proofs use these fixed declarations.
`Block` also appears in `Result`'s effect type, so otherwise pure proofs can have
a syntactic `Block` dependency. The integration examples check exact axiom lists,
now naming the individual assumptions rather than hiding them behind `layout`.

The heap records permissions, not identities or capabilities for live borrows.
`setCell`, `writeBack`, range replacement, and restoration are internal
operations, not independently authorized Rust calls. Matching translated backward
computations must invoke the right restoration at the right type and lifetime.
Wrong-type borrowed decoding is blocked, but same-type continuation identity is
not authenticated. `HeapTests.restoration_is_privileged` explicitly demonstrates
that directly invoking `endShareRange` can make a fresh shared exposure writable.
This is a trust-boundary witness, not a valid Rust program.

`HeapTests.lean` covers composed lifecycles, neighboring-cell framing, nested
sharing, signed movement, empty allocations, access/cleanup rejection, cross-type
borrow protection, mixed-permission failure, and integer-over-pointer invalidation.
The latter examples use different typed indices and partial overlap. Alignment
regressions reject observation, reads, writes, and movement at an insufficiently
aligned base; absent byte values remain unreadable and retain sharing protection.

`tests/lean/RawBoxProofs.lean` proves extracted Box round-trip and stored-pointer
examples. `RawBoxManual.lean` additionally proves corrected read/write/read,
alias-write, and handwritten borrowed-Box/callback examples. The callback consumes
its cell and exposure-cleanup resources before returning the updated safe value.
The repeated-read compiler bug is deliberately unfixed; re-extraction overwrites
the marked manual corrections. See `tests/lean/EXTRACTION.md` for provenance.

From `backends/lean`, check the examples or the complete backend:

```sh
lake build Aeneas.Std.HeapTests
lake build
```

From the repository root, check the end-to-end Box examples without re-extraction:

```sh
make verify-raw-box
```
