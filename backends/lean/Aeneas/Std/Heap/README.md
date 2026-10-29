# Instrumented Byte Memory for Aeneas (WIP)

An experiment based on
[AeneasVerif/aeneas#1433](https://github.com/AeneasVerif/aeneas/pull/1433).
This is a design-feedback model, not a complete formalization of Rust memory.

## Core design

`Heap Repr` maps fresh base identifiers to instrumented representations.
Allocation cleanup authority is separate from permissions to access cells.
Identifiers are never reused; they are model identities, not physical addresses.

`Layout` hides the representation and its instrumentation. Its public projections
give canonical byte contents (`List (BitVec 8)`), a permission for each byte,
type sizes, and typed extents. `BitVec 8` is the payload of Rust `u8`; using it
avoids importing the effectful scalar library into the memory-effect definition.
The model does not expose how permissions or typed-validity flags are stored.

`RawPtr T` contains a base and a natural `index`, counted in `T` cells. Cell `i`
has byte footprint `[i * byteLength T, (i + 1) * byteLength T)`. Thus index
equality across types says nothing about overlap. The permission system is
independent of pointer constness: casting a shared pointer to mutable does not
authorize writes. `MutRawPtr` and `ConstRawPtr` currently abbreviate the same type.
`UnsafeCell` is not modeled.

The canonical byte permissions and typed cells use the same three states:

| Permission | Typed cell | Read | Raw write |
|---|---|---|---|
| `shared 0` | `shared 0 value` | Yes | Yes |
| `shared (depth + 1)` | `shared (depth + 1) value` | Yes | No |
| `uninitialized` | `uninitialized` | No | Yes |
| `borrowed` | `borrowed` | No | No |

`uninitialized` does not include `borrowed`. An exclusive borrow transfers the
value to the safe borrower; the raw representation retains no borrowed payload.
Sharing depths are neither ownership fractions nor counts of raw-pointer aliases.
Safe values remain valid Lean values of their translated types. `MaybeUninit`
and precise treatment of Rust padding are outside this model.

## Typed observations and local updates

`view T r i cell` is a partial, single-valued relation, not a whole-list decoder.
Every byte in a successful cell's footprint must have exactly the cell's permission.
Incompatible permissions therefore make the view fail; no permission averaging
or conversion to a weaker permission is allowed. Even uniform byte permissions
need not make a typed value available: validity is also instrumented.

`decode T r i : Option (Cell T)` is derived from this relation. `none` is
observation failure, not an uninitialized or borrowed cell. `Heap.observe`
includes base lookup; composing it with `Cell.read` is proved equivalent to
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

### Caller-supplied byte codecs

`ByteCodec T` packages a byte length, `encode`, partial `decode`, and a round-trip
law on its supported values. `Layout.Realizes T codec` is the caller's obligation:
the codec has the layout's size, and every initialized `T` observation has exactly
the corresponding encoded bytes in its footprint. The codec's round-trip law
then recovers that value from those bytes.

`Heap.read.bytes` and `Heap.write.bytes` connect these obligations to the actual
heap primitives, not just an auxiliary observation. `HeapTests.byteCodec` and its
write example demonstrate this interface for a single byte.

The generic heap primitives manipulate abstract typed values and do not require
a codec. Concrete byte-content claims require `Realizes`; it is not assumed
automatically. No finite encoding of every value of an arbitrary Lean type is
asserted. In particular, abstract allocation identifiers are unbounded, so stored
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

An initialized update at an integer-classified type invalidates every overlapping
pointer-classified view, even when byte contents happen to be identical. Pointer
validity is not recoverable from bits alone. Reading pointer bytes as an integer
is underspecified: the layout may expose an integer view without changing state,
or conservatively reject it. A write through that integer view cannot preserve
the overlapping pointer's validity.

`kind` and sizes are layout parameters, not inferred from arbitrary Lean types.
The concrete `U32`/`U8` and stored-pointer cross-type examples explicitly state
their size/classification assumptions. The fixed layout axiom does not yet
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
as uninitialized, while `newBlock` and `newSharedExposure` create initialized cells.
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
value availability. Movement before the beginning is rejected, not truncated.

Physical pointer equality, pointer-integer conversions, usable cross-type pointer
cast wrappers, alignment checks, and arbitrary byte-offset pointers are not
provided. The layout laws can describe differently typed footprints at one base;
that does not by itself implement Rust's casting API.

## Separation and effects

Fragments are sets of logical cell and cleanup resources observing a whole heap,
not physical fragments of `Repr`. Typed ranges split and recombine. Cleanup
resources record allocation authority, exact extent, and complete byte coverage.
Resources at one base still must agree on their type and have distinct keys.
Simultaneously owning differently typed resources at one base is not supported
by this connector; the underlying layout nevertheless has cross-type frame laws.

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

`Axioms/Representation.lean` assumes one `layout` satisfying the abstract laws at
each needed universe. No concrete `Layout` implementation or refinement proof
to Rust's operational semantics is supplied. Generic heap and separation proofs
quantify over `Layout`; effect-boundary theorems use the fixed axiom. The fixed
representation also appears in `Result`'s effect type, so otherwise pure proofs
can have a syntactic `layout` dependency.

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
The latter examples use different typed indices and partial overlap.

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
