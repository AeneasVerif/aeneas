# Parametric heap experiment (WIP)

This is an experimental simplification of
[AeneasVerif/aeneas#1433](https://github.com/AeneasVerif/aeneas/pull/1433),
based on commit `8c7727c79465046cf50057b7530fe5855ea79457`.
Compare this branch against `cezar/heap_model`, not `main`.
The new modules can be checked independently, but the existing standard-library
integration is not yet ported. This is a design-feedback snapshot, not a merge-ready PR.

## Design and terminology

`Heap Repr` maps fresh base identifiers to representations, separately records
allocation cleanup authority, and maintains a global freshness counter. Identifiers
are never reused. They are model identities, not physical addresses.

`RawPtr T` contains a base and an offset counted in `T` cells. Mutable and const
raw pointers have the same model type; the pointer does not carry access rights.
`Cell T` records either uninitialized storage or a value with a borrow permission:
`none` is exclusively borrowed, `some 0` is full access, and positive depths allow
shared reads. Uninitialized cells can be written but not read. These depths are
not arbitrary rational ownership fractions.

`Layout` is the representation interface, not the whole memory model. It provides
typed `represent`/`interpret` functions, round-trip and cross-view laws, and a
total typed fresh-storage operation taking a cell count. The generic heap and
separation proofs are parametric in this interface.
`Axioms/Representation.lean` assumes one fixed `Layout` at the universes needed by
translation. No byte or alignment implementation is supplied.
An informal type-tagged example is described beside `Layout`; its consistency
has not been formalized.

A *view* exposes a safe value through temporary explicit storage, with cleanup by
the matching backward computation. Allocation cleanup authority instead allows
recovering an owned allocation or deallocating it. Cell access and cleanup
authority are separate resources. Safe `Box<T>` values remain represented by `T`:
`Box.into_raw` exposes a one-cell owned block, and `Box.from_raw` reads and removes
that whole block. This does not assign physical identities to safe boxes or model
substructural conversion of a field into an independently owned box.

Typed pointer addition is supported within the interpreted extent, including
one-past-the-end. Pointer equality, physical addresses, pointer-integer conversions,
byte arithmetic, alignment, and usable cross-type pointer casts are not provided.
In particular, this experiment does not justify physical pointer-equality assertions.

## Cross-view laws

`ReadLaw` says that varying only unreadable borrowed payloads in a `T` view and
re-encoding it cannot change any authorized `U` read, including success or failure.
It applies to arbitrary initial representations, so even unchanged re-encoding
must preserve all read observations. This excludes forgetting read-observable
padding or other information absent from the `T` view: whether that is the right
strength for a future byte interpretation needs review.

`WriteLaw` says that changing writable `T` cells while carrying protected cells
through unchanged preserves every protected `U` cell, its permission, and its
continued interpretability. It does not equate indices of differently typed cells.
It is not a complete footprint/overlap authorization law: in particular, an
unchanged value alone cannot establish that a write at that location was authorized.
The interface currently has no abstract cross-type footprint relation.

Empty range replacement is explicitly a state-preserving no-op. It does not
re-encode the surrounding representation. Zero-count allocation still creates a
fresh base with cleanup authority; absence of cell resources does not supply that
authority.

## Separation-logic connector

Fragments are sets of logical cell and cleanup resources observing a whole heap,
not pieces of `Repr`. This avoids requiring a physical separation operation on
the representation. Typed ranges can be split and recombined.

Disjoint resources at one base must agree on their type and have distinct resource
keys. Cleanup and cell resources have different keys. This is a restriction on
logical ownership, not a claim that only one physical interpretation exists.
Simultaneously framing different typed views of one base is not supported.
The present frame proofs use same-type round-trip reasoning, not the new
cross-view read/write laws.

The affine relational triples require both an existing successor and correctness
of every successor, for every matching disjoint frame. Frame, bind, consequence,
pure, and resource-dropping rules are proved. Primitive triples cover range
replacement, reads, writes, initialized block creation, typed uninitialized
allocation, shared-view creation, and whole-block cleanup.

From `backends/lean`, check the experimental modules and adapted wrappers with:

```sh
lake build Aeneas.Std.Heap.Allocation Aeneas.Std.Core.Alloc Aeneas.Std.Slice Aeneas.Std.Alloc.Boxed
```

## Remaining work and feedback scope

The central design and law statements are ready for discussion. In particular,
feedback is needed on the read law's re-encoding strength, the write law's
authorization/footprint boundary, the same-type logical ownership restriction,
and how matching backward computations authorize borrow restoration.

Before claiming end-to-end integration:

- Port the old `HeapLemmas.lean` and `HeapTests.lean`, which still use the old
  API and are imported by `Std.lean`. The library is not globally buildable yet;
  no imports or default targets have been removed to conceal this.
- Add borrow/share/end-share, shared-view cleanup, and pointer-addition triples;
  exercise composed Box, slice, allocation, and borrow lifecycles.
- Restore the negative examples for invalid reads/writes, cleanup authority,
  wrong extents, interior pointers, double cleanup, and zero-length cases.
- Review the laws and operation proofs together, and run the complete library
  build and relevant extraction tests.

The relational connector is not an integration with the ordinary `WP.effectWP`,
which rejects effects in the starting branch. Such an integration is separate work.
