# Parametric heap experiment (WIP)

This is an experimental simplification of
[AeneasVerif/aeneas#1433](https://github.com/AeneasVerif/aeneas/pull/1433),
based on commit `8c7727c79465046cf50057b7530fe5855ea79457`.
Compare this branch against `cezar/heap_model`, not `main`.
The standard-library entry point imports the new connector and its parametric
lifecycle examples. This remains a design-feedback experiment, not a complete
formalization of Rust memory or a merge-ready PR.

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

The fixed representation occurs in `Result`'s memory-effect type. Consequently,
some otherwise pure monadic proofs acquire a syntactic `layout` axiom dependency.
The decomposition tests retain exact axiom-report guards including that dependency;
the generic heap, separation, and lifecycle theorems instead quantify over `Layout`
and do not depend on the fixed-instance axiom.

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
allocation, shared-view creation and cleanup, exclusive borrowing and restoration,
nested sharing and restoration, typed pointer addition, and whole-block cleanup.

`Access.lean` uses the cross-view laws to prove that hidden-payload replacement
preserves actual raw-read success/failure, and that writes through `U` preserve
protected `T` cells. The observation function is proved equivalent to the
relational read operation, rather than used as an unconnected proxy.

`HeapTests.lean` composes allocation, initialization, borrow, restoration, read,
and cleanup; separately it exercises same-base neighboring-cell framing, nested
sharing, Box and shared-view lifecycles, and zero-count allocation/addition/cleanup.
Rejection examples cover uninitialized reads, borrowed/shared writes and cleanup,
wrong cleanup authority and extent, interior pointers, repeated cleanup, stale
access/restoration after removal, address reuse, and out-of-bounds addition.
Empty borrow/share ranges remain no-ops even without a live base; pointer addition
still requires an interpreted extent, including for a zero count.

## Permission-restoration trust boundary

The heap records permissions, not identities or capabilities for live borrows.
The `endBorrowRange` and `endShareRange` relations describe privileged backward
operations; they do not prove that the caller owns the matching continuation.
In particular, `HeapTests.restoration_is_privileged` proves that directly invoking
`endShareRange` on a freshly created shared view can make it writable, without a
preceding `shareRange`. Ordinary raw writes are still rejected at the shared depth.

The handwritten Rust models must therefore keep these operations internal, and
the translation must invoke only the matching backward computations with their
required extent/value discipline. The relational triples prove the heap effect
when such an operation is invoked, not the translation's authority to invoke it.
If the intended theorem quantifies over arbitrary Lean callers of these internal
operations, explicit ghost capabilities or borrow identities would be necessary.
No such mechanism is silently assumed or implemented here.

From `backends/lean`, check the heap examples or the complete backend with:

```sh
lake build Aeneas.Std.HeapTests
lake build
```

The complete backend builds successfully with these examples in its import
closure. Axiom reports for the lifecycle and cross-view proofs contain only
Lean's standard logical axioms, not the fixed `layout` assumption.

## Remaining work and feedback scope

The central design and law statements are ready for discussion. In particular,
feedback is needed on the read law's re-encoding strength, the write law's
authorization/footprint boundary, the same-type logical ownership restriction,
and the explicit trusted-translation boundary for borrow restoration.

## Effect-aware verification

`Effects.lean` defines a separate heap-aware interpretation of `Result` using the
existing interaction-tree `DWP`. A guarded heap effect requires a successor to
exist and its continuation to hold for every successor. Failure, divergence, and
disabled effects are rejected. The ordinary effect-free `WP.effectWP` is unchanged.

`HeapWP.Triple` gives the generated `Result` program a framed separation contract.
The generic `Triple.guardedModify` rule lifts existing relational heap triples;
pure, bind, consequence, and frame rules compose them without reconstructing the
program. `EffectSpecs.lean` supplies rules for the actual Box, read/write, and
borrow/share/restoration wrappers. These effect-boundary theorems use the existing
fixed `layout` assumption; the underlying relational proofs remain parametric.

`tests/src/raw_box.rs` and its unmodified extraction `tests/lean/RawBox.lean`
exercise two lifecycles: Box exposure, write/read, and recovery; and a second Box
containing the first Box's raw pointer, loaded and used to update the target.
`RawBoxProofs.lean` proves that both return the replacement for arbitrary `u32`
inputs, consuming their allocation resources and preserving every disjoint frame.
No pointer equality, new axioms, or proof holes are used. This is validation of
the extracted programs against the handwritten Rust models, not a proof of
compiler or model soundness with respect to Rust's operational semantics.

From the repository root:

```sh
make verify-raw-box
```

See `tests/lean/EXTRACTION.md` for the exact extraction command and executable
provenance, including the newer compiler/Charon pair used read-only for this run.

Remaining validation and scope:

- Audit the translation's matching-continuation discipline and run relevant Rust
  extraction examples involving array views and restoration; the Box examples
  above do not exercise backward continuations. The existing
  `tests/src/raw_pointers.rs` fixture is marked as a Lean known failure; it has
  not been re-extracted here.
- Decide whether to retain single-type logical ownership or introduce the
  footprint/overlap interface needed for cross-type framing and authorization
  of even same-value writes.
- Assess the laws against the intended byte/alignment interpretation. A concrete
  `Repr` instance is deliberately not part of this experiment.

The separate heap-aware contracts do not yet have the ordinary `step` tactic's
automation. Cross-type framing, physical byte layout, and higher-order storage of
`Result`-returning closures are not established by these examples.
