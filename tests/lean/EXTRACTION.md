# Raw Box extraction provenance

This log covers the raw-memory fixtures described below, not the other fixtures
in this directory.

## 2026-10-29 — Box lifecycle and stored-pointer lifecycle

```text
command    : make test-raw_box.rs IN_CI=1 AENEAS_EXE=/workspaces/aeneas/bin/aeneas TEST_RUNNER_EXE=/workspaces/aeneas/bin/test_runner CHARON_EXE=/workspaces/aeneas/charon/bin/charon
rust       : AeneasVerif/aeneas, fournet/wip-memory-model, based on 294c3371ff236890f75c5c51ab15dda7eea931af
source     : tests/src/raw_box.rs, Git blob 53bab4c63a894677f715eafcb11136d7adcb7e6a
aeneas     : existing executable in the clean compiler checkout at 985460dbbf187af891aab0201a8c046a2ed98ffe
charon     : existing executable in the clean checkout at 26abff028ced534ebf8e861f2d3dd1743e2aa318
rustc      : nightly-2026-09-17, rustc 1.100.0-nightly (923c95cdf 2026-09-16)
options    : existing test runner; Lean only; IN_CI=1 supplies -checks; no additional options
```

The executables were used read-only. Their compiler checkout/pair is newer than
the experiment's original base and `charon-pin`
(`de8736f7c995ac54dc490345cef9ea5143c06c62`). The latter was not changed; this run
does not attest that the compiler can be rebuilt with that older pin. The emitted
definitions use the redesigned backend's existing Box and raw-pointer wrappers.

Executable SHA-256:

```text
aeneas      cf7676c9726898765d413a8d13749d3b9ed672bde7723614a8990a33a47faffe
test_runner b69fb005c14b31aa0c48a38efa1ca4146231541241b7a21ed9051c4de50e9ddc
charon      742cb2c9d21f278c157946804058373542c4cbc90b629bdd75a498070a25a0f3
```

Outcome: both public functions extracted without external stubs or axioms.
No generated definitions were edited. `RawBoxProofs.lean` is handwritten and
proves framed total-correctness contracts about those definitions, using
`HeapWP` and the fixed `layout` assumption.

Replay the Lean checks with `make verify-raw-box`. This uses the isolated backend
and temporary compiled fixture artifacts rather than populating a second Mathlib
build cache. The normal test Lake targets also include both modules.

## 2026-10-29 — Additional examples and minimized repeated-read bug

```text
commands   : make test-raw_box.rs IN_CI=1 AENEAS_EXE=/workspaces/aeneas/bin/aeneas TEST_RUNNER_EXE=/workspaces/aeneas/bin/test_runner CHARON_EXE=/workspaces/aeneas/charon/bin/charon
             make test-raw_read_write_read.rs IN_CI=1 AENEAS_EXE=/workspaces/aeneas/bin/aeneas TEST_RUNNER_EXE=/workspaces/aeneas/bin/test_runner CHARON_EXE=/workspaces/aeneas/charon/bin/charon
rust       : AeneasVerif/aeneas, fournet/wip-memory-model, based on f1fc114739d6c4f847661996a6de3d5d90a9e4d3
sources    : tests/src/raw_box.rs, Git blob 988995e74be81c50eb64d05033b919200bf99562
             tests/src/raw_read_write_read.rs, Git blob 1b1fbbc3ac0930e57af1f2b4b52873098c965ae4
aeneas     : 985460dbbf187af891aab0201a8c046a2ed98ffe; same read-only executable as above
charon     : 26abff028ced534ebf8e861f2d3dd1743e2aa318; same read-only executable as above
rustc      : nightly-2026-09-17
options    : existing test runner; Lean only; IN_CI=1 supplies -checks
```

Additional Box examples illustrate pointer aliases, whole-pair cells, zero and
one-past pointer addition, and a zero-sized value (one logical typed cell, not an
empty range). Native Rust tests pass and all definitions extract and type-check.
The existing two Box proofs still pass; the additional examples are not yet proved.

The alias example exposes an incorrect repeated-read optimization. The smaller
`RawReadWriteRead.lean` reproduces it without Box allocation or a copied pointer:
`discarded_read` reads through `p`, writes `1` through the same `p`, then reads
again. Its generated definition returns the first read instead of performing the
second. From an initialized writable cell holding `0`, native Rust returns `1`
but the generated program returns `0`. Keeping both read results also reproduces
the bug. No generated definitions were manually repaired or axiomatized.

Post-extraction edits, explicitly requested for design validation before changing
the compiler: restored the second read in `RawBox.alias_write` and in both
`RawReadWriteRead` functions. Their file headers now mark these manual corrections.
Re-extraction with the recorded compiler overwrites them and reproduces the bug;
these corrected definitions are not evidence of a repaired extraction pipeline.

`RawBoxManual.lean` proves the corrected definitions return the replacement
(and the initial value where returned), preserving arbitrary disjoint frames.
It also contains a handwritten borrowed-Box translation with an `into_raw`
prototype returning a pointer and a `Unit → Result T` restoration callback.
This prototype models borrowing via `ptr::from_mut`, not Rust's consuming
`Box::into_raw`. Its callback requires both the full cell and the temporary
exposure-cleanup resource; it reads the updated value, removes the exposure, and returns
the safe value with `emp`. The caller cannot regain a safe value by retaining
the original functional value. The callback contract applies to any subsequently
written value, not just its initial contents.

Returning an effectful callback raises the result universe; the prototype uses
explicit cross-universe `Aeneas.Std.bind` and a proved composition rule.
No compiler or backend primitive was changed. `make verify-raw-box` checks the
original proofs and these manual validation proofs, including exact axiom guards
allowing only the existing `layout` assumption and standard Lean logical axioms.
The pair, pointer-addition, and zero-sized-value examples remain unproved.

## Post-extraction migration — concrete byte heap

No compiler was changed and no extraction was rerun for this migration. The
hashes and commands above record the historical extraction, not a current
toolchain attestation.

`RawBox.lean` and `RawReadWriteRead.lean` were manually adapted to pass explicit
`Aeneas.Std.Repr` descriptors through the memory wrappers. Stored pointers take
their own descriptor, independently of the pointed-to value's descriptor.
The marked repeated-read repairs remain in place. Re-extraction with the
recorded compiler overwrites both kinds of adaptation.

`RawBoxProofs.lean` and `RawBoxManual.lean` now use the concrete byte heap.
Allocation correctness is stated at the actual input heap with explicit finite
counter capacity and representation-size bounds, preserving any matching frame.
Local access and cleanup use framed separation triples. The borrowed-Box
prototype uses temporary non-owned exposure storage; its callback recovers any
subsequently written value and consumes both byte and exposure-cleanup resources.
Cross-universe composition is supplied by the common `HeapWP` bind rules.

There is no remaining `layout`, abstract `Block`, or byte-representation axiom
in these proof dependencies. Exact guards allow only `propext`,
`Classical.choice`, and `Quot.sound`. The descriptors and their completeness
proofs are explicit theorem parameters, not added axioms. `RawBoxProofs.lean`
also provides complete little-endian `u32` and paired-`u32` descriptors and
concrete instantiations of round-trip, pair replacement, and one-past examples.
The pair encoding is a model fixture, not a Rust tuple-ABI refinement claim.

Encoding-producing wrappers now call `Repr.choose` or `Repr.chooseList`
internally. Their results carry the decode-back proof for the supplied
descriptor. The choice contract is proved from completeness and ranges
demonically over all valid encodings; it does not select a fresh descriptor.
This changes the modeled backend primitives, but does not change or rerun the
compiler or remove the fixtures' manual descriptor arguments.

`make verify-raw-box` checks these migrated fixtures and proofs without
re-extraction, including pair replacement and one-past pointer formation.
The zero-sized fixture type-checks, but its raw read is deliberately disabled
for an actual zero-sized descriptor; no read-success theorem is claimed.
General range-level permission/effect contracts also remain to be ported,
although the executable range operations have concrete regression tests.

## Borrowed-Box callback adaptations and raw-API examples

The scalar `borrowed_box` and aggregate `borrowed_pair` examples now have Rust
source in `tests/src/raw_box.rs`. No extraction was run for these additions.
Their definitions in `RawBoxManual.lean` are manually adapted translations:
the local borrowed conversion `to_raw` returns a raw pointer and a backward
function. The function recovers the current value and removes the temporary
exposure; translated callers invoke it before safely dereferencing the Box.
This is not Rust's consuming `Box::into_raw`, and exposure removal does not
deallocate the Rust Box. In the aggregate example, writing through a copied
pointer updates the value subsequently recovered by the callback.

The `raw_api` namespace in that file is a separate model-API exercise, not
additional translated Rust. It proves nested shared range reads through a const
pointer, restoration of writable permissions, exclusive borrow/update/
restoration, and their composition. Restoration calls represent the matching
backward computations, not capabilities available to arbitrary Rust callers.
These proofs use singleton-range contracts, not general multi-element contracts.

`make verify-raw-box` checks all the callback and API compositions, including
exact axiom guards. The native `raw_box.rs` unit test covers both new borrowed
examples. The existing compiler and shared setup remain unchanged.

## Byte offsets, checked failures, and transmute examples

Raw pointers now carry a byte offset, not a descriptor-dependent element index.
The approved pure `RawPtr.cast` preserves that offset and the allocation identity;
typed arithmetic scales by descriptor size, while accesses check both base and
offset alignment. Existing Box and borrow proofs have been propagated. No compiler
was changed or extraction rerun, and the legacy compiler-facing scalar cast
wrapper remains unsupported.

Heap wrappers now use the shared `Result.checkedModify` boundary. A failed
operation's always-enabled request returns `none` at the unchanged heap, and its
continuation emits `.fail .undef`; the successful transitions and correctness
obligations are unchanged. This logical totalization retains the relational
interpretation rather than adding an executable relation interpreter. Encoding
choice remains demonic over the supplied descriptor's valid encodings.

`tests/src/raw_transmute.rs` adds native tests using raw pointer transmutes on the
second element of a `u32` array. `RawTransmute.lean` is entirely handwritten,
not extracted: its framed same-type round-trip contracts prove the raw-pointer
bodies for arbitrary positive-sized descriptors. Its cross-type countermodels
execute the concrete heap operations with alternative little-/big-endian word
descriptors and an identity byte descriptor. They establish the absence of a
uniform cross-type numeric prediction, not nondeterminism of a fixed decoder or
correctness of a compiler transmute translation. Whole-array safe exposure and
restoration and framed contracts for the cross-type bodies remain future work.

`make verify-raw-box` now also checks `RawTransmute.lean`, with exact standard-axiom
guards on its two same-type round-trip proofs. General multi-element separation
and permission contracts remain outside this milestone.

## 2026-10-30 — Unedited extraction through opaque pointer-operation wrappers

```text
command    : make test-raw_transmute_externals.rs IN_CI=1 AENEAS_EXE=/workspaces/aeneas/bin/aeneas TEST_RUNNER_EXE=/workspaces/aeneas/bin/test_runner CHARON_EXE=/workspaces/aeneas/charon/bin/charon
rust       : https://github.com/AeneasVerif/aeneas.git, fournet/wip-memory-model, based on 8872d5e0029caf38268d146ec67fff2cf3a94017
source     : tests/src/raw_transmute_externals.rs, Git blob 69e4aa02ee11de74b00f3d476423b410b4293270
aeneas     : 985460dbbf187af891aab0201a8c046a2ed98ffe; same read-only executable and SHA-256 as above
charon     : 26abff028ced534ebf8e861f2d3dd1743e2aa318; same read-only executable as above
charon-pin : shared compiler 26abff028ced534ebf8e861f2d3dd1743e2aa318; experiment remains de8736f7c995ac54dc490345cef9ea5143c06c62
rustc      : Charon toolchain nightly-2026-09-17, rustc 1.100.0-nightly (923c95cdf 2026-09-16); native test rustc 1.98.0-nightly (14210df0e 2026-05-31)
options    : Charon --opaque=crate::ext; Lean -split-files -all-computable; test runner supplies -checks and the usual diagnostic flags
```

Outcome: all six public callers extracted successfully. `Types.lean`,
`Funs.lean`, and `FunsExternal_Template.lean` in `RawTransmuteExternals/` are
unedited generated artifacts. The template's six axioms are not imported by the
proofs: the separate handwritten `FunsExternal.lean` provides transparent
definitions. The existing test runner regenerates only the template, leaving the
unsuffixed model file untouched; reconcile signatures against the template after
future extractions. No Charon, compiler, or backend source was patched.

The generic Rust transmute wrappers have default `Sized` bounds, so both sides
are thin pointers. Their models simply return `RawPtr.cast`, preserving base and
byte offset without accesses or heap effects. Opaque word/byte access wrappers are
also necessary here: their models supply the already-defined little-endian
`raw_box.u32Repr` and identity `raw_transmute.byteRepr` descriptors. This is a
calibrated model boundary, not a proof of Rust's target layout or of the wrappers'
Rust bodies.

`Properties.lean` proves ordinary-WP mutable/const pointer round trips and framed
heap-WP same-type word/byte write-read contracts directly about the generated
callers, reusing the manual model proofs through proved equality bridges.
Exact axiom guards allow only `propext`, `Classical.choice`, and `Quot.sound`.
The generated cross-type callers are also proved equal to the corresponding
manual models with these descriptors; no new framed cross-type contract or
descriptor-independent numeric prediction is claimed. Native tests exercise the
second element of a two-word array, but safe-array exposure/restoration remains
outside the extracted proof boundary.

Replay the Lean checks with `make verify-raw-box`. Native Rust checks and
`rustfmt --check --edition 2021 tests/src/raw_transmute_externals.rs` also pass.

## 2026-10-30 — Stored-pointer doubly-linked-list kernel

```text
command    : make test-raw_doubly_linked.rs IN_CI=1 AENEAS_EXE=/workspaces/aeneas/bin/aeneas TEST_RUNNER_EXE=/workspaces/aeneas/bin/test_runner CHARON_EXE=/workspaces/aeneas/charon/bin/charon
rust       : https://github.com/AeneasVerif/aeneas.git, fournet/wip-memory-model, based on 141f10647b0f9b60c9e89830eec48ded751ee83e
source     : tests/src/raw_doubly_linked.rs, Git blob 1d56b70a8248f195c2d9605415557eec89089f47
aeneas     : 985460dbbf187af891aab0201a8c046a2ed98ffe; same read-only executable as above
charon     : 26abff028ced534ebf8e861f2d3dd1743e2aa318; same read-only executable as above
charon-pin : shared compiler 26abff028ced534ebf8e861f2d3dd1743e2aa318; experiment remains de8736f7c995ac54dc490345cef9ea5143c06c62
rustc      : Charon nightly-2026-09-17; native rustc 1.98.0-nightly (14210df0e 2026-05-31)
options    : Charon --opaque=crate::ext; Lean -split-files -all-computable; test runner supplies -checks and the usual diagnostic flags
```

Outcome: all six link-operation callers and the derived clone implementation
were emitted. Opaque wrappers directly call Rust's `ptr::read` and `ptr::write`.
`FunsExternal_Template.lean` is the unedited generated template; it is not
imported. `FunsExternal.lean` supplies transparent read/write models taking
an explicit `Repr Node`, not axioms.

Post-extraction edits: `Types.lean` could not elaborate as generated because
Lean rejects the occurrence of recursive `Node` under the phantom parameter of
`RawPtr Node`. Replace its constructor with
`Node.stored : MutRawPtr Unit → MutRawPtr Unit → U32 → Node`, define the original
`Node.mk` as a smart constructor copying both pointer fields' base/byteOffset,
and restore the `Node` phantom tag in `Node.prev` and `Node.next`. The existing
projection equations still hold by `rfl`; `Node.mk_eta` proves the converse.
No pointer identifier or offset is discarded.

`Funs.lean` was manually adapted only to add an explicit `Repr Node` argument
to `init`, `set_next`, `set_prev`, `insert_after`, `remove`, and `remove_after`,
and forward it to every affected call. Control flow and the order of every
stored-pointer read and write are unchanged. Re-extraction overwrites these
two marked adaptations; replay them before checking. There is no patch to
Charon, Aeneas, or the shared setup.

`Properties.lean` proves the local link operations, including empty-ring,
last-node, and detached-node aliasing cases. `ListProperties.lean` proves exact
list-cons/list-tail contracts for arbitrary finite rings with all payloads and
links owned, preserving arbitrary disjoint matching frames. These are heap-WP
contracts, not ordinary effect-free `@[step]` theorems. Descriptor completeness
is a parameter, not a memory-model axiom or a Rust ABI claim. No safe owning
wrapper, traversal proof, allocation/deallocation, or uninitialized-node
initialization proof is included. `make verify-raw-doubly-linked` checks the
entire proof closure with exact standard-axiom guards and no `sorry`.

## 2026-10-30 — Safe owning doubly-linked-list interface

```text
command    : make test-raw_doubly_linked.rs IN_CI=1 AENEAS_EXE=/workspaces/aeneas/bin/aeneas TEST_RUNNER_EXE=/workspaces/aeneas/bin/test_runner CHARON_EXE=/workspaces/aeneas/charon/bin/charon
rust       : https://github.com/AeneasVerif/aeneas.git, fournet/wip-memory-model, based on 141f10647b0f9b60c9e89830eec48ded751ee83e
source     : tests/src/raw_doubly_linked.rs, Git blob 96aa1e24c1806005628ac558e476457b0a0a2774
aeneas     : 985460dbbf187af891aab0201a8c046a2ed98ffe; unchanged shared read-only executable
charon     : 26abff028ced534ebf8e861f2d3dd1743e2aa318; unchanged shared read-only executable
charon-pin : shared compiler 26abff028ced534ebf8e861f2d3dd1743e2aa318; experiment remains de8736f7c995ac54dc490345cef9ea5143c06c62
rustc      : Charon nightly-2026-09-17; native rustc 1.98.0-nightly (14210df0e 2026-05-31)
options    : Charon --opaque=crate::ext; Lean -split-files -all-computable -loops-to-rec; test runner supplies -checks and diagnostic flags
```

The fixture now adds `LinkedList` with private root/length fields and safe
`new`, `len`, `is_empty`, `front`, `back`, `push_front`, `pop_front`, and `clear`
methods, plus `Drop`. Sentinel and payload nodes have stable Box allocations;
moving the list does not move its nodes. No raw pointer escapes this interface.
The payload is copied `u32`, not an arbitrary type with a user destructor.

The external Rust module now has four opaque wrappers: read, write, allocate,
and take/free. Its hand-written Lean models delegate to the existing pointer
and Box operations. `allocate_node` uses `Box.into_raw` on a blank node;
`take_node` uses `Box.from_raw`, matching the Rust move-out/free wrapper.
The generated four-axiom template remains unedited and unimported.

Post-extraction edits: replay the lossless recursive-pointer phantom repair
and explicit `Repr Node` threading documented above. Thread the descriptor
through every heap-touching safe method, the recursive clear helper, Drop,
and its trait dictionary as well. Leave the new `LinkedList` structure and
all extracted control flow unchanged. `-loops-to-rec` emits `clear_loop`
with `partial_fixpoint`; `clear_loop_owned` proves total correctness by
induction on the finite owned sequence, not by assuming loop termination.

`Ownership.lean` extends the existing finite-ring assertion with cleanup
authority for every payload allocation and the sentinel, and an exact length.
It proves endpoint reads, allocating insertion's continuation, reclaiming pop,
total clear, and Drop consuming the entire footprint. `SafeProperties.lean`
proves all nine public contracts against plain-list operations. `ListState`
includes the direct equation `self.toList repr heap = some values`, where
`toList` is a deterministic heap decoder; hidden node addresses serve only
as internal separation-logic witnesses.

These are parametric memory-model proofs, not a proof of Rust's node ABI,
stored-pointer encoding, or compiler correctness. No concrete `Repr Node`
witness is instantiated here; supplying and calibrating one remains separate
work. New/push contracts state
the finite heap-counter and descriptor-size bounds; push also states the
checked length bound. No new axiom or `sorry` is used. Drop's public post
preserves the external frame and heap invariant after consuming list ownership;
it does not enumerate an exact whole-heap allocation-map difference.

`make verify-raw-doubly-linked` includes both new modules and exact axiom guards
for every public theorem. The four native tests include a safe-only sequence
comparison, moves, empty cases, clear/reuse, and destruction of a nonempty list;
they also pass with address/leak sanitization.

## 2026-10-30 — Mutable byte-array view and by-value transmute contracts

```text
commands   : make test-raw_transmute_externals.rs IN_CI=1 AENEAS_EXE=/workspaces/aeneas/bin/aeneas TEST_RUNNER_EXE=/workspaces/aeneas/bin/test_runner CHARON_EXE=/workspaces/aeneas/charon/bin/charon
             make test-raw_value_casts.rs IN_CI=1 AENEAS_EXE=/workspaces/aeneas/bin/aeneas TEST_RUNNER_EXE=/workspaces/aeneas/bin/test_runner CHARON_EXE=/workspaces/aeneas/charon/bin/charon
sources    : tests/src/raw_transmute_externals.rs, Git blob 850dfa3519dd5765ea1b55739efb466075dbefaf
             tests/src/raw_value_casts.rs, Git blob 5a75cb16c2f8b4aa49f62233813666241d1f18c9
aeneas     : 985460dbbf187af891aab0201a8c046a2ed98ffe; unchanged shared read-only executable
charon     : 26abff028ced534ebf8e861f2d3dd1743e2aa318; unchanged shared read-only executable
charon-pin : experiment remains de8736f7c995ac54dc490345cef9ea5143c06c62
rustc      : Charon nightly-2026-09-17; native rustc 1.98.0-nightly (14210df0e 2026-05-31)
options    : Charon --opaque=crate::ext; Lean -split-files -all-computable; test runner supplies -checks and diagnostic flags
```

The array fixture adds opaque four-byte read/write/borrow wrappers, transparent
raw array-pointer callers, and safe `bytes_view(&mut u32) -> &mut [u8; 4]`.
Its regenerated external template records the actual compiler signatures:
`core.ptr.from_mut` returns a pointer plus the old functional value, and
`ext.borrow_four` returns an array plus a pure `Array -> Unit` backward function.
The template is retained unedited and is not imported.

Post-extraction adaptation, confined to `RawTransmuteExternals/Funs.lean`:
replace only `bytes_view`'s return type and borrow plumbing with effectful
backward computations. Pass `raw_box.u32Repr` to the existing `from_mut` model,
then preserve the Rust call order: expose word, cast pointer, borrow array.
The returned callback first restores updated array bytes with `endBorrow`,
then reads the word and consumes its exposure through the matching `from_mut`
callback. Explicit cross-universe binds support this effectful result. The
other generated callers and `Types.lean` are unchanged. Re-extraction overwrites
the marked adaptation; no shared compiler, Charon, or compiler-facing primitive
was changed. The handwritten external model deliberately differs from the
template's pure backward signature and must be reconciled with this adaptation.

`ArrayRepr.lean` supplies the complete four-byte identity descriptor and exact
little-endian conversions. `ArrayProperties.lean` proves raw pointer identity,
framed exact array reads and overwrites, and the safe mutable view's complete
forward/backward contract. Every replacement array restores its exact word;
the callback consumes exposure resources and preserves arbitrary frames.
Access through alignment-one arrays retains the original alignment-four word
resources. Rust native tests use native endian; these model proofs explicitly
instantiate little endian and do not establish Rust-target ABI refinement.

The by-value fixture has four opaque conversions and four transparent callers.
Its `Types.lean`, `Funs.lean`, and four-axiom `FunsExternal_Template.lean` are
unedited extraction output; the template is not imported. The second extraction
refreshes source spans after allowing the deliberate unnecessary-transmute lint.
Handwritten external definitions use `reinterpret`: demonic choice of any
source encoding followed by target decoding, not a canonical encoder.
`reinterpret.spec` proves exact result and unchanged heap from equal sizes and
the requirement that every source encoding decodes to the specified target
value. The concrete contracts prove bool/byte and signed/unsigned round trips,
checked byte-to-bool for every input, and bool-byte copying with unchanged
source. Byte 2's failed bool decoding witnesses why initialization alone is
insufficient. These are models for the specific wrappers, not a new compiler
rule for arbitrary transmute, padding, pointers, lifetimes, or destructors.

`make verify-raw-box` now checks both roots and exact axiom guards on the
end-to-end array/value contracts and the generic compatibility theorem.
Only `propext`, `Classical.choice`, and `Quot.sound` occur; no memory-model
axiom or `sorry` is introduced. Rustfmt passes for both fixtures, the native
value test covers all 256 checked bool inputs and signed boundaries, and the
three native array tests pass with address/leak sanitization.

The heap's [TRANSMUTE.md](../../backends/lean/Aeneas/Std/Heap/TRANSMUTE.md)
compares bytemuck 1.25.2 and zerocopy 0.8.63 with the pair-specific
representation obligations. Library experiments remain session
artifacts, not repository dependencies or translated fixtures. They confirm
checked mutable byte-to-bool acceptance, bool-to-byte mutable rejection,
padding and static-alignment rejection, and the distinct Box allocation-layout
requirement. Neither library's checked mutable cast accepts bool as the source
of a bool-to-two-discriminant-enum view, despite the candidate pairwise
compatibility; that more precise mutable wrapper is not proved here.

## 2026-10-30 — DoublyLinked rename and raw/safe source separation

The earlier `RawDoublyLinked` entries above retain their historical names and
source hashes. The current example is named `DoublyLinked`, with Rust crate and
Lean namespace `doubly_linked`.

```text
command    : make test-doubly_linked.rs IN_CI=1 AENEAS_EXE=/workspaces/aeneas/bin/aeneas TEST_RUNNER_EXE=/workspaces/aeneas/bin/test_runner CHARON_EXE=/workspaces/aeneas/charon/bin/charon
rust       : https://github.com/AeneasVerif/aeneas.git, fournet/wip-memory-model, based on b023a12efe278035d8ad2d0017b735de00b1141a
sources    : tests/src/doubly_linked.rs, Git blob f60b2e52229038639902e215d9bc82a6fd01317d
             tests/src/doubly_linked/raw.rs, Git blob a466b58c77197f05bb4f9d7bd6b3861b1aca969f
             tests/src/doubly_linked/safe.rs, Git blob 767f1306d62ff31acffe0bbd94a4039ac44d5a46
             tests/src/doubly_linked/tests.rs, Git blob c6f5720a446092e37c74f72daa59f886b0f05edc
aeneas     : 985460dbbf187af891aab0201a8c046a2ed98ffe; unchanged shared read-only executable
charon     : 26abff028ced534ebf8e861f2d3dd1743e2aa318; unchanged shared read-only executable
charon-pin : experiment remains de8736f7c995ac54dc490345cef9ea5143c06c62
rustc      : Charon nightly-2026-09-17; native rustc 1.98.0-nightly (14210df0e 2026-05-31)
options    : Charon --opaque=crate::ext; Lean -split-files -all-computable -loops-to-rec; existing test runner supplies -checks and diagnostic flags
```

The Rust entry point includes `raw.rs` (Node, opaque primitive wrappers, and
unsafe ring operations) and `safe.rs` (the private-field owning LinkedList and
Drop). This separates the APIs into source files without introducing new
module-qualified symbols or changing the opaque `crate::ext` boundary.
The four original native tests live in a separate `tests.rs`, with distinct
raw and safe-client test modules; the safe client imports only `LinkedList`.
The Makefile excludes the support directory from independent extraction and
includes its files in formatting; the root's test module preserves native
test discovery.

Re-extraction with the unchanged shared binaries emitted fresh `Types.lean`,
`Funs.lean`, and `FunsExternal_Template.lean`, with correct split-source spans.
The external template remains unedited and unimported; the handwritten
external models are unchanged except for the namespace/import rename.

Post-extraction edits: replay the lossless recursive-pointer phantom repair in
`Types.lean` and explicit `Repr Node` threading documented in the earlier list
entries. Factor `Funs.lean` at the first `LinkedList.new` declaration into
`Raw.lean` (Node trait implementations and intrusive operations) and `Safe.lean`
(all owning methods, clear's recursive helper, and Drop), preserving source
annotations. `Safe.lean` imports `Raw.lean`; replace `Funs.lean` with an import
aggregator for `Safe.lean`. Mark both function files as factored/adapted output.
The adapted function and type bodies are token-identical to the previous
adapted example after the namespace rename, ignoring comments and whitespace.
Re-extraction overwrites the aggregator and type repair; replay the factoring
and descriptor adaptations before checking proofs.

Rename the local raw contracts to `RawProperties.lean`; they import only
`Raw.lean`. `ListProperties.lean` builds the raw-ring sequence contracts.
`Ownership.lean` additionally imports `Safe.lean`, and `SafeProperties.lean`
retains all nine public plain-list contracts. No proof statement, proof body,
or axiom guard is weakened. The library registration and focused verification
target are now `DoublyLinked` and `make verify-doubly-linked`.

The focused Lean closure and exact standard-axiom guards pass. All four native
tests pass both normally and with address/leak sanitization; Rustfmt also
passes for the entry point, both API files, and the test file. No shared tool
or compiler setup is modified.
