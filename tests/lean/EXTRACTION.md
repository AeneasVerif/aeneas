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
