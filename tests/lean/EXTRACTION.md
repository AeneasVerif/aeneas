# Raw Box extraction provenance

This log covers the raw-memory fixtures described below, not the other fixtures
in this directory.

**Current concrete-address migration status:** the backend default build and
the complete existing raw-memory example series pass:

```text
cd backends/lean && lake build
cd tests/lean && lake build RawBox RawBoxProofs RawBoxManual RawReadWriteRead RawTransmute RawValueCasts RawTransmuteExternals RawPointerOps DoublyLinked
```

Box lifecycles, range returns, the four-byte array callback, all five raw
linked-list alias cases and the safe owning-list API are restored. Public
contracts retain arbitrary matching frames and every permitted successor,
without client heap-check/overlap proofs. Accesses and returns retain checked
enabledness; allocation and exposure accept OOM without placement-existence
premises. Owned lifecycles retain
lexical root authority; `ListState` encapsulates it for the safe list API.
Pointer writes use local provenance evidence, including already-stored pointers
to retired views. Generic node proofs take an explicit `NodeLayout` calibration.
Applicable exact axiom guards allow only standard Lean logical axioms.

These are checks of the marked, manually adapted translations, not of a repaired
compiler pipeline. No adapted fixture was overwritten by regeneration. The newer
heap-uninitialized, eight-u16/sixteen-u8, pointer-as-integer and nested boxed-slice
scenarios in `raw_pointer_ops.rs` pass natively but remain under `cfg(test)` and
are not extracted/proved callers. The new `raw_memory_views.rs` companion gives
these scenarios ordinary public entry points. Its stored-pointer observation,
sixteen-byte update, allocation/deallocation lifecycle, and nested Box client now
have proved, explicitly adapted Lean clients. The nested client uses a composable
return-authority protocol, not an exact-final-state callback assumption.
Current extraction blockers are recorded below. Dated results below are historical.

**Relational WP migration:** `WP.spec` and `HeapWP.Spec` accept the explicit
abort `Result.oom`, but still reject panic, undefined behavior, and divergence.
Allocation/exposure specifications quantify over all compatible successors;
unavailable placement reports OOM instead of requiring a client existential.
Read/write/borrow/return operations remain checked, so an invalid access cannot
be excused by the universal WP. OOM does not run later continuations or produce
a value satisfying the successful-return postcondition.

All heap examples, including the safe owning-list API and nested exposures,
use this policy. Their client proofs no longer contain `unseal Result`;
pure-to-heap reasoning uses `HeapWP.Spec.of_spec`. The full default backend and
test-library builds pass, including the OOM, rejected-error, disabled-access,
and universal-choice regressions in `Aeneas.Std.HeapTests`.

## Scalar-vector paper example and complementary views

`tests/src/raw_scale.rs` replaces the proposed increment toy with a single
wrapping-u32 scaling kernel, disjoint and in-place safe wrappers, a shared raw
row-wise outer loop, and a raw-to-safe-to-raw variant. `Row13` privately stores
sixteen initialized u32s at 32-byte alignment; safe clients see `[u32; 13]`
borrows. The three hidden zero lanes are array elements, not compiler padding.
Kernel lengths and matrix row counts are const parameters. Zero iterations
need no pointer access or arithmetic. Its contract excludes partial overlap
without claiming that every partial overlap is Rust UB.

`tests/src/raw_matrix_view.rs` adds a two-row matrix with the same logical and
physical row widths. It compares safe flattening with a raw matrix-to-flat
borrow, a pure safe scaling call, and a raw aggregate read after the borrow ends.
The manually adapted raw kernel and safe outer wrapper have checked framed
proofs, including wrapping arithmetic. This is not unedited end-to-end extraction.

`tests/src/raw_memory_views.rs` separately exercises heap initialization,
eight-u16/sixteen-u8 mutable views, numerical observation of a stored pointer,
and nested boxed subslices. It also copies stored pointers, observes them after
physical deallocation.
The pointer examples do not reconstruct pointers from integer bytes. None uses
opaque Rust wrappers to conceal an unsupported primitive.

**Evidence, not an end-to-end verification claim:**

| Layer | Result |
|---|---|
| Rust debug/release, warnings denied | All twelve pre-zeroization tests pass: five scaling, three matrix, four memory-view tests. |
| Miri, default settings | All twelve pre-zeroization tests pass. This is finite execution evidence, not a proof of all safe API calls. |
| AVX2 code generation | An optimized `Row13` disjoint wrapper uses two 256-bit `vpmulld` instructions and two aligned stores, without a scalar tail. This is a target-specific observation, not a compiler-correctness theorem. |
| Current heap model | `RawPointerOps/Checks.lean` passes, including new scaling checks for disjoint shared-source ranges within one allocation, identical pointers, framing, overflow, zero length, and pure safe-update return followed by raw observation. |
| Whole-file Charon | All three files translate with the pinned Charon. |
| Whole-file Aeneas | All three are registered known failures. `RawMatrixView`, `RawScale`, and `RawMemoryViews` contain marked manual adaptations, not successful whole-file extraction. |
| Matrix proof | `RawMatrixView.lean` checks the concrete descriptor, extracted safe loop/helper, patched raw kernel, and reconstructed safe wrapper, for all wrapping inputs. Exact axiom guards allow only `propext`, `Classical.choice`, and `Quot.sound`. |
| Scaling proof | `RawScale.lean` checks the shared disjoint-or-equal raw kernel for every length, with exact wrapping results, source preservation in the disjoint case, and arbitrary frames. Same-allocation disjoint subranges are covered. `scale_into.spec`, `scale_in_place.spec`, and `scale_via_borrow.spec` prove the safe row wrappers without exposure-placement premises, accepting OOM. The reverse-boundary kernel and wrapper also cover every wrapping input. |
| Memory-view proofs | `RawMemoryViews.lean` checks stored-pointer observation/reuse, the eight-u16/sixteen-u8 update and safe wrapper, first write/read/deallocation, nested Box return, and pointer-copy clients. Exact axiom guards allow only `propext`, `Classical.choice`, and `Quot.sound`. See the adaptation boundaries below. |
| Integration | `cd backends/lean && lake build` and `cd tests/lean && lake build` pass after the relational WP migration. |
| Remaining universal contracts | The outer row loop and its wrappers remain parked. `copy_after_deallocation` has a proved raw tail, not a complete allocation/stack-exposure wrapper theorem. |

The model checks are explicitly handwritten counterparts, with the existing
four-byte little-endian `raw_box.u32Repr`. They do not validate extraction,
establish the row-loop theorem, or derive target ABI layouts. Safe exposure
wrappers cover every permitted forward successor, accepting OOM if placement
is unavailable, and derive backward-return enabledness on continuing paths.

### Checked lifecycle, nested views, and provenance

`RawMemoryViews/Initialization.lean` proves a real uninitialized allocation,
first typed write, exact read, and physical deallocation with arbitrary frames.
The external allocator outcome is an explicit `available : Bool` in the
adaptation. Its null/`handle_alloc_error` branch is modelled by `Result.oom`,
not panic. `first_heap_write.spec` covers either allocator outcome: successful
returns have the exact initialized value; OOM aborts without fabricating one.
This is not a model of the OS allocator's behavior.
`Aeneas/Std/Heap/Lifecycle.lean` proves that deallocation marks the root dead,
preserves disjoint frames, and prevents further reads.

`Nested.lean` and `NestedBox.lean` prove the nested Box example through both real
backward computations: Box-to-raw, raw-to-safe middle slice, smaller raw
re-exposure, inner retirement, outer permission restoration, and Box return.
The result is exactly `[1,1,2,2,2,3,3,3,3,2,2,2,4,4,1,1]`. The two-byte prefix
and suffix are framed through the middle update, and arbitrary external frames
are preserved. `ExclusiveReturn.lean` and `ScopedView.lean` supply the
composable authority: the inner computation may modify its fresh view, must
retire it, and leaves old view records unchanged. The adaptation retains the
emitted safe fill/indexing computations, restores missing effectful backward
calls, and represents the fixed Rust array by an isomorphic `Vector U8 16`.

`Provenance.lean` uses the actual byte-copy operation from `Heap/Copy.lean`.
Copying into uninitialized writable pointer storage preserves symbolic pointer
lanes and returns the exact pointer. Dereferencing the copied pointer requires
separate pointee ownership. Pointer metadata can remain valid after retirement
or physical deallocation; live access cannot. Checked negative contracts reject
reads through retired views and unissued provenance, even at the same numerical
address as a valid pointer. The deallocation/copy/address-observation theorem
starts with exposed stack slots and an owned pointee. It proves that raw tail,
not the complete surrounding Rust allocation and stack-exposure wrapper.

`ByteFill.lean` proves the raw byte loop over arbitrary writable bytes, including
uninitialized bytes and symbolic pointer lanes, without reading an old typed
value. The nested-view client uses this loop to fill the inner exposure.

### Standalone zeroization

`tests/src/raw_zeroize.rs` is a dependency-free adaptation of RustCrypto
**zeroize 1.9.1**, not a verification of the whole crate:
[MaybeUninit slice implementation](https://docs.rs/zeroize/1.9.1/src/zeroize/lib.rs.html#419-442)
and [volatile_set](https://docs.rs/zeroize/1.9.1/src/zeroize/lib.rs.html#740-765).
The inspected crate checksum is
`e13084392c5e4bc371903e2935a5eaeed24905a7511356b883835e18a78f6879`.

The standalone source changes are deliberately small:

- The safe interface is `zeroize<T>(storage: &mut [MaybeUninit<T>])`, as in the
  upstream slice implementation. Raw pointers occur only inside the body;
  no initialized T is read. An arbitrary `&mut [T]` would be unsound when zero
  is invalid for T, so the interface deliberately retains MaybeUninit.
- The volatile helper is inlined and specialized to u8 zero stores instead of
  MaybeUninit<u8>. Both initialize exactly the same bytes.
- The `isize::try_from(size).is_ok()` check is expressed as
  `size <= isize::MAX as usize`. Checked multiplication and the Range loop remain.
- The safe u32 wrapper uses explicit `ptr::from_mut` and a temporary one-element
  MaybeUninit slice. Its return is safe because all-zero u32 is valid. No fence
  is added: the inspected upstream slice path and helper do not use one.

Whole-file Charon and Aeneas emission succeed, including the safe wrapper.
The checked `RawZeroize/Funs.lean` is an **adapted emission**, not untouched output.
`RawZeroize/adaptation.patch` records the exact Types.lean and Funs.lean diffs
from fresh emission:

1. Supply `Repr.u8` to pointer addition.
2. Replace the generated volatile external with `write_volatile := MutRawPtr.write
   Repr.u8`. This is a definition, not an axiom.
3. Replace the generated cast external with a transparent provenance-preserving
   `RawPtr.cast`.
4. Make target layout explicit as `elementSize : Usize`; `size_of` returns it.
   The emitted checked multiplication, Option.expect, isize cast, assertion,
   iterator, and store sequence are retained. The u32 caller supplies four.
5. Replace the emitted pure `Slice (MaybeUninit T)` with local `UninitSlice T`
   metadata (pointer and length). The storage remains in the heap under
   `writableBytes`; it is never decoded into a T or copied into a pure slice.
   The type parameter indexes layout, so the wrapper's cast to MaybeUninit<u32>
   keeps U32 as its pointer index.
6. Model `as_mut_ptr` and the wrapper's temporary `from_raw_parts_mut` as local
   metadata views of the existing exclusive heap region. Ending that temporary
   slice is a no-op: it neither re-encodes stale contents nor creates/retires
   a second exposure. This is a deliberately specialized boundary adaptation,
   not a general model or proof of arbitrary Rust reference aliasing or slicing.
   In particular, the raw-parts model does not itself enforce Rust's non-null,
   alignment, extent, or exclusivity requirements. The actual Rust wrapper
   establishes them from its one-element u32 borrow; the heap proof uses the
   corresponding exclusive resource and layout descriptor.
7. Use the existing `core.ptr.from_mut raw_box.u32Repr` model and execute its
   effectful `back`, instead of returning the stale value saved by the emitter.
8. Remove generated linter/recursion-limit/noncomputable boilerplate and the
   unused TypesExternal import; no generated external axioms are imported.

`RawZeroize/Properties.lean` proves that every byte in `storage.len * elementSize`
becomes numerical zero and the returned storage handle is unchanged, with
arbitrary frames and heap invariant preserved. It proves
the emitted Range loop directly using the existing single-byte access lemmas;
it does not replace the loop with `fill_raw`. The numeric precondition is that
the mathematical byte count fits isize, which also makes checked multiplication
succeed. Empty/ZST ranges have a pure no-access theorem for the adapted model.
This does not license null or otherwise invalid safe Rust slices: Rust's
reference validity requirements still apply even when no bytes are accessed.
Typed restoration requires a witness that the zero bytes encode the requested
value; initialized bytes alone do **not** imply a valid T or T::default().
The safe u32 theorem supplies the zero witness and proves exposure return on
success, without a placement-feasibility precondition; OOM is accepted.

`zeroize.post_read_eq` proves that the exact-zero byte postcondition implies
`Heap.read repr q s = repr.decode (Vector.replicate repr.size (.data 0#u8))`
for every aligned, positive-sized read wholly inside that region, with the
region's provenance. `zeroize.post_read_independent` consequently equates
corresponding reads in any two heaps satisfying that postcondition, even with
different allocation identities and surrounding heaps. Thus any successfully
read value is independent of the initial contents. No zero-value witness is
assumed: if the zero representation is invalid, both reads return none.
This concerns contents while the postcondition holds, not pointer addresses,
lengths, subsequent writes, or secrets retained outside the zeroized region.

This is a heap-effects proof. Rust uses volatile stores, but compiler non-elision,
event ordering, registers, old copies, swap, and physical secret destruction
are outside the theorem. Standard `write_bytes` is not a secure-erasure API.
Typed `Zeroize` need not mean zero bits (NonZero integers become one).
Drop-based `Zeroizing`/`ZeroizeOnDrop` only help when Drop runs; neither leaks,
`forget`, nor abort imply unconditional cleanup.

Reproduce without overwriting the checked adaptation:

```bash
"$CHARON_EXE" rustc --preset=aeneas --dest-file "$OUT/raw_zeroize.llbc" \
  -- --edition=2021 --crate-type=lib tests/src/raw_zeroize.rs
"$AENEAS_EXE" -backend lean -loops-to-rec -split-files -abort-on-error \
  -dest "$OUT" "$OUT/raw_zeroize.llbc"
patch --dry-run -d "$OUT" -p0 < tests/lean/RawZeroize/adaptation.patch
patch -d "$OUT" -p0 < tests/lean/RawZeroize/adaptation.patch
cmp "$OUT/Types.lean" tests/lean/RawZeroize/Types.lean
cmp "$OUT/Funs.lean" tests/lean/RawZeroize/Funs.lean
cd tests/lean && lake build RawZeroize
```

`OUT` must be a fresh disposable directory. `FunsExternal.lean` is the checked-in
primitive and local slice-view model; the raw external templates are not part
of the proof.
The normal `gmake test-raw_zeroize.rs` target also emits successfully, but like
the other adapted fixtures it overwrites Types.lean and Funs.lean: regenerate into a disposable
test-runner destination instead when preserving the proof tree.

Validation of this standalone example:

- Whole-file extraction and patch round-trip pass for Types.lean and Funs.lean.
- `cd tests/lean && lake build RawZeroize RawMemoryViews RawMatrixView RawScale`
  passes. The six exact axiom guards allow only `propext`, `Classical.choice`,
  and `Quot.sound`; no sorry or new axiom is used.
- A temporary Cargo manifest with a `[[test]]` target pointing to
  `tests/src/raw_zeroize.rs` passes `RUSTFLAGS='-D warnings' cargo test`,
  `cargo test --release`, and `cargo miri test` (each with that manifest).
  All three tests pass in each mode: padding/uninitialized and NonZero storage,
  typed zero plus neighboring values, and empty/ZST ranges. Oversized raw calls
  are not tests of this safe API: they cannot be supplied by a valid safe slice.
  The checked multiplication and isize assertion remain in the emitted body
  and their successful path is justified by the theorem's numeric precondition.
- `rustc --edition=2021 --crate-type=lib --emit=llvm-ir -O -D warnings
  tests/src/raw_zeroize.rs -o "$OUT/raw_zeroize.ll"` retains four volatile i8
  stores in zeroize_word on the current toolchain. This is target-specific
  evidence, not a proof of optimizer behavior.
- `gmake format` runs Rust formatting successfully; its ignored OCaml steps
  still report missing ocamlformat. No OCaml code was changed.

### Extraction blockers

Using the rebuilt compiler and Charon pinned by `charon-pin`:

| Entry point | Unedited-source extraction outcome |
|---|---|
| `raw_scale` (whole file) | Rejects a raw cast involving `Row13`: only casts between pointers to literal types are supported on this path. |
| `raw_scale::scale_raw` (isolated root) | Name clash: const and mutable `add` both map to `RawPtr.add`. Recovered whole-file emission also reports a const/mutable `RawPtr.read` collision. |
| `raw_scale::scale_via_borrow_raw` (isolated root) | Emits Lean with discarded updated slice/backward function and missing `Repr` on the final read; it is not a checked model of the Rust call. |
| `raw_matrix_view` (whole file) | Rejects `&raw mut (*matrix)` in the safe wrapper. |
| `raw_matrix_view::scale_raw` (isolated root) | Emits Lean. The checked adaptation supplies descriptors, concrete external models, and the matching effectful backward call, as detailed below. |
| `first_heap_write` | Symbolic translation fails with `Unexpected result: Cps.Unit`. |
| `update_word_bytes` | Emission and Lean typechecking succeed, but against newly generated opaque axioms, **not** the current heap boundary models. Mutable write-back is discarded. |
| `stored_pointer_address` | Emission succeeds; Lean rejects the missing `Repr` argument to `RawPtr.read`. |
| `nested_views` | Emission succeeds; Lean rejects missing descriptors for pointer/Box operations. Generated slice boundary types also use obsolete, pure backward functions. |
| `copy_stored_pointer` (isolated root) | Emission succeeds with opaque copy/cast/size externals; Lean rejects the missing `Repr` on the final pointer read. |
| `raw_zeroize` (whole file) | Emission succeeds. The exact descriptor, primitive, layout, and backward-call adaptations are documented above. |

The byte-view case is particularly important: typechecking alone is insufficient.
The generated `from_raw_parts_mut` has an opaque `Slice T → Unit` callback,
the caller binds it as `_`, and the final result returns the slice saved by
`as_mut_ptr`, not the updated bytes. Its last byte assignment is also absent.
The generated file was kept outside the repository and is not imported by the
passing model checks. The new pointer-copy diagnostics likewise remain
outside the repository. No replacement axioms were added to make these examples
appear verified.

### Commands and reproduction

The ordinary `bin/` tool locations are absent in this checkout. Setting
`AENEAS_EXE` to `src/_build/default/main.exe`, `TEST_RUNNER_EXE` to
`tests/test_runner/_build/default/run_test.exe` (absolute paths), and
`CHARON_EXE` to the recovered pinned Charon executable:

```bash
gmake test-raw_scale.rs test-raw_memory_views.rs test-raw_matrix_view.rs IN_CI=1 \
  AENEAS_EXE="$AENEAS_EXE" TEST_RUNNER_EXE="$TEST_RUNNER_EXE" CHARON_EXE="$CHARON_EXE"
cd tests/lean && lake env lean RawPointerOps/Checks.lean
```

Both commands pass: the first records the **expected failures** in
`tests/src/raw_scale.lean.out`, `raw_memory_views.lean.out`, and
`raw_matrix_view.lean.out`, not working
translations. The second checks the whole existing model regression file,
without writing shared `.lake/build` artifacts while the editor's Lean server
is active. The later sequential integration builds are recorded above.

Per-entry diagnostics use the unchanged Rust sources with Charon's
`--start-from crate::ENTRY`, then Aeneas `-backend lean -loops-to-rec
-abort-on-error`, then `lake env lean` on the generated file. All diagnostic
outputs remain outside the repository.

Native validation used a temporary Cargo manifest with three `[[test]]` targets
pointing directly at these Rust files: `RUSTFLAGS='-D warnings' cargo test`,
the same command with `--release`, and `cargo miri test`, each with
`--manifest-path "$CHECKS/Cargo.toml"`. All passed.
`gmake format IN_CI=1` passes its Rust formatting check; its ignored OCaml
formatting steps report missing `ocamlformat`. No OCaml source was changed.

### Checked matrix adaptation

The current isolated extraction is reproducible with the same pinned tools:

```bash
"$CHARON_EXE" rustc --preset=aeneas \
  --start-from raw_matrix_view::scale_raw \
  --dest-file "$OUT/raw_matrix_view.llbc" \
  -- --edition=2021 --crate-type=lib tests/src/raw_matrix_view.rs
"$AENEAS_EXE" -backend lean -loops-to-rec -split-files -abort-on-error \
  -dest "$OUT" "$OUT/raw_matrix_view.llbc"
```

Both commands pass. Use a disposable output directory: extraction must not
overwrite the marked adaptation in `tests/lean/RawMatrixView/`.
The emitted `Matrix` type and safe function bodies are retained. The generated
external template is not imported: its pointer cast is modeled by the existing
provenance-preserving cast, and its obsolete pure slice callback is replaced by
the existing effectful library primitive. In `scale_raw`, the adaptation:

1. supplies `raw_box.u32Repr` to the slice borrow and `matrixRepr` to the read;
2. retains `(flat, back)` and the updated `flat` returned by the safe helper;
3. invokes `back flat` before reading the matrix through its original pointer.

The safe `scale` wrapper is separately reconstructed using `core.ptr.from_mut`
and its matching backward computation; its original implicit raw coercion is
still rejected by extraction.

`Layout.lean` constructs a complete little-endian, 128-byte, 32-byte-aligned
descriptor with no compiler padding. It proves both matrix/flat-value inverse
laws and exact conversions between whole-matrix and 32-word heap resources.
This explicitly chosen layout is calibrated by Rust layout tests; it is not a
formal derivation of the Rust target ABI.

`Properties.lean` proves the extracted safe loop/helper and
`raw_matrix_view.scale_raw.spec`. The latter quantifies over arbitrary valid
initial matrices and disjoint frames, with wrapping multiplication on all 32
words and no product bound. The resulting heap contains exactly `scaledMatrix k initial`,
and the returned value is its last logical element. `scaledMatrix_values`
identifies every output word with ordinary natural-number multiplication when
products fit;
`scaledMatrix_zeroPadded` preserves the three zero lanes in each row.
The proof uses the authority captured by `borrowRange_return.spec`, not a
client-supplied return-validity assumption.

`Wrappers.lean` proves `scale.spec`: the safe wrapper returns the updated matrix
and its last logical element, executes both backward computations, and preserves
the external frame on success. Like the scaling wrappers, it accepts OOM
without requiring a placement-existence premise.

Validation passed, without refreshing shared backend build artifacts:

```bash
cd tests/lean
for module in Types FunsExternal Funs Layout Properties Wrappers; do
  lake env lean "RawMatrixView/$module.lean" \
    -o ".lake/build/lib/lean/RawMatrixView/$module.olean" || exit 1
done
lake env lean RawMatrixView.lean
```

All six modules compile without warnings, and the root's exact axiom guards
pass. No `sorry`, new axiom, or native decision procedure is used in these
proofs. This checks the adapted matrix library, not the complete default build.
The raw and safe-wrapper theorems include overflowing products.

### Checked scaling adaptation

`tests/lean/RawScale/` retains the emitted scalar and row iterator bodies and
the safe slice loop. To recover the computational bodies despite recorded
translation errors, emit into a disposable directory **without**
`-abort-on-error`:

```bash
"$AENEAS_EXE" -backend lean -loops-to-rec -split-files \
  -dest "$OUT" tests/llbc/raw_scale.llbc
```

This command reports errors; writing files is not successful extraction.
The adaptation makes these explicit changes:

1. supplies `raw_box.u32Repr` to scalar add/read/write and `rowRepr` to row-stride
   pointer addition;
2. replaces emitted casts with transparent, provenance/address-preserving
   `p.cast` operations; the emitted legacy `RawPtr.cast_scalar` always fails;
3. retains exposure cleanup and mutable backward computations, and executes
   the matching slice backward function with the updated slice;
4. exposes a whole aligned row before casting to its first u32, rather than
   allocating a fresh alignment-four scalar view and losing 32-byte alignment;
5. reconstructs `scale_rows_in_place` from its three Rust statements: extraction
   replaced this body with an axiom after rejecting its aggregate mut-to-const
   cast. The reconstruction is marked in `Funs.lean`.

The generated axiom template is not imported. Constructors, logical-prefix
accessors, and derived traits are outside the adaptation's current scope.
`Layout.lean` constructs a concrete 64-byte, 32-byte-aligned little-endian row
descriptor; as with the matrix, this is an explicit ABI model, not an extracted
Rust layout theorem.

The cast-free raw-place alternative `&raw const (*src.add(r)).0[0]` was checked
in a disposable Rust fixture. Rust and Charon accept it, but Aeneas rejects raw
pointer dereferencing in that path. The repository Rust therefore retains its
casts rather than exchanging one extraction blocker for another.

The checked proofs are:

- `Scalar.lean`: the loop-free `scale_one_raw` with equal/disjoint/combined
  contracts, plus `scale_one_into.spec` and `scale_one_in_place.spec`. The safe
  contracts use `empty`, hiding the arbitrary frame without losing it.
- `RangeAccess.lean`: framed indexed reads and pointer addition from range
  resources alone, without allocation-cleanup ownership.
- `RangeWrite.lean`: an indexed write updates exactly one element while framing
  the rest of the range. This works for subranges of the same allocation.
- `Properties.lean`: equality of the two emitted safe-loop fixed points, the
  safe scaling contract, zero-length behavior, the terminating heap loop rule,
  and `scale_via_borrow_raw.spec` using captured matching return authority.
- `Kernel.lean`: `scale_raw.in_place_spec`, `scale_raw.disjoint_spec`, and the
  combined `scale_raw.spec`. These prove the actual emitted iterator/scalar
  algorithm, not a replacement borrow-and-map implementation.
- `RowResources.lean`: row/word resource conversions, exclusive-exposure
  calibration, and read-only decoding of shared rows, including symbolic bytes.
- `Exposure.lean`: shared exposure creates read-only resources, and matching
  cleanup validates the original value and retires the exposure.
- `Wrappers.lean`: `scale_into.spec` and `scale_in_place.spec` compose the raw
  kernel with actual exposures and backward computations. Both return `scaledRow`,
  preserve the external frame, and retire their temporary exposures.
  `scaledRow_get` covers every physical lane (hence the thirteen visible lanes);
  `scaledRow_zero_padding` preserves the three hidden zero lanes.
  `scale_via_borrow.spec` additionally proves the reverse-boundary wrapper,
  returning its first scaled word and the updated row.

The raw loop contracts use exact wrapping multiplication for every u32 input;
they require address arithmetic to fit, not products to fit. `scaledWords_values`
derives ordinary multiplication under product bounds, and `scaledWords_zero`
preserves hidden zero lanes. The disjoint contract preserves the source at any
sharing depth; the equal case owns only one exclusive range. All contracts
preserve arbitrary disjoint frames.

`RawScale/Notation.lean` provides scoped paper-facing notation, enabled by
`open scoped Aeneas.Std.HeapWP`:

```lean
⦃ sourceRange ∗ destinationRange ⦄
scale_raw N k src dst
⦃ _ => sourceRange ∗ scaledDestinationRange ⦄
```

Here `∗` is separating conjunction, and the complete expression expands to
`HeapWP.Triple`; its implicit arbitrary frame is unchanged. Typed result binders,
tuple decomposition, and an explicit postcondition function are supported.
The existing pure notation `c ⦃ result => proposition ⦄` is unchanged.
This is concrete syntax only, not registration with the `step` tactic.
`Scalar.lean`, `Kernel.lean`, and `Wrappers.lean` use it for the scalar, vector,
and safe-wrapper contracts.

### Opening example: one scalar multiplication

`tests/src/raw_scale.rs` starts with `scale_one_raw`, `scale_one_into`, and
`scale_one_in_place`. The vector loop now computes its two indexed pointers and
calls the scalar kernel. Reading still precedes writing; pointer addition for
the destination now precedes the read, as emitted from that Rust call.

Fresh emission with Charon `de8736f7c995ac54dc490345cef9ea5143c06c62` and the
current Aeneas binary produces all three scalar bodies and that factored loop.
The whole-file command still fails on the aggregate mut-to-const cast and
duplicate builtin pointer names (five reported errors, three unique).
The scalar bodies below are actual partial emission, **not** a successful
end-to-end extraction:

```lean
def scale_one_raw
  (k : Std.U32) (src : ConstRawPtr Std.U32) (dst : MutRawPtr Std.U32) :
  Result Unit
  := do
  let value ← RawPtr.read src
  let i ← lift (core.num.U32.wrapping_mul k value)
  MutRawPtr.write dst i

def scale_one_into
  (k : Std.U32) (src : Std.U32) (dst : Std.U32) : Result Std.U32 := do
  let p ← core.ptr.from_ref src
  let (p1, dst1) ← core.ptr.from_mut dst
  scale_one_raw k p p1
  ok dst1

def scale_one_in_place (k : Std.U32) (value : Std.U32) : Result Std.U32 := do
  let (p, value1) ← core.ptr.from_mut value
  let p1 ← RawPtr.cast_scalar Std.U32 .Const p
  scale_one_raw k p1 p
  ok value1
```

The checked adaptation in `RawScale/Funs.lean` is:

```lean
def scale_one_raw (k : U32) (src : ConstRawPtr U32) (dst : MutRawPtr U32) :
    Result Unit := do
  let value ← RawPtr.read raw_box.u32Repr src
  let i ← lift (core.num.U32.wrapping_mul k value)
  MutRawPtr.write raw_box.u32Repr dst i

def scale_one_into (k : U32) (src dst : U32) : Result U32 := do
  let (p, src_back) ← core.ptr.from_ref raw_box.u32Repr src
  let (p1, dst_back) ← core.ptr.from_mut raw_box.u32Repr dst
  scale_one_raw k p p1
  let dst ← dst_back
  src_back
  ok dst

def scale_one_in_place (k : U32) (value : U32) : Result U32 := do
  let (p, back) ← core.ptr.from_mut raw_box.u32Repr value
  let p1 ← ext.cast U32 p
  scale_one_raw k p1 p
  back
```

For the kernel, the only semantic patch is supplying the concrete four-byte
little-endian representation to read/write. For the wrappers, `from_ref` now
returns the pointer and its matching shared backward computation; `from_mut`
receives the same representation, and the mutable return executes the actual
effectful backward computation rather than returning the emitted stale value.
The equal-mode cast preserves address and provenance. All those changes are
manual model adaptations, not compiler-correctness results.

For the paper, the progression is **scalar kernel → unsafe vector loop → safe
disjoint and in-place wrappers**. Show the scalar translation above, then the
Rust `scale_raw` loop (without its recursive Lean translation), then the two
row wrappers. Both wrappers call the same `scale_raw`, which calls
`scale_one_raw` for each lane. The scalar-only safe wrappers remain small
boundary examples, rather than the main vector API.

The adapted vector wrappers in `Funs.lean` expose both return paths explicitly:

```lean
def scale_into (k : U32) (src : Row13) (dst : Row13) : Result Row13 := do
  let (p, src_back) ← ext.row_as_ptr src
  let (p1, dst_back) ← ext.row_as_mut_ptr dst
  scale_raw 16#usize k p p1
  let dst ← dst_back
  src_back
  ok dst

def scale_in_place (k : U32) (buf : Row13) : Result Row13 := do
  let (p, back) ← ext.row_as_mut_ptr buf
  let p1 ← ext.cast U32 p
  scale_raw 16#usize k p1 p
  back
```

`row_as_ptr` obtains its callback from `core.ptr.from_ref rowRepr`;
`row_as_mut_ptr` obtains its callback from `core.ptr.from_mut rowRepr`.
Both cast only the exposed pointer to the first word, retaining the callback
for the containing row. Equal mode exposes one mutable borrow and runs one
callback, not two overlapping exposures.

The scalar raw contracts start from `readable` resources, including symbolic
bytes that decode to the input. A write establishes the stronger `pointsTo`
encoding. At depth zero the resource is exclusive; no representability or
allocation-placement existence assumption is added to the safe contracts.
The root `RawScale.lean` checks their exact axiom dependencies and demonstrates
adding an arbitrary assertion with `HeapWP.frame`.

The safe-wrapper contracts are framed heap triples (`HeapWP.Triple`), not ordinary
effect-free `WP.spec`: their bodies still expose and retire temporary heap views.
Their value postconditions are simply `result = scaledRow k src` and
`result = scaledRow k buf`, with `empty` before and after the call. Here `empty h`
means `h = ∅`, not an empty global heap: the frame and its matching invariant are
implicit in the triple. They impose no product-overflow condition.
The finite-address model can report OOM at either exposure. No placement-existence
premise remains, including no nested destination-feasibility premise after source
placement. Continuing paths cover every permitted placement, not just a favorable
choice. This does not assert that allocation always succeeds.

The shared-source proof permits decodable symbolic pointer lanes, which a
read-only scalar exposure can legally retain in this model. It does not silently
assume that every such exposure has a canonical numeric write encoding.
The original canonical-range kernel theorems remain available unchanged.

Validation passed using the already-built shared dependencies:

```bash
cd tests/lean
for module in Types Layout FunsExternal Funs RangeAccess RangeWrite Properties Notation Kernel RowResources Exposure Wrappers; do
  lake env lean "RawScale/$module.lean" \
    -o ".lake/build/lib/lean/RawScale/$module.olean" || exit 1
done
lake env lean RawScale.lean
lake env lean RawMatrixView.lean
```

The exact root axiom guards permit only `propext`, `Classical.choice`, and
`Quot.sound`. No `sorry`, new axiom, or native decision procedure is used.
The targeted checks do not establish a successful complete default build.

### Paper readiness and next proof milestones

The Rust series covers more than the draft's `copy_incr` running example, but
its proof coverage is narrower than its source-code coverage:

| Draft point | Example coverage | Remaining paper obligation |
|---|---|---|
| One disjoint-or-equal kernel, two safe interfaces | `raw_scale` | Shared raw loop and both safe row wrappers are proved on the marked adaptation; OOM is accepted without placement-existence premises. |
| Compositional outer computation | Shared raw matrix loop in `raw_scale` | Row-wise theorem; a safe outer caller would separately illustrate heap-free composition. |
| Pure safe baseline | In-place `scale_slice` and matrix `scale_safe` | A direct disjoint safe scaling baseline would mirror the draft more closely. |
| Raw-to-safe borrow, update, then raw observation | Both scaling files | Both patched raw kernels and their safe wrappers are proved; automated backward plumbing remains open. |
| Alignment and initialized padding | Private `Row13` and `Matrix` storage | Matrix representation and padding preservation are proved; general `Row<N>` extraction is not. |
| Initialization, mixed-width access, stored pointer bytes | `raw_memory_views` | Mixed-width update and pointer observation are proved on explicit adaptations; the full allocator lifecycle remains open. |
| Owned Box versus nested borrowed views | `raw_memory_views::nested_views` | Composable nested return authority and its client proof. |

The current priority returns to the original, pre-paper roadmap: complete the
first-write allocator lifecycle, then nested re-exposure. Row-wise composition
is parked rather than complete. Compiler/model integration still needs descriptor
plumbing, unambiguous primitive names, aggregate pointer casts, and effectful
matched write-back. The draft itself leaves its loop/wrapper proofs as TODOs;
the checked shared scaling loop and safe row wrappers discharge the corresponding
obligations for this adapted example, subject to the stated placement assumptions.

Nested re-exposure additionally needs a library return-authority theorem usable
after nested heap effects. `borrowRange_return.spec` captures return authority
at the forward state; the matrix proof can use it because `scale_slice` is pure
and preserves that state. It cannot simply be reused after `nested_views` has
created and ended further exposures. This is a missing compositional proof
interface, not evidence that the Rust example is invalid.

A session-only `Row<N>` prototype with storage `[u32; n.div_ceil(8) * 8]`
compiled natively, but pinned Charon rejected its computed const generic.
The agreed paper fixture therefore uses concrete `Row13`, while retaining
const-generic kernel lengths and matrix row counts.

### Checked original memory-view clients

`RawMemoryViews/Repr.lean` constructs a concrete eight-byte little-endian `usize`
descriptor under an explicit `UScalarTy.numBits .Usize = 64` premise.
`Pointer.lean` adapts `stored_pointer_address`
by replacing the opaque pointer cast with the model's transparent cast and
supplying that descriptor to `RawPtr.read`.

`stored_pointer_address.spec` returns exactly the stored pointer's numerical
address while preserving the original pointer `pointsTo` resource, including
all symbolic pointer lanes. It requires permission to the pointer slot, not to
the pointee. `stored_pointer_address.use_spec` frames pointee permission during
observation, reloads the same pointer, and then writes and reads an arbitrary
value through it. It is a composition theorem for the native test's continuation,
not an additional extracted Rust entry point. Neither theorem reconstructs
provenance from numeric bytes.

`ByteLayout.lean` models `[u16; 8]` as sixteen contiguous, little-endian initialized
bytes with alignment two. It proves codec inverses and exact conversions between
whole-array and sixteen-u8 range resources. `ByteView.lean` restores the emitted
caller's missing final assignment and matching effectful callback. Its outer
safe-array exposure is reconstructed with `core.ptr.from_mut`, replacing the
obsolete `as_mut_ptr`/saved-slice plumbing. The two native-byte conversions are
specialized to little endian; the proof does not claim an arbitrary Rust target ABI.
They are pure, total operations grouped with the four safe byte assignments.

`update_word_bytes_raw.spec` returns the byte borrow and restores the aligned
word resource. `update_word_bytes.spec` also runs the outer backward computation
and returns the safe array. Both specify exactly
`updatedWords words first last`: word 0 becomes `first`, word 7 becomes `last`,
and words 1 through 6 remain unchanged (`updatedWords_get`). Arbitrary disjoint
frames are preserved on success. The safe wrapper accepts OOM without an
exposure-feasibility premise.

Validation passed using existing dependencies:

```bash
cd tests/lean
for module in Repr Pointer ByteLayout ByteView; do
  lake env lean "RawMemoryViews/$module.lean" \
    -o ".lake/build/lib/lean/RawMemoryViews/$module.olean" || exit 1
done
lake env lean RawMemoryViews.lean
```

The exact root axiom guards permit only `propext`, `Classical.choice`, and
`Quot.sound`; no new axiom, `sorry`, or native decision procedure is used.
These are universal proofs of adapted clients, not evidence that the extraction
defects listed above are repaired. The existing initialization primitive proof
does not yet prove `first_heap_write`'s allocator/null/error/deallocation path.
In particular, returning an owned view to safe Rust is not physical deallocation.

## Isolated extraction diagnostic for the four newer scenarios

The pinned Charon (`de8736f7c995ac54dc490345cef9ea5143c06c62`) and its OCaml
library were restored in session storage, and the current compiler and test
runner were rebuilt. The ordinary Make target initially failed because its
expected `charon/` installation was absent. Tool recovery did not change the
pin, compiler source, adapted fixtures or global authentication.

An isolated extraction of the four `#[test]` entry points first encountered
test-harness function-pointer translation errors. A temporary copy with only
the `#[test]` attributes removed separated harness issues from the actual
function bodies. With `CHARON_EXE` set to the restored executable and `OUT`
to a temporary output directory, the body diagnostic was:

```bash
sed '/^[[:space:]]*#\[test\]/d' tests/src/raw_pointer_ops.rs > "$OUT/raw_pointer_scenarios.rs"
"$CHARON_EXE" rustc --preset aeneas --sysroot default --opaque 'crate::ext' \
  --start-from 'crate::tests::first_write_initializes_heap_allocation' \
  --start-from 'crate::tests::eight_words_and_sixteen_bytes_share_storage' \
  --start-from 'crate::tests::pointer_loaded_from_memory_as_an_integer' \
  --start-from 'crate::tests::boxed_array_nested_safe_and_raw_subslices' \
  --rustc-arg=--cfg=test --dest-file "$OUT/raw_pointer_scenarios.llbc" \
  -- --edition=2021 --crate-type=lib "$OUT/raw_pointer_scenarios.rs"
src/_build/default/main.exe -backend lean -dest "$OUT/lean" \
  -split-files -all-computable "$OUT/raw_pointer_scenarios.llbc"
```

Result: Charon succeeded; Lean translation failed. The compiler rejects the
raw borrow produced by `&mut target as *mut u32` (`Unsupported operation:
&raw mut (*_3)`) and detects a name clash between const and mutable `read`
under `RawPtr.read`. It also reports missing `Step` model fields
`forward_overflowing` and `backward_overflowing`. Partial generated files and
external templates are not validated translations, and none was imported by
the passing proof targets. This diagnostic is not an unedited-source extraction
claim, because the temporary copy excludes test registration attributes.

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
the safe value with `empty`. The caller cannot regain a safe value by retaining
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
`Node.mk` as a smart constructor copying both pointer fields' base/address,
and restore the `Node` phantom tag in `Node.prev` and `Node.next`. The existing
projection equations still hold by `rfl`; `Node.mk_eta` proves the converse.
No pointer identifier or concrete address is discarded.

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

## Local raw-pointer API examples

```
captured   : 2026-10-30 18:33 UTC
parent     : efe1de18f3f3d768b61c1448f7efbca7d795f0aa
source     : tests/src/raw_pointer_ops.rs, Git blob d8caf26c8a1650efea90b0720dc55cb761e4895e
aeneas     : 985460dbbf187af891aab0201a8c046a2ed98ffe; unchanged shared read-only executable
charon     : 26abff028ced534ebf8e861f2d3dd1743e2aa318; unchanged shared read-only executable
charon-pin : experiment remains de8736f7c995ac54dc490345cef9ea5143c06c62
rustc      : Charon nightly-2026-09-17 (1.100.0-nightly, 923c95cdf 2026-09-16)
options    : Charon --opaque=crate::ext; Lean -split-files -all-computable; existing test runner supplies -checks and diagnostic flags
```

Command, run from the isolated experiment checkout:

```sh
make test-raw_pointer_ops.rs IN_CI=1 \
  AENEAS_EXE=/workspaces/aeneas/bin/aeneas \
  TEST_RUNNER_EXE=/workspaces/aeneas/bin/test_runner \
  CHARON_EXE=/workspaces/aeneas/charon/bin/charon
```

`IN_CI=1` skips the development compiler build. The shared binaries, sources,
and configuration were not changed. The actual Charon revision above differs
from the experiment's historical pin; this entry records the tools actually
used rather than claiming pin synchronization.

The fixture emits `RawPointerOps/Types.lean`, `Funs.lean`, and
`FunsExternal_Template.lean`; all three are preserved without post-extraction
edits. No descriptor-threading or positivity repair is needed for these
callers. The external template remains unimported. `FunsExternal.lean` supplies
transparent handwritten models for all twelve opaque wrappers, with explicit
descriptors and a borrow/restore model for the slice-fill wrapper. Thus this
fixture checks callers against an explicit external-model boundary, not
automatic translation of the standard-library pointer implementations.

The opt-in backend models add replace, restricted swap, unaligned access,
byte movement, and same-allocation distance without builtin registrations.
Separate proof modules cover arbitrary-writable initialization, general
nonempty range permission transfer/restoration, and live aligned empty ranges.
`Properties.lean` proves exact framed contracts for every generated caller;
`Checks.lean` exercises initialization, alignment, permission denial, atomic
range rejection, pointer-distance restrictions, and explicit failure for
unsupported partial-overlap swap.

`make verify-raw-pointer-api` checks the backend proof closure, generated
callers, external models, contracts, concrete checks, and exact axiom guards.
The guarded contracts depend only on `propext`, `Classical.choice`, and
`Quot.sound`; native computation checks are separate. All eight native Rust
tests also pass with address/leak sanitization using nightly-2026-09-17.
Rustfmt passes, as do the existing `verify-raw-box` and `verify-doubly-linked`
regressions. These results establish model contracts and executable-example
behavior, not Rust ABI correspondence or compiler correctness.
