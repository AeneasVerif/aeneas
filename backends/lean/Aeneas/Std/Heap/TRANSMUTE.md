# Transmute, casts, and typed byte views

This document records the design decisions, pitfalls, related work, and
Rust-to-Lean examples for the isolated byte-memory-model experiment.
See the [memory-model overview](README.md) for representations, permissions,
allocation, and safe/raw boundaries, and the
[extraction log](../../../../../tests/lean/EXTRACTION.md) for toolchain provenance
and manual translation adaptations.

**Status:** the representation-level exact-result theorem, thin-pointer
round trips, concrete by-value examples, and mutable word/byte-array view are
proved in the model. This is not a general implementation of Rust's transmute
intrinsic, a Rust ABI calibration, or a compiler-correctness theorem.

## Design decision

Use explicit source and target `Repr` descriptors to state compatibility, and
prove conversions within the model rather than introducing an unproved
transmute specification for every concrete type pair.

The initial supported by-value fragment consists of initialized plain values:
equal-size representations, valid target decoding for **every** source encoding,
and a **unique target value** for a specified source value. This does not require
a unique source encoding. Lifetime-changing references, owning/destructor-bearing
values, and pointer/integer conversions are outside this rule, including when
nested inside aggregates. Thin raw-pointer casts have a separate rule.

Rust still needs an actual implementation. Our fixtures use small Rust wrappers
around real standard operations, mark their bodies opaque for extraction, and
give the external calls transparent Lean models. Generated callers are then
proved against those definitions. The reusable `reinterpret.spec` is a model
theorem, not compiler wiring that intercepts arbitrary Rust transmute IR.

Case-specific unsafe Rust implementations through raw pointers are also a
valid development route: expose storage, cast, access it under the target
descriptor, and restore the safe source value under its descriptor. Their proof
must establish permissions, initialization, target validity, and restoration.
Zero-copy behavior or identical optimized machine code is useful evidence of
runtime fidelity, but does not discharge these obligations by itself.
Neither shared Aeneas nor shared Charon is changed by this experiment.

### By-value compatibility and uniqueness

A [representation](Repr.lean) supplies a size, alignment, partial byte decoder,
and completeness: every source value has some encoding. Completeness alone
does not relate different representations.

The original, more permissive proposal can be written schematically as:

```text
CompatibleAt(S, T, x) :=
  S.size = T.size and
  forall bytes,
    S.decode(bytes) = Some(x) =>
    exists y, T.decode(bytes) = Some(y)

Transmutes(S, T, x, y) :=
  exists bytes,
    S.decode(bytes) = Some(x) and T.decode(bytes) = Some(y)
```

Byte vectors are transported across the size equality. Compatibility is
directional and value-dependent; type-wide compatibility quantifies over `x`.
The permitted result may be the target decoding of **any** source encoding.
Success requires all such encodings to decode, not merely one favourable
encoding.

We chose the stricter, exact-result fragment for the implemented theorem:

```text
ExactAt(S, T, x, expected) :=
  S.size = T.size and
  forall bytes,
    S.decode(bytes) = Some(x) =>
    T.decode(bytes) = Some(expected)
```

In [RawValueCasts/Repr.lean](../../../../../tests/lean/RawValueCasts/Repr.lean),
`raw_value_casts.reinterpret` chooses any encoding of `x`, then decodes those
bytes at the target, failing with `.undef` if decoding fails.
`raw_value_casts.reinterpret.spec` proves exact result `expected` and unchanged
heap from precisely this universal hypothesis.
[Repr.choose](../Primitives.lean) has a demonic, heap-preserving contract:
the proof must cover **every** encoding that decodes to the source value.
It does not select the witness from `Repr.complete` as a canonical encoder.

This is a `HeapWP.Spec` theorem because the implementation uses an encoding-choice
effect, even though its heap is unchanged. The more permissive relational
specification above is a design formulation, not an additional implemented
general theorem.

Uniqueness captures the requirement that representation differences invisible
at the source remain invisible at the target. For padding, source padding must
not become observable target data. However, that observation does **not** solve
Rust's uninitialized-padding problem by itself; see the pitfalls below.

### Thin raw-pointer casts are separate

[RawPtr.cast](../Core/Ptr.lean) preserves allocation identity and byte offset
exactly, changes no storage or permissions, and performs no access.
Casting back recovers the original model pointer, including at a nonzero or
misaligned offset. It needs no equation relating the pointee decoders or sizes:
casting `*mut u32` to `*mut u8` is not a by-value conversion of a `u32` to a `u8`.

The representation **of a pointer value** is distinct from the representation
of its pointee. Reusing the generic by-value rule for pointers would require
calibrated pointer-value descriptors and provenance obligations; the current
pointer-cast model supplies neither an integer address encoding nor a general
pointer representation theorem.

Typed accesses separately check live storage, bounds, alignment, permissions,
initialized bytes, and decoding. Raw constness does not grant permissions.
Fat pointers, slice metadata conversions, and pointer/integer conversions are
not covered by this thin-pointer rule.

### Safe mutable views require restoration

A mutable view is not merely a by-value conversion of its initial contents.
The safe/raw API already requires full ownership transfer for the affected
footprint, and valid restoration before the safe source becomes available again.
Outstanding aliases do not retain conflicting access rights.

The obligations are:

1. Establish target alignment, bounds, permissions, initialization, and unique
   forward decoding.
2. Transfer the footprint's access rights to the borrow; preserve an arbitrary
   disjoint frame.
3. For **every** admitted target replacement and its possible encodings,
   establish source initialization and validity, with the specified restored
   source value. Checking only the initial contents is insufficient.
4. Run the matching effectful backward computation and consume its temporary
   exposure resources before returning the safe source.

For `bytes_view(&mut u32) -> &mut [u8; 4]`,
`raw_transmute_externals.bytes_view.spec` proves the exact forward bytes and
accepts every replacement array in the backward contract. It restores exactly
`fromLittleBytes replacement` and consumes the exposure footprint.
See [ArrayProperties.lean](../../../../../tests/lean/RawTransmuteExternals/ArrayProperties.lean).
Array access uses alignment one, while ownership retains the original
alignment-four word resources; the proof does not equate these alignments.

## Pitfalls and exclusions

The following are distinct obligations, not interchangeable reasons to reject
all casts. The unsafe snippets illustrate invalid generalizations; they are
not executable regression tests.

### Padding, initialization, and representation ambiguity

```rust
#[repr(C, align(4))]
struct Padded(u8);

// Not justified: the three padding bytes need not be initialized.
let bytes: [u8; 4] = unsafe { std::mem::transmute(Padded(7)) };
```

Rust's by-value transmute does not guarantee padding preservation. A decoder
that ignores padding, paired with a byte-array decoder accepting every
initialized vector, would miss this initialization obligation.

The exact-result rule rejects conversions where ignored source bytes influence
the target value. But even a unique target value is not a complete Rust
initialization proof: uninitialized source padding must not become target data.
We discussed a complementary route using `Cell` initialization information to
show that initialized source data suffices for initialized target data, with
padding affecting only padding.

**Current boundary:** `Repr.decode` takes initialized `Vector U8` values.
The heap has uninitialized byte cells, but `Repr.read` requires initialized
bytes over the whole selected footprint. A padding-aware initialization theorem
is not implemented; `MaybeUninit` is not modeled.

[HeapTests.lean](../HeapTests.lean) contains an `alignedByteRepr` whose second
byte is ignored, and proves that choosing an encoding cannot promise that byte
is zero. This demonstrates demonic representation ambiguity for initialized
bytes, not a proof about Rust's uninitialized padding.

### Initialized bytes need not be a valid target value

```rust
// Invalid bool: do not execute.
let value: bool = unsafe { std::mem::transmute(2u8) };
```

Likewise, initialization alone does not establish a valid enum discriminant,
Unicode scalar value, or nonzero integer invariant. Our Rust
`checked_byte_to_bool` checks `value <= 1` before converting.
Its Lean contract returns exactly `decodeBool value` for every input byte.
`bool_writeback_rejected` proves that byte 2 decodes as a byte but not as bool.
The heap regression examples also show an actual invalid-bool read reaching
the explicit undefined-operation failure continuation.

### Forward compatibility does not authorize arbitrary mutable writes

```rust
// Unsound safe wrapper: a caller could write 2 through the returned reference.
fn bad_byte_view(value: &mut bool) -> &mut u8 {
    unsafe { std::mem::transmute(value) }
}
```

Every bool representation is a valid byte, but not every replacement byte is
a valid bool. This is a **rejected restoration obligation**, not a
counterexample to the agreed full-ownership/restoration API.
By contrast, `bool_byte_copy(&mut bool) -> u8` returns an independent copy;
changing that byte cannot invalidate the original bool.
Both have explicit counterparts in
[RawValueCasts](../../../../../tests/lean/RawValueCasts/Properties.lean).

### Alignment and footprint are independent of decoding

Forming a raw pointer cast does not establish that it may be dereferenced:

```rust
let bytes = [0u8; 8];
let word = bytes.as_ptr().wrapping_add(1).cast::<u32>();
// No read: this address is not guaranteed to be aligned for u32.
```

By-value transmute requires equal sizes, not equal source/target alignments:
the compiler places each value appropriately. A borrowed view instead needs
target alignment at the actual location, enough live storage, and suitable
permissions. Neither a decoder equality nor a same-address assertion proves
those facts. Unaligned read/write operations are not modeled here.

The heap records guaranteed base alignment, not physical addresses, and may
conservatively reject a byte-aligned allocation that happens to be physically
word-aligned. `HeapTests.alignmentFailure` and `misalignedAccess` exercise the
checks. Zero-sized representations can exist and thin pointer casts remain
meaningful, but the current typed heap observation/borrow operations reject
zero-sized footprints; no blanket zero-sized borrowed-view theorem is claimed.

### Lifetimes and nested references

```rust
// Unsound safe wrapper: unchanged bits do not extend the referent's lifetime.
fn bad_extend(value: &u32) -> &'static u32 {
    unsafe { std::mem::transmute(value) }
}
```

Byte decoding does not establish continued access to a referent. Lifetime
extension is excluded from the plain-value rule, as are aggregates containing
such references. The safe byte view preserves the input lifetime rather than
extending it. The heap alone does not authenticate which backward continuation
is entitled to restore a borrow; `HeapTests.restoration_is_privileged`
demonstrates why direct Lean restoration calls are not arbitrary authorized
Rust programs.

### Owning values, destructors, and Box allocation layout

On a target where `u32` has alignment four:

```rust
// Invalid ownership conversion: do not execute.
let word = Box::new(42u32);
let bytes: Box<[u8; 4]> = unsafe { std::mem::transmute(word) };
drop(bytes);
```

The original allocation has size four and alignment four. The new Box's
pointee has size four and alignment one; dropping it derives the wrong
deallocation layout from its new type. Deallocation is **type/layout-driven**,
not a fallible dynamic type check. This is undefined behavior, not a guaranteed
runtime error or panic; appearing to work with an allocator proves nothing.

Owning conversions additionally need ownership transfer and correct
destruction/deallocation, including for nested owning fields. They are excluded
from our generic plain-value rule. Borrowing the original word as bytes avoids
changing its eventual deallocation type.
[Heap.freeBlock](Model.lean) checks exact byte coverage, ownership kind,
permissions, and alignment divisibility separately from decoding; separation
resources track cleanup authority. **The executable alignment check is weaker
than Rust's exact deallocation-layout requirement:** it accepts
`repr.align.val` dividing the block's guaranteed alignment, not just equality.
Do not cite it as a proof that the invalid Box conversion above fails in the
model. Owning transmute is excluded, and exact allocator-layout preservation
would need a separate contract/model refinement. Checked model failures are
not promises of Rust runtime checks.

### Pointer/integer provenance and pointer identity

```rust
// Not a generally lossless transmute round trip.
let address: usize = unsafe { std::mem::transmute(pointer) };
let restored: *const u32 = unsafe { std::mem::transmute(address) };
```

Rust explicitly warns that this round trip is not lossless; integer address
equality is not enough to recover provenance. The warning also applies to
integer fields nested in aggregates. Our bases are abstract model identities,
not byte encodings of physical addresses. Neither `RawPtr.cast` nor a
pointee descriptor supplies pointer/integer support.

The pure cast round-trip theorem concerns unchanged base and byte offset.
It does not establish physical pointer equality across separate safe/raw
exposure lifecycles: the value-erased Box boundary can introduce fresh model
identities. Address-sensitive programs remain a separate modeling question.

### Aliasing, interior mutability, and Pin: a correction

`&Cell<u32> -> &u32` with independently usable mutating aliases is not a
counterexample **under our stipulated full-ownership transfer**: those aliases
cannot retain conflicting access while the footprint is borrowed.
Likewise, an argument that simply discards a `Pin` or other ownership invariant
does not refute an API requiring that invariant to be transferred and restored.

This does not mean these conversions are implemented or proved. `UnsafeCell`,
interior-mutability sharing protocols, and pinning are outside the current
representation contracts. Any future extension must carry their invariants;
exclusive initialized bytes alone are not a universal Rust transmutability
criterion.

### Endianness and cross-type observations

Writing a word and reading a byte is predictable **after** calibrating the
descriptors. There is no descriptor-independent numeric prediction: the
little-endian and big-endian models in
[RawTransmute.lean](../../../../../tests/lean/RawTransmute.lean) give different
results at the second word of a two-word allocation.

These are different fixed representation models, not fresh choices of
endianness during execution. Cross-type writes do not introduce unexplained
havoc. A later typed read returns the decoder's result, or fails if decoding
is impossible. Our concrete word/array proofs use the little-endian decoder in
[RawBoxProofs.lean](../../../../../tests/lean/RawBoxProofs.lean);
Rust tests use native-endian operations. No target-independent ABI refinement
is claimed.

### Extraction success and zero-cost code are not safety proofs

Rust compilation or successful Aeneas extraction does not validate unsafe
preconditions. Conversely, a Lean-only implementation with no corresponding
Rust definition is not an extracted Rust program.

The opaque-wrapper route deliberately leaves a modeling boundary. The original
raw-pointer and new by-value callers are unedited extraction output, but their
opaque primitives receive handwritten models. The safe mutable byte view
additionally needs a marked manual adaptation to effectful backward callbacks.
No general intrinsic-transmute or fat-pointer extraction support was added;
the legacy `RawPtr.cast_scalar` wrapper still fails.

## Related work: safe-transmute libraries

The comparison uses
[bytemuck 1.25.2](https://docs.rs/bytemuck/1.25.2/bytemuck/) and
[zerocopy 0.8.63](https://docs.rs/zerocopy/0.8.63/zerocopy/).
Their APIs separate byte exposure, target validity, layout, and mutable
write-back:

| Obligation | bytemuck | zerocopy |
|---|---|---|
| Expose initialized source bytes, without padding | `NoUninit` | `IntoBytes` |
| Accept every bit pattern at target | `AnyBitPattern` | `FromBytes` |
| Validate particular target contents | `CheckedBitPattern` | `TryFromBytes` |
| Unchecked-content mutable cast | Both types `NoUninit + AnyBitPattern` | Both types `IntoBytes + FromBytes` |
| Checked-content mutable cast | Source `NoUninit + AnyBitPattern`; target `NoUninit + CheckedBitPattern` | Source `IntoBytes + FromBytes`; target `IntoBytes + TryFromBytes` |

These are unsafe trait contracts, normally discharged by checked derives, not
automatic facts about arbitrary Rust types. Bytemuck's `Pod` is a stronger
convenient subset, not the only entry point; `Zeroable` alone is insufficient.
Its traits restrict pointers, interior mutability, and ownership-bearing types.
Zerocopy separately tracks layout (`KnownLayout`), shared-reference
immutability (`Immutable`), and alignment one (`Unaligned`).
`AnyBitPattern` permits target padding and does not imply `NoUninit`:
our initialized-byte-only model does not subsume every library padding case.

### Static and dynamic acceptance

Bytemuck's ordinary casts panic on layout failure, `try_*` casts return errors,
and `must_*` casts require statically sufficient layout conditions.
[`checked::try_cast`](https://docs.rs/bytemuck/1.25.2/bytemuck/checked/fn.try_cast.html)
also checks that the actual contents are valid for its target.
Zerocopy's transmute macros check size/alignment compatibility statically;
`try_transmute*` additionally checks contents at runtime. Byte-slice methods can
check layout dynamically. Compile-time assertions may be evaluated only during
code generation, so `cargo check` is not sufficient evidence of acceptance.

By-value casts do not require equal source/target alignments. Reference casts
need a suitably aligned address, and slice casts preserve byte length while
adjusting element count.
[Bytemuck Box casts](https://docs.rs/bytemuck/1.25.2/bytemuck/allocation/fn.try_cast_box.html)
instead require **equal allocation size and alignment**, even when a borrowed
view with lower alignment would be valid. Failed Box casts return the original
owner rather than attempting an invalid deallocation.

| Example | Accepted fragment in both libraries |
|---|---|
| `bool -> u8` | By-value conversion |
| `u8 -> bool` | Checked conversion for 0 and 1; other inputs rejected |
| `&mut u32 -> &mut [u8; 4]` | Mutable view, statically sufficient layout |
| `&mut u8 -> &mut bool` | Checked initial contents; every valid bool write remains a valid byte |
| `&mut bool -> &mut u8` | Rejected even by checked mutable APIs; later writes need not preserve bool validity |
| Padded source exposed as initialized bytes | Rejected by the relevant byte-exposure derives |
| `[u8; 4]` reference cast to `u32` reference | Needs alignment evidence; static alignment-increasing casts rejected |

For mutable casts the asymmetry is important. A checked target may admit only
some bit patterns, but the source must accept arbitrary patterns under these
generic library APIs. See
[bytemuck's checked mutable signature](https://docs.rs/bytemuck/1.25.2/bytemuck/checked/fn.try_cast_mut.html)
and
[zerocopy's checked mutable signature](https://docs.rs/zerocopy/0.8.63/zerocopy/macro.try_transmute_mut.html).
They check forward validity dynamically while ensuring write-back statically.

### Pair-specific proofs can accept a different fragment

```rust
#[repr(u8)]
enum Binary {
    Zero = 0,
    One = 1,
}
```

Both checked mutable APIs reject `&mut bool -> &mut Binary`, since bool does
not implement `AnyBitPattern`/`FromBytes`. A calibrated pair-specific proof could
instead show that both representations admit exactly 0 and 1, with unique
forward decoding and valid restoration for every target update. This is a
candidate extension, **not an implemented or verified Rust wrapper here**.
It still needs the ownership, lifetime, layout, and initialization obligations.

The pinned-library exploration exercised all 256 checked bool inputs, mutable
write-back, zero-copy address identity, restricted-to-restricted by-value
conversion, and Box layout rejection. Separate compilation failures confirmed
the rejected bool/Binary mutable views, padded-source derives, and statically
alignment-increasing casts. These are exploratory session artifacts, not
repository dependencies or Lean proofs of either library.

Zerocopy also documents its relationship to
[Project Safe Transmute](https://rust-lang.github.io/rfcs/2835-project-safe-transmute.html):
compiler-supported transmutability analysis is intended as a building block
for safe libraries, not a replacement for their higher-level ownership and
view APIs. We do not depend on that experimental compiler analysis.

## Rust examples and their formal counterparts

The links below distinguish actual Rust fixtures, manual models, extracted
callers, proved contracts, and examples with no theorem yet.
Lean names are relative to the namespace shown.

| Rust source and example | Formal counterpart and status |
|---|---|
| [raw_transmute.rs](../../../../../tests/src/raw_transmute.rs): `u32_round_trip`, `u8_round_trip` | [RawTransmute.lean](../../../../../tests/lean/RawTransmute.lean), namespace `raw_transmute`: manual bodies and framed `.spec` theorems; exact same-type write/read results |
| Same fixture: `word_to_byte`, `byte_to_word` | Same Lean file: `cross_word_byte_counterexample`, `cross_byte_word_counterexample`, and `no_uniform_*_prediction` prove absence of descriptor-independent predictions; not framed correctness theorems for these two monadic bodies |
| [raw_transmute_externals.rs](../../../../../tests/src/raw_transmute_externals.rs): mutable/const pointer round trips and same-type accesses | [Properties.lean](../../../../../tests/lean/RawTransmuteExternals/Properties.lean), namespace `raw_transmute_externals`: pointer `.spec` theorems use ordinary WP; `u32_round_trip.spec` and `u8_round_trip.spec` use framed heap WP; callers unedited, externals modeled |
| Same fixture: `raw_bytes_view`, `array_pointer_round_trip` | [ArrayProperties.lean](../../../../../tests/lean/RawTransmuteExternals/ArrayProperties.lean): exact raw-pointer `.spec` theorems |
| Same fixture: `read_word_bytes`, `overwrite_word_bytes` | Same proof file: `.spec` theorems give exact `toLittleBytes`/`fromLittleBytes` results and preserve framed word ownership |
| Same fixture: safe `bytes_view` | Same proof file: `bytes_view.spec`, including every replacement, effectful restoration, frame preservation, and exposure cleanup; generated borrow plumbing manually adapted |
| [raw_value_casts.rs](../../../../../tests/src/raw_value_casts.rs): `ext::bool_to_byte`, `ext::byte_to_bool` | [Properties.lean](../../../../../tests/lean/RawValueCasts/Properties.lean), namespace `raw_value_casts`: exact external `.spec` theorems; reverse conversion requires `value.val <= 1` |
| Same fixture: `ext::unsigned_to_signed`, `ext::signed_to_unsigned`, `signed_round_trip` | Same proof file: exact bit-preserving conversion and round-trip `.spec` theorems |
| Same fixture: `bool_byte_round_trip`, `checked_byte_to_bool`, `bool_byte_copy` | Same proof file: `.spec` theorems for exact results, unchanged heap, and unchanged original bool for the copy |
| Generic by-value model behind these external wrappers | [Repr.lean](../../../../../tests/lean/RawValueCasts/Repr.lean): `reinterpret.spec`, universal exact-result compatibility; not a new Rust intrinsic translation |
| Invalid bool write-back, padding ambiguity, alignment, and privileged restoration | `bool_writeback_rejected` and [HeapTests.lean](../HeapTests.lean) give the decoder/heap witnesses described above; not extracted counterexample programs |
| Lifetimes, owning Box transmute, pointer/integer provenance, interior mutability, Pin, fat pointers, and bool/Binary mutable view | Illustrations or exclusions above; no corresponding transmute correctness theorem is claimed |

### Representative safe zero-copy implementation

The actual Rust byte-view fixture follows this shape, with the cast and raw
borrow factored through opaque wrappers for extraction:

```rust
pub fn bytes_view(word: &mut u32) -> &mut [u8; 4] {
    unsafe {
        let pointer = std::ptr::from_mut(word);
        let bytes = ext::transmute_mut::<u32, [u8; 4]>(pointer);
        ext::borrow_four(bytes)
    }
}
```

There is no Rust allocation or byte copy. In the model, exposure storage is
bookkeeping for the safe/raw boundary, not an extra Rust runtime allocation.
The [array descriptor and conversion lemmas](../../../../../tests/lean/RawTransmuteExternals/ArrayRepr.lean)
connect the exact bytes with the word; the backward proof restores any array
replacement before recovering safe access.

### Extraction and reproduction boundary

`RawValueCasts/Funs.lean` and the non-borrowing
`RawTransmuteExternals/Funs.lean` callers are unedited extraction output.
`--opaque=crate::ext` leaves standard-operation wrappers to handwritten
`FunsExternal.lean` definitions; generated axiom templates are not imported.
The byte-view caller's effectful backward signature and restoration plumbing
are explicitly marked manual adaptations, overwritten by re-extraction.
The extraction log records the precise source blobs, unchanged shared tool
versions, and signature differences.

From the repository root, `make verify-raw-box` checks the transmute proof
closure, including both fixture roots and exact axiom guards on the end-to-end
contracts and generic compatibility theorem. The guards allow only `propext`,
`Classical.choice`, and `Quot.sound`, not memory-model axioms or `sorry`.
The Rust fixtures have native tests; the array fixture also passed address/leak
sanitization. Neither native tests nor model proofs establish compiler/ABI
refinement.

## Rust contract references

- [`std::mem::transmute`](https://doc.rust-lang.org/std/mem/fn.transmute.html):
  equal sizes, source/target validity, padding, alignment, and pointer/integer
  caveats.
- [Box memory layout](https://doc.rust-lang.org/std/boxed/index.html#memory-layout)
  and [`GlobalAlloc::dealloc`](https://doc.rust-lang.org/std/alloc/trait.GlobalAlloc.html#tymethod.dealloc):
  allocation-layout obligations.
- [Pointer provenance](https://doc.rust-lang.org/std/ptr/index.html#provenance):
  why equal numerical addresses are not the whole pointer contract.
