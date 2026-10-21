# Type Layout and Representation

This directory formalizes the memory model of Aeneas, used mainly for `unsafe` code and transmutes.

To understand it, you need to consider three levels:
1. **Bytes Level**: A machine (or "abstract") byte is either `init b` (where `b : u8`) or `uninit`, which corresponds to padding.
2. **Mid/Machine-Level**: This is where machine types (like `.enum [list-of-variants] flags`) and machine values (like `.variant 0 (sub-value)`) live. These correspond to MiniRust's "high-level" [types](https://github.com/minirust/minirust/blob/master/spec/lang/types.md)/[values](https://github.com/minirust/minirust/blob/master/spec/lang/values.md). These values can be encoded into the bytes layer and back (`Layout.encode` / `Layout.decode`), also [following MiniRust](https://github.com/minirust/minirust/blob/master/spec/lang/representation.md). We diverge from MiniRust in that we separate machine types (which just contain the list of fields and layout flags) from their layouts, because one such type can potentially have several valid layouts. The layout flags then constrain the valid layouts, to e.g. `repr(C)` layouts. (There can still be multiple valid layouts because the layouts of child fields might vary.) We also prove various properties about layouts and encoding (following [MiniRust](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/lang/representation.md?plain=1#L749)).
3. **Aeneas Level**: The Aeneas level has the Lean types produced by the Aeneas translation (e.g. `inductive` for a Rust `enum`). We generate a `HasLayout` typeclass instance that describes the mid-level type (`RichMType`) for each Aeneas type, along with `embed` and `retract` functions (`retract` returning `Option α` to allow extra Lean-level safety invariants) to go between the Aeneas level and the mid-level.


## TCB

Many of these files are part of the TCB, since they encode how Rust works :tm: and also formalize the guarantees of the [Reference chapter on layouts](https://doc.rust-lang.org/reference/type-layout.html).
For easier reviewability, each file places all TCB-relevant definitions at the top of the file, followed by helper typeclasses, tactics, and lemmas below.

The two most complicated files are `ReprC.lean`, which defines `repr(C)` and the enum layouts built on top of it. `Properties.lean` is also notheworthy for defining what *all* reprs mean, often using the definitions from `ReprC.lean`.

## File Overview (in Dependency Order)

1. **`Prelims.lean`** — Arithmetic preliminaries: bounded maximum (`natMax`), alignment rounding (`alignUp`), and lemmas about powers of two (`isPowerOfTwo`).
2. **`Bytes.lean`** — The bytes level. This file is rather empty, only defining the `AbstractByte`, buffers (`Bytes`), and the definedness order (`le_defined`). Also defines subslice read/write operations, and lemmas about it.
3. **`MTypes.lean`** — The machine/mid-level. Defines helpers for scalar types (`IUScalarTy`, `IUScalar`), machine types (`MType`) and values (`MVal`), and value well-formedness (`MVal.valid_for`).
4. **`Defs.lean`** — Defines the `Layout` data structure, which specifies how `MVal`s are serialized (field offsets, enum tags, ...).
5. **`EncodeDecode.lean`** — Defines the serialization functions (`encode`, `decode`, and helpers for e.g. enums), and *states* the Galos Connection properties we want these lemmas to fullfill (prove is in `GaloisConnection.lean`).
6. **`ReprC.lean`** — Defines the `repr(C)` layout computation for tuples/structs (`mkTuple`) and the fixed enum layout computations (`repr(C)`, `repr(C, prim)`, `repr(prim)` where `prim` is e.g. `u8`)
7. **`Properties.lean`** — Defines layout properties (`ReasonablyAligned`, `Transparent`, `Packed`, `Aligned`, `IsReprCTuple`, `IsReprCEnum`, `IsReprPrimEnum`), leading up to `Layout.satisfies` (which selects the required properties based on the `MType` flags), and proves that the constructions from `ReprC.lean` satisfy these properties when appropriately used.
8. **`Valid.lean`** — Uses the above properties to define layout validity (`Layout.Valid`), which requires that the layout respects the layouting flags (e.g `repr(C, packed(2))`) and that it is "valid" (no overlapping fields etc.).
9. **`GaloisConnection.lean`** — Proofs that any `Layout.Valid` layout satisfies the four Galois Connection properties stated in `EncodeDecode.lean` (`valid_decodeValid`, `valid_decodeMono`, `valid_decodeEncode`, `valid_encodeDecodeLeDefined`).
10. **`Reasonable.lean`** — Defines "Reasonable" `MType`s. An `MType` is reasonable when it can have a layout. Almost all types are reasonable, but we rule out enums with too many variants, as well as `repr(transparent, packed)`.
11. **`RichMTypes.lean`** — Defines `LayoutInput` and `RichMType`, which pair an `MType` with the layouts of its sub-fields/variants, along with `RichMType.example_layout` and the proof that it yields a valid layout (`example_layout_IsValidLayoutForRichMType`).
12. **`HasLayout.lean`** — The `HasLayout` typeclass connecting Lean types extracted by Aeneas to their `MType`. It finally defines `HasLayout.the_layout` using `Classical.choice` to pick an arbitrary layout satisfying `valid_layout`.
