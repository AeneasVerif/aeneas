# Type Layout and Representation

This directory formalizes the memory model of Aeneas, used mainly for `unsafe` code and transmutes.

To understand it, you need to consider three levels:
1. **Bytes Level**: A machine (or "abstract") bytes is either `Init b` (where `b : u8`) or `Uninit`, which corresponds to padding.
2. **Mid/Machine-Level**: This is where machine types (like `.enum [list-of-variants]`) and machine values (like `.variant 0 (sub-value)`) live. These corresponds to MiniRust's "high-level" [types](https://github.com/minirust/minirust/blob/master/spec/lang/types.md)/[values](https://github.com/minirust/minirust/blob/master/spec/lang/values.md). These values can be encoded into the bytes layer and back, also [following MiniRust](https://github.com/minirust/minirust/blob/master/spec/lang/representation.md). We diverge from MiniRust in that we separate machine types (which just contain the list of fields and layout flags) from their layouts, because one such type can potentially have several valid layouts. The layout flags then constrain the valid layouts, to e.g. `repr(C)` layouts. (But it can still be multiple because the layouts of the childs might vary.) We also prove various properties about layouts and encoding (following [MiniRust](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/lang/representation.md?plain=1#L749)).
3. **Aeneas Level**: The Aeneas level has the Lean types produced by the Aeneas translation (i.e. `inductive` for a Rust `enum`). We now generate a typeclass that describes the mid-level type for each Aeneas type, along with an encode/decode function to go between the mid-level and this level.

## File Overview (in Dependency Order)

1. **`Prelims.lean`** — Arithmetic preliminaries: powers of two (`isPowerOfTwo`), bounded maximum (`natMax`), and alignment rounding (`alignUp`).
2. **`Bytes.lean`** — The bytes level. This file is rather empty, only defining the `AbstractByte`, buffers (`Bytes`), and the definedness order (`le_defined`).
3. **`MTypes.lean`** — The machine/Mid-level. Defines some helpers for scalar types (`IUScalarTy`), then machine types (`MType`), machine values (`MVal`), and value well-formedness (`MVal.valid_for`).
4. **`Defs.lean`** — Defines the `Layout` data structure, which is what defines how `MVal`s are serialized, i.e. field offsets and enum tagging.
5. **`EncodeDecode.lean`** — Defines the serialization functions (`encode`, `decode`, and helpers for e.g. enums), and *states* the Galos Connection properties.
6. **`ReprC.lean`** — Defines the `repr(C)` layout for structs and also the functions computing the fixed enum layouts (`repr(C)`, `repr(C, prim)`, `repr(prim`) where `prim` is e.g. `u8`).
7. **`Properties.lean`** — Defines various properties that Layouts can have (`ReasonablyAligned`, `Transparent`, `Packed`, `Aligned`, `IsReprCTuple`, `IsReprCEnum`, `IsReprPrimEnum`), leading up to `Layout.satisfies` (which chooses the properties above based on the `MType` flags), and also proofs that the constructions from `ReprC.lean` satisfy these flags when appropiately used.
8. **`Valid.lean`** — Uses the above properties to define what is a valid layout, namely that it satisfies the flags and has some more general well-formedness properties (e.g. no overlapping fields). Proves these for the `ReprC.lean` construction.
9. **`GaloisConnection.lean`** — Proofs that any `Layout.Valid` layout satisfies the Galois Connection properties stated above. For invalid layouts these might not hold (because e.g. fields overlap).
10. **`Reasonable.lean`** — Defines "Reasonable" `MType`s. An `MType` is reasonable when it can have a layout. Almost all types are reasonable, but we rule out enums with a galactic number of variants, as well as `repr(transparent, packed)`.
11. **`RichMTypes.lean`** — Defines `LayoutInput` and `RichMType`, which pair an `MType` with the layouts of its sub-fields/variants, along with `RichMType.example_layout` and the proof that it yields a valid layout (`example_layout_IsValidLayoutForRichMType`).
12. **`HasLayout.lean`** — The `HasLayout` type class connecting Lean types extracted by Aeneas to their machine types (`MType`) and layouts. We can then define `HasLayout.the_layout` using `Classical.choice` to pick an arbitrary layout satisfying the input constraints.
