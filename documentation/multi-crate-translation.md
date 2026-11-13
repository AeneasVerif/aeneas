# Translating several crates

Aeneas translates one crate at a time. When a crate `B` depends on a crate `A` that has already
been translated, `B`'s translation can **reuse** `A`'s: with the option
`-extern-crate a=PATH`, the items of `A` are mapped to the Lean definitions of `A`'s translation,
and `B`'s generated files import the Lean modules defining them. Without it, `B`'s translation
re-declares `A`'s types and traits and turns `A`'s functions into axioms, so that nothing proved
about `A` applies to `B`.

## Usage

1. Translate `A` with `-emit-json`, which writes the *manifest* `translation.json` in the `-dest`
   directory (see [emit-json.md](emit-json.md)):
   ```
   charon cargo --preset=aeneas                    # in A's directory
   aeneas a.llbc -backend lean -split-files -emit-json -dest lean/A
   ```
2. Translate `B` with `--include a` for Charon and `-extern-crate a=PATH` for Aeneas:
   ```
   charon cargo --preset=aeneas --include a        # in B's directory
   aeneas b.llbc -backend lean -split-files -dest lean/B \
     -extern-crate a=lean/A/translation.json
   ```
   `-extern-crate` can be repeated, once per dependency.
3. Make `A`'s Lean files available to `B`'s Lean project: either in the same Lake package, or by
   adding a `require` for `A`'s project to `B`'s `lakefile`. Aeneas doesn't edit lakefiles.

### Why `--include a`

Charon only sees the signatures of `A`'s items when it translates `B`, unless their bodies are
included. Two things go wrong without the bodies:
- Charon removes the `Self: Trait` argument of a default method whose body doesn't use it
  (`remove_unused_self_clauses`), but only when it sees the body. `A`'s translation then has
  `def Trait.m.default (Self : Type)`, while `B`'s view of it still takes the instance.
- Charon only registers the provided methods of a foreign trait that are used, so `B`'s impls of
  `A`'s traits would miss some fields of `A`'s structures.

With `--include a`, Charon computes the same signatures for `A`'s items in `B` as in `A`. Aeneas
doesn't translate the bodies again: the items are mapped to `A`'s definitions, and their effects
(whether they can fail) are taken from the manifest.

## What `B`'s translation looks like

For a trait of `A` with a default method calling a required method:

```rust
// crate a
pub trait Shape {
    fn area(&self) -> u32;
    fn double_area(&self) -> u32 { 2 * self.area() }
}
pub fn sum_double<T: Shape>(a: &T, b: &T) -> u32 { a.double_area() + b.area() }

// crate b
impl Shape for Square { fn area(&self) -> u32 { self.side * self.side } }
pub fn square_double(s: &Square) -> u32 { s.double_area() }
```

`B`'s translation uses `A`'s structure `a.Shape` and `A`'s default `a.Shape.double_area.default`,
applied to `B`'s own instance:

```lean
public import A.Funs   -- the modules of A recorded in its manifest

impl_def Square.Insts.AShape : a.Shape Square := {
  area := Square.Insts.AShape.area
  double_area := a.Shape.double_area.default Square.Insts.AShape
}

def square_double (s : Square) : Result Std.U32 := do
  a.Shape.double_area.default Square.Insts.AShape s
```

`impl_def` resolves the instance's reference to itself by unfolding `A`'s default, which works
across modules because the generated files are `@[expose]`.

## Proofs

Since `B` calls `A`'s definitions, `A`'s specification theorems apply to `B`'s code. `A` states
them for *any* instance of its traits, assuming specifications of the instance's methods as
hypotheses; `step` proves those hypotheses for `B`'s instances by stepping through `B`'s methods,
so `B`'s proofs are `unfold f; step*` (see `tests/lean/CrossCrate{Lib,User}/Properties.lean`).

## How it works

The manifest records, for each item of `A`, its Rust name and its Lean name, plus what is needed
to use it from another crate: the constructor, field and variant names of types; the constructor
and the field names (parent clauses, constants, types, methods) of traits; and the Lean module to
import to use each item (`lean_module`). For the items `A` leaves opaque, that is the module of the
user's filled copy of the template (e.g. `A.FunsExternal`), which `B` then imports like `A`'s own
files do.

`-extern-crate` loads the manifest (`src/ExternManifest.ml`). Only the writer uses it
(`src/extract/ExtractExternal.ml`): an item of `B`'s crate whose Rust name is listed in the
manifest is named after `A`'s Lean definition and is not emitted. The translation of `B` is
unchanged: `A`'s items go through it as ordinary items of another crate. Matching by the exact Rust
name is enough, since `A`'s items reach `B` under the same names (Charon resolves each use of a
trait to an impl, which has its own name). An item listed twice, in manifests or both in a
manifest and among the models of the standard library, is an error: to provide items of the
standard library through manifests, disable its models with `-no-builtin-models`.

The manifest is checked when it is loaded: it must be the manifest of the crate named on the
command line, written from the output of the same version of Charon, and with the same Lean module
mode (`-use-lean-modules`) as `B`'s translation.

## Tests

`tests/src/cross_crate_lib` (crate `A`) and `tests/src/cross_crate_user` (crate `B`) cover:
default methods calling methods provided by `B` (directly, chained, or not using the `Self`
argument), overriding defaults, generic functions of `A` called with `B`'s instances, `A`'s own
instances, parent traits, `&mut self` defaults, associated constants with defaults, `A`'s generic
impls at `B`'s types, generic traits, associated types, `B`'s traits implemented for `A`'s types,
`A`'s structs and enums (with and without data), `A`'s functions taking `&mut`, and an opaque
function of `A`, modelled in its filled `FunsExternal.lean`. `A` is translated with `-subdir`, so
that the manifest records file paths in a subfolder. The `Makefile` translates `cross_crate_lib`
before `cross_crate_user`.
