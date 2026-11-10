# `translation.json` produced by `-emit-json`

When Aeneas is invoked with `-emit-json` (Lean backend only) it writes a `translation.json` file alongside the generated Lean files.

## Purpose

The manifest describes **what Aeneas did**: the Lean declarations it produced and their connection to the original Rust source. Most fields record data that exists only after translation and is not present in the `.llbc` input. Consumers can join the two artefacts via `def_id` to obtain the full data.

## Location

`translation.json` is written to the top-level output directory passed via `-dest`.

## Schema

```json
{
  "aeneas_version": "abc1234",
  "charon_version": "xyz5678",
  "crate": "my_crate",
  "functions": [...],
  "types": [...],
  "globals": [...],
  "trait_decls": [...],
  "trait_impls": [...]
}
```

### Function entries

| Field | Always present | Meaning |
|---|---|---|
| `def_id` | yes | `FunDeclId` (join key into `.llbc`) |
| `lean_name` | yes | Full Lean name (`Namespace.Name`) |
| `lean_file` | yes | The Lean file this is in, relative to translate.json |
| `rust_name` | yes | Full Rust name |
| `rust_pattern` | no | `rust_name` in name-pattern syntax; absent, with a warning, when the name has no pattern (see "Reading the manifest back") |
| `is_local` | yes | `true` if defined in the current crate, `false` if external |
| `source` | yes | Rust source location: `{ "file": "...", "begin_line": N, "end_line": M }` |
| `is_opaque` | yes | Extracted as an axiom |
| `can_fail` | yes | Return type wrapped in `Result` (function can panic) |
| `can_diverge` | yes | May not terminate |
| `is_rec` | yes | Part of a mutually recursive group |
| `reducible` | yes | Marked as reducible by Aeneas |
| `loop` | loop entries only | `{ "id": N, "pos": [...], "is_body": bool }` |
| `parent_lean_name` | loop entries only | `lean_name` of the enclosing Rust function |

`loop` and `parent_lean_name` appear together or not at all.

**Loop position** (`loop.pos`): nesting path of the loop in the source function. `[0]` is the first top-level loop, `[0, 1]` is the second loop nested inside it, etc. Matches `Pure.fun_decl.loop_pos`.

**One Rust function, many entries**: a function with several loops produces multiple entries all sharing the same `def_id`.

### Type and global entries

Type and global entries carry `def_id`, `lean_name`, `lean_file`, `rust_name`, `rust_pattern`, `is_local`, and `source`; global entries additionally carry `can_fail`. Note that `def_id` is `TypeDeclId` or `GlobalDeclId` respectively.

### Trait entries

`trait_decls` entries carry the same standard fields as type entries: `def_id` (a `TraitDeclId`), `lean_name`, `lean_file`, `rust_name`, `rust_pattern`, `is_local`, and `source`. Traits mapped to external names are not included in the outputted json.

`trait_impls` entries carry the same standard fields (`def_id` is a `TraitImplId`) plus a link to the trait they implement:

| Field | Meaning |
|---|---|
| `impl_trait_def_id` | `TraitDeclId` of the implemented trait. |
| `impl_trait_rust_name` | Full Rust path of the implemented trait. |
| `impl_trait_is_builtin` | `true` when the implemented trait is mapped to external names (the builtin models or those imported through `-external-names`). |

**Note:** `impl_trait_def_id` is always a valid LLBC trait decl. However it has a matching entry in this manifest's `trait_decls` for local traits but not for traits mapped to external names. Equivalently, `impl_trait_is_builtin` iff there is no entry for `impl_trait_def_id` in this manifest's `trait_decls`.

## Reading the manifest back

A `translation.json` written for one crate can be passed to `-external-names` (Lean
backend only) when translating a crate which depends on it, so that the second crate's
references to the first resolve to its Lean names instead of becoming axioms of its own.
No conversion step is needed. `tests/src/roundtrip-lib` and `tests/src/roundtrip-user` are
a worked example.

**`rust_pattern`** is the Rust name in the syntax of Aeneas's name matcher, which is *not*
always the pattern form of `rust_name`: the latter is human-readable and stops being
pattern syntax once an impl block is involved (`m::{impl m::Trait for bool}::f` against
`m::{m::Trait<bool>}::f`), and on `trait_impls` the two describe different things, since
an implementation is looked up under the trait it implements applied to its arguments
(`m::Trait<m::Ty>`) rather than under its own path.

Four cases the reader cannot resolve:

- **A crate translated for several targets at once** (`--targets a,b`) has per-target
  definitions sharing a Rust path, while the pattern syntax has no way to name a target,
  so their rows collapse onto one pattern. A pattern may be mapped only once, so the file
  is refused rather than one architecture's definition silently chosen.
- **Some names have no pattern.** The name matcher prints some patterns it cannot read
  back: const generics parse at one digit but not two, and a disambiguator works on a named
  element but not on the anonymous one (`closure#1` against `_#1`). Other names cannot be
  converted to a pattern at all, or only to one which would also match other names (a name
  involving a type the pattern syntax cannot spell, such as `dyn Trait`); `-emit-json` then
  leaves `rust_pattern` out, with a warning. Such an entry is skipped with a warning (an
  error under `-warnings-as-errors`); the rest of the manifest is used.
- **Two manifests which record the same item.** A manifest also records the items of other
  crates which it uses, such as an opaque type of a dependency, so that a crate further down
  a chain can name them. Two libraries translated side by side each record such an item,
  under their own name (`A.c.T` and `B.c.T`), and a crate which loads both manifests is
  refused: a pattern may be mapped only once, even by identical entries. Translate the
  libraries in a chain instead (`B` with the manifest of `A`), or delete the duplicate rows
  from one of the manifests.
- **A default method or associated constant whose body does not use `Self`.** Charon removes
  the `Self: Trait` clause of such a default when it translates its body, which it does
  for the crate which defines the trait, but not for a crate which uses it. The two crates
  then see different signatures: the Lean definition takes no instance, while a type of
  the downstream crate which keeps the default passes one, and the generated code does not
  typecheck. The implementations in the crate which defines the trait are not affected.

A `functions` row with a `loop` key (other than `null`) is skipped too — it describes a
generated loop declaration under the enclosing function's name, not a definition Rust can
call.

## Writing an `-external-names` file by hand

`-external-names` reads the format above, and only some of its fields: a file can also be
written by hand, to map Rust definitions to models of one's own Lean library (the
`tests/external-names/*.json` files are examples). A file is a JSON object with the
buckets `types`, `functions`, `globals`, `trait_decls` and `trait_impls`, all optional.
Keys the reader does not know are ignored; there is no version.

Every entry has a **`rust_pattern`**, the name-pattern the definition is matched against,
and a **`lean_name`**, the Lean name to use for it. An entry without `rust_pattern`, or
whose pattern does not parse, is skipped with a warning (an error under
`-warnings-as-errors`). The optional fields are:

| Bucket | Field | Default | Meaning |
|---|---|---|---|
| `types` | `keep_params` | all kept | One boolean per type parameter: `false` drops it in Lean |
| `types` | `mut_regions` | Charon's analysis | Positions of the lifetime parameters used for mutable borrows |
| `types` | `body` | computed names: the fields as Aeneas names them, the constructor `<lean_name>.mk`, the variants prefixed with `lean_name` | `{ "kind": "struct", "fields": [...], "constructor": ... }` or `{ "kind": "enum", "variants": [...], "prefix_variant_names": ... }`, where a field or variant is `{ "rust": ..., "extract": ... }` |
| `functions` | `keep_params`, `keep_trait_clauses` | all kept | As for types, for the type parameters and the trait clauses |
| `functions`, `globals` | `can_fail` | `true` | The model returns a `Result` |
| `functions` | `lift` | `true` | A model which cannot fail is still used in the `Result` monad |
| `trait_decls` | `constructor` | `<lean_name>.mk` | The constructor of the structure |
| `trait_decls` | `parent_clauses` | computed names | The names of the parent clauses, in the order of the Rust declaration |
| `trait_decls` | `consts`, `types` | computed names | The associated constants and types, as `{ "rust": ..., "extract": ... }` |
| `trait_decls` | `methods` | computed names | The methods, as `{ "rust": ..., "extract": ..., "has_default": ... }` |
| `trait_impls` | `keep_params`, `keep_trait_clauses` | all kept | As for functions |

The variant names of an enumeration are *bare*: they are prefixed with `lean_name`
unless `prefix_variant_names` is `false`. A field or variant which the `body` leaves out is
reported with a warning.

A method's `has_default` (default `false`) set to `true` maps the trait's default
implementation of the method, the Rust function `<trait>::<rust>`, to the Lean name
`<lean_name>.<extract>.default`, where `<lean_name>` is the trait's, which the Lean
library must then define.

The entries are trusted, and they only supply names: the items of a trait which they leave
out get the names Aeneas computes, as when the trait is translated. In particular,
`-filter-trait-methods` does not apply to the traits modelled in a file: their impls keep
all their methods, so the Lean structure must have a field for each of them. The parent
clauses are matched by position, so an entry names all of them or none.

A Rust pattern may be mapped only once across all the sources (the models which ship with
Aeneas and every file). A model may only replace a missing body: a function or a global,
of any crate, may only be mapped if Charon did not translate its body (the default for the
items of other crates, or `--opaque`), and a type of the crate being translated only if it
is opaque. The traits and trait impls of the crate being translated cannot be mapped. The
types of other crates can: Charon translates the definition of a public type, which the
model describes (see `body`).
