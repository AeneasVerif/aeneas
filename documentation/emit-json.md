# `translation.json` produced by `-emit-json`

When Aeneas is invoked with `-emit-json` (Lean backend only) it writes a `translation.json` file alongside the generated Lean files.

## Purpose

The manifest describes **what Aeneas did**: the Lean declarations it produced and their connection to the original Rust source. Most fields record data that exists only after translation and is not present in the `.llbc` input. Consumers can join the two artefacts via `def_id` to obtain the full data.

## Location

`translation.json` is written to the top-level output directory passed via `-dest`. 

The manifest is also what lets another crate reuse this translation: see
[multi-crate-translation.md](multi-crate-translation.md) (option `-extern-crate`).

## Schema

```json
{
  "aeneas_version": "abc1234",
  "charon_version": "xyz5678",
  "crate": "my_crate",
  "lean_modules": true,
  "functions": [...],
  "types": [...],
  "globals": [...],
  "trait_decls": [...],
  "trait_impls": [...]
}
```

`aeneas_version` is absent with the option `-emit-json-no-version`, which makes the output
reproducible (the tests use it). `lean_modules` records whether the files use the Lean module
system.

Every entry has a `lean_module`: the Lean module to import to use it (e.g. `MyCrate.Funs`; for a
declaration in a `_Template` file, the module of the filled copy, e.g. `MyCrate.FunsExternal`).
Every entry also has a `rust_pattern`: its Rust name as a name-matcher pattern, which identifies the
item from another crate. For trait impls, it is the implemented trait with its arguments (for
instance `my_crate::Shape<my_crate::Circle>`).

### Function entries

| Field | Always present | Meaning |
|---|---|---|
| `def_id` | yes | `FunDeclId` (join key into `.llbc`) |
| `lean_name` | yes | Full Lean name (`Namespace.Name`) |
| `lean_file` | yes | The Lean file this is in, relative to translate.json |
| `lean_module` | yes | The Lean module to import to use it |
| `rust_name` | yes | Full Rust name |
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

Type and global entries carry `def_id`, `lean_name`, `lean_file`, `lean_module`, `rust_name`, `rust_pattern`, `is_local`, and `source`; global entries additionally carry `can_fail`. Note that `def_id` is `TypeDeclId` or `GlobalDeclId` respectively.

Type entries also carry the names needed to use the type from another crate:

| Field | Meaning |
|---|---|
| `constructor` | Structures: full Lean name of the constructor. Absent for enumerations and tuple structures. |
| `fields` | Structures: `{ "rust": ..., "lean": ... }` for each field. |
| `variants` | Enumerations: `{ "rust": ..., "lean": ... }` for each variant, with the full Lean name. |

### Trait entries

`trait_decls` entries carry the same standard fields as type entries: `def_id` (a `TraitDeclId`), `lean_name`, `lean_file`, `lean_module`, `rust_name`, `rust_pattern`, `is_local`, and `source`. Builtin traits are not included in the outputted json. They also carry the names of the structure:

| Field | Meaning |
|---|---|
| `constructor` | Full Lean name of the structure's constructor. |
| `parent_clauses` | Field name of each parent clause, in order. |
| `consts` | `{ "rust": ..., "lean": ... }` field name of each associated constant. |
| `types` | `{ "rust": ..., "lean": ... }` field name of each associated type. |
| `methods` | `{ "rust": ..., "lean": ... }` field name of each method. |

The default methods are function entries (and default constants are global entries) whose
`rust_pattern` is the path of the method in the trait, e.g. `my_crate::Shape::double_area`.

`trait_impls` entries carry the same standard fields (`def_id` is a `TraitImplId`) plus a link to the trait they implement:

| Field | Meaning |
|---|---|
| `impl_trait_def_id` | `TraitDeclId` of the implemented trait. |
| `impl_trait_rust_name` | Full Rust path of the implemented trait. |
| `impl_trait_is_builtin` | `true` when the implemented trait is builtin, or belongs to an external crate (`-extern-crate`). |

**Note:** `impl_trait_def_id` is always a valid LLBC trait decl. However it has a matching entry in this manifest's `trait_decls` for local traits but not for builtin traits or the traits of external crates. Equivalently, `impl_trait_is_builtin` iff there is no entry for `impl_trait_def_id` in this manifest's `trait_decls`.
