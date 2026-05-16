# Manifest design notes

Feature: A file called `manifest.json` is produced alongside the Lean files when Aeneas is invoked with `-emit-manifest`.

## Guiding principle

The manifest describes **what Aeneas did**: the Lean declarations it produced and the connection to the original Rust source, data that is only available after Aeneas translation. It does not duplicate facts that are already available in the LLBC. Consumers of the data are expected to read those from the `.llbc` and join with the `manifest.json` by `def_id`.

Note: the same `def_id` can appear on multiple manifest entries. A Rust fn with N loops produces 1 + 2N entries (the parent + a wrapper and body for each loop), all sharing the parent's `def_id`. On the LLBC side a `def_id` is unique.

## Manifest structure

```
{
  "aeneas_version": "...",
  "charon_version": "...",     // version of the charon that produced the .llbc
  "crate": "...",              // source crate name
  "output": {
    "dest_dir": "...",
    "subdir": "...",           // only present when -subdir was used
    "llbc_file": "...",        // path to the .llbc input
    "lean_files": [...]        // every Lean file written, relative to dest_dir
  },
  "functions": [...],
  "types": [...],
  "globals": [...]
}
```

### Function fields

| Field | When emitted | Meaning |
|---|---|---|
| `def_id` | always | Charon's `FunDeclId` — join key into the `.llbc` |
| `lean_id` | always | Full Lean identifier (`<namespace>.<basename>`) |
| `lean_file` | always | Path to Lean file, relative to `output.dest_dir` |
| `is_opaque` | always | `true` ⇔ Aeneas extracted as an axiom (no body in the Pure AST) |
| `can_fail` | always | `true` ⇔ return type is wrapped in `Result` (function can panic) |
| `can_diverge` | always | `true` ⇔ may not terminate (recursive, loops, or calls divergent fn) |
| `is_rec` | always | `true` ⇔ part of a (mutually) recursive group |
| `reducible` | always | `true` ⇔ Aeneas marked the Lean def with `@[reducible]` |
| `loop` | only on loop wrapper / body entries | contains `loop.id`, `loop.pos`, `loop.is_body` |
| `parent_lean_id` | only on loop wrapper / body entries | `lean_id` of the parent Rust fn |

**Discriminator**: `loop` is present iff `parent_lean_id` is present. 

### Type fields

`def_id`, `lean_id`, `lean_file` — the LLBC carries all other type metadata.

### Global fields

`def_id`, `lean_id`, `lean_file`, `can_fail`. `can_fail` is the only Aeneas-derived semantic fact for globals.

## Implementation

- Activated with the `-emit-manifest` flag (off by default). Lean backend only.
- All manifest code lives in [`src/Manifest.ml`](src/Manifest.ml). The state is a module-local singleton — no changes to upstream record types (`extraction_ctx` is untouched).
- No explicit schema versioning — `aeneas_version` + `charon_version` are the identity markers.

## Deferred / future possibilities

- **`trait_decls[]` array**: analogous to `types[]` and `globals[]`. Requires more design work due to generics, parent bounds, and associated items.
