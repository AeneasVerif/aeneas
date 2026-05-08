# Manifest design thoughts...

Feature: A file called `manifest.json` is produced alongside the Lean files.

## Guiding principle

The manifest describes **what Aeneas did**: the Lean declarations it produced and the connection to the original Rust source, this is the data only available after Aeneas translation. It does not duplicate facts that are already available in the LLBC. Consumers of the data are expected to read those from the `.llbc` and
join with the `manifest.json` by `def_id`.

Note: the same def_id can appear on multiple manifest entries (loop wrappers/bodies share their parent's id). On the LLBC side a def_id is unique.

## Manifest contents

The main content are three arrays of the Lean declarations produced:

- functions
- types
- globals

### Function details
| Field | When emitted | Meaning |
|---|---|---|
| `def_id` | always | Charon's `FunDeclId` |
| `lean_id` | always | Full Lean identifier |
| `lean_file` | always | Path to Lean file |
| `is_opaque` | always | `true` ⇔ Aeneas extracted as an axiom (no body in the Pure AST) |
| `can_fail` | always | `true` ⇔ return type is wrapped in `Result`  |
| `can_diverge` | always | `true` ⇔ may not terminate |
| `is_rec` | always | `true` ⇔ part of a (mutually) recursive group |
| `reducible` | always | `true` ⇔ Aeneas marked the Lean def with `@[reducible]` |
| `num_loops` | only on non-loop entries | how many loops the parent Rust fn has |
| `loop` | only on loop wrapper / body entries | contains `loop.id`, `loop.pos`, `loop.is_body` |
| `parent_lean_id` | only on loop wrapper / body entries | the `lean_id` of the parent Rust fn  |

### Additionally the file contains the following data:

- `crate` (the source-crate name)
- `aeneas_version`
- `charon_version` (is also the version of the `.llbc`)
- `llbc_file` 

## Implementation

- By default the manifest isn't produced, it is activated with the flag `-emit-manifest`. 
- The majority of the code resides in [src/Manifest.ml](../src/Manifest.ml).
- No explicit schema versioning, just the version of Aeneas which produced it (todo later).

## Possibilities

- Add a hash of the `.llbc` bytes in the manifest.json to guarantee the connection from one file to the other
- Include a top-level `trait_decls[]` array analogous to `types[]`, `globals[]`.
