# `translation.json` produced by `-emit-json`

When Aeneas is invoked with `-emit-json` (Lean backend only) it writes a `translation.json` file alongside the generated Lean files.

## Purpose

The manifest describes **what Aeneas did**: the Lean declarations it produced and their connection to the original Rust source. It records data that exists only after translation and is not present in the `.llbc` input. It does **not** duplicate facts already available in the `.llbc`.

Consumers join the two artefacts via `def_id`.

## Location

`translation.json` is written to the top-level output directory passed via `-dest`. All paths inside the file are relative to that directory (i.e., relative to `translation.json` itself).

## Schema

```json
{
  "aeneas_version": "abc1234",
  "charon_version": "xyz5678",
  "crate": "my_crate",
  "output": {
    "subdir": "SubDir",
    "llbc_file": "input.llbc",
    "lean_files": ["SubDir/Types.lean", "SubDir/Funs.lean"]
  },
  "functions": [...],
  "types": [...],
  "globals": [...]
}
```

`llbc_file` is the basename of the `.llbc` input. `lean_files` are relative to the directory containing `translation.json`. `subdir` is omitted when the `-subdir` flag was not used.

### Function entry fields

| Field | Always present | Meaning |
|---|---|---|
| `def_id` | yes | `FunDeclId` (join key into `.llbc`) |
| `lean_id` | yes | Fully-qualified Lean name (`Namespace.BaseName`) |
| `lean_file` | yes | Path relative to `dest_dir` |
| `is_opaque` | yes | Extracted as an axiom (no body in the Pure AST) |
| `can_fail` | yes | Return type wrapped in `Result` (function can panic) |
| `can_diverge` | yes | May not terminate |
| `is_rec` | yes | Part of a mutually recursive group |
| `reducible` | yes | Marked `@[reducible]` by Aeneas |
| `loop` | loop entries only | `{ "id": N, "pos": [...], "is_body": bool }` |
| `parent_lean_id` | loop entries only | `lean_id` of the enclosing Rust function |

`loop` and `parent_lean_id` appear together or not at all.

**Loop position** (`loop.pos`): nesting path of the loop in the source function. `[0]` is the first top-level loop, `[0, 1]` is the second loop nested inside it, etc. Matches `Pure.fun_decl.loop_pos`.

**One Rust function, many entries**: a function with N loops produces 1 + 2N entries all sharing the same `def_id` — the parent, a wrapper, and a body for each loop.
