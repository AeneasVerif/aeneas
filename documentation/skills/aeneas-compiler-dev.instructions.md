---
name: aeneas-compiler-dev
description: Dev workflow, formatting, tests, error macros, build rules for the Aeneas compiler
---

# Aeneas Compiler Development — Skill File

## ⛔ NEVER Clean the Lake Cache

**NEVER run `lake clean` or delete the `.lake/` directory.** Doing so forces a full
rebuild of all dependencies from scratch, which takes a very long time (30+ minutes).
If the build fails due to stale cache entries, fix the root cause (e.g., stale imports,
missing renames) instead of wiping the cache. When encountering build errors, use the
`lake build` → `lean_lsp.py` → `lake build` iterative loop to diagnose and fix issues
incrementally.

## Building: Fixing Errors Iteratively

When fixing build errors across multiple files, use this loop:

1. **`lake build`** — identify the first failing module and its errors
2. **`lean_lsp.py`** — open the failing file, inspect errors with `errors`, fix
   interactively with `edit`/`batch_start`/`batch_end`, confirm with `check`
3. **`lake build`** — confirm the fix, find the next failing module (if any)
4. Repeat until the build succeeds

This is much faster than running `lake build` after every single edit, because the LSP
gives sub-second feedback on individual files while `lake build` must re-elaborate all
downstream modules.

## Workflow: Lean Backend Changes

For skill file editing rules (structure, symlinks, sync script), see the `skill-file-authoring` skill file.

When modifying the Lean backend (files under `backends/lean/`), **always ask the user**
whether the documentation and skill files need to be updated afterwards. The following
may need updating:
- `CLAUDE.md` (project conventions)
- `documentation/skills/*.instructions.md` (canonical skill files)
- `documentation/*.md` (standalone documentation)
- `docs/` (user-facing documentation)

## Formatting

After modifying OCaml code or Rust test files (in `tests/src/`), run:

```bash
gmake format
```

This reformats the entire codebase (OCaml via `ocamlformat`, Rust via `rustfmt`).
Always do this before reviewing your changes or handing off to a reviewer.

## Regenerating Tests

After modifying the compiler or Rust test files, regenerate the test outputs:

```bash
# Regenerate all tests
gmake test

# Regenerate a single test file (e.g., paper.rs)
gmake test-paper.rs
```

This runs the Charon→Aeneas pipeline and updates the generated Lean/Coq/F* files
in `tests/`. Always regenerate after changing the compiler or the Rust source of a test.

## Adding a Unit Test

When adding a new Rust test file in `tests/src/`:

1. **Mark it as Lean-only by default** — add this magic comment at the top of the file:
   ```rust
   //@ [!lean] skip
   ```
   This tells the test runner to only extract for the Lean backend.

2. **Update `tests/lean/lakefile.lean`** — add a `lean_lib` entry for the generated
   module. The entries are sorted alphabetically; insert the new one in the right place.

3. **Mark test functions with `#[verify::test]`** — this generates `#assert` checks
   in the extracted code. Requires `#![feature(register_tool)]` and
   `#![register_tool(verify)]` at the crate level. Only functions with no generics,
   no parameters (or unit parameter), and implicit unit return type qualify.

4. **Regenerate** with `gmake test-yourfile.rs`.

## Error Handling: Always Use PPX Macros

Aeneas defines custom PPX macros for all error handling. These macros automatically
inject `__FILE__` and `__LINE__` at the call site, enabling precise error tracking
and span-aware reporting.

### ⛔ NEVER use these OCaml constructs directly

| Banned | Why | Use instead |
|---|---|---|
| `raise (Failure ...)` | Not caught by the Aeneas error recovery; no span tracking | `[%craise]` or `[%craise_opt_span]` |
| `raise ...` | Same: bypasses `CFailure` handling, breaks error collection | `[%craise]` / `[%internal_error]` |
| `assert false` | Uncaught, no span, no file/line in error message | `[%internal_error]` or `[%sanity_check]` |
| `assert (...)` | Same: uncaught, no span | `[%cassert]` or `[%sanity_check]` |
| `failwith "..."` | Same as `raise (Failure ...)` | `[%craise]` or `[%craise_opt_span]` |
| `Option.get` | Raises `Invalid_argument`, uncaught | `[%silent_unwrap]` or `[%unwrap_with_span]` |
| `Map.find` | Raises `Not_found`, uncaught | `Map.find_opt` + `[%unwrap_with_span]` |
| `List.find` | Raises `Not_found`, uncaught | `List.find_opt` + `[%unwrap_with_span]` |
| `List.nth` | Raises `Failure`/`Invalid_argument`, uncaught | `List.nth_opt` + `[%unwrap_with_span]` |
| Calling `craise` directly | Works, but misses `__FILE__`/`__LINE__` injection | `[%craise]` (the PPX macro) |

**Why this matters:** Aeneas uses `try ... with CFailure _ -> ...` to recover from
errors and continue processing (e.g., extracting other functions even when one fails).
Raw OCaml exceptions like `Failure`, `Invalid_argument`, or `Assert_failure` are NOT
caught by these handlers, causing the entire tool to abort instead of reporting the
error gracefully. The PPX macros avoid having to write `__FILE__` and `__LINE__`
by hand everywhere — they inject these automatically at the call site.

### Error Raising

| Macro | Arguments | Use when |
|---|---|---|
| `[%craise]` | `span msg` | Raising an error with a known span |
| `[%craise_opt_span]` | `span_opt msg` | Span might be `None` |
| `[%craise_recover]` | `recover span msg` | Caller decides if error is recoverable |
| `[%internal_error]` | `span` | Unreachable code path (uses generic message) |
| `[%internal_error_opt_span]` | `span_opt` | Same, with optional span |

**Example:**
```ocaml
(* Raising an error *)
[%craise] def.item_meta.span "Unsupported: closures with captures"

(* Unreachable branch *)
match expr with
| ELiteral _ -> ...
| _ -> [%internal_error] span
```

### Assertions

| Macro | Arguments | Use when |
|---|---|---|
| `[%cassert]` | `span condition msg` | Checking a user-facing condition |
| `[%cassert_opt_span]` | `span_opt condition msg` | Same, optional span |
| `[%classert]` | `span condition lazy_msg` | Message is expensive to compute |
| `[%sanity_check]` | `span condition` | Internal invariant (generic error message) |
| `[%sanity_check_opt_span]` | `span_opt condition` | Same, optional span |
| `[%cassert_recover]` | `recover span condition msg` | Recoverable assertion |
| `[%sanity_check_recover]` | `recover span condition` | Recoverable internal check |

**Example:**
```ocaml
(* User-facing assertion *)
[%cassert] span (List.length inputs = 2)
  "Expected exactly 2 arguments"

(* Internal invariant *)
[%sanity_check] span (ty_is_unit ret_ty)
```

### Warnings

| Macro | Arguments | Use when |
|---|---|---|
| `[%warn]` | `span msg` | Non-fatal issue worth reporting |
| `[%warn_opt_span]` | `span_opt msg` | Same, optional span |
| `[%cassert_warn]` | `span condition msg` | Warn if condition is false |
| `[%cassert_warn_opt_span]` | `span_opt condition msg` | Same, optional span |

### Option Unwrapping

| Macro | Arguments | Use when |
|---|---|---|
| `[%unwrap_with_span]` | `span option msg` | Unwrap with custom error message |
| `[%unwrap_opt_span]` | `span_opt option msg` | Same, optional span |
| `[%silent_unwrap]` | `span option` | Unwrap with generic internal error |
| `[%silent_unwrap_opt_span]` | `span_opt option` | Same, optional span |
| `[%option_get]` | `span option` | Alias for silent unwrap |

**Example:**
```ocaml
(* Unwrap with descriptive error *)
let fn_decl = [%unwrap_with_span] span
  (FunDeclId.Map.find_opt id ctx.fun_decls)
  ("Unknown function: " ^ FunDeclId.to_string id)

(* Unwrap internal lookup (should never fail) *)
let ty = [%silent_unwrap] span (get_type_from_ctx ctx id)
```

### Error Registration (Non-Raising)

| Macro | Arguments | Use when |
|---|---|---|
| `[%save_error]` | `span msg` | Record error but continue execution |
| `[%save_error_opt_span]` | `span_opt msg` | Same, optional span |

### Extraction-Specific

| Macro | Arguments | Use when |
|---|---|---|
| `[%admit_raise]` | `span msg fmt` | Output `sorry`/`admit` and record error |
| `[%extract_raise]` | `span msg fmt code` | Output fallback code and record error |

### Type Checking (Pure Translation)

| Macro | Arguments | Use when |
|---|---|---|
| `[%pure_type_check]` | `condition span` | Type-checking invariant in pure code gen |

Note: argument order is `condition span` (reversed from `cassert`).

### Location Tracking

| Macro | Arguments | Use when |
|---|---|---|
| `[%add_loc]` | `fn` | Inject `__FILE__ __LINE__` into a function that expects them |

`[%add_loc] f` expands to `f __FILE__ __LINE__`. Use it when calling a function whose
first two parameters are `file : string` and `line : int` (the same convention as the
error macros) but which isn't itself a PPX macro.

```ocaml
(* Without add_loc — must pass file/line manually *)
Substitute.make_subst_from_generics __FILE__ __LINE__ sg.item_binder_params generics

(* With add_loc — file/line injected automatically *)
[%add_loc] Substitute.make_subst_from_generics sg.item_binder_params generics
```

### Logging

| Macro | Evaluation | Use when |
|---|---|---|
| `[%ltrace]` | Lazy | Finest-grained tracing |
| `[%ldebug]` | Lazy | Debug-level logging |
| `[%linfo]` | Lazy | Informational messages |
| `[%lwarning]` | Lazy | Warning-level logging |

Lazy variants (preferred) defer message construction until the log level is active.

**Example:**
```ocaml
[%ltrace] ("Translating function: " ^ name_to_string ctx def.item_meta.name)
```

## Exception Types

Aeneas defines two custom exceptions in `Errors.ml`:

```ocaml
exception CFailure of { span : Meta.span option; file : string; line : int; msg : string }
exception RFailure  (* Recoverable failure *)
```

- `CFailure`: The standard error type. Caught by error-recovery `try/with` blocks.
- `RFailure`: Used when `recover = true` in `craise_recover` / `cassert_recover`.

## Choosing the Right Macro

```
Need to report a problem?
├─ Is this an unreachable code path?
│  → [%internal_error] span
│
├─ Is this an internal invariant that should always hold?
│  → [%sanity_check] span condition
│
├─ Is this a user-facing error (bad input, unsupported feature)?
│  → [%craise] span "message"
│  → [%cassert] span condition "message"
│
├─ Is this a non-fatal warning?
│  → [%warn] span "message"
│
├─ Need to unwrap an Option?
│  ├─ Internal lookup (should never be None)?
│  │  → [%silent_unwrap] span opt
│  └─ Could legitimately be None?
│     → [%unwrap_with_span] span opt "what was expected"
│
└─ In the extraction phase, need to output fallback code?
   → [%admit_raise] span "message" fmt
```

## Naming Convention: `_opt_span` Suffix

Most macros have an `_opt_span` variant that accepts `Meta.span option` instead of
`Meta.span`. Use the base variant when you have a span available (preferred — gives
better error messages), and `_opt_span` when the span might be absent.
