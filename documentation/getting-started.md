# From Rust to First Proof: Getting Started

A complete walkthrough from Rust source code to a verified Lean proof using Aeneas.

## Prerequisites

1. **Lean 4** — matching the toolchain in `backends/lean/lean-toolchain`
2. **Charon** — Rust compiler frontend that produces LLBC ([github.com/AeneasVerif/charon](https://github.com/AeneasVerif/charon))
3. **Aeneas** — translates LLBC to Lean (`./bin/aeneas`)
4. **lean-lsp-mcp** — MCP server for interactive proof development (`pip install lean-lsp-mcp`)

## Step 1: Translate Rust to LLBC

From your Rust crate root (where `Cargo.toml` lives):

```bash
charon cargo --preset=aeneas --dest-file=my_crate.llbc
```

This compiles the Rust code and produces `my_crate.llbc`, a serialized intermediate representation.

**Common charon flags:**
- `--exclude=<path>` — skip specific functions/traits (e.g., `core::fmt::Debug::fmt`)
- `--opaque=<path>` — make items opaque (don't expand their body)
- `--translate-all-methods` — include all trait method implementations

## Step 2: Generate Lean Code

```bash
aeneas -backend lean my_crate.llbc -dest proofs -subdir /MyCrate/Code -split-files -namespace MyCrate
```

This creates Lean files under `proofs/MyCrate/Code/`:

| Generated file                   | Contains                                         |
|----------------------------------|--------------------------------------------------|
| `Types.lean`                     | Rust types → Lean inductive types                |
| `Funs.lean`                      | Rust functions → Lean monadic functions          |
| `FunsExternal_Template.lean`     | Stubs for external functions (you complete this) |
| `TypesExternal_Template.lean`    | Stubs for external types (you complete this)     |

**Key aeneas flags:**
- `-split-files` — one file per declaration group (recommended for large crates)
- `-dest <dir>` — output directory
- `-subdir <dir>` — subdirectory within dest
- `-namespace <name>` — Lean namespace prefix

## Step 3: Set Up the Lean Project

Create a Lean project in the `proofs/` directory:

```
proofs/
├── lakefile.lean
├── lean-toolchain
├── MyCrate.lean                      ← module root (import all)
└── MyCrate/
    ├── Code/                         ← generated code (step 2 output)
    │   ├── Types.lean
    │   ├── Funs.lean
    │   ├── FunsExternal.lean         ← rename from _Template, fill in
    │   └── TypesExternal.lean        ← rename from _Template, fill in
    ├── Spec/                         ← your pure specifications
    │   └── Basic.lean
    └── Properties/                   ← your proofs
        └── Basic.lean
```

**`lean-toolchain`** — copy from Aeneas:
```bash
cp /path/to/aeneas/backends/lean/lean-toolchain proofs/lean-toolchain
```

**`lakefile.lean`:**
```lean
import Lake
open Lake DSL

require aeneas from "/path/to/aeneas/backends/lean"

package «my-crate» {}

@[default_target]
lean_lib «MyCrate»
```

**Handle the `_Template` files:**
```bash
cd proofs/MyCrate/Code
cp FunsExternal_Template.lean FunsExternal.lean
cp TypesExternal_Template.lean TypesExternal.lean
```
Then fill in the external definitions in those files. These model functions that Aeneas couldn't translate (e.g., FFI, std library internals).

## Step 4: Write Your First Spec

Create `proofs/MyCrate/Properties/Basic.lean`:

```lean
import Aeneas
import MyCrate.Code.Funs

open MyCrate

#setup_aeneas_simps

-- Suppose the generated code contains:
--   def add_overflow (a : U32) (b : U32) : Result U32 := a + b

@[step]
theorem add_overflow_spec (a b : U32) (h : a.val + b.val ≤ U32.max) :
  add_overflow a b ⦃ c => c.val = a.val + b.val ⦄ := by
  unfold add_overflow
  step
```

Key elements:
- **`import Aeneas`** — brings in all Aeneas tactics and primitives
- **`#setup_aeneas_simps`** — configures simp lemmas for Aeneas patterns
- **`@[step]`** — registers the theorem for the `step` tactic
- **`⦃ c => ... ⦄`** — weakest-precondition notation: "the function succeeds and the result `c` satisfies..."

## Step 5: For AI Agents: Develop the Proof Incrementally

Use the `lean-lsp-mcp` MCP server for interactive proof development. It provides
tools like `lean_goal`, `lean_edit`, and `lean_diagnostic_messages` for inspecting
proof state and iterating on proofs with sub-second feedback.

Install it with `pip install lean-lsp-mcp` (or `uvx lean-lsp-mcp`). See the
[lean-lsp-mcp skill file](skills/lean-lsp-mcp.instructions.md) for the full
tool reference and workflow.

Zero errors + zero sorry = proof complete.

## Step 6: Build the Full Project

```bash
cd proofs && lake build
```

## Checklist

- [ ] `charon cargo --preset=aeneas` produces `.llbc` without errors
- [ ] `aeneas -backend lean` generates `Types.lean` + `Funs.lean`
- [ ] `_Template` files renamed and filled in
- [ ] `lean-toolchain` matches Aeneas backend
- [ ] `lakefile.lean` has `require aeneas from ...`
- [ ] `lake build` succeeds (generated code compiles)
- [ ] First `@[step]` theorem type-checks
- [ ] `lean-lsp-mcp` tools can open and query files
