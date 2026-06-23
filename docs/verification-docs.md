# Aeneas Verification Docs (`aeneas-doc`)

Generate static HTML documentation for Rust crates verified with Aeneas.
The output shows verification status, theorem statements, and statistics
for every function — like a verification-aware rustdoc.

## Quick Start

```bash
# 1. Translate to Lean and emit translation.json (Aeneas-side inventory)
aeneas -backend lean -emit-json my-crate.llbc

# 2. (Optional) Generate Lean doc info (step theorems)
cd proofs/ && lake exe doc_extract MyModule lean-doc.json

# 3. Generate HTML
cd /path/to/aeneas/scripts
python3 -m aeneas_doc generate \
  --translation translation.json \
  --lean-doc lean-doc.json \
  --rust-src /path/to/src/ \
  --output /tmp/verification-docs/

# 4. Open in browser
open /tmp/verification-docs/index.html
```

## What It Shows

### Verification Status Categories

| Status | Badge | Meaning |
|--------|-------|---------|
| **Verified** | ✓ (green) | Has `@[step]` theorem with complete proof |
| **Partially verified** | ◐ (blue) | Has `@[step]` theorem but proof contains `sorry` |
| **Specified** | ○ (yellow) | Has `@[step]` theorem but proof is entirely `sorry` |
| **Unverified** | ✗ (red) | No `@[step]` theorem |
| **External** | ⚠ (purple) | Opaque/axiomatized (no body in LLBC) |

### Pages

- **Index**: Crate overview with progress bars, stats, and module listing
- **Module pages**: Per-module function listing with status badges
- **Function pages**: Rust source, theorem statement (syntax-highlighted), status
- **External functions**: Table of all axiomatized functions
- **Source viewer**: Rust source files with line numbers and highlighting
- **Search**: Client-side function search from the index page

## Architecture

```
┌──────────────┐     ┌───────────────────┐     ┌──────────────────┐
│  .llbc file  │     │ aeneas -backend   │     │  Lean project    │
│  (Charon)    │────▶│  lean -emit-json  │     │  lake exe        │
└──────────────┘     │ → translation.json│     │  doc_extract     │
                     └────────┬──────────┘     │  → lean-doc.json │
                              │                └────────┬─────────┘
                              │                         │
                     ┌────────▼─────────────────────────▼──┐
                     │  python3 -m aeneas_doc generate     │
                     │  (Python stdlib only, no pip deps)   │
                     └────────────────┬────────────────────┘
                                      │
                              ┌───────▼───────┐
                              │ Static HTML   │
                              │ (open in any  │
                              │  browser)     │
                              └───────────────┘
```

### Components

1. **Aeneas `-emit-json` mode** (`src/EmitJson.ml`): when translating with the Lean
   backend, the `-emit-json` flag writes a `translation.json` alongside the Lean
   files, listing all functions, types, globals and traits with their Lean names,
   Rust names, source spans, and opacity. (Introduced in AeneasVerif/aeneas#1009.)

2. **Lean doc extractor** (`backends/lean/AeneasDocExtract.lean`): Lean executable
   that loads a verification project's environment, finds all `@[step]` theorems,
   extracts which function each specifies, classifies sorry status, and pretty-prints
   theorem statements.

3. **HTML generator** (`scripts/aeneas_doc/`): Python (stdlib only). `translation.py`
   adapts `translation.json` (reading Rust source snippets from `--rust-src`);
   `generator.py` matches Rust declarations to their Lean specs by Lean name,
   computes statistics, and renders static HTML with vendored highlight.js.

> **Note:** `translation.json` is intentionally minimal and does not carry the call
> graph or Rust visibility. The dependency graph is therefore edgeless and the
> "visibility" column reflects locality to the crate being verified rather than
> `pub`/private.

## Dependencies

- **Python 3** (stdlib only — no pip install needed)
- **Aeneas** (for the `-emit-json` flag)
- **Lean 4 + Lake** (for building the doc extractor)
- **highlight.js** (vendored in `scripts/aeneas_doc/static/`, BSD-3-Clause)

## Options

```
python3 -m aeneas_doc generate [OPTIONS]

Required:
  --translation PATH  Aeneas translation.json (from `aeneas -emit-json`)
  --output PATH       Output directory for generated HTML

Optional:
  --lean-doc PATH    Lean doc-extract JSON (from `lake exe doc_extract`)
  --rust-src PATH    Rust source directory (for source viewing)
  --title TEXT       Documentation title (defaults to crate name)
  --open             Open in browser after generation
```

## Makefile Integration

```makefile
# In your verification project Makefile:
AENEAS := /path/to/aeneas
LLBC := my-crate.llbc

verification-docs: $(LLBC)
	$(AENEAS)/bin/aeneas -backend lean -emit-json -dest /tmp/lean $(LLBC)
	cd proofs && lake exe doc_extract MyModule /tmp/lean-doc.json
	cd $(AENEAS)/scripts && python3 -m aeneas_doc generate \
	  --translation /tmp/lean/translation.json \
	  --lean-doc /tmp/lean-doc.json \
	  --rust-src src/ \
	  --output docs/verification/ \
	  --title "My Crate"
```

## License

The tool itself is part of the Aeneas project (Apache 2.0).
highlight.js is vendored under BSD-3-Clause — see `scripts/aeneas_doc/static/NOTICE`.
