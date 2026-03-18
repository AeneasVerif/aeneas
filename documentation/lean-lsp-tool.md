# Lean LSP Tool (`lean_lsp.py`)

A Python script that wraps Lean 4's language server (`lake serve`) to provide incremental proof checking, goal inspection, and file editing — designed for both interactive use and AI agent automation.

**Location:** `scripts/lean_lsp.py`

## Why This Tool Exists

When developing Lean proofs, you need to:
- See proof goals at specific points in the proof
- Get immediate feedback when a tactic succeeds or fails
- Edit proofs incrementally without rebuilding from scratch

The Lean language server provides all of this via LSP, but speaking raw JSON-RPC is impractical. This tool wraps it in a simple command-based interface with both human-readable and JSON output modes.

## Quick Start

### One-shot: query a single goal
```bash
python3 scripts/lean_lsp.py MyProject/File.lean 42
```

### One-shot: check errors in a file
```bash
python3 scripts/lean_lsp.py MyProject/File.lean errors
```

### REPL: interactive session
```bash
python3 scripts/lean_lsp.py --repl
```

### REPL: agent-friendly JSON mode
```bash
python3 scripts/lean_lsp.py --repl --json
```

### REPL: scripted usage (piped commands)
```bash
echo -e "open File.lean\ngoal 42\nquit" | python3 scripts/lean_lsp.py --repl --json
```

## Command-Line Flags

| Flag | Description |
|---|---|
| `--repl` | Start persistent REPL mode (keeps server running) |
| `--json` | Machine-readable JSON output (one JSON object per stdout line) |
| `--fail-fast` | Exit REPL on first error (for scripted usage) |
| `--project-root DIR` | Override Lean project root (default: auto-detect via `lakefile.toml`) |

**Environment variable:** `LEAN_PROJECT_ROOT` — same as `--project-root`.

## REPL Commands

### File Management

**`open <file.lean>`** — Open a file and wait for elaboration to complete.
- File path is relative to project root (or absolute)
- Returns line count, sorry positions, and any errors
- Elaboration may take 10–180 seconds depending on imports

**`update`** — Re-read the current file from disk and re-elaborate. Use after editing the file externally.

**`replace <file.lean>`** — Re-read a specific file from disk and send as update.

### Proof Goal Inspection

**`goal <line> [col]`** — Query the proof state at a position.
- Line is 1-indexed, col is 0-indexed (default: 4)
- Returns the list of goals (hypotheses + target)
- Place on a `sorry` to see what needs to be proved
- Place after a tactic to see what remains

**`sorry`** — List all lines containing `sorry` in the current file. These are your proof obligations.

**`hover <line> <col>`** — Get type/documentation info at a position. Useful for checking term types.

**`complete <line> <col>`** — Get available completions (tactics, terms) at a position.

**`definition <line> <col>`** — Find the definition location of a symbol.

### Diagnostics

**`diagnostics [line]`** — All diagnostics, optionally filtered to a line.

**`errors`** — Errors only (severity 1).

**`warnings`** — Warnings only (severity 2).

**`info <line>`** — All diagnostics at a specific line (full messages, no truncation).

### Editing

**`edit <line> <content>`** — Replace a single line.
- Preserves the original line's indentation (provide just the tactic text)
- Sends the change and waits for re-elaboration
- Returns errors after elaboration

**`edit_range <start> <end> <content>`** — Replace a range of lines (inclusive).
- Use `\n` (literal backslash-n) for newlines in content
- Content is used exactly as provided (include any indentation)
- Example: `edit_range 35 37 unfold foo\n  progress\n  simp_all`

**`insert <after_line> <content>`** — Insert new line(s) after a given line.
- Use `0` to insert at the beginning of the file
- Use `\n` for multi-line inserts
- Example: `insert 35   progress as ⟨x, h⟩\n  simp [*]`

**`delete <start> [end]`** — Delete line(s) (inclusive).
- Single line: `delete 35`
- Range: `delete 35 40`

### Batch Editing

**`batch_start`** — Enter batch mode. Edit commands modify the in-memory text but do NOT trigger re-elaboration.

**`batch_end`** — Exit batch mode. Sends all accumulated changes and waits for one re-elaboration.

**Use batch mode whenever you need to make multiple edits.** Without it, each edit triggers a separate re-elaboration (10–60 seconds each). With batch mode, you pay the cost only once.

### Status and Control

**`status`** — Returns current file path, version number, line count, whether elaboration is complete, and any processing ranges still being checked.

**`wait`** — Block until elaboration is complete. Returns error/warning counts.

**`logs`** — Show Lean server log messages (and clear them).

## JSON Output Format

With `--json`, every command produces exactly one JSON line on stdout:

```json
{"command": "open", "status": "ok", "file": "Foo.lean", "lines": 200, "elapsed": 12.3, "sorry_lines": [{"line": 42, "text": "sorry"}, {"line": 67, "text": "sorry"}], "errors": [], "error_count": 0}
{"command": "goal", "status": "ok", "line": 42, "col": 4, "goals": ["x : U32\nh : x.val < 100\n⊢ add_one x ⦃ r => r.val = x.val + 1 ⦄"], "elapsed": 0.2}
{"command": "edit", "status": "ok", "line": 42, "old": "sorry", "new": "unfold add_one", "ready": true, "elapsed": 3.1, "errors": [], "error_count": 0}
{"command": "errors", "status": "ok", "diagnostics": [], "count": 0}
{"command": "status", "status": "ok", "file": "/path/Foo.lean", "version": 3, "lines": 200, "ready": true, "processing_ranges": []}
```

Errors are always structured:
```json
{"command": "goal", "status": "error", "error": "No file open"}
{"command": "edit", "status": "error", "error": "Line 999 out of range (1-200)"}
```

Diagnostics are normalized:
```json
{"severity": "ERROR", "severity_code": 1, "line": 42, "end_line": 42, "col": 4, "end_col": 10, "message": "type mismatch..."}
```

## Architecture

The tool runs `lake serve` as a subprocess and communicates via LSP JSON-RPC over stdio. A background reader thread collects diagnostics, file progress notifications, and log messages. The REPL loop dispatches commands to the LSP client.

```
Agent ──stdin──▶ lean_lsp.py ──JSON-RPC──▶ lake serve (Lean LSP)
Agent ◀──stdout── lean_lsp.py ◀──JSON-RPC── lake serve
```

Incremental checking is handled by the Lean server — after an edit, only the changed portion and its dependents are re-elaborated, which is typically much faster than rebuilding from scratch.

## Common Lean Error Messages

When working with lean_lsp.py, you'll encounter these errors in diagnostics. Here's what they mean and how to debug them:

### "application type mismatch"
**Cause:** A function or tactic received an argument of the wrong type.
**Debug:** Use `hover <line> <col>` to check the actual types involved. Often caused by passing the wrong hypothesis to `progress`.

### "unsolved goals"
**Cause:** Your tactic sequence didn't close all goals.
**Debug:** Use `goal <line>` on the line after your last tactic to see what remains.

### "unknown identifier '...'"
**Cause:** You referenced a name that doesn't exist in scope.
**Debug:** Check imports. Use `complete <line> <col>` to see available names. Common cause: missing `import Aeneas` or project-specific imports.

### "type mismatch" (in `progress`)
**Cause:** `progress` found a spec but its postcondition doesn't match the current goal.
**Debug:** Use `progress with <specific_theorem>` to control which spec is applied. Check if you need a more specific spec variant.

### "tactic ... failed, ..."
**Cause:** The tactic couldn't make progress on the current goal.
**Debug:** Use `goal <line>` to see the exact goal shape, then consult the tactic decision tree to pick the right tactic.

### "maximum recursion depth has been reached" / termination error
**Cause:** Usually means `progress` applied the theorem being proved recursively. See the termination pitfall in proof-strategies.md.
**Fix:** Add `split` or `cases` before `progress` to case-split first.

### "(kernel) declaration has been defined with sorry"
**Cause:** There's still a `sorry` in the proof. This is a warning, not an error — the proof is incomplete.
**Debug:** Use `sorry` command to list remaining obligations.
