# Lean LSP Tool — Skill File for AI Agents

## IMPORTANT: Always Use This Tool for Lean Proofs

When working on Lean proofs in an Aeneas project, **always** start a `lean_lsp.py` REPL session. It gives you:
- Incremental checking (no need to rebuild the entire file on each change)
- Proof goal context at any line (what remains to be proved)
- Diagnostics (errors, warnings) without leaving the terminal
- Type information via hover
- Batch edits that trigger only one re-elaboration

Without this tool, you are flying blind — you cannot see proof goals, you cannot tell if a tactic worked, and you must recompile the whole file after every change.

## Starting a Session

```bash
# From the Lean project root (where lakefile.toml lives):
python3 /path/to/aeneas/scripts/lean_lsp.py --repl --json
```

Always use `--json` — it gives you one JSON object per line, easy to parse programmatically. Every response has `"status": "ok"` or `"status": "error"`.

If driving from a subprocess (piped stdin), prompts are automatically suppressed.

## Core Workflow

### 1. Open a file
```
open MyProject/Properties/Foo.lean
```
Response includes: line count, sorry positions, processing ranges. **Returns immediately**
without waiting for full elaboration (~0.5s). Use `wait` after open to block until
elaboration finishes.

```
wait
```
Blocks until the entire file is elaborated. You can also `wait <line>` to block until
a specific line is ready (but note: during import elaboration, Lean reports the entire
file as one processing range, so `wait <line>` may not be faster than `wait` for files
with heavy imports).

### 2. Find what needs proving
```
sorry
```
Lists all `sorry` positions — these are your proof obligations.

### 3. Inspect a proof goal
```
goal <line> [col]
```
Query the proof state at any line (1-indexed). Place it on the `sorry` line or on a tactic line to see what the goal looks like after that tactic. Default column is 4 (typical indent).

### 4. Edit a line
```
edit <line> <new_tactic>
```
Replaces the line (preserving indentation), sends the change to the server, and waits for re-elaboration. Returns errors if any.

### 5. Check the result
```
goal <line>
errors
```
After editing, inspect the new goal or check if errors were resolved.

### 6. Iterate until done
Repeat steps 3–5: inspect goal → try a tactic → check result.

## Complete Command Reference

### File Operations
| Command | Description |
|---|---|
| `open <file.lean>` | Open file (returns immediately, non-blocking) |
| `update` | Re-read current file from disk |
| `replace <file.lean>` | Re-read a different file from disk |

### Viewing and Searching
| Command | Description |
|---|---|
| `show [start] [end]` | Show current file with line numbers (requires open file) |
| `grep <pattern> [glob]` | Search current file, or project files if glob given |
| `search <pattern> [glob]` | Search project `.lean` files (default: `**/*.lean`) |
| `cat <file> [start] [end]` | Read another file with line numbers |
| `ls [path]` | List directory contents |

### Goal and Diagnostics
| Command | Description |
|---|---|
| `goal <line> [col]` | Proof goal at position (1-indexed line, 0-indexed col) |
| `diagnostics [line]` | All diagnostics, optionally filtered to a line |
| `errors` | Errors only |
| `warnings` | Warnings only |
| `info <line>` | All diagnostics at a specific line |
| `sorry` | List all sorry positions |
| `hover <line> <col>` | Type/documentation at position |
| `complete <line> <col>` | Available completions at position |
| `definition <line> <col>` | Go to definition |

### Editing
| Command | Description |
|---|---|
| `edit <line> <content>` | Replace one line (preserves indent) |
| `edit_range <start> <end> <content>` | Replace lines start..end (`\n` for newlines) |
| `insert <after_line> <content>` | Insert after line (`\n` for newlines, 0=prepend) |
| `delete <start> [end]` | Delete line(s) |

### Batch Editing (Critical for Multi-Line Changes)
| Command | Description |
|---|---|
| `batch_start` | Start batch mode — edits modify text but skip re-elaboration |
| `batch_end` | End batch — send all changes, wait for one re-elaboration |

**Always use batch mode for multi-line edits.** Without it, each `edit` triggers a full re-elaboration cycle (potentially 30+ seconds each).

### Status and Control
| Command | Description |
|---|---|
| `status` | Current file, version, line count, elaboration state |
| `wait [line]` | Block until elaboration finishes (optionally up to line) |
| `check` | Wait for full elaboration, return all errors and warnings with messages |
| `next_error` | Wait until a new error appears (or elaboration finishes with no new errors) |
| `logs` | Server log messages |
| `quit` | Exit |

## Proof Development Strategy

### The sorry-driven workflow

1. **Start with sorry:** Write the theorem statement with `sorry` as the proof body
2. **Open the file** and wait for elaboration
3. **Query the goal** at the sorry line to see what needs to be proved
4. **Replace sorry** with a tactic (e.g., `unfold foo`)
5. **Add sorry below** the tactic to pause and inspect the new goal
6. **Repeat:** inspect goal → add next tactic → add sorry → inspect
7. **Remove the final sorry** when the proof is complete

### Example session (JSON mode)

```
open MyProject/Properties/Add.lean
→ {"command":"open","status":"ok","lines":42,"sorry_lines":[{"line":35,"text":"sorry"}],"ready":false,"processing_ranges":[...],...}

wait
→ {"command":"wait","status":"ok","ready":true,"elapsed":15.2,"error_count":0,"warning_count":1}

goal 35
→ {"command":"goal","status":"ok","goals":["⊢ add_overflow a b ⦃ c => c.val = a.val + b.val ⦄"],...}

edit 35 unfold add_overflow
→ {"command":"edit","status":"ok","ready":true,"elapsed":2.1,"errors":[],...}

goal 35
→ {"command":"goal","status":"ok","goals":["⊢ a.val + b.val ≤ U32.max → ..."],...}

insert 35 step
→ {"command":"insert","status":"ok","ready":true,"elapsed":1.8,"errors":[],...}

errors
→ {"command":"errors","status":"ok","diagnostics":[],"count":0}
```

### Batch edit example

```
batch_start
delete 35 37
insert 34 unfold add_overflow\n  step\n  simp_all
batch_end
→ {"command":"batch_end","status":"ok","ready":true,"elapsed":3.2,"errors":[],...}
```

## Key Tips

1. **Always use `--json`** for agent interaction — structured output, no ambiguity
2. **Check `sorry` first** after opening — they mark your proof obligations
3. **Use `goal` liberally** — it's fast (sub-second) and tells you exactly what remains
4. **Use `hover`** to check types of terms you're unsure about
5. **Use `batch_start`/`batch_end`** for multi-line edits — avoids N separate re-elaborations
6. **Use `status`** to check if elaboration is still running or file is ready
7. **Use `errors` after every edit** — if count is 0, your tactic worked
8. **`edit` preserves indentation** — provide just the tactic text, not the leading spaces
9. **`edit_range` and `insert` use exact content** — include indentation in the content
10. **Use `\n` in content** for multi-line inserts: `insert 35 tactic1\n  tactic2\n  tactic3`

## MANDATORY: Use lean_lsp.py Instead of lake build

**DO NOT use `lake build` to iterate on proofs.** It rebuilds everything from scratch (2–5 min per cycle). The LSP gives incremental feedback in 5–30 seconds. Your workflow must be:

```
open file → wait → sorry → goal → edit → errors → repeat
```

**Never** fall back to `lake build` loops. Only use `lake build` once at the very end to confirm the final result.

## The step*? Workflow for Complex Function Bodies

When developing a proof for a function body with many monadic calls:

1. Write `step*?` as the tactic
2. Run `info <line>` in the LSP — the "Try this: ..." diagnostic contains the expanded script
3. Copy the expanded script into your proof and work through it
4. Once the full proof works, try collapsing back into a single `step*`
5. If `step*` works, use it (shorter is better). If not, keep the expanded form.

**How it works:** `step*?` generates a suggestion via `addTryThisTacticSeqSuggestion`.
In VS Code this is a clickable code action. In `lean_lsp.py`, it appears as an INFO
diagnostic at the `step*?` line — use `info <line>` or `diagnostics` to read it.

**Example workflow:**
```
-- Step 1: Write step*? to generate script
edit 42 step*?

-- Step 2: Read the "Try this:" suggestion
info 42
-- → [INFO] line 42: Try this:
--     let* ⟨ x2, x2_post ⟩ ← U32.add_spec
--     let* ⟨ x3, x3_post ⟩ ← U32.add_spec
--     let* ⟨ ⟩ ← U32.add_spec

-- Step 3: Replace with the expanded script (using batch mode)
batch_start
delete 42
insert 41 let* ⟨ x2, x2_post ⟩ ← U32.add_spec\n  let* ⟨ x3, x3_post ⟩ ← U32.add_spec\n  let* ⟨ ⟩ ← U32.add_spec
batch_end

-- Step 4: Once everything works, try collapsing
edit 42 step*
```

## JSON Response Examples (Common Scenarios)

### Successful proof step
```json
{"command":"edit","status":"ok","line":42,"old":"sorry","new":"unfold add_overflow","ready":true,"elapsed":2.1,"errors":[],"error_count":0}
```
Agent action: `errors` returns 0 → tactic worked. Use `goal 43` to see remaining goals.

### Failed tactic (type mismatch)
```json
{"command":"edit","status":"ok","line":42,"old":"sorry","new":"omega","ready":true,"elapsed":1.5,"errors":[{"severity":"ERROR","severity_code":1,"line":42,"end_line":42,"col":2,"end_col":7,"message":"omega failed to prove the goal..."}],"error_count":1}
```
Agent action: `omega` can't solve this — try `scalar_tac` or `agrind` instead. Use `goal 42` to re-inspect.

### Progress fails (no matching spec)
```json
{"command":"edit","status":"ok","line":42,"old":"sorry","new":"step","ready":true,"elapsed":3.0,"errors":[{"severity":"ERROR","severity_code":1,"line":42,"end_line":42,"col":2,"end_col":10,"message":"step failed: no matching spec found for 'my_function'"}],"error_count":1}
```
Agent action: `my_function` has no spec. Search for one (`grep -r "theorem.*my_function.*spec"`) or write one.

### Proof complete (no errors, no sorry)
```json
{"command":"errors","status":"ok","diagnostics":[],"count":0}
{"command":"sorry","status":"ok","sorry_lines":[],"count":0}
```
Agent action: Both empty → proof is complete. No remaining obligations.
