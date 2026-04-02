---
name: lean-lsp-mcp
description: Lean LSP MCP tools for interactive Lean proof development — tool reference, workflows, and examples
---

# Lean LSP MCP — Skill File for AI Agents

/- Adapted from the lean-lsp-mcp README (MIT License, (c) Oliver Dressler).
   Source: https://github.com/oOo0oOo/lean-lsp-mcp
   MIT License is compatible with this project's Apache-2.0 License. -/

## IMPORTANT: Always Use Lean MCP Tools for Lean Proofs

When working on Lean proofs in a Lean project, **always** use the lean-lsp-mcp
tools. These tools are available directly in your tool palette — you do NOT need to
start a subprocess, launch a REPL, or run any setup commands.

**If the tools are not in your palette** (i.e., you cannot find `lean_goal`,
`lean_diagnostic_messages`, etc. among your available tools), **STOP IMMEDIATELY
and signal the user BEFORE doing anything else** — do not attempt proof work, do
not fall back to `lake build` loops, do not dispatch proof agents. Tell the user:
> "The lean-lsp-mcp tools are not available in my tool palette. These tools are
> essential for efficient Lean proof development: they provide interactive feedback
> (proof goals, diagnostics, type information) without rebuilding the project.
> Without them, the only option is `lake build`, which can easily take minutes on
> a big file and does not provide intermediate goal states — making iterative proof
> development impractical. Please connect the MCP server or install it
> (`pip install lean-lsp-mcp` or `uvx lean-lsp-mcp`) and configure it in your MCP
> client settings. See https://github.com/oOo0oOo/lean-lsp-mcp for setup
> instructions."
**If you get "Error: Not connected"** when calling a lean-lsp-mcp tool, the MCP
server has likely crashed and is restarting. Wait a couple of minutes and retry.
This is a transient error — the server will typically recover on its own. Do NOT
fall back to `lake build` loops or stop working entirely; just wait briefly and
retry the tool call.

**Do NOT proceed with proof work without these tools** — wait for the user to
connect the MCP server. Falling back to `lake build` loops wastes minutes per
iteration where the MCP tools give sub-second feedback.

The tools give you:
- Proof goal context at any position (`lean_goal`)
- Diagnostics (errors, warnings) without rebuilding (`lean_diagnostic_messages`)
- Type information via hover (`lean_hover_info`)
- Try multiple tactics without modifying the file (`lean_multi_attempt`)
- Code actions for `step*?` suggestions (`lean_code_actions`)
- External search tools (LeanSearch, Loogle, Lean Finder, Hammer, State Search)
- Verification of axiom usage (`lean_verify`)

Without these tools, you are flying blind — you cannot see proof goals, you cannot
tell if a tactic worked, and you must recompile the whole file after every change.

**Do NOT use `lake build` to iterate on proofs.** The MCP tools give incremental
feedback in seconds. `lake build` rebuilds from scratch and can easily take minutes
on a big file. Only use `lake build` once at the very end to confirm the final result.

**NEVER run `lake clean` or delete `.lake/`.** This forces a full rebuild (30+ min).
Fix root causes instead.

## Tool Reference

### File and Goal Inspection (read-only — use freely)

| Tool | Purpose | Key Parameters |
|---|---|---|
| `lean_goal` | **THE MOST IMPORTANT TOOL** — get proof goals at a position | `file_path`, `line`, optional `column` |
| `lean_diagnostic_messages` | Get errors/warnings/infos for a file | `file_path`, optional `severity`, `start_line`, `end_line` |
| `lean_file_outline` | Get imports and declarations with type signatures | `file_path` |
| `lean_hover_info` | Get type and docs for a symbol | `file_path`, `line`, `column` |
| `lean_term_goal` | Get expected type at a position | `file_path`, `line`, optional `column` |
| `lean_completions` | Get autocompletions (use on incomplete code) | `file_path`, `line`, `column` |
| `lean_declaration_file` | Find where a symbol is declared | `file_path`, `symbol` |
| `lean_references` | Find all references to a symbol | `file_path`, `line`, `column` |
| `lean_code_actions` | Get quick fixes and "Try This" suggestions | `file_path`, `line` |
| `lean_run_code` | Run a self-contained Lean code snippet (must include imports) | `code` |
| `lean_verify` | Check axioms used by a theorem | `file_path`, `theorem_name` |

### Tactic Exploration (does NOT modify the file)

| Tool | Purpose | Key Parameters |
|---|---|---|
| `lean_multi_attempt` | **Try multiple tactics and see results** — does not modify the file | `file_path`, `line`, `snippets` (array of tactics) |

`lean_multi_attempt` is extremely valuable: pass 3+ candidate tactics and see which
ones close the goal (or make progress) — all without touching the file. Use this
before committing to a tactic with `edit`.

### File Modification

| Tool | Purpose | Key Parameters |
|---|---|---|
| `lean_build` | Rebuild project and restart LSP | optional `clean`, `lean_project_path` |

**Important:** The MCP server manages a single LSP session per project. When you
edit a `.lean` file on disk (using `edit`/`create` tools), the LSP server picks up
the change automatically (typically within a few seconds). You do NOT need to call
`lean_build` after every edit.

### When to use `lean_build` (and when NOT to)

`lean_build` runs `lake build` and restarts the LSP server. It takes **10–30+
minutes** on large projects. Use it ONLY when:

- **You modified a dependency file** and need to refresh the imports in the file
  you are currently working on (e.g., you changed a lemma in `A.lean` and
  need `B.lean` to pick up the new version).
- **You added new `import` statements** that require recompilation of upstream modules.
- As a **final build check** after completing all proof work, to confirm the project
  compiles cleanly end-to-end.

Before calling `lean_build`, think twice — you will easily be waiting 10+ minutes. If
you only edited the file you are currently working on, you do NOT need `lean_build`
— the LSP picks up changes automatically.

### ⛔ NEVER call `lean_build` to recover from LSP timeouts or crashes

When an MCP tool call times out or returns an error (e.g., `McpError: MCP error
-32001: Request timed out`), the LSP server has likely crashed and is auto-restarting.
**Do NOT call `lean_build`** — it triggers a full `lake build` and restarts the LSP,
which is massive overkill. The LSP auto-restarts on its own within 1–2 minutes.

**The correct recovery procedure:**
1. **Wait 2 minutes.** Do other work (update plan, write comments, think about the
   next proof step) — do not poll the LSP repeatedly during this time.
2. **Retry the MCP tool call.** If it still times out, wait another 2 minutes and
   retry once more.
3. **Only if the LSP is still unresponsive after 3 retries**, call `lean_build`.

This applies to ALL MCP tool failures — `lean_goal`, `lean_diagnostic_messages`,
`lean_multi_attempt`, etc. The pattern is always: **wait, then retry**.

### External Search Tools (rate-limited)

| Tool | Purpose | Rate Limit |
|---|---|---|
| `lean_leansearch` | Search Mathlib via natural language (leansearch.net) | 3 req/30s |
| `lean_loogle` | Search Mathlib by type signature (loogle.lean-lang.org) | 3 req/30s |
| `lean_leanfinder` | Semantic search by mathematical meaning (Lean Finder) | 10 req/30s |
| `lean_state_search` | Find lemmas to close the current goal (premise-search.com) | 6 req/30s |
| `lean_hammer_premise` | Get premise suggestions for automation tactics | 6 req/30s |
| `lean_local_search` | Search local project + stdlib for declarations | No limit |

**Use `lean_local_search` first** — it is fast, free, and confirms declarations exist
before you try to use them. Use the external tools when you need Mathlib results or
cannot find what you need locally.

### Profiling

| Tool | Purpose | Key Parameters |
|---|---|---|
| `lean_profile_proof` | Run `lean --profile` on a theorem — returns per-line timing | `file_path`, `line` |

**Use sparingly** — profiling is slow. Only profile when a proof is taking too long
and you need to identify the bottleneck.

## Core Workflow

### 1. Edit the file on disk, then inspect goals

The MCP tools operate on the file as it exists on disk. Your workflow is:

1. **Edit the `.lean` file** using the standard `edit`/`create` tools
2. **Use `lean_goal`** to inspect the proof state (the LSP picks up the change)
3. **Use `lean_diagnostic_messages`** to check for errors

### 2. The sorry-driven workflow

1. **Start with sorry:** Write the theorem statement with `sorry` as the proof body
2. **Use `lean_goal`** on the sorry line to see what needs to be proved
3. **Use `lean_multi_attempt`** to try several tactics at once
4. **Replace sorry** with the successful tactic (via `edit` tool)
5. **Add sorry below** the tactic to pause and inspect the new goal
6. **Repeat:** `lean_goal` -> `lean_multi_attempt` -> `edit` -> `lean_goal`
7. **Remove the final sorry** when the proof is complete

### 3. Check proof state — use lean_goal liberally

`lean_goal` is your most important tool. Call it:
- On sorry lines to see what needs to be proved
- On tactic lines to see the state before/after the tactic
- After every edit to verify the tactic did what you expected

**Omit `column`** to see both `goals_before` (line start) and `goals_after` (line end)
— this shows how the tactic transforms the proof state. "no goals" means the proof
is complete at that point.

### 4. Try multiple tactics before committing

Use `lean_multi_attempt` to test tactics without modifying the file:

```
lean_multi_attempt(
  file_path="MyProject/Properties/Foo.lean",
  line=42,
  snippets=["agrind", "scalar_tac", "grind", "bv_tac 16", "simp [*]; agrind"]
)
```

This returns the resulting goal state for each tactic. Pick the one that works best,
then apply it with `edit`.

### 5. Verify a completed proof

After finishing a proof:

1. **`lean_diagnostic_messages`** with `severity="error"` — must return empty
2. **`lean_verify`** with the theorem name — checks axiom usage, flags suspicious
   patterns (sorry, native_decide in non-test code, etc.)
3. **`lean_build`** — one final build to confirm everything compiles cleanly

## Diagnosing Slow Incremental Replay — KEEPING LEAN REACTIVE IS CRITICAL

> **Terminology:** "Interactivity" and "incrementality" mean the same thing in this
> context — the ability to edit one tactic and get near-instant feedback because Lean
> only re-elaborates the changed part. We use both terms interchangeably.

Keeping Lean reactive during interactive proof development is **the single most important
factor for productivity**. Fast feedback (< 0.5s per tactic) enables rapid iteration —
try a tactic, see the result, adjust, repeat. Slow feedback destroys this loop.

**Target: < 0.5s response when appending a tactic at the end of the proof.** When you
add a new tactic line at the bottom of a proof, Lean should react almost immediately
(under half a second) because only the new tactic needs elaboration — everything above
is already cached. If instead you see multi-second delays, big chunks of the proof are
being re-elaborated. **Step back and restructure the proof** rather than tolerating the
slowness — it compounds over many edit cycles.

**Common causes:**

1. **`by ...` blocks inside `apply`/`exact`/`refine` arguments.** For example:
   ```lean
   apply lemma arg1 (by scalar_tac) (by agrind) (by grind)
   exact foo (by bv_tac 16) (by simp_all)
   ```
   The entire `apply`/`exact`/`refine` expression (including all `by` blocks) is
   elaborated as a single unit. Editing *any* `by` block forces re-elaboration of
   *all* of them. If those `by` blocks contain expensive tactics, every edit pays
   the full cost.

   **Fix:** Extract inline `by` blocks into `have` statements:
   ```lean
   -- SLOW: all by-blocks re-elaborate together
   apply lemma arg1 (by scalar_tac) (by agrind) (by grind)

   -- FAST: each have is independently checkpointed
   have h1 : precond1 := by scalar_tac
   have h2 : precond2 := by agrind
   have h3 : precond3 := by grind
   apply lemma arg1 h1 h2 h3
   ```

2. **Large proof blocks without `have` boundaries.** Each tactic step is an elaboration
   checkpoint, but `have` is especially effective: it creates a self-contained sub-proof
   whose result is cached. If the sub-proof's input hasn't changed, the elaborator can
   skip it entirely during incremental replay. Without `have` boundaries, changes can
   force re-elaboration of large contiguous sections.

   **Fix:** Use `have` to break large proofs into independently checkpointed sections,
   especially around expensive tactic calls.

## The step*? Workflow for Complex Function Bodies

When developing a proof for a function body with many monadic calls:

1. Write `step*?` as the tactic (via `edit` tool on disk)
2. Call `lean_code_actions` on that line — it returns the expanded proof script
   as a "Try This" resolved edit
3. Alternatively, call `lean_diagnostic_messages` on that line — the expansion
   appears as an INFO diagnostic
4. Copy the expanded script into your proof and work through it
5. Once the full proof works, try collapsing back into a single `step*`
6. If `step*` works, use it (shorter is better). If not, keep the expanded form.

**How it works:** `step*?` generates a suggestion via `addTryThisTacticSeqSuggestion`.
`lean_code_actions` retrieves it as a resolved edit with the full tactic sequence.

## Key Tips

1. **Use `lean_goal` after every edit** — it is the primary feedback mechanism
2. **Use `lean_multi_attempt` to explore** — try 3-5 tactics at once without touching the file
3. **Use `lean_local_search` before guessing** — verify lemma names exist before using them
4. **Use `lean_hover_info` to check types** — essential when building complex proof terms
5. **Use `lean_code_actions` for step*?** — retrieves the expanded proof script
6. **Use `lean_diagnostic_messages` after edits** — check for errors (empty = tactic worked)
7. **Use `lean_verify` on completed proofs** — confirms no `sorry`, checks axiom usage
8. **Use `lean_state_search` when stuck** — finds lemmas that could close the current goal
9. **Use `lean_hammer_premise` for automation hints** — suggests lemmas for `simp only [...]`
10. **File edits are via the standard `edit`/`create` tools** — MCP tools are read-only
    (except `lean_build`). Edit the file on disk, then use MCP tools to inspect the result.
11. **`lean_multi_attempt` does not modify the file** — it only shows what *would* happen.
    After choosing a tactic, you must apply it yourself with the `edit` tool.
