# Launching Proof Agents — Skill File

## Overview

When using AI agents (e.g., GitHub Copilot background agents) to work on Lean proofs
in an Aeneas project, the agent needs specific instructions to be effective. Agents
run in isolated contexts and don't automatically see project-level configuration or
skills files. This document explains how to launch them properly.

## Agent Prompt Template

Every proof agent prompt should include:

### 1. Pointer to skills files (read first)

```
## Aeneas Skills — READ FIRST

Before doing anything, read these files for essential proof guidance:
- <path-to-aeneas>/documentation/skills/aeneas-lean-core.md
- <path-to-aeneas>/documentation/skills/lean-lsp-tool.md
- <path-to-aeneas>/documentation/skills/aeneas-tactics-quickref.md
```

### 2. Mandatory lean_lsp.py usage

```
### MANDATORY: Use lean_lsp.py — NOT lake build

DO NOT use `lake build` to iterate on proofs. Use lean_lsp.py:

  cd <project-lean-root>
  python3 <path-to-aeneas>/scripts/lean_lsp.py --repl --json

Workflow: open → sorry → goal → edit → errors → repeat
Only use `lake build` once at the very end to confirm the final result.
```

### 3. The progress*? workflow

```
### Use progress*? to develop proofs

For function bodies with multiple monadic calls:
1. Write `progress*?` as the tactic
2. Run `info <line>` to read the "Try this:" suggestion
3. Copy the expanded `let*` script into your proof
4. Fix any failing sub-goals
5. Once done, try collapsing back to `progress*`
```

### 4. Task-specific context

- Which file to edit (full path)
- Which sorry's to fill (line numbers)
- Available specs and lemmas
- Proof strategy hints
- What NOT to modify

### 5. Constraints

```
## Key Rules
- NEVER unfold Aeneas stdlib definitions — search for existing lemmas
- NEVER use `omega` — use `scalar_tac`, `agrind`, or `grind` instead
- DO NOT COMMIT
```

## File Isolation

When multiple agents run in parallel, each must work on a **separate file**.
Two agents editing the same file will create merge conflicts. Additionally,
the files must **not depend on each other**: file A depends on file B if A
transitively imports B. If A imports B, then changes to B would invalidate A's
elaboration, causing the agent working on A to see spurious errors.

- ✅ Agent A on `Ntt.lean`, Agent B on `CompressEncode.lean` (no import relationship)
- ❌ Agent A on `Ntt.lean` inner loop, Agent B on `Ntt.lean` outer loop (same file)
- ❌ Agent A on `VectorOps.lean`, Agent B on `Ntt.lean` (if VectorOps imports Ntt)

## Task Decomposition and Agent Supervision

When the user asks for a large task (e.g., "prove all sorry's in this file"), do NOT
give the entire task to a single agent in one shot. Instead:

1. **Decompose into small tasks**: Each agent call should target one or two specific
   sorry's, or one well-defined sub-problem. Small tasks are easier for agents to
   complete successfully.

2. **Give one small task at a time**: Launch an agent with a focused objective. When it
   reports back, analyze the result before deciding what to do next.

3. **Supervise actively**: When an agent reports:
   - **Step back**: Understand whether the work is going well. Did the agent make progress?
     Did it get stuck? Is it going in circles?
   - **Diagnose slowness**: If the agent is slow, check why — is it using `lake build`
     instead of `lean_lsp.py`? Is it stuck on a heartbeat explosion? Is it trying an
     approach that won't work?
   - **Assess the approach**: Is the proof strategy sound? Should you redirect the agent
     with different hints?
   - **Report to the user**: Surface interesting findings — e.g., "the agent discovered
     that spec X is missing", "this sorry requires a new lemma about bit operations",
     "the agent reduced 8 sorry's to 3 but the remaining ones are hard because..."

4. **Iterate**: Based on the agent's report, launch a follow-up agent with refined
   instructions, or pivot to a different approach. Never let an agent run for hours
   without checking in.

## Incremental Strategy

Proofs should be done incrementally:

1. **Skeleton first**: State all theorem signatures with `sorry` proofs. Verify builds.
2. **Easy sorry's next**: Fill in the straightforward ones (loop framework, base cases).
3. **Hard sorry's last**: Bit-level reasoning, complex invariants — these may need
   multiple agent iterations.

After each agent completes:
- Review its output (did it succeed? partial? fail?)
- Verify the file builds (`lake build` once)
- If partial, launch a follow-up agent with refined instructions

## Common Agent Failure Modes

| Failure | Cause | Fix |
|---------|-------|-----|
| Agent uses `lake build` loops | Didn't read LSP skill | Stronger prompt, mandate LSP |
| `progress*` times out | Too many monadic calls | Use `progress*?` workflow |
| Unfolds stdlib definitions | Didn't read core skill | Add "don't unfold" rule to prompt |
| Uses `omega` | `omega` can't reason about scalars, `U32.max`, list lengths, etc. | NEVER use `omega` — use `scalar_tac`, `agrind`, or `grind` |
| Uses `omega` | Cannot reason about scalars, definitions, etc. | Use `scalar_tac`, `agrind`, or `grind` |
| Edits wrong file/section | Ambiguous instructions | Be very specific about what to change |

## Example: Full Agent Prompt

```
Fix the inner loop sorry in `/path/to/Ntt.lean`.

## Aeneas Skills — READ FIRST
Read these files: [list paths]

### MANDATORY: Use lean_lsp.py
[lean_lsp.py instructions]

## The Sorry
`poly_element_ntt_layer_generic_loop0_loop0_spec` at line ~421.

## Proof Strategy
Use `loop.spec_decr_nat` with measure `iter.end - iter.start`.
Use `progress*?` to generate the body proof script, then fix sub-goals.

## Available Specs
- `butterfly_spec`, `mod_add_spec`, etc.

## Key Rules
- NEVER unfold stdlib
- NEVER use `omega` — use `scalar_tac` instead, or `agrind` (prefer), or `grind`
- ONLY modify the specified sorry
- DO NOT COMMIT
```
