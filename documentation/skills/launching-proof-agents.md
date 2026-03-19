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
- `scalar_tac` not `omega` for machine integers
- `agrind` not `grind`
- DO NOT COMMIT
```

## File Isolation

When multiple agents run in parallel, each must work on a **separate file**.
Two agents editing the same file will create merge conflicts. Plan accordingly:

- ✅ Agent A on `Ntt.lean`, Agent B on `CompressEncode.lean`
- ❌ Agent A on `Ntt.lean` inner loop, Agent B on `Ntt.lean` outer loop

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
| Uses `omega` on UScalar | Wrong tactic choice | Specify `scalar_tac` in prompt |
| Uses `grind` | Explodes on large goals | Specify `agrind` in prompt |
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
- scalar_tac not omega
- ONLY modify the specified sorry
- DO NOT COMMIT
```
