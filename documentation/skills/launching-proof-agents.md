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

5. **Reinforce lean_lsp.py usage on every interaction**: Agents tend to fall back to
   `lake build` loops. Every time you launch an agent or send it a follow-up message,
   remind it: "Use lean_lsp.py for all proof iteration — do NOT use lake build." This
   is not optional — agents that use `lake build` waste 2–5 minutes per cycle instead
   of 5–30 seconds with the LSP.

## Two-Phase Workflow: Statements First, Then Proofs

**Never let agents write proofs before the theorem statements are validated.**
Agents tend to prove trivially weak postconditions (e.g., just `res.length = n`)
when the spec should express full functional correctness (e.g., relating the output
to a pure specification function). Proving a wrong/weak theorem is wasted work.

### Phase 1: Statement Agents (fast, parallelizable)

Launch agents to write theorem statements with `sorry` proofs. Each agent:

1. **Reads the auto-generated Rust→Lean code** (in `Funs.lean`) to understand the
   function's structure, arguments, and return type.
2. **Reads the pure specification** (in the spec file) to understand what the function
   should compute.
3. **Writes the theorem statement** with appropriate:
   - Preconditions (input lengths, bounds, divisibility)
   - Postcondition relating the output to the specification function
   - Any bridge definitions needed (e.g., `Slice.toMatrix`, `sliceToByteVec`)
4. **Verifies the statement typechecks** (sorry proof is fine at this stage)
5. **Reports back** with the statement for review

**Agent prompt for Phase 1:**
```
Write the theorem statement (with sorry proof) for `function_name.spec`.

Read:
- The auto-generated code in Funs.lean (line N)
- The pure specification `Spec.Foo.Bar` in FooSpec.lean (line M)

The postcondition must express FULL FUNCTIONAL CORRECTNESS:
- NOT just length preservation (that's trivially weak)
- NOT just `True` (useless)
- It must relate the output to the spec function using bridge definitions
  like `Slice.toMatrix`, etc.

Verify the statement typechecks with `sorry` as the proof.
DO NOT attempt the proof — just the statement.
```

### Phase 2: Review Gate (human or code-review agent)

Before launching proof agents, **review every theorem statement**.

**Important:** When the user asks to do a large batch of proofs or launch parallel
proof agents, **ask the user upfront** how they want the review gate handled:

- **(a) Human reviews statements** — Best when the user is actively working and wants
  tight control. Statement agents report back, the user inspects postconditions, then
  proof agents are launched. Higher quality but requires the user to be available.
- **(b) Code-review agent validates** — Best when the user wants agents to work
  uninterrupted for a long time (e.g., overnight). A code-review agent checks that
  postconditions reference the spec functions and aren't trivially weak, then proof
  agents launch automatically. Faster end-to-end but may miss subtle issues.
- **(c) Skip review, go straight to proofs** — Only if the user has already written
  and validated the theorem statements themselves.

Ask this question **before starting any work**, so the user can choose the workflow
that fits their availability. Never assume one mode silently.

**The review gate is a loop, not a one-shot check:**

```
┌──────────────────────────────────────┐
│  Statement agents write statements   │
└──────────────┬───────────────────────┘
               ▼
┌──────────────────────────────────────┐
│  Reviewer checks postconditions      │◄─┐
│  (human or code-review agent)        │  │
└──────────────┬───────────────────────┘  │
               │                          │
          ┌────┴────┐                     │
          │ Valid?  │                     │
          └────┬────┘                     │
         yes   │   no                     │
               │    └─────────────────────┘
               │    Statement agents fix
               ▼    postconditions
┌──────────────────────────────────────┐
│  Proof agents fill sorry proofs      │
└──────────────────────────────────────┘
```

The reviewer sends back specific feedback (e.g., "postcondition too weak — must relate
to `Spec.Frodo.Encode`, not just length") and the statement agent revises. This repeats
until all statements are validated. Only then do proof agents launch.

**Review checklist (for human or code-review agent):**

- Is the postcondition strong enough? Does it express full functional correctness?
- Does it relate to the pure specification function (not just structural properties)?
- Are the preconditions reasonable? (not too strong, not missing necessary ones)
- Are bridge definitions correct?

**Common weak-postcondition patterns to reject:**
- `res.length = n` — length only, says nothing about values
- `True` or `fun _ => True` — vacuously true
- Missing existential for length + functional property
- Only one half of a bidirectional property (e.g., only correctness, not bounds)

### Phase 3: Proof Agents (slower, parallelizable)

Only after statements are validated, launch agents to fill the `sorry` proofs.
Each proof agent works on one file (for isolation) and targets specific sorry's.

### Summary: Fleet Organization

```
┌─────────────────────────────────────────────────┐
│  Phase 1: Statement Agents (parallel per file)  │
│  - Read Funs.lean + Spec                        │
│  - Write theorem statements + sorry             │
│  - Typecheck                                    │
└────────────────────┬────────────────────────────┘
                     │ report statements
                     ▼
┌─────────────────────────────────────────────────┐
│  Phase 2: Review Gate                           │
│  - Human or code-review agent validates         │
│  - Check postconditions are strong enough       │
│  - Fix any issues before proceeding             │
└────────────────────┬────────────────────────────┘
                     │ approved statements
                     ▼
┌─────────────────────────────────────────────────┐
│  Phase 3: Proof Agents (parallel per file)      │
│  - Fill sorry proofs                            │
│  - Use lean_lsp.py for iteration                │
│  - Report progress                              │
└─────────────────────────────────────────────────┘
```

After each proof agent completes:
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
