---
name: launching-proof-agents
description: Multi-agent proof orchestration, review gates, and task decomposition for Aeneas Lean proofs
---

# Launching Proof Agents — Skill File

## Overview

When using AI agents (e.g., GitHub Copilot background agents) to work on Lean proofs
in an Aeneas project, the agent needs specific instructions to be effective. Agents
run in isolated contexts and don't automatically see project-level configuration or
skills files. This document explains how to launch them properly.

## Meta: Validating Instruction Requests

When the user asks to update these skill files (or any agent instructions), the
supervisor must **step back and evaluate whether the proposed instruction is practical
and actionable** before applying it. Specifically:

1. **Can agents actually do this?** Background agents run autonomously in a single turn
   — they cannot send intermediate messages, ask clarifying questions mid-run, or
   respond to external signals. Any instruction that requires mid-run interaction
   (e.g., "report every 10 minutes", "ask the supervisor before proceeding") is
   **not actionable** and will be silently ignored by the agent.

2. **Is the instruction enforceable?** Instructions like "always do X" are only effective
   if the agent can reasonably detect when X applies. Vague instructions ("be careful
   with performance") are less effective than specific ones ("if a tactic takes > 10s,
   extract the sub-goal as a `have` lemma").

3. **Does it conflict with existing guidance?** Check for contradictions with other
   skill files. For example, an instruction to "use `omega` for simple arithmetic"
   would conflict with the banned-tactics list.

**If the proposed instruction is not actionable or practical**, report this to the user
with an explanation of *why* it won't work and propose a practical alternative. For
example: "Background agents can't report mid-run — instead, I'll decompose tasks into
smaller units so each agent completes faster, giving us natural checkpoints."

Do NOT silently add instructions that agents cannot follow — this creates false
expectations and wastes prompt space.

## Agent Prompt Template

Every proof agent prompt should include:

### 1. Pointer to skills files (read first)

```
## Aeneas Skills — READ FIRST

Before doing anything, read these files for essential proof guidance:
- <path-to-aeneas>/documentation/skills/aeneas-lean-core.instructions.md
- <path-to-aeneas>/documentation/skills/lean-lsp-tool.instructions.md
- <path-to-aeneas>/documentation/skills/aeneas-tactics-quickref.instructions.md
```

### 2. Mandatory lean_lsp.py usage

```
### MANDATORY: Use lean_lsp.py — NOT lake build

DO NOT use `lake build` to iterate on proofs. Use lean_lsp.py:

  cd <project-lean-root>
  python3 <path-to-aeneas>/scripts/lean_lsp.py --repl --json

Workflow: open → sorry → goal → edit → errors → repeat
Only use `lake build` once at the very end to confirm the final result.

⛔ NEVER run `lake clean` or delete `.lake/`. This forces a full rebuild (30+ min). Fix root causes instead.
```

### 3. The step*? workflow

```
### Use step*? to develop proofs

See lean-lsp-tool.instructions.md for the full step*? workflow.
In short: write `step*?` → `info <line>` to read the expanded script →
copy it into your proof → fix sub-goals → collapse back to `step*` if possible.
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
- NEVER spawn sub-agents that work on Lean files (see below)
- DO NOT COMMIT
```

### 6. No sub-agent spawning

**⛔ Proof agents must NEVER spawn sub-agents that open or edit Lean files.**
This is a hard rule, not a suggestion. Reasons:

1. **Resource exhaustion**: Each Lean LSP instance consumes ~8 GB of RAM. The
   supervisor carefully controls how many run in parallel. An agent spawning its
   own Lean sub-agent can push the system into swapping, making ALL agents slower.
2. **File conflicts**: The supervisor tracks which agent works on which file. A
   sub-agent working on the same file as its parent (or another agent) causes
   merge conflicts and spurious elaboration errors.
3. **Loss of control**: The supervisor cannot see or manage sub-agents spawned by
   other agents. This breaks the observability model.

Agents may use the `task` tool for **non-Lean tasks only** (e.g., launching an
`explore` agent to search the codebase, or a `task` agent to run a shell command).
Any agent that needs to work on a Lean file must do so itself — if the task is too
large, it should report back and let the supervisor decompose it.

## File Isolation and Parallelism Limits

### How many agents in parallel?

**Ask the user upfront** how many agents can work on Lean files simultaneously. Each
Lean LSP server instance consumes significant memory (~8 GB). A good default is:

> **Max parallel Lean agents = RAM (in GB) / 8**

For example: 64 GB RAM → up to 8 parallel agents. Exceeding this causes swapping,
which makes all agents drastically slower — better to run fewer agents fast than many
agents slowly.

### Lean process budget tracking

The supervisor must **explicitly track how many agents are running Lean processes**
(lean_lsp.py or lake build) at any given time. This is a hard resource constraint.

**When launching agents, classify each as:**
- **Lean agent** — will open lean_lsp.py or run lake build. Counts against the Lean
  process budget. Examples: proof agents, statement agents, review agents that build.
- **Non-Lean agent** — only reads files, runs grep/glob, does analysis. Does NOT count
  against the budget. Examples: explore agents, code-review agents (read-only).

**Before every launch**, state the budget explicitly:
> "Lean process budget: 4 max. Currently running: 2 (a-mulas, c-encode).
> Launching 2 more (b-mulsa, d-toplevel) → 4/4. At capacity."

**When an agent completes**, update the count and consider dispatching waiting work:
> "a-mulas completed. Lean processes: 3/4. Dispatching follow-up agent for
> MulASPlusE remaining sorry."

**Never exceed the budget.** If all slots are full, queue the work and dispatch
when a slot frees up.

### File isolation rules

When multiple agents run in parallel, each must work on a **separate file**.
Two agents editing the same file will create merge conflicts. Additionally,
the files must **not depend on each other**: file A depends on file B if A
transitively imports B. If A imports B, then changes to B would invalidate A's
elaboration, causing the agent working on A to see spurious errors.

- ✅ Agent A on `Ntt.lean`, Agent B on `CompressEncode.lean` (no import relationship)
- ❌ Agent A on `Ntt.lean` inner loop, Agent B on `Ntt.lean` outer loop (same file)
- ❌ Agent A on `VectorOps.lean`, Agent B on `Ntt.lean` (if VectorOps imports Ntt)

### Pre-Launch Conflict Check (MANDATORY)

**Before launching any fleet of agents**, the supervisor must explicitly verify
that no two agents will conflict. For each pair of agents in the batch:

1. **Same-file check**: Are any two agents targeting the same `.lean` file?
   If yes, merge them into one agent or serialize them (run one after the other).

2. **Import-dependency check**: Does any agent's file import (directly or
   transitively) another agent's file? Trace the `import` chain. If A imports B,
   the agent on A must wait until the agent on B finishes and its changes are saved.

3. **Shared-definition check**: Do any two agents' files depend on a shared
   definition file (e.g., `Defs.lean`, `MatDefs.lean`) that a *third* agent is
   also modifying? If so, the third agent must finish first.

**How to verify:** Before launching, list each agent's target file and quickly
check the `import` statements at the top of each file. Draw the dependency edges
and confirm there are no conflicts. State this check explicitly in your reasoning
(e.g., "CT.lean imports Defs.lean, MulBS.lean imports MatDefs.lean — no mutual
dependencies, safe to parallelize").

**If you discover a conflict after agents are already running**, stop the
conflicting agent immediately, wait for the other to finish, then relaunch.

## Task Decomposition and Agent Supervision

When the user asks for a large task (e.g., "prove all sorry's in this file"), do NOT
give the entire task to a single agent in one shot. Instead:

1. **Decompose into small tasks**: Each agent call should target **1-2 specific
   sorry's** in a single file. This gives the supervisor a checkpoint after each
   agent, enabling strategy redirection.

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

4. **Review completed work for reusable lemmas**: When an agent finishes, review the
   helpers, definitions, and lemmas it introduced. Classify them into three categories:

   **(a) Project-wide helpers** — lemmas that are general within the project but not
   general enough for the Aeneas stdlib. Move these to shared definition files
   (e.g., `Defs.lean`, `MatDefs.lean`) so other proof files can import them.
   Examples: index arithmetic helpers (`mul_NBAR_add_div`), project-specific
   simp lemmas, bridge definitions between Aeneas types and spec types.

   **(b) Aeneas stdlib candidates** — lemmas that are fully general and would benefit
   any Aeneas user, not just this project. **Do not move these yourself.** Instead,
   collect them and report to the user as a batch:
   "These lemmas from agent X are good candidates for the Aeneas stdlib:
   - `Slice.getElem_set_ne` — general Slice lemma about set-at-different-index
   - `UScalar.bv_xor_eq` — missing `@[bvify_simps]` lemma for XOR
   - ..."
   The user decides whether and when to upstream them.

   **(c) Proof-local helpers** — lemmas that are specific to one theorem's proof.
   Leave these `private` in the Properties file where they were created.

   **When moving (a) to shared files:** Be careful about import cycles. Only move
   a lemma to `Defs.lean` if it doesn't require imports beyond what `Defs.lean`
   already has. Same for `MatDefs.lean`. If a helper needs imports from a Properties
   file, it stays in the Properties file.

5. **Iterate**: Based on the agent's report, launch a follow-up agent with refined
   instructions, or pivot to a different approach. Never let an agent run for hours
   without checking in.

6. **Reinforce lean_lsp.py usage on every interaction**: Agents tend to fall back to
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
4. **Sketches the proof strategy**: Before finalizing, the statement agent **must always
   sketch the proof** — this is not optional. Lay out the key steps in plain language,
   checking that each step follows. For loops and recursive functions, **explicitly state
   the loop invariant** — this directly guides the mechanized proof. Write this sketch
   as a comment in the theorem body (above the `sorry`).

   The sketch should cover:
   - The main proof structure (unfold + progress, case split, loop invariant, etc.)
   - Which existing specs will be needed (list them by name)
   - Any auxiliary lemmas that will be required
   - Edge cases (empty inputs, zero-length slices, boundary values)
   - Off-by-one errors in the Rust code
   - Potential bugs in the implementation (e.g., incorrect masks, wrong shift amounts,
     missing modular reductions)
   - Whether the spec and implementation actually agree on all inputs

   If the agent suspects a bug, it should report it rather than writing a statement
   that papers over the issue.

5. **Assesses function decomposition (for functions > 30 lines)**: For large functions
   (> 30 lines of generated Lean code), the statement agent must assess whether the
   function should be **split using the fold/refolding technique** (see "Function
   Decomposition" in the crypto verification skill file). This is critical for proof
   performance — proofs for large monolithic functions are slow and hard to maintain.

   The agent should:
   - Identify natural sub-computations in the function body (e.g., a setup phase,
     a loop body, a finalization step, repeated sub-patterns like Montgomery reduction)
   - For each proposed split, define the **auxiliary function** (the subsequence of
     monadic operations to extract) and write its **spec** (theorem statement with
     `sorry` proof)
   - Indicate where the **fold theorem** will be needed (which lines of the original
     function body correspond to each auxiliary function)
   - Include the auxiliary function specs in the output alongside the main theorem

   Example output structure:
   ```lean
   -- Auxiliary function: extracted from lines 15-25 of the main function
   private def setup_phase (params : U32) (buf : Slice U16) : Result (Slice U16) := do
     ...

   -- Fold theorem (to be proved)
   private theorem fold_setup_phase ... :
     (do /- lines 15-25 inline -/ f result) = (do let r ← setup_phase params buf; f r) := by
     sorry

   -- Auxiliary spec
   @[local progress]
   theorem setup_phase.spec ... :
     setup_phase params buf ⦃ res => ... ⦄ := by sorry

   -- Main theorem (uses auxiliary specs via progress)
   @[progress]
   theorem main_function.spec ... :
     main_function ... ⦃ res => ... ⦄ := by sorry
   ```

   If the function is small enough (≤ 30 lines) or naturally simple (few monadic steps),
   the agent should note "no decomposition needed" and explain why.

6. **Verifies the statement typechecks** (sorry proof is fine at this stage)
7. **Reports back** with the statement for review

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

ALWAYS sketch the proof strategy as a comment above the sorry. Include:
- Main proof structure (unfold + progress, case split, loop invariant, etc.)
- Which existing specs are needed (by name)
- Any auxiliary lemmas required
- Edge cases and potential bugs to watch for

If the function is > 30 lines of generated Lean code, assess whether it should
be SPLIT using the fold/refolding technique. If yes:
- Define the auxiliary functions (extracted subsequences of monadic operations)
- Write their specs (theorem statements with sorry)
- Indicate where fold theorems are needed
- Include all of this in your output

Verify the statement typechecks with `sorry` as the proof.
DO NOT attempt the mechanized proof — just the statement + sketch + decomposition.
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
- **Is the postcondition strong enough for callers?** Check which other theorems
  (e.g., outer loop specs, top-level function specs) will need this theorem's result
  via `step`. Those callers will only see the postcondition — so it must contain
  everything they need. For example, if an outer loop needs both the length AND
  element-wise values of a slice, the inner loop's postcondition must provide both.
  Trace the call chain: find the callers in the generated Lean code, look at what
  their proof goals will require, and verify the postcondition delivers it.
- **Is the theorem actually true?** The reviewer should actively look for corner cases
  and potential bugs in the Rust implementation that would make the theorem false.
  Check: edge cases (empty inputs, boundary values), off-by-one errors, incorrect
  bit manipulation, missing modular reductions. If a bug is suspected, flag it
  immediately rather than letting proof agents waste time on an unprovable theorem.
- **Is the proof sketch present, complete, and correct?** Every statement must include
  a proof sketch as a comment. Check that it covers: main proof structure, required
  specs by name, auxiliary lemmas, and edge cases. Are the steps logically sound? Are
  loop invariants stated correctly and strong enough? Does the sketch actually cover
  all cases? A missing, vague, or incorrect sketch should be sent back — it will
  mislead the proof agent.
- **Is the function decomposition adequate?** For functions > 30 lines: did the agent
  assess whether splitting is needed? If yes, are the auxiliary functions well-chosen
  (natural sub-computations, not arbitrary splits)? Are their specs strong enough for
  the main proof to use via `progress`? If the agent said "no decomposition needed",
  is that justified? A function with 50+ monadic steps that wasn't decomposed should
  be flagged.

**Common weak-postcondition patterns to reject:**
- `res.length = n` — length only, says nothing about values
- `True` or `fun _ => True` — vacuously true
- Missing existential for length + functional property
- Only one half of a bidirectional property (e.g., only correctness, not bounds)

### Phase 3: Proof Agents with Review Loop (slower, parallelizable)

Only after statements are validated, launch agents to fill the `sorry` proofs.
Each proof agent works on one file (for isolation) and targets specific sorry's.

**Detecting unprovable theorems and Rust bugs:**

If a proof agent spends a long time stuck on a goal that won't close, it should
consider the possibility that the theorem is **unprovable** — either because:
- The theorem statement is wrong (preconditions too weak, postcondition too strong)
- There is a **bug in the Rust source code** (the implementation doesn't match the spec)

The agent should actively look for counterexamples: try specific parameter values,
trace the Rust logic by hand, check if a particular input would violate the
postcondition. If a bug is found or suspected, the agent must **stop proving
immediately and report the finding**.

The master should also watch for this: if an agent has been stuck on the same goal
for multiple iterations without progress, remind it: "Consider whether this theorem
is actually true. Look for counterexamples or bugs in the Rust code."

**🚨 CRITICAL: When a bug in the Rust code is discovered, report it IMMEDIATELY
and IMPERATIVELY to the user.** This is one of the most valuable outcomes of formal
verification — finding real bugs. Do not bury it in a status update. Make it
prominent: "BUG FOUND in `function_name`: [description of the bug]. The Rust code
does X but the spec requires Y. Counterexample: [specific input that triggers it]."

**🚨 CRITICAL: When an axiom or external model is too weak, report it IMMEDIATELY.**
In Aeneas projects, external functions (FFI, stdlib, crypto primitives) are modeled via
hand-written definitions and axiomatized step specs (typically in `ExternalSpecs.lean`
or similar files). If a statement or proof agent discovers that such an axiom has a
postcondition that is too weak to prove the needed theorem (e.g., `fun _ => True` when
the proof needs functional properties of the output), the agent MUST:

1. **Report immediately** — do not silently work around a fundamentally weak axiom.
2. **Identify the axiom** — name the specific axiom/spec and its file location.
3. **Explain what is missing** — what postcondition property does the proof need?
4. **Suggest the fix** — propose a strengthened postcondition. For example:
   "The axiom `encrypt_block.spec` has postcondition `True`, but the outer loop proof
   needs it to return the AES encryption of the input block. Suggested fix:
   ```lean
   axiom frodokem.encrypt_block.spec (c : aes.soft.Aes128) (block : Array U16 8#usize) :
     frodokem.encrypt_block c block ⦃ fun out =>
       out = specEncryptBlock c block ⦄
   ```
   where `specEncryptBlock` is a pure specification of AES-128 block encryption."

**What happens after reporting depends on the workflow mode.** Before launching agents,
the supervisor must ask the user which mode to use:

- **(a) Stop and wait** — The agent stops working on the blocked theorem and reports back.
  Best when the user is available and wants to fix the axiom before the agent continues.
- **(b) Continue and assume locally** — The agent locally assumes the spec it needs
  (as a local `axiom` or `sorry`'d lemma with a
  `-- TODO: the spec for X in ExternalSpecs.lean is too weak; strengthen it and move this assumption there`
  comment) and continues proving as far as possible. Best when the user is away and wants
  maximum progress. The supervisor collects these local assumptions and presents them to
  the user for review later.

The supervisor should ask this question **once upfront** (not per-agent), and include
the chosen mode in every agent prompt.

This applies equally to statement agents (who may realize the axiom is too weak to even
*state* a meaningful theorem) and proof agents (who get stuck because the axiom provides
no usable information).

**After a proof agent makes good progress on a theorem** (e.g., reduces sorry count,
completes a loop proof, fills a significant chunk), a **review agent** should check
the proof against the skill files and project guidelines. This is also a loop:

**Before handing off to the review agent, the proof agent MUST verify that the entire
file builds without errors.** Run `lake build <module>` (e.g., `lake build Properties.CT`)
and confirm 0 errors. Warnings about `sorry` are acceptable if some sorry's remain, but
there must be NO type errors, NO elaboration failures, NO tactic failures. If the file
doesn't build cleanly, the proof agent must fix the errors before reporting.

```
┌──────────────────────────────────────┐
│  Proof agent works on sorry's        │
│  (reports progress to master)        │
├──────────────────────────────────────┤
│  Proof agent runs lake build         │
│  → MUST be 0 errors before handoff   │
└──────────────┬───────────────────────┘
               ▼
┌──────────────────────────────────────┐
│  Review agent checks proof quality   │◄─┐
│  (re-reads skill files, checks       │  │
│   idioms, tactics, build, style)     │  │
└──────────────┬───────────────────────┘  │
               │                          │
          ┌────┴────┐                     │
          │ Clean?  │                     │
          └────┬────┘                     │
         yes   │   no                     │
               │    └─────────────────────┘
               │    Proof agent fixes issues
               ▼    (reports fixes to master)
┌──────────────────────────────────────┐
│  Done — report final result          │
└──────────────────────────────────────┘
```

**Review agent checklist for proofs:**

- **Does the file build without errors?** The review agent MUST run `lake build <module>`
  and verify 0 errors. If the proof agent handed off a broken file, send it back immediately.
  `sorry` warnings are acceptable; type errors, tactic failures, and elaboration errors are NOT.
- **Is the proof idiomatic?** Uses standard Aeneas patterns (step, WP.spec_mono,
  split_ifs, etc.) rather than ad-hoc workarounds? Follows the patterns documented
  in proof-patterns.instructions.md?
- **Is the proof clean and not verbose?** No unnecessary intermediate steps, no
  copy-paste bloat, no redundant `have` statements that could be inlined. Each tactic
  call should earn its place.
- **Does the proof use only idiomatic tactics?** This is a critical idiomaticity criterion.
  Re-read the skill files and **grep the file for banned tactics**:
  - `omega` — **BANNED.** Replace with `agrind`, `grind`, or `scalar_tac`
  - `linarith` — **BANNED.** Replace with `agrind`, `grind`, or `scalar_tac`
  - `nlinarith` — **BANNED.** Replace with `agrind`, `grind`, `scalar_tac +nonLin`, or `simp_scalar`
  - These tactics cannot reason about Aeneas scalar types (U8, U32, Usize, etc.),
    `Slice.length`, `Vec.length`, or any Aeneas-specific concepts. A proof using them
    is non-idiomatic and fragile — it must be rewritten, even if it currently works.
  - Also check: uses `agrind` over `grind`? Uses `ring` in `calc`/`have` steps?
  - Does not unfold Aeneas stdlib definitions?
- **Are all warnings addressed?** After building, check the warning output. The following
  warnings are **NOT acceptable** and must be fixed before the proof is considered done:
  - `"This simp argument is unused"` — remove the unused lemma from `simp only [...]`
  - `"Too many ids provided"` — reduce the binder count in `step as ⟨...⟩`
  - `"unused variable"` — remove or rename with `_` prefix
  - `"'tactic' does nothing"` / `"'tactic' tactic is never executed"` — remove the dead tactic
  - The ONLY acceptable warnings are `"declaration uses 'sorry'"` (for remaining sorry's).
- No big `simp only [...]` calls in implementation proofs? (model is unstable)
- Complex arithmetic/bitwise sub-proofs extracted as auxiliary lemmas?
- Are helper lemmas properly named and documented if non-obvious?
- **No early case splits on parameters?** If the proof does `cases p` at the top level
  (duplicating the entire proof for each parameter variant), it should be refactored:
  case splits should be local (inside sub-goals) or handled via `attribute [local agrind]`.
- **Spaces around binary operators in comments?** Check that comments and doc strings
  use `j < N`, not `j<N`. Missing spaces cause VS Code highlighting bugs.
- **Is the proof fast enough?** Profile with `set_option trace.profiler true in` and
  check that the proof completes in **< 30 seconds wall-clock** (even for the biggest
  functions of 50+ lines). If it's slower, identify the bottleneck tactic and send the
  proof back for optimization — decompose the function, extract auxiliary lemmas,
  minimize the context, or pick better tactics. See the "Wall-clock time target"
  section in `aeneas-tactics-quickref`.

**Skill file freshness:**

- **Every agent invocation** (statement agents, proof agents, review agents) **must
  include the "read skill files first" instruction** in its prompt — both the
  **Aeneas skill files** (in the aeneas repo under `documentation/skills/`) and any
  **project-local skill files** (e.g., `.github/instructions/`, `.claude/skills/`).
  Since each agent invocation is a fresh context, this ensures the agent always works
  from the latest version of all skill files — including any mid-run updates the
  master made (with user approval).
- If the reviewer finds **many guideline violations** (e.g., 3+ issues that the
  skill files clearly address), the feedback to the proof agent should include an
  explicit instruction: **"Re-read the skill files before fixing these issues."**
  This forces the proof agent to refresh its understanding rather than just
  mechanically patching the flagged spots. The proof agent may have read an older
  version of the skills, or may have drifted from the guidelines over a long run.

**Progress reporting and task granularity:** Background agents run autonomously and
cannot send intermediate progress reports — they complete their task and return a
single final result. **The supervisor controls observability through task granularity.**

**Startup cost awareness:** Each agent pays a significant startup cost: reading skill
files (~1 min), starting lean_lsp.py, and elaborating the file (~3-10 min depending
on file size and imports). This cost is paid per agent, regardless of task size.

**The right granularity depends on sorry difficulty.** Before dispatching, the
supervisor must assess each sorry's expected difficulty:

- **Easy sorry's** (e.g., top-level wrappers that just unfold + `step*`, simple
  arithmetic bounds, proofs with clear sketches): batch several per agent (3-5).
- **Medium sorry's** (e.g., loop invariant proofs with known patterns, proofs
  needing a few auxiliary lemmas): give 1-2 per agent.
- **Hard sorry's** (e.g., complex loop invariants with bitwise/modular reasoning,
  proofs requiring new bridge definitions, proofs where the approach is unclear):
  give exactly 1 per agent — these can take 30-60 min each, and the supervisor
  needs to review the approach before continuing.

**How to assess difficulty:** Read the proof sketch (if present), look at the
function's monadic step count, check if similar proofs exist in the codebase,
and consider whether the needed specs/lemmas already exist. When uncertain,
err on the side of fewer sorry's per agent — it's better to dispatch a second
round quickly than to wait 90 min for an overloaded agent.

- **Give each agent 1-2 sorry's** in a specific file: "Fill the sorry at line 130
  in MulASPlusE.lean" or "Fill sorry's at lines 130 and 168 in MulASPlusE.lean".
- **Parallelize across files**: Launch multiple agents simultaneously, each targeting
  a different file. Startup costs overlap, so wall-clock time is the slowest agent.
- **Multiple agents on the same file**: Two agents can work on the same file in
  parallel IF they target non-overlapping sorry's (different theorems). Each runs
  its own LSP instance. The supervisor must merge their edits carefully afterwards.
- **Small related files can be batched**: If KeyGen.lean (1 sorry) and Decaps.lean
  (1 sorry) are small and independent, one agent can handle both sequentially.

For example, with 13 sorry's across 6 files, assessed as 3 hard + 5 medium + 5 easy:
- ✅ Agent A: 1 hard sorry (MulASPlusE line 946 — complex loop invariant)
- ✅ Agent B: 2 medium sorry's (MulSAPlusE lines 837, 875)
- ✅ Agent C: 1 hard sorry (EncodeDecode line 278 — bit-packing)
- ✅ Agent D: 5 easy sorry's (KeyGen + Encaps + Decaps — wrapper unfolds)
- ✅ Round 2: dispatch remaining sorry's based on Round 1 results
- ❌ 1 agent for all 13 sorry's across 6 files (no parallelism, no observability)

**Instruct agents to report what they accomplished** in their final response:
- Which sorry's were filled (and which remain, if any)
- What approach was used for each
- Any blockers or missing lemmas discovered
- Whether the file builds cleanly after their changes

**When an agent's task is inherently large** (e.g., a single complex loop invariant
proof that takes 30+ min), instruct it to report partial progress in its final
response even if it couldn't complete the proof:
- What approach was tried
- How far it got (e.g., "reduced the goal to X but couldn't close Y")
- What it thinks is needed to finish

This lets the master maintain situational awareness and intervene early if needed (e.g.,
redirect an agent that's going in circles, provide missing context, escalate to the user).

## Master Synthesis: Learning from Agent Reports

The master orchestrator should not just passively relay agent results. It should
**synthesize patterns** across completed agents' reports to identify systemic issues
and improvement opportunities. Small, focused tasks make this easier — each
completion is a data point about what's working and what isn't.

After a batch of agents completes (or between rounds of dispatching), the master
should ask itself:

### 1. Proof Strategy Issues
- Are multiple agents struggling with the same kind of sub-goal? (e.g., all stuck
  on bitwise reasoning, or all failing to close a loop invariant)
- Would a different proof strategy unblock several agents at once?
- Is there a common missing lemma that, if proved once, would help many proofs?
- Should the master pause agents, prove that lemma centrally, then resume?

### 2. Skill File Updates
- Are agents repeatedly making the same mistake despite reading the skill files?
  → The skill file is missing guidance on that specific pattern.
- Did an agent discover a useful technique not yet documented?
  → Add it to the skills so future agents benefit.
- Are agents confused by ambiguous or outdated instructions?
  → Clarify the skill files.

### 3. Automation and Tooling Opportunities
- Is there a repetitive mechanical step that agents do manually every time?
  → Could it be automated (e.g., a new tactic, a script, a code generator)?
- Are agents spending a lot of time on boilerplate (e.g., writing bridge definitions,
  unfolding the same chain of lets)?
  → Consider adding automation or shared infrastructure.
- Is the `lean_lsp.py` workflow missing a feature that would speed up agents?

### 4. Reporting to the User
The master should surface these synthesis findings to the user, not just raw agent
results. For example:

- "Three agents are all stuck on ZMod bitwise reasoning — we may need a shared lemma
  `zmod_and_pow2` before they can proceed."
- "Agents keep using `grind` instead of `agrind` — I've updated the skill file to
  make this more prominent."
- "The inner-loop pattern `for i in (0..n).step_by(k)` appears in 4 functions. The
  first agent found a workaround; I'll propagate it to the others."
- "I notice agents spend ~30% of their time on bridge definitions. We could add
  `Slice.toBitstring` to Defs.lean to eliminate this across all encode/decode proofs."

**Important:** The master does NOT act on these findings autonomously. It reports
them to the user as recommendations and waits for validation before making changes.
For example:
- "I noticed X pattern — should I update the skill file?" (wait for yes/no)
- "Three agents are blocked on the same lemma — should I pause them and prove it
  centrally?" (wait for approval)
- "Agent A found a useful workaround — should I propagate it to the others?" (wait)

The user decides what to act on. The master's job is to synthesize and surface
insights, not to make unilateral decisions about strategy, skill files, or tooling.

This synthesis loop is what makes a fleet of agents more effective than the same
agents running independently — the master surfaces cross-agent patterns and the
user steers improvements.

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
│  Phase 2: Statement Review Gate (loop)          │
│  - Human or code-review agent validates         │
│  - Check postconditions are strong enough       │
│  - Fix any issues, re-review until approved     │
└────────────────────┬────────────────────────────┘
                     │ approved statements
                     ▼
┌─────────────────────────────────────────────────┐
│  Phase 3: Proof Agents + Review Loop            │
│  - Proof agent fills 1-2 sorry proofs           │
│  - Review agent checks quality & guidelines     │
│  - Fix issues, re-review until clean            │
│  - Supervisor dispatches next batch of sorry's   │
└─────────────────────────────────────────────────┘
```

After each proof+review cycle completes:
- Master reviews the final output (did it succeed? partial? fail?)
- Verify the file builds (`lake build` once)
- If partial, launch a follow-up agent with refined instructions

## Common Agent Failure Modes

| Failure | Cause | Fix |
|---------|-------|-----|
| Agent uses `lake build` loops | Didn't read LSP skill | Stronger prompt, mandate LSP |
| `step*` times out | Too many monadic calls | Use `step*?` workflow |
| Unfolds stdlib definitions | Didn't read core skill | Add "don't unfold" rule to prompt |
| Uses `omega` | `omega` can't reason about scalars, `U32.max`, list lengths, etc. | NEVER use `omega` — use `scalar_tac`, `agrind`, or `grind` |
| Uses `nlinarith` | Same issues as `omega` — can't reason about scalars | NEVER use `nlinarith` — use `scalar_tac` or `simp_scalar` |
| Uses `linarith` | Same issues as `omega` — can't reason about scalars | NEVER use `linarith` — use `scalar_tac` or `agrind` |
| Edits wrong file/section | Ambiguous instructions | Be very specific about what to change |
| Increases `maxRecDepth` | Trying to work around recursion depth errors | NEVER increase `maxRecDepth` — diagnose the root cause (bad proof structure or simp loop). Report to user if it's a tactic bug |
| Tactic silently fails | Tactic doesn't do what it should (e.g., `progress` can't find a lemma that exists) | Report to user — may be a tactic bug worth fixing upstream |
| Spawns Lean sub-agents | Agent tries to parallelize by spawning sub-agents | NEVER spawn sub-agents that work on Lean files — resources are tight, and it causes file conflicts |

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
Use `step*?` to generate the body proof script, then fix sub-goals.

## Available Specs
- `butterfly_spec`, `mod_add_spec`, etc.

## Key Rules
- NEVER unfold stdlib
- NEVER use `omega` — use `scalar_tac` instead, or `agrind` (prefer), or `grind`
- ONLY modify the specified sorry
- DO NOT COMMIT
- After completing this sorry, STOP and return results — do NOT proceed to other work
```
