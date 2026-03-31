---
name: launching-proof-agents
description: Multi-agent proof orchestration, review gates, and task decomposition for Aeneas Lean proofs
---

# Launching Proof Agents — Skill File

## Overview

When using AI agents (e.g., GitHub Copilot background agents) to work on Lean proofs
in an Aeneas project, the agent needs specific instructions to be effective. Agents
run in their own context window but **do have access to MCP tools and skill files**.
Instruct them to invoke relevant skills (e.g., `aeneas-lean-core`, `lean-lsp-mcp`)
as their first action — this is more reliable than copying instructions into prompts.

**For general agent management rules** (resource budgets, file isolation, spawning
rules, task granularity, etc.), see the `agent-fleet-management` skill file. This
file only covers proof-specific workflow and instructions.

## Agent Prompt Template

Every proof agent prompt should include:

### 1. Skills invocation (FIRST action)

Agents have access to MCP tools and skill files. Instead of copying instructions
into prompts, instruct agents to **invoke skills directly** as their first action:

```
## Skills — Invoke FIRST

As your FIRST action, invoke these skills (use the `skill` tool):
1. `aeneas-lean-core` — translation model, spec patterns, pitfalls
2. `aeneas-tactics-quickref` — which tactic for which goal
3. `lean-lsp-mcp` — mandatory tooling for proof checking

Then invoke `aeneas-crypto-verification` if working on crypto-specific proofs.

These skills contain ALL the rules and patterns you need. Read them carefully
before writing any Lean code.
```

### 2. Mandatory lean-lsp-mcp usage

```
### MANDATORY: Use lean-lsp-mcp tools — NOT lake build

DO NOT use `lake build` to iterate on proofs. Use the lean-lsp-mcp tools
(see the `lean-lsp-mcp` skill file for full reference).

The tools (`lean_goal`, `lean_diagnostic_messages`, `lean_multi_attempt`, etc.)
are available directly in your tool palette. If they are not available, ask the
user to install lean-lsp-mcp (see the `lean-lsp-mcp` skill file).

Workflow: edit file on disk → lean_goal → lean_multi_attempt → edit → repeat
Only use `lake build` once at the very end to confirm the final result.

⛔ NEVER run `lake clean` or delete `.lake/`. This forces a full rebuild (30+ min). Fix root causes instead.
```

### 3. The step*? workflow

```
### Use step*? to develop proofs

See the `lean-lsp-mcp` skill file for the full step*? workflow.
In short: write `step*?` → `lean_code_actions` on that line to read the expanded
script → copy it into your proof → fix sub-goals → collapse back to `step*` if possible.
```

### 4. Task-specific context

- Which file to edit (full path)
- Which sorry's to fill (line numbers)
- Available specs and lemmas
- Proof strategy hints
- What NOT to modify

### 5. Constraints

The file-modification rules depend on the isolation model (see "Agent Working Tree"
section below). Include the appropriate variant in the agent prompt:

**For separate-clone agents (each agent has its own clone):**
```
## Key Rules
- NEVER unfold Aeneas stdlib definitions — search for existing lemmas
- NEVER use `omega` — use `agrind` (preferred), `grind`, or `scalar_tac`
- When stuck or unsure what tactic to use: **always try `agrind` first** (then `grind`). Do NOT use `simp_all` — it is very slow in big contexts and drops hypotheses.
- NEVER spawn sub-agents that work on Lean files (see below)
- Your PRIMARY task is the assigned file(s), but you MAY modify other files
  in your clone if needed (e.g., shared definitions, axiom files, bridge lemmas).
  The supervisor will handle merging across clones.
- ⛔ NEVER run `git checkout`, `git restore`, `git stash`, `git reset`,
  or any command that reverts/discards/overwrites file changes.
- DO NOT COMMIT
```

**For same-clone agents (multiple agents share one working tree):**
```
## Key Rules
- NEVER unfold Aeneas stdlib definitions — search for existing lemmas
- NEVER use `omega` — use `agrind` (preferred), `grind`, or `scalar_tac`
- When stuck or unsure what tactic to use: **always try `agrind` first** (then `grind`). Do NOT use `simp_all` — it is very slow in big contexts and drops hypotheses.
- NEVER spawn sub-agents that work on Lean files (see below)
- ⛔ ONLY modify YOUR assigned file(s) — NEVER edit ANY other .lean file.
  Other agents are working in parallel on other files. If you touch their
  files, you will break their work. If you need something from another file,
  use a local `private axiom` with a TODO comment (see below).
- ⛔ NEVER run `git checkout`, `git restore`, `git stash`, `git reset`,
  or any command that reverts/discards/overwrites file changes. Other agents
  have uncommitted work on disk. Any git revert command DESTROYS their work.
  If your file has unexpected content, read it and make targeted edits — never
  bulk-revert.
- DO NOT COMMIT
```

### 6. File modification restriction

**This section applies only to same-clone (Option B) isolation.** When agents work
in separate clones, they may freely modify any file in their clone — the supervisor
handles merging.

**Same-clone rule: ⛔ Agents must ONLY modify the file(s) they have been explicitly assigned.**
They must NEVER edit other files — not shared definition files (Defs.lean,
MatDefs.lean), not external specs (ExternalSpecs.lean), not other Properties files.

**If an agent needs a stronger spec or axiom from another file**, it must NOT
modify that file. Instead:

1. **Introduce a local version** in its own file — a `private axiom` or a
   `sorry`'d `private theorem` that states what it needs:
   ```lean
   -- TODO: strengthen encrypt_block.spec in ExternalSpecs.lean to provide
   -- functional correctness (currently only gives `True`). Move this local
   -- axiom there once the external spec is updated.
   --
   -- WHY NEEDED: The outer loop proof needs to know that the external function
   -- returns a meaningful result, not just `True`. Without this, the loop
   -- invariant cannot relate the accumulated output to the specification.
   --
   -- WHY VALID: The Rust code calls the corresponding library function, which
   -- implements the standard algorithm. The postcondition simply states that
   -- the output equals the spec's pure function applied to the same inputs.
   private axiom external_fn_spec (key : KeyType) (input : Array U16 8#usize) :
     my_module.external_fn key input ⦃ fun out =>
       out = specExternalFn key input ⦄
   ```

2. **The comment must explain TWO things:**
   - **Why needed** — what does the proof require that the current spec doesn't
     provide? Which specific goal or sub-goal is blocked?
   - **Why valid** — why is the proposed postcondition true? What does the Rust
     code actually do that justifies this spec? The supervisor needs this to
     validate the spec before consolidating it into the shared file.

3. **Report the dependency** in its final response so the supervisor can
   coordinate the fix across files.

**Why:** Multiple agents may run in parallel on different files. If agent A edits
`ExternalSpecs.lean` while agent B also depends on it, B's elaboration breaks.
Only the supervisor coordinates cross-file changes — after all agents complete.

### 7. No sub-agent spawning / file isolation / resource limits

These rules are defined in the `agent-fleet-management` skill file. Key points
for proof agents:

- **⛔ NEVER spawn sub-agents that run Lean processes** (lean-lsp-mcp, lake build)
- **Same-clone only: ⛔ ONLY modify your assigned file(s)** — use local axioms with
  TODO comments for specs from other files (see section 6 above). In separate-clone
  mode, you may modify any file in your clone.
- **⛔ NEVER use git checkout/restore/reset** — see `agent-fleet-management` for why
- Agents may use lightweight `explore` agents for codebase searches

## Agent Working Tree: Same Clone vs. Separate Clones

Before dispatching any fleet of agents, the supervisor must ask the user which
isolation model to use. **Always prefer separate clones when available** — they
eliminate entire classes of conflicts.

### Option A: Separate clones (clone-level isolation) — PREFERRED

Each agent works in its own git clone of the repository. This eliminates all file
conflict risks:
- Each agent has its own working tree — no import-dependency issues
- Agents can freely read any file in their clone without concern
- No `agent_files` tracking needed (one agent per clone = no conflicts)
- Each clone can have its own lean-lsp-mcp / LSP session — no MCP contention

**The supervisor must ask the user where the clones are.** Do NOT search for available
clones on your own — the user may have clones used for other purposes. Example prompt:

> "Should I dispatch agents in the current clone (with file-level isolation), or use
> separate git clones? If separate clones, where are they? (e.g., `../external/ProjectClone1`,
> `../external/ProjectClone2`, etc.)"

**Workflow with separate clones:**

1. **User provides clone paths** (e.g., `../external/ProjectClone1`, `../external/ProjectClone2`, `../external/ProjectClone3`)
2. **Verify all clones are at the same commit** as the main repo (`git -C <clone> rev-parse HEAD`)
3. **Dispatch one agent per clone** (max agents = number of available clones)
4. **Agent works entirely within its clone** — builds, edits, lean-lsp-mcp all use clone paths
5. **Agent must NOT commit**
6. **After all agents complete:** collect diffs from each clone (`git -C <clone> diff`), apply patches to main repo, resolve conflicts, build, verify

**lean-lsp-mcp paths:** Instruct agents to use their clone's paths for all MCP tools
(e.g., `file_path="/path/to/ProjectClone2/src/lean/..."`, not the main repo path).

**Spare clones:** If the user provides more clones than needed for a batch, the extras
serve as spares for follow-up batches or replacements if an agent fails.

### Option B: Same clone (file-level isolation) — FALLBACK

All agents work in the same git working tree. Each agent is assigned specific file(s)
and may ONLY modify those. This requires careful file-ownership tracking (see
`agent-fleet-management` for the `agent_files` SQL table and dispatch checklist).
Import-dependency conflicts remain a risk. Use this only when separate clones are
not available.

## File Isolation and Parallelism (Lean-Specific)

<!-- ⚠️ SYNC RULE: general file ownership, SQL tracking, and "agents cannot cancel"
     rules are in agent-fleet-management and global-rules -->

**This section applies only when using same-clone (Option B) isolation.** With
separate clones, file isolation is automatic and these checks are unnecessary.

See the `agent-fleet-management` skill file for the general rules (file ownership
tracking via SQL `agent_files` table, dispatch checklist, "agents cannot cancel"
constraint). Additional Lean-specific notes:

- **Import-dependency check**: Lean files form an import DAG. If file A imports
  file B (directly or transitively), the agent on A must wait until B's agent
  finishes. Check `import` statements at the top of each file before launching.
- **Examples**:
  - ✅ Agent A on `ModuleA.lean`, Agent B on `ModuleB.lean` (no import relationship)
  - ❌ Agent A on `ModuleA.lean` inner loop, Agent B on `ModuleA.lean` outer loop (same file)
  - ❌ Agent A on `Helpers.lean`, Agent B on `ModuleA.lean` (if Helpers imports ModuleA)

## Task Decomposition and Agent Supervision

When the user asks for a large task (e.g., "prove all sorry's in this file"), do NOT
give the entire task to a single agent in one shot. Instead:

1. **Decompose into small tasks**: The number of sorry's per agent depends on
   difficulty (see the `agent-fleet-management` skill file for the general
   difficulty-based sizing rule). For proof agents specifically:
   - **Easy sorry's** (wrapper unfolds, clear `step*` proofs): 3-5 per agent
   - **Medium sorry's** (loop invariants with known patterns): 1-2 per agent
   - **Hard sorry's** (complex bitwise/modular reasoning, unclear approach): 1 per agent

2. **Give one small task at a time**: Launch an agent with a focused objective. When it
   reports back, analyze the result before deciding what to do next.

3. **Supervise actively**: When an agent completes and reports back:
   - **Step back**: Did the agent make progress? Did it get stuck? Did it go in circles?
   - **Diagnose issues from the output**: Did it use `lake build` instead of the lean-lsp-mcp tools?
     Did it hit heartbeat explosions? Did it try an approach that won't work?
   - **Assess the approach**: Is the proof strategy sound? Should the next agent try
     differently?
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
   instructions, or pivot to a different approach.

6. **Reinforce lean-lsp-mcp usage in every agent prompt**: Agents tend to fall back to
   `lake build` loops even when told not to. **Instruct agents to invoke the
   `lean-lsp-mcp` skill as their first action** — this is more reliable than copying
   instructions into the prompt, since agents have access to skill files and MCP tools.
   Additionally, every agent prompt MUST include the `⛔ HARD REQUIREMENT` block
   (see "Example: Full Agent Prompt" below) as the FIRST section. Key elements:
   - "Your FIRST action must be using lean-lsp-mcp tools (lean_goal, etc.)"
   - "If you use lake build for iterative proof development, your work will be REJECTED"
   
   **Why agents ignore the rule**: They see `lake build` in training data and default
   to it. The combination of (a) skill invocation and (b) an explicit rejection
   consequence in the prompt is the most reliable fix.

## Two-Phase Workflow: Statements First, Then Proofs

**Never let agents write proofs before the theorem statements are validated.**
Agents tend to prove trivially weak postconditions (e.g., just `res.length = n`)
when the spec should express full functional correctness (e.g., relating the output
to a pure specification function). Proving a wrong/weak theorem is wasted work.

**⚠️ Always write the final full-correctness postcondition from the start.** Do NOT
write a weaker version (e.g., only `wfArray`/`wfSlice`/length preservation) with the
intent of strengthening it later. Upgrading postconditions is extremely expensive —
it changes the theorem interface, breaking every caller that uses it via `step`, and
often cascades across many theorems and files. Instead: write the final statement
(full spec equality + structural conjuncts), use `sorry` for the proof, then close
sorrys one by one. This enables modular, parallel proof work — each conjunct can be
tackled independently without touching the statement or its callers.

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
   - The main proof structure (unfold + step, case split, loop invariant, etc.)
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
   @[local step]
   theorem setup_phase.spec ... :
     setup_phase params buf ⦃ res => ... ⦄ := by sorry

   -- Main theorem (uses auxiliary specs via step)
   @[step]
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

## Skills — Invoke FIRST
As your FIRST action, invoke these skills (use the `skill` tool):
1. `aeneas-lean-core` — postcondition quality rules, spec patterns
2. `aeneas-crypto-verification` — multi-level verification pipeline
3. `lean-lsp-mcp` — mandatory tooling for type-checking statements

Read:
- The auto-generated code in Funs.lean (line N)
- The pure specification `Spec.Foo.Bar` in FooSpec.lean (line M)

The postcondition must express FULL FUNCTIONAL CORRECTNESS as a direct equality:
- repr(output) = Spec.algorithmName(repr(input1), repr(input2), ...)
- Use representation/conversion functions on BOTH inputs and outputs
- NOT just length preservation (that's trivially weak)
- NOT just `True` (useless)
- NOT relational specs (simulation relations, abstract state) — use direct equalities
- Structural properties (wfArray, lengths) are supplementary conjuncts, not the main spec
- Apply the VACUITY TEST: would this postcondition hold if the implementation returned
  arbitrary/zero data? If yes, it's too weak.

ALWAYS sketch the proof strategy as a comment above the sorry. Include:
- Main proof structure (unfold + step, case split, loop invariant, etc.)
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

<!-- ⚠️ SYNC RULE: review loop mechanics are defined in global-rules "Mandatory Review Loop" -->

Before launching proof agents, **review every theorem statement**.

**The review loop applies to ALL agent outputs — not just proofs.** Plans, proof
plans, specification mappings, function mapping tables, and any other structured
output produced by agents must also go through the do → review → fix → converge
loop. A plan with incorrect line numbers, stale function references, or logically
inconsistent dependency graphs wastes significant agent time downstream.

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
to the spec function, not just length") and the statement agent revises. This repeats
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
  the main proof to use via `step`? If the agent said "no decomposition needed",
  is that justified? A function with 50+ monadic steps that wasn't decomposed should
  be flagged.
- **Decomposition adequacy (proof-level)**: Read the Aeneas-generated function body
  being verified. Identify the algorithmic phases (see `aeneas-crypto-verification`
  "Function Decomposition"). Check that each complex phase (bitwise ops, wrapping
  arithmetic, signed/unsigned casts) has its own fold helper with a focused spec.
  Check that existing mathematical lemmas (`MontReduction.lean`, `ModArith.lean`)
  are reused where applicable. A proof that closes >15 goals after `step*` without
  fold helpers should be flagged.
<!-- ⚠️ SYNC RULE: source of truth is aeneas-lean-core "Every fold helper must have a step spec" -->
- **Does every fold helper have a step spec?** A fold helper without a corresponding
  `@[local step]` spec theorem is useless scaffolding — the parent proof can fold the
  code but can't `step` through the helper. Every fold helper must have a spec with a
  full functional-correctness postcondition (even if sorry'd). Flag any fold helper
  that lacks a spec.
<!-- ⚠️ SYNC RULE: source of truth is aeneas-lean-core "Every function spec requires loop specs too" -->
- **Are loop specs present for all loops?** When a function contains loops (translated
  as `_loop`, `_loop0`, `_loop1` auxiliary functions), the proof requires `@[step]`
  specs for each loop. Check that every loop has a spec with a full postcondition
  (even if sorry'd). A function spec without its loop specs is unprovable. Flag any
  function spec whose loops lack specs.
- **Are axioms and external specs sound?** For any `axiom`, `private axiom`, or
  sorry'd `private theorem` introduced by the agent (including local assumptions
  about external functions), verify all of the following:
  - **Non-vacuous postcondition:** The postcondition says something meaningful.
    A postcondition of `True` is acceptable **only** when the axiom's sole purpose
    is to assert that the external function succeeds (doesn't crash/diverge) — e.g.,
    `cpu_features_present feature ⦃ _ => True ⦄` asserts it returns *some* boolean.
    But if the proof actually needs properties of the return value and the axiom
    only provides `True`, the axiom is too weak and must be strengthened.
  - **Minimal postcondition:** The postcondition doesn't assert more than what the
    external function actually guarantees. An overly strong axiom is unsound — it
    introduces an unjustified assumption that may be false for some inputs, even if
    it doesn't outright derive `False`. For example, an axiom
    `hash input ⦃ out => out = spec_hash input ⦄` is fine if the external function
    genuinely implements `spec_hash`. But adding `∧ out.length < 100` when the
    external function doesn't guarantee that is an unjustified extra assumption.
  - **Sufficient preconditions:** The preconditions are strong enough to make the
    postcondition actually true. If the axiom states `f x ⦃ y => y < 100 ⦄` but
    this only holds when `x > 0`, the missing precondition makes the axiom unsound.
  - **No hidden contradictions:** Check whether the axiom, combined with other axioms
    in the project, could derive `False`. In particular, check for overlapping axioms
    about the same function with incompatible postconditions, or axioms whose
    preconditions are unsatisfiable (making them vacuously true but misleading).
  - **Justification comment present:** Every axiom must have a comment explaining
    WHY it is sound — what property of the external system/function justifies it.
    An axiom without justification should be flagged.

**Common weak-postcondition patterns to reject:**
- `res.length = n` — length only, says nothing about values
- `True` or `fun _ => True` — vacuously true
- Missing existential for length + functional property
- Only one half of a bidirectional property (e.g., only correctness, not bounds)

<!-- ⚠️ SYNC RULE: source of truth is agent-fleet-management "Review depth and priority" -->
**⚠️ MANDATORY: Axiom files must be reviewed immediately after creation.**

Every new axiom file or trust boundary (hash bridge, SIMD model, external function
specs, etc.) MUST get a **dedicated code-review agent immediately after creation**,
before any other work proceeds. This is not optional — it is the highest-priority
review task. The supervisor must never mark an axiom-creating task as "done" until
a separate reviewer has verified the axioms.

**Why:** Axioms are more dangerous than sorry's. A sorry is an honest gap — the proof
system tracks it and everyone knows it's incomplete. A wrong axiom is a silent lie:
it makes all downstream proofs vacuous while appearing to succeed. An axiom file with
incorrect postconditions (e.g., missing spec connections, vacuous simulation relations)
can waste weeks of proof work building on a foundation that proves nothing.

**Axiom review checklist** (in addition to the general review checklist above):
- **Does every axiom connect output to the specification?** An axiom that only asserts
  structural properties (e.g., `output.length = n`, `offset advances`) without
  connecting the output VALUES to the spec function is critically incomplete. The
  output must be related to the pure spec (e.g., `output = Spec.SHAKE128(input)[offset..offset+len]`).
- **Are simulation/abstraction relations non-vacuous?** A `Simulates` relation defined
  as `True` provides zero guarantees — any implementation state "simulates" any abstract
  state. Either make the relation `opaque` (axiom without body) or give it real content.
- **Could an incorrect implementation satisfy all axioms?** Mentally substitute a
  trivially wrong implementation (e.g., one that always returns zeros) and check
  whether it would satisfy every axiom. If yes, the axioms are too weak.
- **Are axiom chains consistent?** When multiple axioms model a stateful protocol
  (init → absorb → squeeze → result), verify the chain is consistent: state flows
  correctly, accumulated data is preserved, offsets advance properly.
<!-- ⚠️ SYNC RULE: source of truth is aeneas-crypto-verification "Axiomatizing SIMD/Intrinsic Operations" -->
- **Do SIMD/intrinsic axioms cite reference documentation?** Every SIMD axiom must
  include a docstring naming the intrinsic, linking to the vendor reference (Intel
  Intrinsics Guide, ARM NEON docs, etc.), and quoting or summarizing the operation.
  An axiom without a reference link should be flagged.
<!-- ⚠️ SYNC RULE: source of truth is aeneas-lean-core "Axiom organization" -->
- **Are axioms grouped in `Axioms.lean` or `Axioms/`?** All intentional axioms must
  be in a dedicated file or directory for auditability. Axioms scattered across proof
  files should be flagged.
<!-- ⚠️ SYNC RULE: source of truth is aeneas-lean-core "Axiom organization" -->
- **Is a problematic axiom being left unfixed to avoid refactoring?** If a reviewer
  identifies an axiom that is incorrect or too weak, it must be fixed regardless of
  how many proofs depend on it. "It would break too many proofs" is never acceptable.

### Phase 3: Proof Agents with Review Loop (slower, parallelizable)

Only after statements are validated, launch agents to fill the `sorry` proofs.
Each proof agent works on one file (for isolation) and targets specific sorry's.

**🚨 The purpose of the review/fix loop is to CLOSE sorry's — not just to validate
code quality.** Reviews that only check style, banned tactics, and axiom soundness
but ignore remaining sorry's are incomplete. Every review cycle must: (1) count
remaining sorry's, (2) assess which are closable, (3) dispatch fix agents to close
them. The loop continues until all sorry's are either closed or genuinely blocked
by missing infrastructure. See the review checklist below for details.

**Detecting unprovable theorems and Rust bugs:**

If a proof agent spends a long time stuck on a goal that won't close, it should
consider the possibility that the theorem is **unprovable** — either because:
- The theorem statement is wrong (preconditions too weak, postcondition too strong)
- There is a **bug in the Rust source code** (the implementation doesn't match the spec)

The agent should actively look for counterexamples: try specific parameter values,
trace the Rust logic by hand, check if a particular input would violate the
postcondition. If a bug is found or suspected, the agent must **stop proving
immediately and report the finding**.

**Include in every proof agent prompt:** "If you spend a long time stuck on a goal
that won't close, consider whether the theorem is actually true. Look for
counterexamples or bugs in the Rust code. Report findings immediately."

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
   "The axiom `external_fn.spec` has postcondition `True`, but the outer loop proof
   needs it to return the correct output. Suggested fix:
   ```lean
   axiom my_module.external_fn.spec (key : KeyType) (input : Array U16 8#usize) :
     my_module.external_fn key input ⦃ fun out =>
       out = specExternalFn key input ⦄
   ```
   where `specExternalFn` is a pure specification of the external function."

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

**Every proof review is a full review from scratch.** The reviewer must re-read the
proof files and re-check every item in the checklist — not just verify that specific
issues from a prior round were fixed. Do NOT tell the reviewer what the prior round
found; this biases toward rubber-stamping. The prompt should be identical to a
first-time review.

**Before handing off to the review agent, the proof agent MUST verify that the entire
file builds without errors.** Run `lake build <module>` (e.g., `lake build Properties.CT`)
and confirm 0 errors. Warnings about `sorry` are acceptable if some sorry's remain, but
there must be NO type errors, NO elaboration failures, NO tactic failures. If the file
doesn't build cleanly, the proof agent must fix the errors before reporting.

```
┌──────────────────────────────────────┐
│  Proof agent works on sorry's        │
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

**🚨 MOST IMPORTANT CHECK: Are there remaining sorry's?**

The #1 job of the review/fix loop is to **close sorry's**. A review that validates code
quality (no banned tactics, good style, etc.) but ignores remaining sorry's has failed
its primary purpose. The review MUST:

1. **Count remaining sorry's** — run `grep -n 'sorry' FILE` and list every sorry line
2. **For each sorry, assess**: Is it closable with current infrastructure? Does it need
   a missing lemma, a local axiom, or a spec from another file?
3. **Flag every closable sorry as a mandatory fix** — the fix agent MUST attempt to
   close it, not just document why it's hard
4. **For genuinely blocked sorry's**: identify the specific blocker (missing stdlib spec,
   missing hash bridge lemma, etc.) and report it as a concrete action item

**Convergence = zero sorry's, or every remaining sorry is blocked by a specific,
documented infrastructure gap** (missing Aeneas stdlib spec, missing external function
model, etc.). "Well-documented sorry" is NOT convergence — if the sorry can be closed
with existing infrastructure, it MUST be closed. A review that accepts closable sorry's
as "converged" must be rejected.

<!-- ⚠️ SYNC RULE: source of truth is aeneas-lean-core "Proof Style and Maintainability"
     and aeneas-tactics-quickref "Proof Style Rules". See skill-file-authoring for sync rules. -->

**⚠️ BEFORE DIVING INTO SPECIFIC CHECKS:** Re-read the spec theorem conventions in
the `aeneas-lean-core` skill file — tuple decomposition in postconditions, result type
annotation, naming, docstrings, indentation rules, `⦃ ⦄` notation conventions. Check
each convention mechanically against the code under review. Mechanical rule violations
are the easiest to miss when reviewing "by feel" — they require deliberate
checklist-style checking.

**⚠️ READ THE FILES, DON'T JUST GREP.** The reviewer must **read the modified proof
files** — not just run grep patterns. Grep catches mechanical violations (banned
tactics, maxRecDepth) but misses structural problems (multi-line inline `(by ...)`
blocks, proof organization, unnecessary complexity). Reading a typical proof file
costs ~10-15K tokens — this is affordable and catches far more issues.

### Build and warnings

- **Does the file build without errors?** Run `lake build <module>` and verify 0
  errors. `sorry` warnings are acceptable; type errors, tactic failures, and
  elaboration errors are NOT.
- **Are all warnings addressed?** (Rule: "Address all warnings")
  The ONLY acceptable warning is `"declaration uses 'sorry'"`.
  **This applies to sorry'd proofs too** — dead tactics, unused simp args, and unused
  variables around a sorry must be fixed.
  ```bash
  # After building, check warning output for:
  # "This simp argument is unused" — remove from simp only [...]
  # "Too many ids provided" — reduce binders in step as ⟨...⟩
  # "unused variable" — remove or prefix with _
  # "'...' tactic does nothing" / "is never executed" — remove dead tactic
  # "Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice" — replace <;> with ;
  ```

### Banned constructs (mechanical grep)

Run these grep checks on every file under review. **Any match is a mandatory fix.**

```bash
# Banned tactics (Rule: "BANNED TACTICS"; Pitfalls #1-#5 preference order)
grep -n '\bomega\b' FILE          # → replace with agrind > grind > scalar_tac
grep -n '\blinarith\b' FILE       # → replace with agrind > grind > scalar_tac
grep -n '\bnlinarith\b' FILE      # → replace with agrind > grind > scalar_tac +nonLin

# Never increase maxRecDepth (item 11: "NEVER increase maxRecDepth")
grep -n 'maxRecDepth' FILE        # → diagnose simp loop, never raise limit

# maxHeartbeats too high (item 13: "Keep maxHeartbeats reasonable")
grep -n 'maxHeartbeats' FILE      # → verify value < 8_000_000; if higher, proof needs restructuring

# set_option ... in inside proof script (item 13) — breaks incrementality
grep -n 'set_option.*in$' FILE    # → check if inside a proof (by block); OK before theorem declaration

# ⛔ Converting sorry → axiom (NEVER allowed)
grep -n '^axiom' FILE             # → if agent added new axioms that were sorry before, REJECT
# Agents must NEVER convert a sorry into an axiom. The whole point is to PROVE the theorem.
# If the proof is too hard, leave it as sorry and report what was tried.

# ⛔ Axiomatizing transparent functions (NEVER allowed — with ONE exception)
# Check every `axiom` in the file. If the function being axiomatized is TRANSPARENT
# (i.e., its body is available in the generated Lean code), the axiom MUST be rejected.
# Only external/opaque functions (FFI, stdlib without source, FunsExternal.lean) may be axioms.
#
# THE ONLY EXCEPTION: functions that use features strictly outside Aeneas' model of Rust.
# Specifically: raw pointer operations (core::ptr::read_volatile, core::ptr::write_volatile,
# as_ptr, add, etc.) cannot be reasoned about in the Aeneas framework because Aeneas does
# not model raw pointers. For such functions, axiomatize the raw pointer ops (e.g., model
# `read_volatile(a.as_ptr().add(i))` as `a[i]`) and then prove the rest of the function.
#
# Common violation: agent axiomatizes a function with "too many monadic steps" (~100-200 steps).
# Fix: fold decomposition to split into phases, then step through each phase.
# "Too many steps" is NEVER a valid reason to axiomatize — it's a reason to decompose.

# Unfold of Aeneas stdlib definitions (item 10: "NEVER unfold Aeneas stdlib")
grep -n 'unfold.*Aeneas\|unfold.*Std\.\|unfold.*core\.' FILE
# → search for existing lemma instead of unfolding

# step* <;> tactic (Rule: "Avoid step* <;> tactic")
grep -n 'step\*.*<;>' FILE       # → use focused goal blocks (· ) instead

# all_goals (Rule: "NEVER use all_goals — banned everywhere")
grep -n 'all_goals' FILE          # → ALWAYS replace with focused · blocks. No exceptions.

# Inline (by ...) in exact/apply/refine (Rule: "Extract inline by blocks"; item 15: "proof reactive")
grep -n 'exact.*(by ' FILE        # → check: 3+ blocks or any multi-line block → extract
grep -n 'apply.*(by ' FILE        # (same check)
grep -n 'refine.*(by ' FILE       # (same check)
# ⚠️ These greps only catch single-line cases. The most common violation is multi-line:
#   exact lemma arg1
#       (by tac1) (by tac2)    ← grep misses this
# The reviewer MUST also read multi-line exact/apply/refine statements manually.
# "Expensive" = multi-line, tactic sequences (tac1; tac2), first|..., or slow tactics.
# Note: all_goals is banned outright (see above), so it's never acceptable here either.
# A single cheap (by scalar_tac) or (by grind) is acceptable only with 1-2 blocks total.
# ⚠️ ALSO CHECK THEOREM TYPE SIGNATURES for embedded (by ...) blocks — especially
# getElem bounds proofs like (by cases p <;> simp_all [...] <;> agrind). These cause
# severe kernel slowness on every application of the theorem (measured 6× slowdown).
# Fix: use get_elem_tactic override with agrind (preferred), or (by agrind) / (by grind)
# / (by scalar_tac) for individual bounds. NEVER cases p <;> simp_all in a type.
```

### Checks requiring manual inspection

These cannot be reliably grepped — the reviewer must read the proof:

- **`(by ...)` in theorem TYPE SIGNATURES?** (Rule: "Never embed (by ...) in type signatures")
  Check theorem parameters and postconditions for embedded `(by ...)` blocks — especially
  for `getElem` array bounds. **Accepted tactics in type signatures** (in preference order):
  `agrind`, `grind`, `scalar_tac`. **BANNED:** `cases p <;> simp_all [...] <;> tactic`
  (produces huge proof terms, causes kernel slowness — measured 6× slowdown).
  Best approach: the file should have a `get_elem_tactic` override with `agrind` so
  that `a[i]` auto-discharges bounds without any `(by ...)` at all. If a standalone
  helper lemma is used, that's also acceptable.

- **Auto-param tactics in recursive theorems?** (item 16: "auto-param tactic loops")
  In recursive `spec_gen` theorems, all parameters must be explicit — no `:= by ...`
  defaults. Look for `:= by` in theorem parameter lists (not in proof bodies).

<!-- ⚠️ SYNC RULE: source of truth is aeneas-lean-core "Postcondition quality" -->
- **Postcondition quality?** (Rule: "Postcondition quality")
  - Does the postcondition link to a spec function (not just structural properties
    like length preservation)?
  - Are well-formedness invariants threaded through (precondition → postcondition)?
  - Are there existential quantifiers over non-proposition variables? If so, flag them
    — the postcondition should use explicit conversion functions, not existential
    witnesses.
  - Does the postcondition use conversion *functions* (e.g., `toPoly`) rather than
    *relations* (e.g., `isPoly`)?
  - **For top-level/public API functions:** Is the postcondition a single-call equality
    with the spec function (`output_converted = Spec.F(input_converted)`)? If the
    postcondition existentially quantifies over internal algorithm variables (e.g.,
    intermediate matrices, hash outputs, sampled values, temporary buffers) instead of
    stating a direct result, it is a **decomposed postcondition** and must be rejected.
    The decomposition belongs in the proof, not the theorem statement. A caller of the
    function should be able to use the postcondition without knowing how the algorithm
    works internally.

<!-- ⚠️ SYNC RULE: source of truth is aeneas-lean-core "Interface functions must map to the spec" -->
- **Do interface functions map to spec functions?** (Rule: "Interface functions must
  map to the spec") Public Rust API functions and FFI/external functions should
  straightforwardly map to well-identified spec functions. Their postconditions should
  make this mapping explicit.

- **Are fold theorems non-vacuous?** (Rule: "Fold theorem vacuity check")
  For each fold theorem (typically named `fold_*` or `*_fold`), check that the LHS
  and RHS are **different**. The LHS must be the original inline monadic steps from
  the generated code; the RHS must use the fold helper. If both sides are identical
  (provable by `rfl`), the theorem is vacuous and must be either fixed (fill in the
  real LHS) or removed and replaced with a TODO comment.

- **Do fold theorems use curried continuations?** (Rule: "Fold theorem continuation
  must use curried arguments, not tuples")
  When the fold helper returns a tuple, the continuation `f` must take separate
  curried arguments (`f : A → B → C → Result α` with `f a b c`), NOT a single
  tuple (`f : A × B × C → Result α` with `f (a, b, c)`). The tuple form silently
  breaks `simp` matching — the theorem type-checks and proves but does nothing
  when applied inside a parent function.

- **Have fold theorems been tested?** (Rule: "Always test fold theorems")
  Every fold theorem must be tested by writing a small `example` that unfolds the
  parent function and applies `simp only [fold_*]`, verifying that it actually
  makes progress. A fold theorem that doesn't rewrite is worse than no fold theorem.

### NEVER trust comments

When reviewing code, proofs, specs, and axioms, reviewers must **never trust comments
at face value**. Always independently assess whether each comment is accurate:
- Does a comment claim a function preserves an invariant? Verify it in the postcondition.
- Does a comment say "this is sound because..."? Check the reasoning independently.
- Does a comment reference a spec section or line number? Verify the reference is current.
Comments can be stale, misleading, or outright wrong — they are documentation, not proof.

### Structural and style checks (manual inspection)

These require reading the proof, not just grepping:

- **Is the proof idiomatic?** (Rule: all of "Proof Style and Maintainability")
  Uses standard Aeneas patterns (step, WP.spec_mono, split_ifs, etc.) rather than
  ad-hoc workarounds? Follows patterns in the `proof-patterns` skill file?

- **No big `simp only [...]` in implementation proofs?** (Rule: "Avoid large simp only")
  Big lemma lists in `simp only` make proofs fragile when the model changes.
  OK in spec lemmas. Prefer `simp [*]`, `agrind`, or targeted rewrites.

- **Complex sub-proofs extracted as auxiliary lemmas?** (Rule: "Extract auxiliary lemmas")
  No 15-line arithmetic blocks inlined in the middle of `step*`.

- **Recurring index bounds extracted as standalone helpers?** (item 22: "recurring index bounds")
  Bounds like `k * N + q < NBAR * N` should not be proved inline repeatedly.

- **No early case splits on parameters?** (Rule: "Avoid early case splits")
  `cases p` at proof top duplicates everything. Case splits should be local or
  handled via `attribute [local agrind]`.

- **`agrind` preferred over `grind`?** (item 5: "`grind` explodes")
  `grind` should only appear when `agrind` fails. In loop proofs (`spec_gen`),
  prefer `agrind` over `scalar_tac` throughout (item 21: "prefer `agrind` in spec_gen").
  **`simp_all` should NOT be used as a general-purpose tactic** — it is very slow
  in big contexts and drops hypotheses. Flag any `simp_all` that could be `agrind`.

- **Shifts simplified?** (Rule: "Simplify shifts early")
  `>>>` should be rewritten as `/ 2^n`, `<<<` as `* 2^n`.

- **Spaces around binary operators in comments?** (Rule: "Spaces around binary operators")
  `j < N`, not `j<N`. Missing spaces cause VS Code highlighting bugs.

- **Helper lemmas properly named and documented if non-obvious?**

- **Repeated `simp [...]; solver` in cdot sub-goals?** If the same constants appear
  in `simp` calls before a solver (`scalar_tac`, `agrind`, `grind`, `bv_tac`) in 3+
  sub-goals after `step`/`step*`, they should be promoted to solver attributes
  (`@[scalar_tac_simps]`, `@[agrind =]`, `@[grind =]`, `@[bvify]`) so `step`/`step*`
  discharges the sub-goals automatically and they disappear. Also flag
  `have hFoo : CONST.val = N := by simp` — the underlying definition likely needs
  attributes. (Rule: "Register Rust global/const definitions with solver attributes")

- **Repeated inline `(by ...)` proof blocks?** (item 22: "recurring index bounds")
  If the same `(by tactic_sequence)` appears 3+ times — in theorem signatures
  (`getElem` bounds), `have` statements, or `exact`/`apply` arguments — it should
  be extracted as a standalone lemma with solver attributes (`@[agrind =]`). With
  the lemma registered, a `get_elem_tactic` override (`agrind`) auto-discharges
  the bound — no `(by ...)` needed at all. Flag any `(by cases p <;> simp_all [...]
  <;> agrind)` in a type signature — this is always wrong (use `get_elem_tactic`
  override or `(by agrind)` instead).

- **Is the proof clean and not verbose?** No copy-paste bloat, no redundant `have`
  that could be inlined. Each tactic call should earn its place.

### Performance checks

- **Is the proof fast enough?** (item 14: "Keep proof wall-clock time < 60s")
  Use the `measure` tactic wrapper (see the `aeneas-tactics-quickref` skill file,
  "Profiling proof time") to check that the proof completes in **< 60 seconds
  wall-clock**. **Do NOT use `trace.profiler` for this** — it only measures tactic
  execution and misses kernel type-checking time, which can dominate. If slower than
  60s, send back for optimization.

- **Is the proof reactive for interactive development?** (item 15: "Extract inline by blocks")
  Adding a tactic at the end should take < 0.5s. If not, look for inline `(by ...)`
  blocks (see grep above) and suggest extracting them into `have` statements.

- **Are `maxHeartbeats` values reasonable?** (item 13: "Keep maxHeartbeats reasonable")
  If any `set_option maxHeartbeats` exceeds 8M, the proof needs restructuring.

- **Are sorry'd proofs fast?** (item 24: "Sorry'd proofs must be fast")
  A sorry'd proof should use plain `sorry`, not `step* <;> (first | ... | sorry)` or
  `cases p <;> step* <;> sorry`. Expensive sorry'd proofs waste build time for zero
  verification value.

**Skill file freshness:**

- **Every agent invocation** (statement agents, proof agents, review agents) **must
  include the "invoke skills first" instruction** in its prompt. Since agents have
  access to skills via the `skill` tool, the preferred approach is to instruct them
  to invoke skills directly (e.g., `aeneas-lean-core`, `lean-lsp-mcp`). This ensures
  agents always work from the latest version of all skill files — including any
  mid-run updates the supervisor made (with user approval).
- As a fallback, the prompt may also list explicit file paths to skill files
  (e.g., `documentation/skills/aeneas-lean-core/SKILL.md`). This is less preferred
  because skill invocation is more reliable and doesn't require the supervisor to
  know exact file paths.
- If the reviewer finds **many guideline violations** (e.g., 3+ issues that the
  skill files clearly address), the prompt for the follow-up fix agent should include:
  **"Re-read the skill files before fixing these issues."**
  The follow-up agent is a fresh context and may have different knowledge — explicitly
  pointing it to the skill files ensures it doesn't repeat the same violations.

**Progress reporting and task granularity:** See the `agent-fleet-management` skill file
for the general rules. Proof-specific notes:

- **Assess sorry difficulty before dispatching** — read the proof sketch (if present),
  check the function's monadic step count, check if similar proofs exist, and consider
  whether needed specs/lemmas already exist.
- **Give each agent sorry's in a specific file**: "Fill the sorry at line 130
  in MatrixMul.lean" or "Fill sorry's at lines 130 and 168 in MatrixMul.lean".
- **Parallelize across files**: Launch multiple agents simultaneously, each targeting
  a different file. Startup costs overlap, so wall-clock time is the slowest agent.
- **Small related files can be batched**: If two small files (1 sorry each) are
  independent, one agent can handle both sequentially.

For example, with 13 sorry's across 6 files, assessed as 3 hard + 5 medium + 5 easy:
- ✅ Agent A: 1 hard sorry (MatrixMul.lean line 946 — complex loop invariant)
- ✅ Agent B: 2 medium sorry's (TransposeMul.lean lines 837, 875)
- ✅ Agent C: 1 hard sorry (EncodeDecode.lean line 278 — bit-packing)
- ✅ Agent D: 5 easy sorry's (TopLevel1 + TopLevel2 + TopLevel3 — wrapper unfolds)
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

## Master Synthesis

See the `agent-fleet-management` skill file for the general cross-agent synthesis
rules. Proof-specific patterns to watch for:

- Multiple agents stuck on the same kind of sub-goal (e.g., bitwise reasoning)
  → may need a shared lemma proved centrally
- Agents discovering missing specs in shared axiom/external files → consolidate after fleet
- Common bridge definitions needed across proofs → add to shared `Defs.lean`/`Basic.lean`

**The master does NOT act on these findings autonomously** — it reports to the user
and waits for approval.

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
- **Run the cleaning step** (see below) before redispatching
- If partial, launch a follow-up agent with refined instructions

### Cleaning Step (between review and redispatch)

**Before redispatching proof agents**, the supervisor (or a dedicated general-purpose
agent) must resolve infrastructure gaps that blocked the previous round. This is
critical — redispatching agents into the same blockers wastes time.

The cleaning step handles cross-file and infrastructure work that proof agents can't
do (because they're file-isolated):

1. **Revert illegitimate axioms** — Any `axiom` for a transparent function must be
   converted back to `theorem ... := by sorry`. Transparent functions (those whose body
   is in the generated Lean code) must NEVER be axiomatized, regardless of size.
   "Too many monadic steps" → fold decomposition, not axiomatization.
   **Exception:** functions containing features strictly outside Aeneas' Rust model
   (raw pointers: `read_volatile`, `write_volatile`, `as_ptr`) may axiomatize ONLY the raw
   pointer operations, then prove the rest of the function around the axiom.

2. **Prove missing stdlib specs** — If agents reported missing `@[step]` specs for
   Aeneas stdlib functions (e.g., `Array.index_mut` with `Range`, `core.result.Result.unwrap`),
   prove them in the appropriate stdlib file or a shared project file, and add `@[step]`.

3. **Prove missing bridge lemmas** — Cross-cutting lemmas needed by multiple files
   (e.g., `sliceToSpecBytes ↔ arrayToSpecBytes`, hash output → spec function bridges)
   should be proved in shared files (e.g., `Basic.lean`, `HashBridge.lean`).

4. **Add missing imports** — If file A needs a spec from file B but doesn't import it,
   add the import (after checking for circular dependencies).

5. **Deduplicate across files** — Collect duplicate theorems, axioms, and helpers that
   appear in multiple files (e.g., identical `stdlib_fn.spec` stubs in two files,
   `default_value_spec` in multiple places, `Array_index_mut_Range` stubs).
   Move each to a single shared file (e.g., `Basic.lean`, a new `StdlibSpecs.lean`, or
   the appropriate Axioms file) with `@[step]`, then remove all local duplicates and
   add imports. This prevents agents from re-introducing private axioms that already
   exist elsewhere.

6. **Strengthen axiom postconditions** — If external function axioms are too weak
   (e.g., missing `wfSlice`/`wfArray` in postconditions), strengthen them in the
   axiom file.

6. **Create fold helpers for large functions** — If a function has 100+ monadic steps
   and the previous agent couldn't handle it, create fold helpers (identify natural
   phases, define helper functions, prove fold theorems) before redispatching.

7. **Build & verify** — Run `lake build` and ensure 0 errors. The next round of agents
   must start from a clean baseline.

**The cleaning step is NOT optional.** Skipping it and redispatching agents into the
same blockers is the #1 cause of wasted agent time. If no infrastructure gaps were
found, the cleaning step is trivially empty — but it must always be explicitly checked.

**⛔ The cleaning step MUST run after ALL agents in the wave complete — never
while agents are still running.** Infrastructure changes (import fixes, shared
file edits, deduplication) touch files that running agents depend on. Applying them
mid-wave corrupts running agents' builds and can trigger `git checkout` cascades
where agents try to "fix" unexpected file content by reverting to HEAD.

<!-- ⚠️ SYNC RULE: expanded infrastructure-between-waves rule is in
     agent-fleet-management "Infrastructure tasks MUST run between waves" -->

## Common Agent Failure Modes

| Failure | Cause | Fix |
|---------|-------|-----|
| Agent uses `lake build` loops | Didn't read lean-lsp-mcp skill | Stronger prompt, mandate lean-lsp-mcp tools |
| `step*` times out | Too many monadic calls | Use `step*?` workflow |
| Unfolds stdlib definitions | Didn't read core skill | Add "don't unfold" rule to prompt |
| Uses `omega` | `omega` can't reason about scalars, `U32.max`, list lengths, etc. | NEVER use `omega` — use `agrind` > `grind` > `scalar_tac` |
| Uses `nlinarith` | Same issues as `omega` — can't reason about scalars | NEVER use `nlinarith` — use `agrind` > `grind` > `scalar_tac +nonLin` / `simp_scalar` |
| Uses `linarith` | Same issues as `omega` — can't reason about scalars | NEVER use `linarith` — use `agrind` > `grind` > `scalar_tac` |
| Uses `simp_all` as default | `simp_all` is very slow in big contexts and drops hypotheses | Use `agrind` as default tactic — it is faster and safer. If simplification is needed, use `simp [*]` or `simp [h1, h2]` |
| Edits wrong file/section | Ambiguous instructions | Be very specific about what to change |
| Increases `maxRecDepth` | Trying to work around recursion depth errors | NEVER increase `maxRecDepth` — diagnose the root cause (bad proof structure or simp loop). Report to user if it's a tactic bug |
| Tactic silently fails | Tactic doesn't do what it should (e.g., `step` can't find a lemma that exists) | Report to user — may be a tactic bug worth fixing upstream |
| Spawns Lean sub-agents | Agent tries to parallelize by spawning sub-agents | NEVER spawn sub-agents that work on Lean files — resources are tight, and it causes file conflicts |
| Edits other files | Agent modifies shared defs or specs it wasn't assigned | NEVER edit files other than assigned ones — introduce local axioms with TODO comments instead |
| Agent crashes mid-edit | API loss, timeout, resource limit | Check for referenced-but-undefined identifiers; create missing defs in shared files |
| `scalar_tac` loops in spec_gen | `maxRecDepth` in loop invariant proof | Mass-replace ALL `scalar_tac` → `agrind` in the proof body |
| Review ignores remaining sorry's | Review only checks quality, not completeness | **Reviews MUST flag remaining sorry's and dispatch fix agents** — "well-documented sorry" is not convergence |
| Axiomatizes transparent function | Function has "too many steps" (~100-200 monadic lets) | **NEVER axiomatize transparent functions** — use fold decomposition to split into phases, then step through each. Exception: raw pointer ops (read_volatile, write_volatile) may be axiomatized as array indexing |
| Skips cleaning step | Redispatches into same blockers | **Always run cleaning step** between review and redispatch — resolve infrastructure gaps first |
| Reverts files via git | Runs `git checkout`/`git restore`, wiping other agents' uncommitted work | **NEVER use git checkout/restore/reset** — make targeted edits only. Include the git ban in every agent prompt |
| Infrastructure agent conflicts with proof agents | Supervisor dispatches cross-file agent (e.g., diamond fix, import changes) while proof agents are running on those files | **Infrastructure tasks MUST run between waves** — never while proof agents are running on affected files |
| Supervisor skips `agent_files` tracking | Doesn't INSERT/query file ownership before dispatch, causing same-file conflicts | **Always maintain `agent_files` table** — INSERT before dispatch, SELECT before every new agent, DELETE on completion |

## Example: Full Agent Prompt (separate-clone mode)

```
Fix the inner loop sorry in `/path/to/clone/MyModule.lean`.

## Step 1: Invoke Skills
As your FIRST action, invoke these skills (use the `skill` tool):
1. `aeneas-lean-core` — translation model, spec patterns, pitfalls
2. `aeneas-tactics-quickref` — which tactic for which goal
3. `lean-lsp-mcp` — mandatory tooling for proof checking

## Step 2: ⛔ HARD REQUIREMENT — lean-lsp-mcp tools ONLY
After reading the skills, do ALL proof checking via lean-lsp-mcp tools
(`lean_goal`, `lean_diagnostic_messages`, `lean_multi_attempt`, etc.).
Edit the file on disk, then use `lean_goal` and `lean_diagnostic_messages`
to inspect the result.
`lake build` is ONLY allowed as a SINGLE final verification after all proofs are done.
If you use `lake build` for iterative proof development, your work will be REJECTED.

## The Sorry
`my_function_loop0_loop0_spec` at line ~421.

## Proof Strategy
The loop is a recursive function — use `unfold` + `step` with case split.
Use `step*?` to generate the body proof script, then fix sub-goals.

## Available Specs
- `helper_spec`, `mod_add_spec`, etc.

## Key Rules
- NEVER unfold stdlib
- NEVER use `omega` — use `agrind` (preferred), `grind`, or `scalar_tac`
- When stuck: **always try `agrind` first** (then `grind`). Do NOT use `simp_all` — it is very slow in big contexts and drops hypotheses.
- Your PRIMARY task is `MyModule.lean`, but you MAY modify other files in
  your clone if needed (e.g., shared defs, axiom files, bridge lemmas).
  The supervisor will handle merging across clones.
- ⛔ NEVER run `git checkout`, `git restore`, `git stash`, `git reset`, or
  any command that reverts/discards file changes.
- NEVER commit or push without explicit user approval
- After completing this sorry, STOP and return results — do NOT proceed to other work
```

## Example: Full Agent Prompt (same-clone mode)

```
Fix the inner loop sorry in `/path/to/MyModule.lean`.

## Step 1: Invoke Skills
As your FIRST action, invoke these skills (use the `skill` tool):
1. `aeneas-lean-core` — translation model, spec patterns, pitfalls
2. `aeneas-tactics-quickref` — which tactic for which goal
3. `lean-lsp-mcp` — mandatory tooling for proof checking

## Step 2: ⛔ HARD REQUIREMENT — lean-lsp-mcp tools ONLY
After reading the skills, do ALL proof checking via lean-lsp-mcp tools
(`lean_goal`, `lean_diagnostic_messages`, `lean_multi_attempt`, etc.).
Edit the file on disk, then use `lean_goal` and `lean_diagnostic_messages`
to inspect the result.
`lake build` is ONLY allowed as a SINGLE final verification after all proofs are done.
If you use `lake build` for iterative proof development, your work will be REJECTED.

## The Sorry
`my_function_loop0_loop0_spec` at line ~421.

## Proof Strategy
The loop is a recursive function — use `unfold` + `step` with case split.
Use `step*?` to generate the body proof script, then fix sub-goals.

## Available Specs
- `helper_spec`, `mod_add_spec`, etc.

## Key Rules
- NEVER unfold stdlib
- NEVER use `omega` — use `agrind` (preferred), `grind`, or `scalar_tac`
- When stuck: **always try `agrind` first** (then `grind`). Do NOT use `simp_all` — it is very slow in big contexts and drops hypotheses.
- ⛔ ONLY modify `/path/to/MyModule.lean` — NEVER edit ANY other .lean file.
  Other agents are working in parallel on other files. Editing them will
  destroy their work. Use local `private axiom` + TODO for cross-file needs.
- ⛔ NEVER run `git checkout`, `git restore`, `git stash`, `git reset`, or
  any command that reverts/discards file changes. Other agents have uncommitted
  work on disk — any git revert command DESTROYS their work silently.
- NEVER commit or push without explicit user approval
- After completing this sorry, STOP and return results — do NOT proceed to other work
```
