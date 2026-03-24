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

**For general agent management rules** (resource budgets, file isolation, spawning
rules, task granularity, etc.), see `agent-fleet-management.instructions.md`. This
file only covers proof-specific workflow and instructions.

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

DO NOT use `lake build` to iterate on proofs. Use lean_lsp.py
(see lean-lsp-tool skill file for full reference):

  cd <project-lean-root>
  python3 <path-to-aeneas>/scripts/lean_lsp.py --repl --json --log /tmp/lean_lsp_<agent-name>.log

**`--log` is MANDATORY** — always pass a unique log path per agent.

Workflow: open → wait → sorry → goal → edit → errors → repeat
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
- NEVER use `omega` — use `agrind`, `grind`, or `scalar_tac` instead
- NEVER spawn sub-agents that work on Lean files (see below)
- ONLY modify your assigned file(s) — NEVER edit other files (see below)
- DO NOT COMMIT
```

### 6. File modification restriction

**⛔ Agents must ONLY modify the file(s) they have been explicitly assigned.**
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

These rules are defined in `agent-fleet-management.instructions.md`. Key points
for proof agents:

- **⛔ NEVER spawn sub-agents that run Lean processes** (lean_lsp.py, lake build)
- **⛔ ONLY modify your assigned file(s)** — use local axioms with TODO comments
  for specs from other files (see section 6 above)
- Agents may use lightweight `explore` agents for codebase searches

## File Isolation and Parallelism (Lean-Specific)

See `agent-fleet-management.instructions.md` for the general rules. Additional
Lean-specific notes:

- **Import-dependency check**: Lean files form an import DAG. If file A imports
  file B (directly or transitively), the agent on A must wait until B's agent
  finishes. Check `import` statements at the top of each file before launching.
- **Examples**:
  - ✅ Agent A on `Ntt.lean`, Agent B on `CompressEncode.lean` (no import relationship)
  - ❌ Agent A on `Ntt.lean` inner loop, Agent B on `Ntt.lean` outer loop (same file)
  - ❌ Agent A on `VectorOps.lean`, Agent B on `Ntt.lean` (if VectorOps imports Ntt)

## Task Decomposition and Agent Supervision

When the user asks for a large task (e.g., "prove all sorry's in this file"), do NOT
give the entire task to a single agent in one shot. Instead:

1. **Decompose into small tasks**: The number of sorry's per agent depends on
   difficulty (see `agent-fleet-management.instructions.md` for the general
   difficulty-based sizing rule). For proof agents specifically:
   - **Easy sorry's** (wrapper unfolds, clear `step*` proofs): 3-5 per agent
   - **Medium sorry's** (loop invariants with known patterns): 1-2 per agent
   - **Hard sorry's** (complex bitwise/modular reasoning, unclear approach): 1 per agent

2. **Give one small task at a time**: Launch an agent with a focused objective. When it
   reports back, analyze the result before deciding what to do next.

3. **Supervise actively**: When an agent completes and reports back:
   - **Step back**: Did the agent make progress? Did it get stuck? Did it go in circles?
   - **Diagnose issues from the output**: Did it use `lake build` instead of `lean_lsp.py`?
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

6. **Reinforce lean_lsp.py usage in every agent prompt**: Agents tend to fall back to
   `lake build` loops. Every time you launch an agent, include in the prompt:
   "Use lean_lsp.py for all proof iteration — do NOT use lake build." This
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

Read:
- The auto-generated code in Funs.lean (line N)
- The pure specification `Spec.Foo.Bar` in FooSpec.lean (line M)

The postcondition must express FULL FUNCTIONAL CORRECTNESS:
- NOT just length preservation (that's trivially weak)
- NOT just `True` (useless)
- It must relate the output to the spec function using bridge definitions
  like `Slice.toMatrix`, etc.

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

<!-- ⚠️ SYNC RULE: source of truth is aeneas-lean-core "Proof Style and Maintainability"
     and aeneas-tactics-quickref "Proof Style Rules". See skill-file-authoring for sync rules. -->

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
  ```

### Banned constructs (mechanical grep)

Run these grep checks on every file under review. **Any match is a mandatory fix.**

```bash
# Banned tactics (Rule: "BANNED TACTICS"; Pitfalls #1-#5 preference order)
grep -n '\bomega\b' FILE          # → replace with agrind > grind > scalar_tac
grep -n '\blinarith\b' FILE       # → replace with agrind > grind > scalar_tac
grep -n '\bnlinarith\b' FILE      # → replace with agrind > grind > scalar_tac +nonLin

# Never increase maxRecDepth (Pitfall #11)
grep -n 'maxRecDepth' FILE        # → diagnose simp loop, never raise limit

# maxHeartbeats too high (Pitfall #13)
grep -n 'maxHeartbeats' FILE      # → verify value < 8_000_000; if higher, proof needs restructuring

# Unfold of Aeneas stdlib definitions (Pitfall #10)
grep -n 'unfold.*Aeneas\|unfold.*Std\.\|unfold.*core\.' FILE
# → search for existing lemma instead of unfolding

# step* <;> tactic (Rule: "Avoid step* <;> tactic")
grep -n 'step\*.*<;>' FILE       # → use focused goal blocks (· ) instead

# all_goals (Rule: "Avoid step* <;> tactic")
grep -n 'all_goals' FILE          # → acceptable ONLY if single cheap tactic (e.g., all_goals agrind).
                                   #   BAD if contains first|..., tactic sequences, or expensive tactics.

# Inline (by ...) in exact/apply/refine (Rule: "Extract inline by blocks"; Pitfall #15)
grep -n 'exact.*(by ' FILE        # → check: 2+ expensive blocks or any multi-line block → extract
grep -n 'apply.*(by ' FILE        # (same check)
grep -n 'refine.*(by ' FILE       # (same check)
# ⚠️ These greps only catch single-line cases. The most common violation is multi-line:
#   exact lemma arg1
#       (by tac1) (by tac2)    ← grep misses this
# The reviewer MUST also read multi-line exact/apply/refine statements manually.
# "Expensive" = multi-line, tactic sequences (tac1; tac2), first|..., all_goals, or slow tactics.
# A single cheap (by scalar_tac) or (by grind) is acceptable.
```

### Checks requiring manual inspection

These cannot be reliably grepped — the reviewer must read the proof:

- **Auto-param tactics in recursive theorems?** (Pitfall #16)
  In recursive `spec_gen` theorems, all parameters must be explicit — no `:= by ...`
  defaults. Look for `:= by` in theorem parameter lists (not in proof bodies).

### Structural and style checks (manual inspection)

These require reading the proof, not just grepping:

- **Is the proof idiomatic?** (Rule: all of "Proof Style and Maintainability")
  Uses standard Aeneas patterns (step, WP.spec_mono, split_ifs, etc.) rather than
  ad-hoc workarounds? Follows patterns in proof-patterns.instructions.md?

- **No big `simp only [...]` in implementation proofs?** (Rule: "Avoid large simp only")
  Big lemma lists in `simp only` make proofs fragile when the model changes.
  OK in spec lemmas. Prefer `simp [*]`, `agrind`, or targeted rewrites.

- **Complex sub-proofs extracted as auxiliary lemmas?** (Rule: "Extract auxiliary lemmas")
  No 15-line arithmetic blocks inlined in the middle of `step*`.

- **Recurring index bounds extracted as standalone helpers?** (Pitfall #22)
  Bounds like `k * N + q < NBAR * N` should not be proved inline repeatedly.

- **No early case splits on parameters?** (Rule: "Avoid early case splits")
  `cases p` at proof top duplicates everything. Case splits should be local or
  handled via `attribute [local agrind]`.

- **`agrind` preferred over `grind`?** (Pitfall #5)
  `grind` should only appear when `agrind` fails. In loop proofs (`spec_gen`),
  prefer `agrind` over `scalar_tac` throughout (Pitfall #21).

- **Shifts simplified?** (Rule: "Simplify shifts early")
  `>>>` should be rewritten as `/ 2^n`, `<<<` as `* 2^n`.

- **Spaces around binary operators in comments?** (Rule: "Spaces around binary operators")
  `j < N`, not `j<N`. Missing spaces cause VS Code highlighting bugs.

- **Helper lemmas properly named and documented if non-obvious?**

- **Is the proof clean and not verbose?** No copy-paste bloat, no redundant `have`
  that could be inlined. Each tactic call should earn its place.

### Performance checks

- **Is the proof fast enough?** (Pitfall #14)
  Profile with `set_option trace.profiler true in` and check that the proof
  completes in **< 60 seconds wall-clock**. If slower, send back for optimization.

- **Is the proof reactive for interactive development?** (Pitfall #15)
  Adding a tactic at the end should take < 0.5s. If not, look for inline `(by ...)`
  blocks (see grep above) and suggest extracting them into `have` statements.

- **Are `maxHeartbeats` values reasonable?** (Pitfall #13)
  If any `set_option maxHeartbeats` exceeds 8M, the proof needs restructuring.

- **Are sorry'd proofs fast?** (Pitfall #24)
  A sorry'd proof should use plain `sorry`, not `step* <;> (first | ... | sorry)` or
  `cases p <;> step* <;> sorry`. Expensive sorry'd proofs waste build time for zero
  verification value.

**Skill file freshness:**

- **Every agent invocation** (statement agents, proof agents, review agents) **must
  include the "read skill files first" instruction** in its prompt — both the
  **Aeneas skill files** (in the aeneas repo under `documentation/skills/`) and any
  **project-local skill files** (e.g., `.github/instructions/`, `.claude/skills/`).
  Since each agent invocation is a fresh context, this ensures the agent always works
  from the latest version of all skill files — including any mid-run updates the
  master made (with user approval).
- If the reviewer finds **many guideline violations** (e.g., 3+ issues that the
  skill files clearly address), the prompt for the follow-up fix agent should include:
  **"Re-read the skill files before fixing these issues."**
  The follow-up agent is a fresh context and may have different knowledge — explicitly
  pointing it to the skill files ensures it doesn't repeat the same violations.

**Progress reporting and task granularity:** See `agent-fleet-management.instructions.md`
for the general rules. Proof-specific notes:

- **Assess sorry difficulty before dispatching** — read the proof sketch (if present),
  check the function's monadic step count, check if similar proofs exist, and consider
  whether needed specs/lemmas already exist.
- **Give each agent sorry's in a specific file**: "Fill the sorry at line 130
  in MulASPlusE.lean" or "Fill sorry's at lines 130 and 168 in MulASPlusE.lean".
- **Parallelize across files**: Launch multiple agents simultaneously, each targeting
  a different file. Startup costs overlap, so wall-clock time is the slowest agent.
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

## Master Synthesis

See `agent-fleet-management.instructions.md` for the general cross-agent synthesis
rules. Proof-specific patterns to watch for:

- Multiple agents stuck on the same kind of sub-goal (e.g., bitwise reasoning)
  → may need a shared lemma proved centrally
- Agents discovering missing specs in `ExternalSpecs.lean` → consolidate after fleet
- Common bridge definitions needed across proofs → add to `Defs.lean`/`MatDefs.lean`

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
- If partial, launch a follow-up agent with refined instructions

## Common Agent Failure Modes

| Failure | Cause | Fix |
|---------|-------|-----|
| Agent uses `lake build` loops | Didn't read LSP skill | Stronger prompt, mandate LSP |
| `step*` times out | Too many monadic calls | Use `step*?` workflow |
| Unfolds stdlib definitions | Didn't read core skill | Add "don't unfold" rule to prompt |
| Uses `omega` | `omega` can't reason about scalars, `U32.max`, list lengths, etc. | NEVER use `omega` — use `agrind` > `grind` > `scalar_tac` |
| Uses `nlinarith` | Same issues as `omega` — can't reason about scalars | NEVER use `nlinarith` — use `agrind` > `grind` > `scalar_tac +nonLin` / `simp_scalar` |
| Uses `linarith` | Same issues as `omega` — can't reason about scalars | NEVER use `linarith` — use `agrind` > `grind` > `scalar_tac` |
| Edits wrong file/section | Ambiguous instructions | Be very specific about what to change |
| Increases `maxRecDepth` | Trying to work around recursion depth errors | NEVER increase `maxRecDepth` — diagnose the root cause (bad proof structure or simp loop). Report to user if it's a tactic bug |
| Tactic silently fails | Tactic doesn't do what it should (e.g., `step` can't find a lemma that exists) | Report to user — may be a tactic bug worth fixing upstream |
| Spawns Lean sub-agents | Agent tries to parallelize by spawning sub-agents | NEVER spawn sub-agents that work on Lean files — resources are tight, and it causes file conflicts |
| Edits other files | Agent modifies shared defs or specs it wasn't assigned | NEVER edit files other than assigned ones — introduce local axioms with TODO comments instead |
| Agent crashes mid-edit | API loss, timeout, resource limit | Check for referenced-but-undefined identifiers; create missing defs in shared files |
| `scalar_tac` loops in spec_gen | `maxRecDepth` in loop invariant proof | Mass-replace ALL `scalar_tac` → `agrind` in the proof body |

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
The loop is a recursive function — use `unfold` + `step` with case split.
Use `step*?` to generate the body proof script, then fix sub-goals.

## Available Specs
- `butterfly_spec`, `mod_add_spec`, etc.

## Key Rules
- NEVER unfold stdlib
- NEVER use `omega` — use `agrind` (preferred), `grind`, or `scalar_tac`
- ONLY modify the specified sorry
- NEVER commit or push without explicit user approval
- After completing this sorry, STOP and return results — do NOT proceed to other work
```
