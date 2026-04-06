---
name: verification-campaigns
description: Planning and executing verification campaigns — from-scratch primitives, new/changed functions, and recovery after code changes
---

# Verification Campaigns

This skill covers how to plan and execute a **verification campaign**: a sustained,
multi-phase effort to verify a complete cryptographic primitive (or recover from
major code changes that break existing proofs). Read this skill when:

- Verifying a new implementation from scratch
- Major code changes introduced new functions, deleted functions, or broke existing
  theorem statements
- Resuming a stalled campaign after significant time away

**Prerequisites:** Read the `aeneas-lean-core`, `aeneas-tactics-quickref`, and
`launching-proof-agents` skill files before starting a campaign. This skill assumes
familiarity with the Aeneas proof model and agent orchestration.

## Trigger Conditions

Read this skill when ANY of the following apply:

1. **New primitive:** The user asks to verify a Rust implementation that has no
   existing proof files.
2. **Significant change in the Lean model:** The shape of `Funs.lean` / `Types.lean`
   changed significantly. This can happen because:
   - The user added, removed, or modified Rust functions
   - Aeneas was updated (new translation pass, bug fix, different code generation)
   - Different Aeneas options were used (e.g., activation/deactivation of
     `-loops-to-rec`)
   - Charon was updated (different MIR lowering)
   The result is new functions, changed signatures, or structurally
   different loop/control-flow translations.
3. **Mass breakage:** More than ~5 files have errors after a code change, or the
   build fails on multiple proof files simultaneously.
4. **New or changed functions:** The user added, removed, or modified Rust functions
   that need (new or updated) theorem statements — even a single new function
   triggers the Recovery Mode workflow.

**Do NOT use this skill for:** fixing a single sorry, adding one lemma, or routine
proof maintenance. Those are normal proof tasks covered by `proof-patterns` and
`aeneas-lean-core`.

---

## Phase 1: Plan the Structure

### 1.1 Understand the Code

Before writing any Lean, thoroughly study:

- **The Rust source code** — read every function, understand the data flow, identify
  phases (e.g., absorb/squeeze in a sponge construction). Pay attention to mutable
  state threading, loop patterns, and conditional branches.
- **The Lean translation** (`Funs.lean`) — identify how Aeneas translated each Rust
  function. Note any translation artifacts (e.g., state not threaded through recursive
  calls — see known Aeneas bugs).
- **The specification** (`Spec/` directory) — understand the target spec. The spec is
  the source of truth and **must not be modified**. If the implementation cannot be
  proven to refine the spec, report the discrepancy to the user.

### 1.2 Plan the Folder Structure

Organize proof files to maximize parallelism and keep build times low:

- **Axioms** go in `Axioms/` only. This includes:
  - Models of external/opaque Rust definitions (from `TypesExternal_Template.lean`
    and `FunsExternal_Template.lean`)
  - Axiomatized external functions (in `FunsExternals.lean`)
    with their corresponding `@[step]` theorems
- **Proofs** go in `Properties/PRIMITIVE/`, decomposed into sub-folders by logical
  component (e.g., `KeccakPerm/`, `Absorb/`, `Squeeze/`, `Variants/`)
- **Target: < 60s build time per file.** This means roughly one big function
  (~100 lines of Rust) per file, or a few small functions (~25 lines each) per file.
- **Shared definitions** (bridge functions, conversion helpers, well-formedness
  predicates) go in a `Properties/Basic.lean`, or eventually into several files in a
  folder `Properties/Basic/` if there are many such definitions.

### 1.3 Get User Approval

Present the folder structure plan to the user before creating files. Include:
- The file tree with one-line descriptions
- Which Rust functions map to which proof files
- Where bridge/conversion definitions will live

---

## Phase 2: Populate and Converge

### 2.1 Create the Scaffold

Create all proof files with:

- Axioms and their `@[step]` lemmas
- `@[step]` theorem statements for every function to verify
- Proof bodies as `unfold FUNCTION_NAME; sorry`
- All bridge/conversion functions needed to link implementation types to spec types.
  **Every bridge/conversion function and spec helper must have a concrete body — never
  `sorry`.** A sorry'd definition makes every theorem that references it vacuously true.
  See the `aeneas-lean-core` skill, "Sorry'd definitions vs sorry'd theorems."

Write theorem statements per the `aeneas-lean-core` skill file. In particular:
- **Full functional correctness (FC)** in every postcondition — not just structural
  properties. The composability test: "knowing ONLY this postcondition, could a caller
  derive its own FC?"
- This applies to **all** functions, not just top-level ones. Auxiliary/helper function
  specs must also state FC.

### 2.2 Write Informal Proofs

Dispatch statement formalization agents to write an informal proof for each theorem.
The informal proof goes in a `/- ... -/` comment between the theorem statement and the
`unfold ...; sorry`. Each agent must:

1. **Go through the function body line by line.** For each monadic call:
   - Look up the corresponding `@[step]` theorem (don't guess — read the actual file)
   - Verify the preconditions hold given the current context
   - State what the postcondition gives
   - Explain how the postcondition feeds into the caller's FC goal

2. **Write justifications for every non-trivial step.** Include inequality chains,
   equality chains, case splits, and arithmetic reasoning. The level of detail should
   be enough for a mechanizer to translate directly into tactics.

3. **Introduce fold helpers** when the function body has > 20 monadic let-bindings or
   has clearly separable phases. Each fold helper gets its own theorem statement
   (with FC postcondition) and informal proof.

4. **Introduce auxiliary lemmas** when a sub-proof would be long or involves a key
   insight that should be stated independently (e.g., bridge lemmas connecting
   implementation-level and spec-level representations).

5. **Report blockers precisely** (see the `aeneas-lean-core` skill, "No Vague Blockers"
   pitfall). If a precondition is too weak, a definition is missing, or a step theorem
   is too weak, state exactly what is needed and where.

### 2.3 The Review-Fix Convergence Loop

After the scaffold is populated, enter the **mandatory review-fix loop** by which you
repeatedly dispatch reviewers and fix the issues until reviewers do not report any issues:

#### Dispatch Reviewers

Dispatch separate reviewer agents — one per logical domain (e.g., one for KeccakPerm,
one for Absorb, one for Squeeze+Variants). Each reviewer must check:

**Theorem statement review (for every `@[step]` and `@[progress]` theorem):**

1. **FC completeness**: Does the postcondition fully specify the output in spec-level
   terms? Apply the composability test.
2. **Auxiliary function FC**: Auxiliary (non-top-level) function specs must ALSO have
   FC — not just structural properties. A reviewer must flag any spec that only states
   index advancement, flag preservation, or bounds without a spec-level equality.
3. **Precondition minimality**: Are preconditions necessary? Are "by design"
   limitations (e.g., "absorb mode only") documented with comments?
4. **API coverage** (see `aeneas-lean-core` "API coverage"): For public-facing
   functions, do the preconditions cover ALL valid calling patterns documented in
   the Rust API? Read the Rust trait docs and function comments. If a precondition
   excludes a valid pattern, this is a **critical issue** — the spec must be
   generalized. No exceptions.
5. **Invariant threading**: If the function takes a well-formedness
   precondition, the postcondition should guarantee well-formedness of the result.
6. **Postcondition clarity**: No inline computation (let-bindings with
   if-then-else, case splits, non-trivial expressions) in postconditions. Any such
   logic must be extracted into a named `def`/`abbrev` in the shared definitions file.
   (See `aeneas-lean-core` "No inline computation in postconditions.")
7. **No existential quantifiers over non-propositions**: `∃ a, P a` where `a` is
   a value (not a proof) is banned. However, `∃ (_ : P), Q` where `P` is a
   proposition used for dependent typing is **allowed** — do not flag it.
8. **Factor repeated guards**: When multiple conjuncts share the same guard
   (e.g., `(¬wipe → A) ∧ (¬wipe → B)`), factor it out: `¬wipe → (A ∧ B)`.
   Applies to any predicate — implications, case splits, hypotheses.
   (See `aeneas-lean-core` "Factor repeated guards in conjunctions.")

**Informal proof review (line-by-line call-graph tracing):**

5. **Exhaustive monadic call enumeration.** For each `@[step]` theorem, the
   reviewer must open the corresponding function body in `Funs.lean` and
   **list every `let ... ←` binding** (monadic call) in the review output.
   For each binding, the reviewer must state one of:
   - **Has spec**: "`<call>` — by `<theorem_name>`". (where `<theroem_name>` is a
     step theorem).
     Then verify: preconditions satisfied, postcondition provides what the
     caller needs, FC clause feeds into the top-level FC goal.
   - **MISSING spec** (critical): "`<call>` — **NO step spec exists** for
     `<full_lean_name>`". This is a critical issue: without it, `step` cannot
     make progress through this call, and the proof is blocked.
   **All functions** must have a step spec, even axiomatized functions.

   This enumeration must be **exhaustive** — cross-checked against the actual
   function body in `Funs.lean`, not just the informal proof's summary. If the
   informal proof skips a monadic call, that is itself a critical issue.

   **External/stdlib calls deserve extra scrutiny.** Calls to functions defined
   in `FunsExternal.lean` (axioms for std library, iterator methods, Pin API,
   FFI) are the most likely to lack specs. For each such call, verify the spec
   exists in one of: the Aeneas stdlib, the project's `Axioms/` folder, or an
   iterator/stdlib specs file. A bare axiom with no postcondition (`axiom f :
   A → Result B`) is NOT a spec — it says nothing about what `f` returns.

   **Opaque types compound missing specs.** If an external function operates on
   an opaque type (e.g., an iterator with no ghost state, `Pin T` with no
   structure), then no meaningful spec can be written for it either. Flag both:
   the missing spec AND the opaque type that prevents writing one.

6. **Bridge lemma coverage**: Are all necessary conversions between implementation
   types and spec types covered? (e.g., `toBitstring ↔ toStateArray`,
   `iterRounds ↔ P 6 24`)
7. **Fold helper decomposition**: Are long functions properly split? Could any
   phase spec's postcondition be stronger?

**Structural review:**

8. **Function coverage**: Every Rust function in the Aeneas translation (`Funs.lean`)
   that is part of the primitive being verified must have a corresponding `@[step]`
   theorem. Every axiom (in `Axioms/`) must have a corresponding `@[step]` lemma.
   Cross-check against the generated code — no function should be forgotten.
8b. **External dependency audit**: Collect all external functions called
   (directly or transitively) by the verified functions. For each one, verify
   a `@[step]` spec exists. Any external axiom that is called but has no spec is a
   **critical gap** — list it by full Lean name and the file(s) where it is called.
9. **Axiom audit**: List every `axiom`, `sorry`, `native_decide` found. Sorry in
   proof bodies is expected (WIP); **sorry in definition bodies (bridge functions,
   spec helpers, conversion functions) is a critical issue** — every theorem
   referencing that definition is vacuously true. These must be filled with concrete
   Lean expressions immediately.
10. **Import completeness**: Do all referenced names resolve?
11. **Dead code**: Remove unused definitions, orphaned comments, stale TODOs.
12. **Documentation**: Non-obvious preconditions have explanatory comments.
    Spec definitions have docstrings.
13. **File size**: No file should be so large that build time will exceed 60s once
    proofs are filled in.

#### Fix ALL Issues

After each review round, fix **every** issue — including warnings and minor items.
Do not dismiss warnings as "low priority" or "cosmetic." Seemingly minor issues
often hide deeper problems (a missing `wfKeccakState` hints at a provably false
theorem; a stale TODO suggests the FC chain is incomplete). All issues must be
resolved before starting Phase 3 (mechanized proofs), which is difficult and
time-consuming — discovering a flawed theorem statement mid-mechanization wastes
far more effort than fixing it now.

**For the agent fixing issues:** Do not skip warnings. Every item flagged by a
reviewer — critical or warning — must be addressed. If you believe a reviewer
finding is a false alarm, explain why concretely (e.g., cite the skill rule that
permits the pattern), but do not silently skip it. Specific rules:

- **Stale TODOs**: Remove or update. A TODO that says "needs strengthening" when the
  strengthening was already done is misleading.
- **Duplicate docstrings**: Merge into one.
- **Missing well-formedness predicate (e.g., `wfKeccakState`)** in postconditions: Add it
  if the function preserves well-formedness.
- **Documentation comments on non-obvious preconditions**: Add them. Explain *why*
  the precondition is needed and how callers can satisfy it.
- **Bug tracker references**: When a precondition works around a known bug, reference
  the bug tracker entry (e.g., "see BUG.md item 4").

#### Converge

Loop: dispatch reviewers → fix → dispatch reviewers → fix → ... until a review round
returns 0 critical issues and 0 warnings (or all remaining warnings are explicitly
documented as "by design" with comments in the code).

#### Final From-Scratch Review

Once the loop converges, dispatch reviewers to **review everything from scratch** —
not just the changes from the last round. This catches issues that slipped through
incremental reviews. Do NOT tell the reviewers what prior rounds found
(anti-rubber-stamping rule).

If the from-scratch review finds new issues, enter another fix-review loop until it
converges again.

### 2.4 Completion Criteria

Phase 2 is complete when:

- [ ] Every Rust function has a corresponding `@[step]` theorem
- [ ] Every theorem statement has full FC in its postcondition
- [ ] Every theorem has a detailed informal proof
- [ ] All fold helpers and bridge lemmas are in place
- [ ] Final from-scratch review passes with 0 critical issues
- [ ] Build passes cleanly (no errors; only pre-existing warnings from other modules)
- [ ] User has been shown the top-level theorems

---

## Recovery Mode: After Code Changes

This mode applies whenever the set of functions to verify changes. This includes:

- **Major breakage**: Aeneas re-extraction or Rust refactoring broke existing proofs
- **New functions added**: The user added Rust functions that need verification, or
  existing functions gained new code paths that need covering
- **Functions removed or renamed**: Existing theorems reference stale definitions
- **Translation changes**: Different Aeneas/Charon options changed the shape of the
  generated code

Even adding a single new function triggers this mode — the new function needs a
theorem statement, informal proof, and must pass the review loop before mechanization.

### Step 1: Triage

1. Run `lake build` and collect all errors.
2. Categorize:
   - **Signature changes**: Function type changed → theorem statement needs updating
   - **New functions**: No theorem exists → create new proof file
   - **Deleted functions**: Theorem references non-existent function → remove or adapt
   - **Field renames**: Bulk rename in proof files (often mechanical)
   - **Semantic changes**: Function behavior changed → theorem statement AND informal
     proof need rework

### Step 2: Plan the Recovery

- For signature/field changes: batch mechanical fixes
- For new functions: plan new proof files (follow Phase 1 planning)
- For semantic changes: treat as a mini-campaign — new informal proof + review loop
- For deleted functions: remove proof files, update imports

### Step 3: Execute with Review Loop

Apply fixes, then enter the same review-fix convergence loop as Phase 2. The review
scope should cover all modified files plus any files that import them (transitive
impact).

---

## Anti-Patterns to Avoid

1. **Declaring a blocker without checking.** Before claiming a definition is missing
   from the stdlib, search for it. Before claiming a theorem is too weak, read its
   actual postcondition. (See `aeneas-lean-core` pitfall "No Vague Blockers.")

2. **Structural-only postconditions.** A spec that only says "state_index advanced by
   N" without stating what the state *contains* (in spec-level terms) is useless for
   FC composition. Every phase/helper must export a spec-level equality.

3. **Dismissing reviewer warnings.** "Minor" warnings accumulate into major confusion.
   Fix them all, every round.

4. **Stale TODOs.** A TODO that says "needs FC strengthening" after the FC was already
   added is worse than no TODO — it implies the work wasn't done.

5. **Rubber-stamp reviews.** Never tell a reviewer what prior rounds found. Each review
   must be independent (see `global-rules` §6).

6. **Skipping the from-scratch review.** Incremental reviews miss issues introduced by
   fixes. The final from-scratch review is mandatory.

7. **Modifying the spec.** The specification (`Spec/` directory) is audited and
   immutable. If the implementation doesn't match, that's a bug in the implementation
   (or a translation artifact) — report it, don't "fix" the spec.
