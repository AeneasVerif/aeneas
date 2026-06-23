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
