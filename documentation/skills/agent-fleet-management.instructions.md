---
name: agent-fleet-management
description: Resource management, file isolation, task sizing, and supervisor rules for AI agent fleets
---

# Agent Fleet Management — Skill File

## Overview

This file contains **general rules for managing fleets of AI agents** working on a
shared codebase. All skill files that involve agent supervision (proof agents,
formalization agents, etc.) must follow these rules and reference this file rather
than duplicating them.

For rules about writing, editing, and reviewing skill files, see
`skill-file-authoring.instructions.md`.

## Resource Management

### Heavy processes

Some agents run resource-intensive processes. The most common example is a **Lean LSP
server** (~8 GB RAM each), but this applies to any heavy process (compilers, solvers,
large builds, etc.).

The supervisor must:

1. **Ask the user upfront** for the maximum number of concurrent heavy processes.
   A good default for Lean projects:
   > **Max parallel Lean agents = RAM (in GB) / 8**

   For example: 64 GB RAM → up to 8 parallel Lean agents. Exceeding this causes
   swapping, which makes ALL agents drastically slower.

2. **Classify each agent at launch** as:
   - **Heavy-process agent** — will run a Lean LSP, `lake build`, or other
     resource-intensive process. Counts against the budget.
   - **Lightweight agent** — only reads files, runs grep/glob, does analysis.
     Does NOT count against the budget. Examples: explore agents, code-review
     agents (read-only).

3. **State the budget explicitly before every launch:**
   > "Heavy-process budget: 4 max. Currently running: 2 (agent-a, agent-c).
   > Launching 2 more (agent-b, agent-d) → 4/4. At capacity."

4. **Update the count on completion** and dispatch queued work:
   > "agent-a completed. Heavy processes: 3/4. Dispatching follow-up agent."

5. **Never exceed the budget.** If all slots are full, queue the work and dispatch
   when a slot frees up.

## Agent Isolation Rules

### File ownership

Each agent is assigned specific file(s). It may **ONLY modify those files**.
It must NEVER edit other files — not shared definition files, not spec files,
not other agents' files.

**If an agent needs a different version of a spec or definition from another file:**

1. **Introduce a local version** in its own file — a `private axiom` or a
   `sorry`'d `private theorem` that states what it needs.

2. **The comment must explain TWO things:**
   - **Why needed** — what does the proof/formalization require that the current
     version doesn't provide? Which specific goal is blocked?
   - **Why valid** — why is the proposed version correct? What justifies it?

3. **Report the dependency** in its final response so the supervisor can coordinate
   the cross-file change.

**Why:** Multiple agents may run in parallel on different files. If agent A edits
a shared file while agent B also depends on it, B's elaboration or build breaks.
Only the supervisor coordinates cross-file changes — after all agents complete.

### No unauthorized sub-agent spawning

**⛔ Agents must NEVER spawn sub-agents that run heavy processes** (Lean LSP, builds,
solvers, etc.). This is a hard rule, not a suggestion. Reasons:

1. **Resource exhaustion**: The supervisor carefully controls how many heavy processes
   run in parallel. An agent spawning its own sub-agent can push the system over
   budget, causing swapping and making ALL agents slower.
2. **File conflicts**: The supervisor tracks which agent works on which file. A
   sub-agent working on the same file as its parent (or another agent) causes
   conflicts.
3. **Loss of control**: The supervisor cannot see or manage sub-agents spawned by
   other agents. This breaks the observability model.

Agents may use lightweight sub-agents (e.g., `explore` agents to search the codebase)
that don't run heavy processes. Any agent that needs heavy-process work done must
do it itself — if the task is too large, it should report back and let the supervisor
decompose it.

### File conflict prevention (pre-launch check)

**Before launching any fleet of agents**, the supervisor must verify that no two
agents will conflict. For each pair of agents in the batch:

1. **Same-file check**: Are any two agents targeting the same file?
   If yes, merge them into one agent or serialize them.

2. **Dependency check**: Does any agent's file depend on (import) another agent's
   file? If A depends on B, the agent on A must wait until B's agent finishes.

3. **Shared-definition check**: Do multiple agents depend on a shared file that a
   third agent is also modifying? If so, the third agent must finish first.

**State this check explicitly** before launching:
> "CT.lean imports Defs.lean, MulBS.lean imports MatDefs.lean — no mutual
> dependencies, safe to parallelize."

**If you discover a conflict after agents are already running**, stop the
conflicting agent immediately, wait for the other to finish, then relaunch.

## Task Granularity and Progress

### Background agents cannot report mid-run

Background agents run autonomously and return a single final result. They cannot
send intermediate progress reports. **The supervisor controls observability through
task granularity.**

### Difficulty-based task sizing

Before dispatching, the supervisor must assess each task's expected difficulty:

- **Easy tasks** (e.g., mechanical unfold + automation, clear patterns): batch
  several per agent (3-5).
- **Medium tasks** (e.g., known patterns needing some manual work): give 1-2
  per agent.
- **Hard tasks** (e.g., complex reasoning, unclear approach): give exactly 1
  per agent — these can take 30-60 min, and the supervisor needs to review
  the approach before continuing.

**When uncertain, err toward fewer tasks per agent** — it's better to dispatch
a second round quickly than wait 90 min for an overloaded agent.

### Startup cost awareness

Each agent pays a startup cost (reading skill files, initializing tools, loading
files). This cost is paid per agent regardless of task size. Account for it when
choosing granularity — don't create many tiny agents if startup dominates.

### Agent final reports

Instruct agents to report in their final response:
- What was accomplished (and what remains, if any)
- What approach was used
- Any blockers or missing dependencies discovered
- Whether their files build cleanly

For inherently large tasks where the agent may not finish, instruct it to report
partial progress: what was tried, how far it got, what it thinks is needed.

## Supervisor Responsibilities

### Default workflow: do → review → fix → converge

Whenever the user asks to perform a task (proof work, code changes, skill file edits,
etc.), the supervisor should **propose and follow this loop**:

```
1. Do the task (yourself or via agents)
2. Dispatch reviewer(s) — every review is a **full review from scratch**.
   Do NOT tell reviewers to "confirm fixes" or reference prior rounds.
   The reviewer prompt should be identical to a first-time review.
3. Fix issues found by reviewers
4. Go to step 2 until a review returns zero issues
5. Report final result to user
```

**Before starting**, propose this workflow to the user and ask for validation:
> "I'll [do X], then dispatch a reviewer to check [Y]. I'll fix any issues and
> iterate until it converges. Sound good?"

The user may want to skip the review (for trivial tasks), do the review themselves,
or adjust the scope. Always ask rather than assume.

**Review depth depends on the task:**
- **Skill file edits**: reviewer checks cross-file consistency, actionability, and
  that examples match rules (see `skill-file-authoring.instructions.md`).
- **Proof work**: reviewer runs the full checklist (see launching-proof-agents).
  **The reviewer should read the modified files** (not just grep) — the token cost
  is modest (~15K tokens per file) and grep alone misses structural issues like
  multi-line inline `(by ...)` blocks and proof organization problems.
- **Mechanical changes** (bulk rename, sed replacement): reviewer spot-checks a
  sample + verifies the build passes. Full read not needed.

**Convergence:** The loop typically converges in 1-2 iterations. If a third review
still finds issues, escalate to the user — the task or the guidelines may need
rethinking.

### Active supervision

When an agent completes:
- **Review the result**: Did it succeed? Partially? Fail?
- **Assess the approach**: Was it sound? Should the next agent try differently?
- **Report to the user**: Surface interesting findings.

### Status table format

When giving a status report — whether the user asked for it, or you are reporting
proactively (e.g., agent completion results, phase transitions, progress updates) —
**always include the current date and time** at the top of the report (e.g.,
"**Status at 2026-03-22 06:50 UTC**"). This helps the user track progress over time,
especially during long autonomous runs.

Present a table with these columns:

| Column | Description |
|--------|-------------|
| **File** | The Properties file name (without `.lean`) |
| **Sorry's** | Current number of `sorry` occurrences in the file |
| **Δ** | Change in sorry count since the last status check (e.g., ↓3, ↑1, —) |
| **Modified** | Whether the file has been modified since the last status check (✏️ yes / — no) |
| **Agent** | Which agent is working on it (name + 🔄), or — if none |
| **Runtime** | How long the agent has been running (e.g., 2.3h) |
| **Build** | Whether the file builds cleanly since last modification (✅ / ❌ / ❓ unknown) |

**How to populate each column:**
- **Sorry's**: `grep -c 'sorry' <file>` on disk
- **Δ**: Compare with the count from the previous status check (track in session state)
- **Modified**: `git diff --name-only` or compare file mtimes since last check
- **Agent**: From the agent list (`list_agents`)
- **Runtime**: From agent metadata (seconds since launch)
- **Build**: Track whether a successful `lake build <module>` has run since the file
  (or any of its transitive dependencies) was last modified. If unknown, show ❓.

Include a summary line below the table: total sorry's, total non-obsolete sorry's,
notable wins (files that hit 0, big drops), and any concerns.

### Cross-agent synthesis

After a batch of agents completes, synthesize patterns:
- Are multiple agents struggling with the same issue?
- Is there a common missing definition/lemma that would help many agents?
- Are agents making the same mistakes? (→ update skill files)
- Are there automation opportunities? (→ report to user)

**The supervisor does NOT act on synthesis findings autonomously.** It reports
recommendations to the user and waits for approval before making changes.

### Consolidation after fleet completion

After all agents in a fleet complete:
1. **Merge results**: Apply each agent's file changes (no conflicts if isolation
   rules were followed).
2. **Consolidate local workarounds**: Collect all local axioms/sorry'd theorems
   with TODO comments. Group them by the shared file that needs updating.
   Present to the user for cross-file changes.
3. **Classify reusable artifacts**: Review helpers and lemmas agents introduced.
   Identify which should be moved to shared files, which are stdlib candidates
   (report to user), and which stay local.
4. **Run a full build** to verify everything integrates cleanly.
