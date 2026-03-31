---
name: agent-fleet-management
description: General rules for managing fleets of AI agents working on a shared codebase
---

# Agent Fleet Management — Skill File

## Overview

This file contains **general rules for managing fleets of AI agents** working on a
shared codebase. All skill files that involve agent supervision (proof agents,
formalization agents, etc.) must follow these rules and reference this file rather
than duplicating them.

For rules about writing, editing, and reviewing skill files, see
the `skill-file-authoring` skill file.

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

### Agents cannot kill other agents

Agents (including the supervisor) **cannot cancel or kill other running agents.**
There is no API for it — `stop_bash` does NOT stop background agents, it only
stops shell sessions. If you need a stuck or misdirected agent stopped, **ask
the user** to cancel it (e.g., via `/tasks` in the CLI). If you attempt to
"cancel" an agent (which silently does nothing) and then dispatch a replacement,
you get two agents editing the same file — causing conflicts and data loss.
**DO NOT** dispatch a replacement for an agent that is running, as it will create
conflicts.

**⛔ Stuck agent protocol:**
1. **Diagnose**: Check `read_agent` (wait: false) + `list_agents` to confirm it's stuck
2. **ASK THE USER** to kill it — never try to kill it yourself
3. **Wait for confirmation** — the user will say "done" or "killed"
4. **Verify with `list_agents`** — confirm the agent shows as cancelled/completed
5. **Only then** clean up `agent_files` and dispatch a replacement

**NEVER skip step 4.** Even after the user says "killed", always call `list_agents`
to verify the agent is no longer running before dispatching any replacement.

### File ownership tracking

<!-- ⚠️ SYNC RULE: SQL mechanism and dispatch checklist defined in global-rules
     "Agent File Ownership and Conflict Prevention" -->

Maintain a SQL table `agent_files` to track which files each running agent owns.
Before dispatching any agent: (1) call `list_agents`, (2) query `agent_files` for
conflicts, (3) only dispatch if no file is already owned. When an agent completes
or is cancelled, delete its entries. See the `global-rules` skill file for the
full SQL schema and dispatch checklist.

**Conflicts include transitive dependencies.** If file A imports file B (directly
or transitively), editing A and B simultaneously is a conflict — the agent on A
sees a stale version of B.

### File assignment

Each agent is assigned specific file(s). It may **ONLY modify those files**.
It must NEVER edit other `.lean` files — not shared definition files, not spec
files, not other agents' files — because **other agents are working in parallel
on those files**. Editing a file that another agent is working on will corrupt
their in-progress work, break their elaboration, or cause silent data loss when
the `edit` tool applies string-matching patches to stale content.

**This is the single most common cause of lost work in multi-agent runs.**

**Alternative: Clone-based isolation (PREFERRED).** When separate git clones of the
repository are available, the supervisor should assign **one agent per clone** instead
of enforcing file-level isolation within a shared working tree. This is strictly safer —
there is zero risk of file conflicts, import-dependency races, or accidental
`git checkout` damage. The tradeoff is that the supervisor must merge diffs post-hoc.

**The supervisor must ask the user** whether to use same-clone (file-level isolation)
or separate clones. If the user chooses separate clones, the supervisor must also
ask where the clones are located — do NOT search for available clones on your own,
as clones in the filesystem may be in use for other purposes.

**Always prefer clone-based isolation** when clones are available; fall back to
file-level isolation only when a single working tree is the only option. See the
`launching-proof-agents` skill file for the full clone workflow.

### ⛔ NEVER use git checkout, git restore, or any file-reverting command

**Agents must NEVER run `git checkout`, `git restore`, `git stash`, `git reset`,
or any command that reverts, discards, or overwrites uncommitted file changes.**
This is a **hard ban** — the same level as banned tactics.

**Why:** In a multi-agent environment, other agents may have made uncommitted changes
to files that this agent doesn't own. Running `git checkout -- .` or
`git restore <file>` destroys their work silently. Even reverting "just your own
file" is dangerous — `git checkout -- <file>` reverts to HEAD, which may lose
changes from a DIFFERENT agent that touched the file before you.

**If your file has unexpected content or build errors:**
1. **Read the file** to understand the current state
2. **Make targeted edits** (using the `edit` tool) to fix only the broken parts
3. **NEVER bulk-revert** — if the file seems badly broken, report the problem
   and let the supervisor handle it

**If you need a clean version of a file you don't own:**
- Read it (read-only) — that's fine
- NEVER revert it to get a "known good" state

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

**If you discover a conflict after agents are already running**, DO NOT dispatch a
conflicting agent. Wait for the existing agent to complete, then dispatch.

### Infrastructure tasks MUST run between waves — never during

Some tasks are inherently cross-cutting: they touch shared files (import fixes,
shared definitions, diamond conflict resolution), modify files that multiple proof
agents work on, or change imports that affect the build DAG. These are called
**infrastructure tasks**.

**⛔ NEVER dispatch an infrastructure agent while proof agents are running on
files that the infrastructure agent would touch.** The infrastructure agent will
either: (a) overwrite the proof agent's uncommitted changes, or (b) break the
proof agent's build by changing imports/definitions mid-elaboration.

**The correct pattern is wave-based:**

```
Wave N proof agents run (each on their own file)
  ↓ all complete
Supervisor reads results + runs cleaning/infrastructure step
  ↓ infrastructure changes applied (imports, shared defs, diamond fixes, etc.)
  ↓ lake build passes
Wave N+1 proof agents run
```

**Infrastructure tasks include:**
- Adding/removing imports in a file
- Resolving diamond import conflicts (touches multiple files)
- Moving definitions between files (reorganization or deduplication)
- Proving shared specs or theorems (if proof agents import it)
- Changing axiom files that proof agents import

**If an infrastructure need is discovered mid-wave:** Document it, wait for all
proof agents in the current wave to complete, then do the infrastructure work
before dispatching the next wave. Do NOT try to "squeeze in" infrastructure
changes between agent completions — even if one agent finished, others may still
be running on files that import the shared file you'd modify.

### Mid-flight modification check

**Before modifying ANY file** (whether by the supervisor directly or by a new
agent), check whether any running agent's target file transitively imports it.
If so, **DO NOT modify the file** until that agent completes — modifying a
dependency invalidates the olean cache and can break the agent's build mid-work.

This applies to the **supervisor too**, not just agents. Trace the import chain
of every running agent's target file before editing any shared file (e.g.,
`grep '^import' <agent-target-file>` and recurse).

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

**Review depth and priority depends on the task:**
- **Axiom files / trust boundaries** (HIGHEST PRIORITY): Every new axiom file or
  trust boundary (e.g., hash bridge, SIMD model) MUST get a dedicated code-review
  agent **immediately after creation**, before any other work proceeds. Never mark
  an axiom-creating task as "done" until a separate reviewer has verified the axioms.
  Axiom reviews focus on mathematical correctness (see the `launching-proof-agents`
  skill file for the axiom review checklist). **Axioms are more dangerous than
  sorry's** — a sorry is an honest gap, but a wrong axiom is a silent lie that makes
  all downstream proofs vacuous.
- **Skill file edits**: reviewer checks cross-file consistency, actionability, and
  that examples match rules (see the `skill-file-authoring` skill file).
- **Proof work**: reviewer runs the full checklist (see the `launching-proof-agents`
  skill file). **The reviewer should read the modified files** (not just grep) — the
  token cost is modest (~15K tokens per file) and grep alone misses structural issues
  like multi-line inline `(by ...)` blocks and proof organization problems.
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
| **Sorry's** | Current number of `sorry` occurrences + `axiom` declarations in the file |
| **Δ** | Change in sorry/axiom count since the last status check (e.g., ↓3, ↑1, —) |
| **Modified** | Whether the file has been modified since the last status check (✏️ yes / — no) |
| **Agent** | Which agent is working on it (name + 🔄), or — if none |
| **Runtime** | How long the agent has been running (e.g., 2.3h) |
| **Build** | Whether the file builds cleanly since last modification (✅ / ❌ / ❓ unknown) |

**How to populate each column:**
- **Sorry's**: Count both `sorry` and `axiom` declarations: `grep -c 'sorry\|^axiom\|^private axiom' <file>`.
  Axioms are unproved assumptions — they are proof obligations just like `sorry`'s.
  When reporting, distinguish them: e.g., "3 (2 sorry + 1 axiom)".
  Further classify axioms into two categories:
  - **Intentional axioms**: model external/FFI functions that *cannot* be proved from
    Lean alone (e.g., RNG, AES block encryption, unsafe casts). These are permanent
    trust assumptions — track them but don't count them as proof debt.
  - **Proof-debt axioms**: axioms that *could* be theorems with more work (e.g.,
    functions axiomatized because their iterator combinators lack specs, or axioms
    with postconditions that are too weak). These are proof obligations to resolve.
  In the summary, report both: e.g., "13 total (5 sorry + 6 intentional axioms +
  2 proof-debt axioms)".
- **Δ**: Compare with the count from the previous status check (track in session state)
- **Modified**: `git diff --name-only` or compare file mtimes since last check
- **Agent**: From the agent list (`list_agents`)
- **Runtime**: From agent metadata (seconds since launch)
- **Build**: Track whether a successful `lake build <module>` has run since the file
  (or any of its transitive dependencies) was last modified. If unknown, show ❓.

Include a summary line below the table: total sorry's + axioms, total non-obsolete
obligations, notable wins (files that hit 0, big drops), and any concerns.

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
