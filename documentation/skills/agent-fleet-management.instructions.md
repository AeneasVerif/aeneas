# Agent Fleet Management — Skill File

## Overview

This file contains **general rules for managing fleets of AI agents** working on a
shared codebase. All skill files that involve agent supervision (proof agents,
formalization agents, etc.) must follow these rules and reference this file rather
than duplicating them.

## Meta: Validating Instruction Requests

When the user asks to update skill files (or any agent instructions), the supervisor
must **step back and evaluate whether the proposed instruction is practical and
actionable** before applying it. Specifically:

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
   would conflict with the banned-tactics list in Aeneas projects.

**If the proposed instruction is not actionable or practical**, report this to the user
with an explanation of *why* it won't work and propose a practical alternative. For
example: "Background agents can't report mid-run — instead, I'll decompose tasks into
smaller units so each agent completes faster, giving us natural checkpoints."

Do NOT silently add instructions that agents cannot follow — this creates false
expectations and wastes prompt space.

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

### Active supervision

When an agent completes:
- **Review the result**: Did it succeed? Partially? Fail?
- **Assess the approach**: Was it sound? Should the next agent try differently?
- **Report to the user**: Surface interesting findings.

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
