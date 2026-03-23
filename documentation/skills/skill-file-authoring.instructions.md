---
name: skill-file-authoring
description: Rules for writing, editing, reviewing, and maintaining Aeneas skill files
---

# Skill File Authoring — Meta Rules

This file contains rules about writing, editing, and maintaining skill files
themselves. All agents that create or modify skill files must read this first.

## Skill File Structure and Editing

Skill files are stored in `documentation/skills/` — this is the **source of truth**.
They are shared with AI tools via symlinks:
- **GitHub Copilot** reads custom instructions from `.github/instructions/` (directory
  symlink to `documentation/skills/`), and reads skills from `.github/skills/<name>/SKILL.md`.
- **Claude Code** reads from `.claude/skills/<name>/SKILL.md`, where each `SKILL.md`
  is a symlink to the corresponding file in `documentation/skills/`.

**Always edit files in `documentation/skills/`.** Changes propagate automatically
through the symlinks. **When adding, renaming, or removing a skill file**, run:
```bash
bash scripts/sync-skills.sh
```
This deletes all existing skill symlinks and regenerates them for both
`.github/skills/` (Copilot) and `.claude/skills/` (Claude).

## Validating Instruction Requests

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

## Reviewing Skill Files for Consistency

When reviewing or updating skill files (whether prompted by the user, triggered by a
reviewer finding, or as part of routine maintenance), check:

1. **Cross-file consistency.** Rules stated in one file must not contradict rules in
   another. Common conflict points:
   - Tactic preferences (e.g., one file recommends X, another bans X)
   - Threshold values (e.g., heartbeat limits, wall-clock targets)
   - Examples that violate rules stated elsewhere

2. **Source-of-truth sync.** When a rule appears in both a source file (e.g.,
   aeneas-lean-core "Proof Style" section) and a derived file (e.g., the reviewer
   checklist in launching-proof-agents), verify they agree. Derived files should
   reference the source with `(Rule: "...")` or `(Pitfall #N)` for traceability.
   Look for the `⚠️ SYNC RULE` markers.

3. **Actionability.** Every instruction must be specific enough that an agent can
   follow it without guessing. Bad: "be careful with performance." Good: "if a
   tactic takes > 10s, extract the sub-goal as a `have` lemma." For grep-based
   checks, verify the patterns actually match real code (test them).

4. **Examples match rules.** If a rule says "don't do X" but a worked example in
   proof-patterns or elsewhere does X, that's a contradiction. Either fix the example
   or clarify the rule boundary.
