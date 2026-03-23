---
name: skill-file-authoring
description: Rules for writing, editing, reviewing, and maintaining Aeneas skill files
---

# Skill File Authoring — Meta Rules

This file contains rules about writing, editing, and maintaining skill files
themselves. All agents that create or modify skill files must read this first.

## YAML Frontmatter Requirement

Every skill file must begin with a YAML frontmatter block:

```yaml
---
name: kebab-case-name
description: One-line description of what this skill covers
---
```

Both fields are required:
- **`name`**: kebab-case identifier (e.g., `aeneas-lean-core`, `proof-patterns`)
- **`description`**: concise summary, used by Copilot CLI and Claude to decide when
  to load the skill

This is required by the Copilot CLI `/skills` mechanism (`SKILL.md` format) and by
Claude Code's skill discovery. Files without frontmatter will not be detected as skills.

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

## Keeping Derived Checklists in Sync

Some skill files contain **derived checklists** — condensed versions of rules whose
source of truth lives in another file. For example, the reviewer checklist in
`launching-proof-agents` is derived from the "Proof Style and Maintainability" section
in `aeneas-lean-core` and the "Proof Style Rules" in `aeneas-tactics-quickref`.

**Rules for derived content:**

1. **Mark derived sections** with a `⚠️ SYNC RULE` comment identifying the source:
   ```markdown
   <!-- ⚠️ SYNC RULE: source of truth is aeneas-lean-core "Proof Style and Maintainability" -->
   ```

2. **When updating a source-of-truth section**, check all files that reference it
   (search for `SYNC RULE` markers mentioning the source file) and update the
   derived versions to match.

3. **Derived content should reference the source** with `(Rule: "...")` or
   `(Pitfall #N)` for traceability, so reviewers can verify alignment.

4. **When reviewing**, re-read the source-of-truth sections to verify derived
   checklists haven't drifted.
