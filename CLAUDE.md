# Aeneas — Lean Backend

Aeneas translates Rust programs to pure Lean code for formal verification.

## Skill Files

All detailed instructions for AI agents live in `documentation/skills/`. These are
the **source of truth** — they are symlinked to `.github/instructions/` (for GitHub
Copilot) and `.claude/skills/` (for Claude Code). **Always edit files in
`documentation/skills/`**; changes propagate automatically through the symlinks.

| Skill file | Covers |
|---|---|
| `aeneas-compiler-dev` | Dev workflow, formatting, tests, error macros, **skill file structure**, **build rules** |
| `aeneas-lean-core` | Translation model, spec patterns, tactic reference, pitfalls |
| `aeneas-tactics-quickref` | Tactic decision tree, banned tactics, combinations |
| `lean-lsp-mcp` | lean-lsp-mcp MCP tools for interactive proof development |
| `launching-proof-agents` | Multi-agent proof orchestration, review gates |
| `verification-campaigns` | Planning and executing large verification campaigns |
| `proof-patterns` | Worked proof examples (loops, dot products, comparisons) |
| `aeneas-crypto-verification` | Crypto-specific proof strategies (Montgomery, NTT, etc.) |

## Key Documentation

- `documentation/getting-started.md` — **Start here:** Rust → LLBC → Lean → first proof
- `documentation/aeneas-overview.md` — How Aeneas works, translation model, workflow
- `documentation/proof-strategies.md` — Proof strategies (step, loops, decomposition, specs)
- `documentation/tactics-reference.md` — All tactics with docstrings and examples
- `documentation/crypto-verification.md` — Crypto verification guide (ML-KEM/Kyber patterns)
- `documentation/tips-and-tricks.md` — Pitfalls, tips, and tricks
- `documentation/glossary.md` — Glossary of Aeneas-specific terms
