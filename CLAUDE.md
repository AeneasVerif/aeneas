# Aeneas — Lean Backend

Aeneas translates Rust programs to pure Lean code for formal verification.

## Key Documentation

- `documentation/getting-started.md` — **Start here:** Rust → LLBC → Lean → first proof
- `documentation/aeneas-overview.md` — How Aeneas works, translation model, workflow
- `documentation/proof-strategies.md` — Proof strategies (progress, loops, decomposition, specs)
- `documentation/tactics-reference.md` — All tactics with docstrings and examples
- `documentation/crypto-verification.md` — Crypto verification guide (ML-KEM/Kyber patterns)
- `documentation/tips-and-tricks.md` — Pitfalls, tips, and tricks
- `documentation/lean-lsp-tool.md` — The `lean_lsp.py` tool for incremental proof development

- `documentation/glossary.md` — Glossary of Aeneas-specific terms

## Critical: Use lean_lsp.py for Lean Proofs

When working on Lean proofs, **always** start a `lean_lsp.py` REPL session for incremental checking and goal inspection:

```bash
python3 scripts/lean_lsp.py --repl --json
```

See `documentation/skills/lean-lsp-tool.md` for full usage.

## Conventions

- Prefer `agrind` over `grind` (grind calls tend to explode)
- Never use deprecated tactics: `fsimp`, `fsimp_all`, `Brute`, `saturate`, `ReduceZMod`
- Specifications are always pure (never in the Result monad)
- Tag specs with `@[progress]` for automation
- Use `#setup_aeneas_simps` at the top of proof files

## Note on Skill Discovery

Skills are stored in `documentation/skills/` and symlinked to:
- `.claude/skills/` (for Claude Code)
- `.github/instructions/` (for GitHub Copilot)

If skills aren't loading automatically, read them directly from `documentation/skills/`.
