# fork-ledger-check

## Summary

The rebase of the fork relies on its patch ledger: every fork commit carries
exactly one `Fork-Patch: <patch-name>` trailer, and every patch has a
description file `fork/patches/<patch-name>.md`. This patch checks the ledger
in CI, so that a missing trailer or a forgotten description update is noticed
in the PR rather than at the next rebase.

`fork/scripts/check-ledger.py` implements the rules and documents them in its
docstring. It has two modes:

- `pr` checks a pull request. The PR passes if its ledger is valid for
  Squash and merge (exactly one trailer at the end of the PR title and
  description) or for Rebase and merge (exactly one trailer in every
  commit, no merge commits); the job summary says which. Either way, the
  PR must add or change the description file of every patch it names, and
  no other description file. A PR based on a `dev` from before the last
  rebase gets a single violation with the command that rebases it.
- `stack` checks a whole fork stack: one trailer per commit, a description
  file for every named patch and a named patch for every description file,
  and with `--adjacent` that each patch's commits are adjacent.

The workflow `Fork ledger` (`.github/workflows/fork-ledger.yml`) runs PR mode
on PRs to `dev`, and stack mode on pushes to `dev`, on manual runs, and (with
`--adjacent`) on PRs from `dev-YYYY-MM-DD-rebased` branches. It runs on
GitHub-hosted runners without nix.

## Invariants

- The repository's default squash commit message is "Pull request title and
  description", so the trailer at the end of a PR description ends up in the
  squashed commit.
- Rebases keep the old `dev` as a branch `dev-YYYY-MM-DD` and name the new
  one `dev-YYYY-MM-DD-rebased`. The checker uses the old branches to
  recognise PRs based on a pre-rebase `dev`, and the workflow uses the new
  branch's name to check rebase PRs in stack mode.

## Tests

- None; the workflow can only be tested on GitHub. Running
  `fork/scripts/check-ledger.py stack --upstream upstream/main --head origin/dev`
  checks the current `dev`.

## Rebase notes

- The patch touches no upstream file, so conflicts are not expected.

## History

- 2026-11-16: created.
