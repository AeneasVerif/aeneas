#!/usr/bin/env bash
set -eo pipefail

elan default "$(cat lean-toolchain)"

# Fetch pre-compiled Mathlib binaries.
if ! lake exe cache get; then
  echo "::warning::Mathlib cache extraction failed; continuing with source build"
fi

# Unset CI to force precompilation of modules, which is disabled by default in
# CI in lakefile.lean. This ensures releases contain the shared libraries
# required for plugin loading.
CI="" lake build

# Delete heavy dependency sources to keep the release archive small.
rm -rf .lake/packages
