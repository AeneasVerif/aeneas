#!/usr/bin/env bash
set -eo pipefail

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd -- "$script_dir/.." && pwd)"
lean_dir="$repo_root/dist_staging/backends/lean"

cd "$lean_dir"
cp "$repo_root/backends/lean/lean-toolchain" .
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
