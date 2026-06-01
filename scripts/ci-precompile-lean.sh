#!/usr/bin/env bash
set -eo pipefail

if [[ $# -ne 2 ]]; then
  echo "usage: $0 SOURCE_LEAN_DIR TARGET_LEAN_DIR" >&2
  exit 2
fi

source_dir="$(cd "$1" && pwd)"
target_dir="$(cd "$2" && pwd)"

cd "$target_dir"
cp "$source_dir/lean-toolchain" .
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
