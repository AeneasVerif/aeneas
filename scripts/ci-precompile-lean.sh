#!/usr/bin/env bash
set -eo pipefail

elan default "$(cat lean-toolchain)"

# Unset CI to force precompilation of modules, which is disabled by default in
# CI in lakefile.lean. This ensures releases contain the shared libraries
# required for plugin loading.
unset CI

# Fetch pre-compiled Mathlib binaries.
if ! lake exe cache get; then
  echo "::warning::Mathlib cache extraction failed; continuing with source build"
fi

lake build

# Pack prebuilt oleans into an archive for Lake's automatic olean download.
# Users who pin to a release tag get these instead of compiling from source.
lake pack

# Delete heavy dependency sources to keep the release archive small.
rm -rf .lake/packages
