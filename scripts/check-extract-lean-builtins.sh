#!/usr/bin/env bash
# Check that the extraction of Lean builtins is in sync with Aeneas' Lean stdlib

make extract-lean-std-cached
if ! git diff --quiet src/extract/; then
  echo 'ERROR: Lean builtins extraction does not match Aeneas Lean std library. Run `make extract-lean-std` to regenerate ExtractBuiltinLean.ml.'
  exit 1
fi
