#!/bin/bash

# Generate `lakefile.lean` from `lakefile.lean-template` plus one `lean_lib` target per test file.

cp lakefile.lean-template lakefile.lean

printf "/- File created by \`tests/lean/script.sh\`. -/\n\n" >> lakefile.lean

for entry in $(printf '%s\n' *.lean | LC_ALL=C sort -f)
do
  suffix=".lean"
  entry=${entry%"$suffix"}
  if [ "$entry" != "lakefile" ]; then
    if [ "$entry" = "SepLogic" ]; then
      # The separation-logic suite is not wired into `lake build`: several of its
      # examples are still a work in progress.  Build it with `lake build SepLogic`.
      echo "lean_lib $entry" >> lakefile.lean
    else
      echo "@[default_target] lean_lib $entry" >> lakefile.lean
    fi
  fi
done
