#!/bin/bash

cp lakefile.lean-template lakefile.lean

for entry in *.lean
do
  suffix=".lean"
  entry=${entry%"$suffix"}
  if [ "$entry" != "lakefile" ]; then
    echo "@[default_target] lean_lib $entry" >> lakefile.lean
  fi
done
