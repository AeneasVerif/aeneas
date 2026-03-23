#!/bin/bash
# sync-claude-skills.sh — Create Claude Code symlinks for all skill files
#
# Claude Code reads skills from .claude/skills/<name>/SKILL.md.
# The source of truth is documentation/skills/*.instructions.md.
# This script deletes ALL existing symlinks and regenerates them.
#
# Run this script from the Aeneas repo root whenever you add, rename,
# or remove a skill file.

set -euo pipefail

SKILLS_SRC="documentation/skills"
SKILLS_DST=".claude/skills"

if [ ! -d "$SKILLS_SRC" ]; then
  echo "Error: $SKILLS_SRC not found. Run this from the Aeneas repo root." >&2
  exit 1
fi

# Delete all existing skill symlink dirs
if [ -d "$SKILLS_DST" ]; then
  removed=0
  for dst_dir in "$SKILLS_DST"/*/; do
    [ -d "$dst_dir" ] || continue
    rm -rf "$dst_dir"
    removed=$((removed + 1))
  done
  echo "Cleaned $removed existing skill dirs."
fi

mkdir -p "$SKILLS_DST"

# Recreate symlinks for all current skill files
created=0
for src in "$SKILLS_SRC"/*.instructions.md; do
  name=$(basename "$src" .instructions.md)
  dst_dir="$SKILLS_DST/$name"
  dst_link="$dst_dir/SKILL.md"
  rel_path="../../../$src"

  mkdir -p "$dst_dir"
  ln -s "$rel_path" "$dst_link"
  echo "✓ $name"
  created=$((created + 1))
done

echo
echo "Done: $created symlinks created."
