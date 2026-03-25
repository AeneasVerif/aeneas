#!/bin/bash
# sync-skills.sh — Create skill symlinks for both Copilot CLI and Claude Code
#
# Source of truth: documentation/skills/*.instructions.md
#
# Creates:
#   .github/skills/<name>/SKILL.md  → for Copilot CLI (/skills mechanism)
#   .claude/skills/<name>/SKILL.md  → for Claude Code
#
# This script deletes ALL existing symlinks and regenerates them.
# Run from the Aeneas repo root whenever you add, rename, or remove a skill file.

set -euo pipefail

SKILLS_SRC="documentation/skills"
COPILOT_DST=".github/skills"
CLAUDE_DST=".claude/skills"

if [ ! -d "$SKILLS_SRC" ]; then
  echo "Error: $SKILLS_SRC not found. Run this from the Aeneas repo root." >&2
  exit 1
fi

# Clean and regenerate for a given destination
sync_dir() {
  local dst="$1"
  local label="$2"

  # Delete existing
  if [ -d "$dst" ]; then
    local removed=0
    for dst_dir in "$dst"/*/; do
      [ -d "$dst_dir" ] || continue
      rm -rf "$dst_dir"
      removed=$((removed + 1))
    done
    echo "[$label] Cleaned $removed existing skill dirs."
  fi

  mkdir -p "$dst"

  # Compute relative path depth from dst to repo root
  # .github/skills/<name>/SKILL.md → needs ../../../../documentation/skills/...
  # .claude/skills/<name>/SKILL.md → needs ../../../../documentation/skills/...
  local depth
  depth=$(echo "$dst" | tr '/' '\n' | wc -l | tr -d ' ')
  # +1 for the <name> subdirectory
  local prefix=""
  for _ in $(seq 1 $((depth + 1))); do
    prefix="../$prefix"
  done

  local created=0
  for src in "$SKILLS_SRC"/*.instructions.md; do
    local name
    name=$(basename "$src" .instructions.md)
    local dst_dir="$dst/$name"
    local dst_link="$dst_dir/SKILL.md"
    local rel_path="${prefix}$src"

    mkdir -p "$dst_dir"
    ln -s "$rel_path" "$dst_link"
    created=$((created + 1))
  done
  echo "[$label] Created $created symlinks."
}

sync_dir "$COPILOT_DST" "Copilot"
sync_dir "$CLAUDE_DST" "Claude"

echo
echo "Done. Verify with: ls .github/skills/ .claude/skills/"
