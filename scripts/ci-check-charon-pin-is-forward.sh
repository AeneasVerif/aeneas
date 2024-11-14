#!/usr/bin/env bash
# Checks that the charon pin moves forward from the previous pin, to ensure we don't regress the Charon version.

NEW_CHARON_PIN="$(cat flake.lock | jq -r .nodes.charon.locked.rev)"
OLD_CHARON_PIN="$(git show origin/main:flake.lock | jq -r .nodes.charon.locked.rev)"
echo "This PR updates the charon pin from $OLD_CHARON_PIN to $NEW_CHARON_PIN"

git clone https://github.com/AeneasVerif/charon
cd charon

# Fetch commits in PRs
git config remote.origin.fetch "+refs/pull/*/head:refs/remotes/origin/pr/*"
git fetch --all

if ! git merge-base --is-ancestor "$OLD_CHARON_PIN" "$NEW_CHARON_PIN"; then
    echo "Error: the new charon pin does not have the old one as its ancestor. The pin must only move forward."
    exit 1
fi
