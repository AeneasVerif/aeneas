#!/usr/bin/env bash
# Checks that the charon pin:
# - moves forward from the previous pin, to ensure we don't regress the charon version;
# - is merged into Charon.

NEW_CHARON_PIN="$(cat flake.lock | jq -r .nodes.charon.locked.rev)"
OLD_CHARON_PIN="$(git show origin/main:flake.lock | jq -r .nodes.charon.locked.rev)"
echo "This PR updates the charon pin from $OLD_CHARON_PIN to $NEW_CHARON_PIN"

git clone https://github.com/AeneasVerif/charon
cd charon
CHARON_MAIN="$(git rev-parse HEAD)"

if ! git merge-base --is-ancestor "$OLD_CHARON_PIN" "$NEW_CHARON_PIN"; then
    echo "Error: the new charon pin does not have the old one as its ancestor. The pin must only move forward."
    exit 1
fi

if ! git merge-base --is-ancestor "$NEW_CHARON_PIN" "$CHARON_MAIN"; then
    echo "Error: commit $NEW_CHARON_PIN is not merged into Charon."
    exit 1
fi
