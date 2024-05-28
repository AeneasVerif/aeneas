#!/usr/bin/env bash
if ! which jq 2> /dev/null 1>&2; then
    echo 'Error: command `jq` not found; please install it.'
    exit 1
fi
echo '# This is the commit from https://github.com/AeneasVerif/charon that should be used with this version of aeneas.' > ./charon-pin
jq -r .nodes.charon.locked.rev flake.lock >> ./charon-pin
