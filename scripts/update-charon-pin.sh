#!/usr/bin/env bash
if ! which jq 2> /dev/null 1>&2; then
    echo 'Error: command `jq` not found; please install it.'
    exit 1
fi

if [ -L charon ]; then
    echo '`./charon` is a symlink; we will use the commit there for our new pin.'
    COMMIT="$(git -C charon rev-parse HEAD)"
    nix flake lock --override-input charon "github:aeneasverif/charon/$COMMIT"
else
    echo 'Pinning the latest commit from Charon `main`'
    nix flake lock --update-input charon
fi

# Keep the commit revision in `./charon-pin` as well so that non-nix users can know which commit to use.
echo '# This is the commit from https://github.com/AeneasVerif/charon that should be used with this version of aeneas.' > ./charon-pin
jq -r .nodes.charon.locked.rev flake.lock >> ./charon-pin
