#!/usr/bin/env bash
# This script checks that `./charon` contains a correctly set-up charon. Pass `--force` to execute the suggested commands.

FORCE=
if [[ "$1" == "--force" ]]; then
    FORCE=1
fi

rebuild() {
    if which nix 2> /dev/null 1>&2; then
        nix develop --command bash -c "make test"
    elif which rustup 2> /dev/null 1>&2; then
        make test
    else
        echo 'Error: Neither `rustup` nor `nix` appears to be installed. Install one or the other in order to build `charon`.'
        exit 1
    fi
}

PINNED_COMMIT="$(tail -1 charon-pin)"
if [ ! -e ./charon ]; then
    if [[ "$FORCE" == "1" ]]; then
        git clone https://github.com/AeneasVerif/charon
        cd charon && git checkout "$PINNED_COMMIT" && rebuild
        exit 0
    else
        echo 'Error: `charon` not found. Please clone the charon repository into `./charon` at the commit specified '\
             'in `./charon-pin`, or make a symlink to an existing clone of charon:'
        echo '  $ git clone https://github.com/AeneasVerif/charon'
        echo '  $ cd charon && git checkout '"$PINNED_COMMIT"' && make test'
        echo 'To do this automatically, run `make setup-charon`.'
        exit 1
    fi
fi

# If charon is a symlink, we assume it's a working copy so we won't check
# commit hashes.
CHARON_IS_SYMLINK=
if [ -L charon ]; then
    echo 'Warning: `./charon` is a symlink; we assume it is a working copy and will not check commit hashes.'
    CHARON_IS_SYMLINK=1
fi

cd charon

ACTUAL_COMMIT="$(git rev-parse HEAD)"
if [[ "$CHARON_IS_SYMLINK" != "1" && "$ACTUAL_COMMIT" != "$PINNED_COMMIT" ]]; then
    if [[ "$FORCE" == "1" ]]; then
        git fetch origin && git checkout "$PINNED_COMMIT" && rebuild
        exit 0
    else
        echo 'Error: `charon` commit is not the pinned commit. Update the charon repository to the commit specified in `./charon-pin`:'
        echo '  $ cd charon && git fetch origin && git checkout '"$PINNED_COMMIT"' && make test'
        echo 'To do this automatically, run `make setup-charon`.'
        exit 1
    fi
fi

if [[ "$FORCE" == "1" ]]; then
    rebuild
    exit 0
else
    if [ ! -f bin/charon ]; then
        echo 'Error: `./bin/charon` not found. The charon binary is needed to run aeneas tests; please build it:'
        echo '  $ cd charon && make test'
        echo 'To do this automatically, run `make setup-charon`.'
        exit 1
    fi
fi
