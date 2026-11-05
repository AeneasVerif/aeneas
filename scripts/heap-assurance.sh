#!/usr/bin/env bash
set -euo pipefail

usage() {
    echo "Usage: $0 rust NEW_OUTPUT_DIR [all|debug|release|miri]" >&2
    echo "       $0 extract NEW_OUTPUT_DIR" >&2
    echo "Extraction uses AENEAS_EXE, CHARON_EXE, TEST_RUNNER_EXE (defaults: repository bin paths)." >&2
    exit 2
}

[[ $# -ge 2 && $# -le 3 ]] || usage
mode=$1
output=$2
selection=${3:-all}
case "$mode:$selection" in
    rust:all|rust:debug|rust:release|rust:miri) ;;
    extract:all) [[ $# -eq 2 ]] || usage ;;
    *) usage ;;
esac
[[ ! -e "$output" && ! -L "$output" ]] || {
    echo "Refusing to overwrite existing output: $output" >&2
    exit 2
}
root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)

if [[ "$mode" == extract ]]; then
    aeneas=$(realpath -- "${AENEAS_EXE:-$root/bin/aeneas}")
    charon=$(realpath -- "${CHARON_EXE:-$root/charon/bin/charon}")
    runner=$(realpath -- "${TEST_RUNNER_EXE:-$root/bin/test_runner}")
    for executable in "$aeneas" "$charon" "$runner"; do
        [[ -x "$executable" ]] || { echo "Missing executable: $executable" >&2; exit 1; }
    done
fi

# Copy the fixture tree so extraction diagnostics and emissions cannot overwrite
# checked-in adaptations. Keep the output for inspection rather than deleting it.
mkdir -p -- "$output/tests/src/doubly_linked" "$output/tests/lean"
output=$(cd -- "$output" && pwd)
for fixture in raw_ryu_mwe raw_zmij_mwe raw_memory_views doubly_linked; do
    cp -- "$root/tests/src/$fixture.rs" "$output/tests/src/"
done
for source in raw safe tests; do
    cp -- "$root/tests/src/doubly_linked/$source.rs" "$output/tests/src/doubly_linked/"
done
cd -- "$output"

if [[ "$mode" == extract ]]; then
    for fixture in raw_ryu_mwe raw_zmij_mwe raw_memory_views doubly_linked; do
        "$runner" "$charon" "$aeneas" tests/llbc "tests/src/$fixture.rs" -checks
    done
    echo "Extraction expectations passed: Ryu/Zmij/memory views failed as marked; list emitted."
    echo "Inspect $output/tests/{src,llbc,lean}; this does not verify emitted Lean."
else
    cat > Cargo.toml <<'EOF'
[package]
name = "heap-assurance"
version = "0.1.0"
edition = "2021"

[[test]]
name = "ryu"
path = "tests/src/raw_ryu_mwe.rs"

[[test]]
name = "zmij"
path = "tests/src/raw_zmij_mwe.rs"

[[test]]
name = "memory"
path = "tests/src/raw_memory_views.rs"

[[test]]
name = "list"
path = "tests/src/doubly_linked.rs"
EOF
    export RUSTFLAGS="${RUSTFLAGS:+$RUSTFLAGS }-Dwarnings"
    cargo --version
    rustc --version
    if [[ "$selection" == all || "$selection" == debug ]]; then cargo test --quiet; fi
    if [[ "$selection" == all || "$selection" == release ]]; then cargo test --quiet --release; fi
    if [[ "$selection" == all || "$selection" == miri ]]; then cargo miri test --quiet; fi
    echo "Rust $selection checks passed; harness and artifacts retained in $output."
fi
