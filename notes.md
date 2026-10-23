# Speeding up `make extract-lean-std` and `make extract-lean-keywords`

## Problem

The two scripts that regenerate OCaml files from the Lean library were slow in CI:

| Target | Script | Output | Time in CI |
|---|---|---|---|
| `make extract-lean-std` | `backends/lean/AeneasExtract.lean` | `src/extract/ExtractBuiltinLean.ml` | 8m 11s |
| `make extract-lean-keywords` | `backends/lean/ExtractLeanKeywords.lean` | `src/extract/LeanKeywords.ml` | 39s |

These timings come from the `lean` job of CI run 39803487062, on a PR that touched Lean. That job took about 15 minutes in total. Building the library and all of `tests/lean` took only 5m 42s, less than the `extract-lean-std` check alone.

## Cause

Both scripts were `lean_exe` targets run with `lake exe`. Building a native executable compiles every imported module to C and then to object code. Both scripts imported all of `Aeneas`, and therefore Mathlib.

- The CI log shows about 1,764 object files compiled for `extract`, 1,193 of them Mathlib modules, then a 20s link.
- Mathlib's cache (`lake exe cache get`) provides `.olean` files but no object files, so this compilation happened from scratch on every run.
- `extract_lean_keywords` looked cheap only because it reused the object files built just before by `extract`. Run alone, it would have paid the same cost.

None of this native code was needed. Both scripts load the `Aeneas` environment at runtime from the `.olean` files, with `importModules`. The compile-time import of `Aeneas` only made the executables bigger.

## Fix

Run both scripts in the interpreter, with `lake env lean --run`. Loading the imports from `.olean` files compiles no C.

- **`Makefile`:** both targets now run `lake exe cache get && lake build Aeneas && lake env lean --run <script>`. The explicit `lake build Aeneas` replaces the implicit build that `lake exe` did. The interpreter needs the `.olean` files of the imports, and the scripts load the full `Aeneas` environment at runtime.
- **`AeneasExtract.lean`:**
  - It imports only `Aeneas.Extract.Extract`, which depends on `Lean` and a few `AeneasMeta` modules, with no Mathlib.
  - It uses the public `Lean.enableInitializersExecution` instead of a private `@[extern "lean_enable_initializer_execution"]` declaration. The interpreter can't run that extern; it fails with "Could not find native implementation of external declaration".
- **`ExtractLeanKeywords.lean`:** `import Aeneas` became `import Lean`. The script reads the `Aeneas` environment at runtime, so the compile-time import only loaded it a second time.
- **`backends/lean/lakefile.lean`:** removed the `lean_exe extract` and `lean_exe extract_lean_keywords` targets. Nothing else referred to them.

`ci.yml` doesn't need changing, since it calls the `make` targets.

Use the `make` targets rather than running the scripts directly. The scripts write the `.ml` files unformatted, and the targets then run `cd src && dune fmt` to produce the committed layout. Running `lake env lean --run AeneasExtract.lean` on its own leaves a large, formatting-only diff in `ExtractBuiltinLean.ml`, which `dune fmt` removes. The old `lake exe extract` behaved the same way.

## Results (local)

With the library already built:

| Target | Before (CI) | After (local) |
|---|---|---|
| `make extract-lean-std` | 8m 11s | 11s |
| `make extract-lean-keywords` | 39s | 11s |

- Both generated files are byte-identical to the ones from the old executables, both with and without `CI=true`.
- Expected effect in CI: the `lean` job drops from about 15 to about 7 minutes. In CI, `lake build Aeneas` in these targets should just replay, because the earlier `lake build Aeneas AeneasMeta --wfail` step builds the library under the same settings. This hasn't been measured in a real CI run yet.

## Pitfall when measuring locally

`backends/lean/lakefile.lean` sets `precompileModules := notCI` for `AeneasMeta`. Switching between runs with and without `CI` set changes that option. That invalidates Lake's build traces and rebuilds `AeneasMeta` and everything downstream, which took about an hour here. Time the targets with a fixed `CI` setting, after a warm-up build.

## Running the two scripts in parallel

Measured with the interpreted scripts:

| | Time |
|---|---|
| Sequential | 22s |
| Parallel | 14s |

- Running them in parallel is safe. They only read the same `.olean` files, and each writes its own output file.
- Most of each script's time is spent loading the `Aeneas` environment. A single script that loads it once and writes both files would get about the same speed-up with a simpler CI step. Neither was done, since the gain is small after the interpreter change.
- With the old native executables, parallelism wouldn't have helped. Both would have needed the same object files in the same Lake workspace.
