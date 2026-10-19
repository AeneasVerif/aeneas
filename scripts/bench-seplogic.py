#!/usr/bin/env python3
"""Time the files exercising the separation-logic tactics.

Run `lake build` (in backends/lean and tests/lean) first: this elaborates each file with
`lake lean FILE -- --profile` (which loads the precompiled tactic libraries, like `lake build`),
keeps the best of N runs, and prints, in milliseconds, the elaboration time (wall time minus
import), the child CPU time, and the main profiler categories.

Usage: scripts/bench-seplogic.py [-n RUNS] [--json OUT]
"""
import argparse, json, re, resource, subprocess, time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BACKEND = ROOT / "backends/lean"
TESTS = ROOT / "tests/lean"
FILES = [
    (BACKEND, "Aeneas/SepLogic/Tactic/Tests/IFrame.lean"),
    (BACKEND, "Aeneas/SepLogic/Tactic/Tests/IIntro.lean"),
    (BACKEND, "Aeneas/SepLogic/Tactic/Tests/IRewrite.lean"),
    (BACKEND, "Aeneas/SepLogic/Tactic/Tests/ISimp.lean"),
    (BACKEND, "Aeneas/Std/RawPtr.lean"),
    (BACKEND, "Aeneas/Std/Buffer.lean"),
    (BACKEND, "Aeneas/Tactic/Step/Tests/SpatialGhosts.lean"),
    (BACKEND, "Aeneas/Tactic/Step/Tests/IntroOutputs.lean"),
    (TESTS, "SepLogic/UnitTest.lean"),
    (TESTS, "SepLogic/Buffer.lean"),
    (TESTS, "SepLogic/Step.lean"),
    (TESTS, "SepLogic/Solutions.lean"),
    (TESTS, "SepLogic/TripleLiftings.lean"),
]
CATEGORIES = ["tactic execution", "interpretation", "type checking", "simp"]
LINE = re.compile(r"^\t(.+?) ([\d.]+)(ms|s)$")


def profile(cwd: Path, file: str) -> dict[str, float]:
    cpu_before = resource.getrusage(resource.RUSAGE_CHILDREN)
    start = time.monotonic()
    out = subprocess.run(["lake", "lean", file, "--", "--profile"], cwd=cwd,
                         capture_output=True, text=True)
    wall = (time.monotonic() - start) * 1000
    cpu_after = resource.getrusage(resource.RUSAGE_CHILDREN)
    if out.returncode != 0:
        raise SystemExit(f"{file} failed:\n{out.stdout}{out.stderr}")
    times = {}
    for line in out.stdout.splitlines() + out.stderr.splitlines():
        if m := LINE.match(line):
            times[m[1]] = float(m[2]) * (1000 if m[3] == "s" else 1)
    times["elab"] = wall - times.get("import", 0)
    times["cpu"] = 1000 * sum(getattr(cpu_after, f) - getattr(cpu_before, f)
                              for f in ("ru_utime", "ru_stime"))
    return times


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("-n", type=int, default=5)
    parser.add_argument("--json")
    parser.add_argument("--only", action="append", default=[],
                        help="only the files containing this substring (repeatable)")
    args = parser.parse_args()
    columns = ["elab", "cpu"] + CATEGORIES
    print(f"{'file':48}" + "".join(f"{c[:12]:>14}" for c in columns))
    results, totals = {}, dict.fromkeys(columns, 0.0)
    for cwd, file in FILES:
        if args.only and not any(s in file for s in args.only):
            continue
        runs = [profile(cwd, file) for _ in range(args.n)]
        best = min(runs, key=lambda r: r["elab"])
        results[file] = best
        for c in columns:
            totals[c] += best.get(c, 0)
        print(f"{file:48}" + "".join(f"{best.get(c, 0):>14.0f}" for c in columns))
    print(f"{'TOTAL':48}" + "".join(f"{totals[c]:>14.0f}" for c in columns))
    if args.json:
        Path(args.json).write_text(json.dumps(results, indent=1))


if __name__ == "__main__":
    main()
