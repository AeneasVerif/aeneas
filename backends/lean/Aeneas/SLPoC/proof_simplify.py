#!/usr/bin/env python3
"""Compilation-guided simplification of separation-logic proof scripts."""

from __future__ import annotations

import argparse
import difflib
import os
from dataclasses import dataclass
from pathlib import Path
import re
import subprocess
import sys
from typing import Iterable


BACKEND_ROOT = Path(__file__).resolve().parents[2]
SIMPLE_NAME = r"(?:[^\W\d]|_)[\w']*"
PLAIN_SL_STEP = re.compile(r"^(?P<indent>[ \t]*)sl_step[ \t]*(?:\r?\n|$)")
PLAIN_SL_PULL = re.compile(
    r"^(?P<indent>[ \t]*)sl_pull[ \t]+"
    rf"(?P<args>{SIMPLE_NAME}(?:[ \t]+{SIMPLE_NAME})*)"
    r"[ \t]*(?P<newline>\r?\n|$)"
)
RINTRO_KEYWORDS = {"rfl"}


@dataclass(frozen=True)
class Edit:
    start: int
    stop: int
    replacement: str
    kind: str


class LeanChecker:
    def __init__(self) -> None:
        self.runs = 0

    def check(self, source: str) -> tuple[bool, str]:
        self.runs += 1
        try:
            result = subprocess.run(
                ["lake", "env", "lean", "--stdin"],
                cwd=BACKEND_ROOT,
                input=source,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                check=False,
            )
        except OSError as error:
            raise RuntimeError(f"could not run Lean: {error}") from error
        return result.returncode == 0, result.stdout


def apply_edits(source: str, edits: Iterable[Edit]) -> str:
    result = source
    stop = len(source)
    for edit in sorted(edits, key=lambda item: item.start, reverse=True):
        if edit.stop > stop:
            raise ValueError("overlapping proof simplifications")
        result = result[: edit.start] + edit.replacement + result[edit.stop :]
        stop = edit.start
    return result


def accepted_edits(
    source: str, candidates: list[Edit], checker: LeanChecker
) -> list[Edit]:
    accepted: list[Edit] = []

    def visit(group: list[Edit]) -> None:
        if not group:
            return
        trial = apply_edits(source, [*accepted, *group])
        works, _ = checker.check(trial)
        if works:
            accepted.extend(group)
        elif len(group) > 1:
            middle = len(group) // 2
            visit(group[:middle])
            visit(group[middle:])

    visit(candidates)
    return accepted


def sl_step_candidates(source: str) -> list[Edit]:
    lines = list(re.finditer(r".*(?:\r?\n|$)", source))
    candidates: list[Edit] = []
    index = 0
    while index < len(lines):
        first = PLAIN_SL_STEP.fullmatch(lines[index].group())
        if first is None:
            index += 1
            continue
        stop_index = index + 1
        while stop_index < len(lines):
            following = PLAIN_SL_STEP.fullmatch(lines[stop_index].group())
            if following is None or following["indent"] != first["indent"]:
                break
            stop_index += 1
        if stop_index - index >= 2:
            newline = "\r\n" if lines[index].group().endswith("\r\n") else "\n"
            if not lines[stop_index - 1].group().endswith(("\n", "\r")):
                newline = ""
            candidates.append(
                Edit(
                    lines[index].start(),
                    lines[stop_index - 1].end(),
                    f"{first['indent']}sl_step*{newline}",
                    "sl_step run",
                )
            )
        index = stop_index
    return candidates


def sl_pull_drop_candidates(source: str) -> list[Edit]:
    candidates: list[Edit] = []
    for line in re.finditer(r".*(?:\r?\n|$)", source):
        match = PLAIN_SL_PULL.fullmatch(line.group())
        if match is None:
            continue
        candidates.append(
            Edit(
                line.start(),
                line.end(),
                f"{match['indent']}sl_pull{match['newline']}",
                "sl_pull arguments",
            )
        )
    return candidates


def sl_pull_anonymous_candidates(source: str) -> list[Edit]:
    candidates: list[Edit] = []
    for line in re.finditer(r".*(?:\r?\n|$)", source):
        match = PLAIN_SL_PULL.fullmatch(line.group())
        if match is None:
            continue
        args_start = line.start() + match.start("args")
        for identifier in re.finditer(SIMPLE_NAME, match["args"]):
            name = identifier.group()
            if name == "_" or name in RINTRO_KEYWORDS:
                continue
            candidates.append(
                Edit(
                    args_start + identifier.start(),
                    args_start + identifier.end(),
                    "_",
                    "unused sl_pull name",
                )
            )
    return candidates


def simplify(source: str, checker: LeanChecker) -> tuple[str, list[Edit]]:
    works, output = checker.check(source)
    if not works:
        raise ValueError(f"the input does not compile:\n{output.rstrip()}")

    all_accepted: list[Edit] = []
    for find_candidates in (
        sl_step_candidates,
        sl_pull_drop_candidates,
        sl_pull_anonymous_candidates,
    ):
        candidates = find_candidates(source)
        accepted = accepted_edits(source, candidates, checker)
        source = apply_edits(source, accepted)
        all_accepted.extend(accepted)
    return source, all_accepted


def unified_diff(path: Path, before: str, after: str) -> str:
    return "".join(
        difflib.unified_diff(
            before.splitlines(keepends=True),
            after.splitlines(keepends=True),
            fromfile=str(path),
            tofile=str(path),
        )
    )


def write_atomic(path: Path, source: str) -> None:
    temporary = path.with_name(f".{path.name}.proof-simplify-{os.getpid()}")
    try:
        temporary.write_text(source, encoding="utf-8", newline="")
        os.chmod(temporary, path.stat().st_mode)
        os.replace(temporary, path)
    finally:
        temporary.unlink(missing_ok=True)


def read_source(path: Path) -> str:
    with path.open(encoding="utf-8", newline="") as source_file:
        return source_file.read()


def parse_args(args: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Simplify sl_step and sl_pull proof scripts, retaining only changes "
            "accepted by Lean."
        )
    )
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument(
        "-i", "--in-place", action="store_true", help="rewrite each input file"
    )
    mode.add_argument(
        "--check",
        action="store_true",
        help="exit unsuccessfully if an input can be simplified",
    )
    parser.add_argument("files", nargs="+", type=Path, metavar="FILE.lean")
    return parser.parse_args(args)


def main(args: list[str]) -> int:
    options = parse_args(args)
    changed = False
    failed = False
    for path in options.files:
        checker = LeanChecker()
        try:
            before = read_source(path)
            after, edits = simplify(before, checker)
        except (OSError, RuntimeError, ValueError) as error:
            print(f"{path}: {error}", file=sys.stderr)
            failed = True
            continue

        if before == after:
            print(f"{path}: already simplified ({checker.runs} Lean runs)", file=sys.stderr)
            continue
        changed = True
        summary = ", ".join(
            f"{sum(edit.kind == kind for edit in edits)} {kind}"
            for kind in ("sl_step run", "sl_pull arguments", "unused sl_pull name")
            if any(edit.kind == kind for edit in edits)
        )
        if options.in_place:
            write_atomic(path, after)
            print(
                f"{path}: {summary} ({checker.runs} Lean runs)", file=sys.stderr
            )
        elif options.check:
            print(f"{path}: can be simplified ({summary})", file=sys.stderr)
        else:
            sys.stdout.write(unified_diff(path, before, after))
            print(
                f"{path}: {summary} ({checker.runs} Lean runs)", file=sys.stderr
            )

    if failed or (options.check and changed):
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
