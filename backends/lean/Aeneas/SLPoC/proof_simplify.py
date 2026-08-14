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
PLAIN_SL_PURE = re.compile(r"^(?P<indent>[ \t]*)sl_pure[ \t]*(?:\r?\n|$)")
PLAIN_SL_STEP_STAR = re.compile(
    r"^(?P<indent>[ \t]*)sl_step\*(?:[ \t]+[0-9]+)?[ \t]*(?:\r?\n|$)"
)
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


@dataclass(frozen=True)
class RejectedEdit:
    line: int
    before: str
    replacement: str
    kind: str
    reason: str
    batch_size: int


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


def accepted_batch(
    source: str, candidates: list[Edit], checker: LeanChecker
) -> tuple[list[Edit], list[RejectedEdit]]:
    if not candidates:
        return [], []
    works, output = checker.check(apply_edits(source, candidates))
    if works:
        return candidates, []
    return [], rejected_edits(source, candidates, output)


def accepted_selectively(
    source: str, candidates: list[Edit], checker: LeanChecker
) -> tuple[list[Edit], list[RejectedEdit]]:
    accepted: list[Edit] = []
    rejected: list[RejectedEdit] = []

    def visit(group: list[Edit]) -> None:
        if not group:
            return
        works, output = checker.check(apply_edits(source, [*accepted, *group]))
        if works:
            accepted.extend(group)
        elif len(group) > 1:
            middle = len(group) // 2
            visit(group[:middle])
            visit(group[middle:])
        else:
            rejected.extend(rejected_edits(source, group, output))

    visit(candidates)
    return accepted, rejected


def first_error(output: str) -> str:
    for line in output.splitlines():
        if match := re.search(r"\berror:\s*(.*)", line):
            return match.group(1).strip()
    return "Lean rejected the rewrite"


def rejected_edits(
    source: str, candidates: list[Edit], output: str
) -> list[RejectedEdit]:
    reason = first_error(output)
    batch_size = len(candidates)
    return [
        RejectedEdit(
            line=source.count("\n", 0, edit.start) + 1,
            before="; ".join(
                line.strip()
                for line in source[edit.start : edit.stop].strip().splitlines()
            ),
            replacement=edit.replacement.strip(),
            kind=edit.kind,
            reason=reason,
            batch_size=batch_size,
        )
        for edit in candidates
    ]


def line_scope(source: str, line: re.Match[str], indent: str) -> str:
    indent_width = len(indent.expandtabs(2))
    for following in re.finditer(r".*(?:\r?\n|$)", source[line.end() :]):
        text = following.group()
        stripped = text.strip()
        if (
            not stripped
            or stripped.startswith("--")
            or stripped.startswith("/-")
            or stripped.startswith("*")
            or stripped.startswith("-/")
        ):
            continue
        leading = text[: len(text) - len(text.lstrip(" \t"))]
        if len(leading.expandtabs(2)) < indent_width:
            return source[line.end() : line.end() + following.start()]
    return source[line.end() :]


def name_occurs(source: str, name: str) -> bool:
    return re.search(
        rf"(?<![\w']){re.escape(name)}(?![\w'])", source
    ) is not None


def unused_pull_names(
    source: str, line: re.Match[str], match: re.Match[str]
) -> set[str]:
    scope = line_scope(source, line, match["indent"])
    return {
        identifier.group()
        for identifier in re.finditer(SIMPLE_NAME, match["args"])
        if identifier.group() not in RINTRO_KEYWORDS
        and identifier.group() != "_"
        and not name_occurs(scope, identifier.group())
    }


def bounded_sl_step_candidates(source: str) -> list[Edit]:
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
            count = stop_index - index
            newline = "\r\n" if lines[index].group().endswith("\r\n") else "\n"
            if not lines[stop_index - 1].group().endswith(("\n", "\r")):
                newline = ""
            candidates.append(
                Edit(
                    lines[index].start(),
                    lines[stop_index - 1].end(),
                    f"{first['indent']}sl_step* {count}{newline}",
                    "bounded sl_step run",
                )
            )
        index = stop_index
    return candidates


def generated_bound_candidates(accepted: list[Edit]) -> list[Edit]:
    candidates: list[Edit] = []
    shift = 0
    for edit in sorted(accepted, key=lambda item: item.start):
        start = edit.start + shift
        stop = start + len(edit.replacement)
        replacement = re.sub(r"\*[ \t]+[0-9]+", "*", edit.replacement, count=1)
        candidates.append(Edit(start, stop, replacement, "sl_step bound"))
        shift += len(edit.replacement) - (edit.stop - edit.start)
    return candidates


def tactic_pair_candidates(
    source: str, first_patterns: tuple[re.Pattern[str], ...],
    second_patterns: tuple[re.Pattern[str], ...]
) -> list[Edit]:
    lines = list(re.finditer(r".*(?:\r?\n|$)", source))
    candidates: list[Edit] = []
    index = 0
    while index + 1 < len(lines):
        first = next(
            (
                match
                for pattern in first_patterns
                if (match := pattern.fullmatch(lines[index].group())) is not None
            ),
            None,
        )
        if first is None:
            index += 1
            continue
        second = next(
            (
                match
                for pattern in second_patterns
                if (match := pattern.fullmatch(lines[index + 1].group())) is not None
            ),
            None,
        )
        if second is None or second["indent"] != first["indent"]:
            index += 1
            continue
        newline = "\r\n" if lines[index + 1].group().endswith("\r\n") else "\n"
        if not lines[index + 1].group().endswith(("\n", "\r")):
            newline = ""
        candidates.append(
            Edit(
                lines[index].start(),
                lines[index + 1].end(),
                f"{first['indent']}sl_step*{newline}",
                "sl_pure/sl_step pair",
            )
        )
        index += 2
    return candidates


def sl_step_pure_candidates(source: str) -> list[Edit]:
    return tactic_pair_candidates(
        source, (PLAIN_SL_STEP, PLAIN_SL_STEP_STAR), (PLAIN_SL_PURE,)
    )


def sl_pure_step_candidates(source: str) -> list[Edit]:
    return tactic_pair_candidates(
        source, (PLAIN_SL_PURE,), (PLAIN_SL_STEP, PLAIN_SL_STEP_STAR)
    )


def sl_pull_drop_candidates(source: str) -> list[Edit]:
    candidates: list[Edit] = []
    for line in re.finditer(r".*(?:\r?\n|$)", source):
        match = PLAIN_SL_PULL.fullmatch(line.group())
        if match is None:
            continue
        names = {
            identifier.group()
            for identifier in re.finditer(SIMPLE_NAME, match["args"])
            if identifier.group() not in RINTRO_KEYWORDS
            and identifier.group() != "_"
        }
        if names - unused_pull_names(source, line, match):
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
        unused = unused_pull_names(source, line, match)
        args_start = line.start() + match.start("args")
        for identifier in re.finditer(SIMPLE_NAME, match["args"]):
            name = identifier.group()
            if name not in unused:
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


def simplify(
    source: str, checker: LeanChecker
) -> tuple[str, list[Edit], list[RejectedEdit]]:
    candidate_finders = (
        sl_step_pure_candidates,
        sl_pure_step_candidates,
        sl_pull_drop_candidates,
        sl_pull_anonymous_candidates,
        bounded_sl_step_candidates,
    )
    if not any(find_candidates(source) for find_candidates in candidate_finders):
        return source, [], []

    works, output = checker.check(source)
    if not works:
        raise ValueError(f"the input does not compile:\n{output.rstrip()}")

    all_accepted: list[Edit] = []
    all_rejected: list[RejectedEdit] = []
    for find_candidates in (sl_step_pure_candidates, sl_pure_step_candidates):
        candidates = find_candidates(source)
        accepted, rejected = accepted_selectively(source, candidates, checker)
        source = apply_edits(source, accepted)
        all_accepted.extend(accepted)
        all_rejected.extend(rejected)
    for find_candidates in (sl_pull_drop_candidates, sl_pull_anonymous_candidates):
        candidates = find_candidates(source)
        accepted, rejected = accepted_batch(source, candidates, checker)
        source = apply_edits(source, accepted)
        all_accepted.extend(accepted)
        all_rejected.extend(rejected)

    candidates = bounded_sl_step_candidates(source)
    accepted, rejected = accepted_batch(source, candidates, checker)
    source = apply_edits(source, accepted)
    all_accepted.extend(accepted)
    all_rejected.extend(rejected)

    candidates = generated_bound_candidates(accepted)
    accepted, rejected = accepted_selectively(source, candidates, checker)
    source = apply_edits(source, accepted)
    all_accepted.extend(accepted)
    all_rejected.extend(rejected)
    return source, all_accepted, all_rejected


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


def report_rejections(path: Path, rejected: list[RejectedEdit]) -> None:
    if not rejected:
        return
    print(f"{path}: {len(rejected)} rejected candidate(s):", file=sys.stderr)
    for candidate in rejected:
        batch = (
            f", batch of {candidate.batch_size}"
            if candidate.batch_size > 1
            else ""
        )
        print(
            f"  line {candidate.line}: {candidate.kind}{batch}: "
            f"`{candidate.before}` -> `{candidate.replacement}` "
            f"({candidate.reason})",
            file=sys.stderr,
        )


def main(args: list[str]) -> int:
    options = parse_args(args)
    changed = False
    failed = False
    for path in options.files:
        checker = LeanChecker()
        try:
            before = read_source(path)
            after, edits, rejected = simplify(before, checker)
        except (OSError, RuntimeError, ValueError) as error:
            print(f"{path}: {error}", file=sys.stderr)
            failed = True
            continue

        if before == after:
            outcome = "no rewrites accepted" if rejected else "already simplified"
            print(f"{path}: {outcome} ({checker.runs} Lean runs)", file=sys.stderr)
            report_rejections(path, rejected)
            continue
        changed = True
        summary = ", ".join(
            f"{sum(edit.kind == kind for edit in edits)} {kind}"
            for kind in (
                "bounded sl_step run",
                "sl_step bound",
                "sl_pure/sl_step pair",
                "sl_pull arguments",
                "unused sl_pull name",
            )
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
        report_rejections(path, rejected)

    if failed or (options.check and changed):
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
