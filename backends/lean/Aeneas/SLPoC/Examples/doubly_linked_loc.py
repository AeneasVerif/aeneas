#!/usr/bin/env python3
"""Regenerate the doubly-linked-list relevant-LOC report in README.md."""

from __future__ import annotations

import argparse
import hashlib
import re
import sys
import urllib.request
from dataclasses import dataclass
from pathlib import Path


HERE = Path(__file__).resolve().parent
README = HERE.parent / "README.md"
LEAN_EXAMPLE = HERE / "DoublyLinkedList.lean"
LEAN_LIB = HERE / "VerusStd.lean"

# `DoublyLinkedList.lean` holds the executable definitions and then the ghost
# state, the specifications and the proofs; this header separates the two.
LEAN_SPEC_MARKER = "/-! # Ghost state, specifications and proofs"

VERUS_COMMIT = "99ae45aa8e3568ec4933d23c6573a59efcd08ca3"
VERUS_URL = (
    "https://raw.githubusercontent.com/verus-lang/verus/"
    f"{VERUS_COMMIT}/examples/doubly_linked.rs"
)
VERUS_SHA256 = "52abe834f0d6596bbaebcabb92330476707df184bb5456aeaf7c573ac01394c3"

REPORT_BEGIN = "<!-- BEGIN GENERATED DOUBLY LINKED LOC REPORT -->"
REPORT_END = "<!-- END GENERATED DOUBLY LINKED LOC REPORT -->"


@dataclass(frozen=True)
class Definition:
    name: str
    start_line: int
    loc: int


@dataclass(frozen=True)
class Comparison:
    label: str
    verus: tuple[str, ...] = ()
    lean_exec: tuple[str, ...] = ()
    lean_spec: tuple[str, ...] = ()


COMPARISONS = (
    Comparison("`Node`", ("doubly_linked_list::Node",), ("Node",)),
    Comparison(
        "`DoublyLinkedList`",
        ("doubly_linked_list::DoublyLinkedList",),
        ("DoublyLinkedList",),
    ),
    Comparison(
        "ghost state / `Cells`",
        ("doubly_linked_list::GhostState",),
        lean_spec=("DoublyLinkedList.Cells",),
    ),
    Comparison(
        "`prev_of` / `prevOf`",
        ("doubly_linked_list::DoublyLinkedList::prev_of",),
        lean_spec=("DoublyLinkedList.prevOf",),
    ),
    Comparison(
        "`next_of` / `nextOf`",
        ("doubly_linked_list::DoublyLinkedList::next_of",),
        lean_spec=("DoublyLinkedList.nextOf",),
    ),
    Comparison(
        "`well_formed_node` / `nodeAt`",
        ("doubly_linked_list::DoublyLinkedList::well_formed_node",),
        lean_spec=("DoublyLinkedList.nodeAt",),
    ),
    Comparison(
        "`well_formed` / representation predicates",
        ("doubly_linked_list::DoublyLinkedList::well_formed",),
        lean_spec=(
            "DoublyLinkedList.nodesFrom",
            "DoublyLinkedList.nodes",
            "DoublyLinkedList.wellFormed",
            "DoublyLinkedList.isList",
        ),
    ),
    Comparison(
        "`view`",
        ("doubly_linked_list::DoublyLinkedList::view",),
        lean_spec=("DoublyLinkedList.view",),
    ),
    Comparison(
        "`new`",
        ("doubly_linked_list::DoublyLinkedList::new",),
        ("DoublyLinkedList.new",),
        (
            "DoublyLinkedList.new.spec",
            "DoublyLinkedList.new.isList_spec",
        ),
    ),
    Comparison(
        "`push_empty_case` / `pushEmptyCase`",
        ("doubly_linked_list::DoublyLinkedList::push_empty_case",),
        ("DoublyLinkedList.pushEmptyCase",),
        ("DoublyLinkedList.pushEmptyCase.spec",),
    ),
    Comparison(
        "`push_back` / `pushBack`",
        ("doubly_linked_list::DoublyLinkedList::push_back",),
        ("DoublyLinkedList.pushBack",),
        (
            "DoublyLinkedList.pushBack.spec",
            "DoublyLinkedList.pushBack.isList_spec",
        ),
    ),
    Comparison(
        "`pop_back` / `popBack`",
        ("doubly_linked_list::DoublyLinkedList::pop_back",),
        ("DoublyLinkedList.popBack",),
        (
            "DoublyLinkedList.popBack.spec",
            "DoublyLinkedList.popBack.isList_spec",
        ),
    ),
    Comparison(
        "`push_front` / `pushFront`",
        ("doubly_linked_list::DoublyLinkedList::push_front",),
        ("DoublyLinkedList.pushFront",),
        (
            "DoublyLinkedList.pushFront.spec",
            "DoublyLinkedList.pushFront.isList_spec",
        ),
    ),
    Comparison(
        "`pop_front` / `popFront`",
        ("doubly_linked_list::DoublyLinkedList::pop_front",),
        ("DoublyLinkedList.popFront",),
        (
            "DoublyLinkedList.popFront.spec",
            "DoublyLinkedList.popFront.isList_spec",
        ),
    ),
    Comparison(
        "`get` (including the Lean loop)",
        ("doubly_linked_list::DoublyLinkedList::get",),
        (
            "DoublyLinkedList.getLoop",
            "DoublyLinkedList.get",
        ),
        (
            "DoublyLinkedList.getLoop.spec",
            "DoublyLinkedList.get.spec",
            "DoublyLinkedList.get.isList_spec",
        ),
    ),
    Comparison(
        "`Iterator`",
        ("doubly_linked_list::Iterator",),
        ("Iterator",),
    ),
    Comparison(
        "`Iterator::list`",
        ("doubly_linked_list::Iterator::list",),
    ),
    Comparison(
        "`Iterator::index`",
        ("doubly_linked_list::Iterator::index",),
    ),
    Comparison(
        "`Iterator::valid`",
        ("doubly_linked_list::Iterator::valid",),
        lean_spec=("Iterator.valid",),
    ),
    Comparison(
        "`Iterator::new`",
        ("doubly_linked_list::Iterator::new",),
        ("Iterator.new",),
        ("Iterator.new.spec",),
    ),
    Comparison(
        "`Iterator::value`",
        ("doubly_linked_list::Iterator::value",),
        ("Iterator.value",),
        ("Iterator.value.spec",),
    ),
    Comparison(
        "`Iterator::move_next` / `moveNext`",
        ("doubly_linked_list::Iterator::move_next",),
        ("Iterator.moveNext",),
        ("Iterator.moveNext.spec",),
    ),
    Comparison(
        "`main::run` / example",
        ("main::run",),
        lean_spec=("Example.run", "Example.run.spec"),
    ),
    Comparison("entry-point `main`", ("main",)),
)

# These local Lean lemmas play the role of Verus/vstd sequence facts,
# `PPtr`/`PointsTo` permission lookup, and tracked-map operations. They are
# separate from linked-list-specific structural lemmas and tactic tests.


def strip_comments(text: str, line_marker: str) -> list[str]:
    """Remove line and nested block comments while preserving line numbers."""
    output: list[str] = []
    block_depth = 0
    for line in text.splitlines():
        cleaned: list[str] = []
        i = 0
        in_string = False
        escaped = False
        while i < len(line):
            if block_depth:
                if line.startswith("/*", i) or line.startswith("/-", i):
                    block_depth += 1
                    i += 2
                elif line.startswith("*/", i) or line.startswith("-/", i):
                    block_depth -= 1
                    i += 2
                else:
                    i += 1
                continue

            char = line[i]
            if in_string:
                cleaned.append(char)
                if escaped:
                    escaped = False
                elif char == "\\":
                    escaped = True
                elif char == '"':
                    in_string = False
                i += 1
                continue

            if char == '"':
                in_string = True
                cleaned.append(char)
                i += 1
            elif line.startswith(line_marker, i):
                break
            elif line.startswith("/*", i) or line.startswith("/-", i):
                block_depth = 1
                i += 2
            else:
                cleaned.append(char)
                i += 1
        output.append("".join(cleaned))
    if block_depth:
        raise ValueError("unterminated block comment")
    return output


PURE_DELIMITERS = re.compile(r"^[\s,;:.(){}\[\]]+$")
# Only the boilerplate that has a Rust counterpart in `RUST_NON_CODE` is
# ignored.  `attribute` is *not*: registering a lemma with the automation is
# proof engineering, and its Verus counterparts (`#[verifier::…]`,
# `broadcast use`) are counted too.
LEAN_NON_CODE = re.compile(
    r"^(?:import|namespace|end|open|variable|variables|"
    r"section|set_option)\b"
)
RUST_NON_CODE = re.compile(r"^(?:use|mod|impl|verus)\b|^#!")


def is_relevant_line(line: str, language: str) -> bool:
    code = line.strip()
    if not code or PURE_DELIMITERS.fullmatch(code):
        return False
    if re.fullmatch(r"[·|]+", code):
        return False
    ignored = LEAN_NON_CODE if language == "lean" else RUST_NON_CODE
    return ignored.match(code) is None


LEAN_DECLARATION = re.compile(
    r"^\s*(?:@\[[^\]]+\]\s*)*"
    r"(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*"
    r"(?:abbrev|def|opaque|theorem|lemma|structure|inductive|class|instance|example)"
    r"(?:\s+([^\s(:{]+))?"
)


ATTRIBUTE_BLOCK = "<attributes:"


def declaration_count(definitions: list[Definition]) -> int:
    """Number of actual declarations, ignoring the `attribute` block entries."""
    return sum(
        1 for definition in definitions if not definition.name.startswith(ATTRIBUTE_BLOCK)
    )


def lean_definitions(text: str) -> list[Definition]:
    lines = strip_comments(text, "--")
    namespaces: list[str] = []
    starts: list[tuple[int, str]] = []

    for index, line in enumerate(lines):
        stripped = line.strip()
        namespace = re.match(r"^namespace\s+(\S+)", stripped)
        if namespace:
            namespaces.append(namespace.group(1))
            continue
        if re.match(r"^end(?:\s+\S+)?\s*$", stripped):
            if namespaces:
                namespaces.pop()
            continue

        # An `attribute` command belongs to no declaration in particular: it
        # configures the automation for the whole development.  Give it an entry
        # of its own so that it lands in the unmapped support bucket instead of
        # inflating whichever declaration happens to precede it.
        if stripped.startswith("attribute"):
            starts.append((index, f"{ATTRIBUTE_BLOCK}{index + 1}>"))
            continue

        declaration = LEAN_DECLARATION.match(line)
        if declaration:
            raw_name = declaration.group(1) or f"<example:{index + 1}>"
            qualified = ".".join((*namespaces, raw_name))
            qualified = re.sub(r"^Aeneas\.SLPoC\.", "", qualified)
            starts.append((index, qualified))

    definitions: list[Definition] = []
    for position, (start, name) in enumerate(starts):
        end = starts[position + 1][0] if position + 1 < len(starts) else len(lines)
        loc = sum(is_relevant_line(line, "lean") for line in lines[start:end])
        definitions.append(Definition(name, start + 1, loc))
    return definitions


def brace_delta(line: str) -> int:
    delta = 0
    in_string = False
    escaped = False
    for char in line:
        if in_string:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
        elif char == '"':
            in_string = True
        elif char == "{":
            delta += 1
        elif char == "}":
            delta -= 1
    return delta


def block_end(lines: list[str], start: int) -> int:
    depth = 0
    opened = False
    for index in range(start, len(lines)):
        delta = brace_delta(lines[index])
        if "{" in lines[index]:
            opened = True
        if opened:
            depth += delta
            if depth == 0:
                return index
    raise ValueError(f"unclosed Rust block starting at line {start + 1}")


RUST_DEFINITION = re.compile(
    r"^\s*(?:pub(?:\([^)]*\))?\s+)?"
    r"(?:(?:closed|open|proof|spec|exec|ghost|tracked)\s+)*"
    r"(?:(struct|enum)\s+([A-Za-z_]\w*)|fn\s+([A-Za-z_]\w*))"
)
RUST_MODULE = re.compile(r"^\s*mod\s+([A-Za-z_]\w*)\s*\{")
RUST_IMPL = re.compile(
    r"^\s*impl(?:\s*<[^{}]*?>)?\s+([A-Za-z_][A-Za-z0-9_]*)[^{}]*\{"
)


def rust_definitions(text: str) -> list[Definition]:
    lines = strip_comments(text, "//")
    modules: list[tuple[int, int, str]] = []
    impls: list[tuple[int, int, str]] = []

    for index, line in enumerate(lines):
        module = RUST_MODULE.match(line)
        if module:
            modules.append((index, block_end(lines, index), module.group(1)))
        impl = RUST_IMPL.match(line)
        if impl:
            impls.append((index, block_end(lines, index), impl.group(1)))

    definitions: list[Definition] = []
    for index, line in enumerate(lines):
        declaration = RUST_DEFINITION.match(line)
        if not declaration:
            continue
        raw_name = declaration.group(2) or declaration.group(3)
        context = [
            name
            for start, end, name in sorted(modules, key=lambda item: item[0])
            if start < index < end
        ]
        containing_impl = [
            (start, name)
            for start, end, name in impls
            if start < index < end
        ]
        if containing_impl:
            context.append(max(containing_impl)[1])
        context.append(raw_name)
        end = block_end(lines, index)
        loc = sum(is_relevant_line(item, "rust") for item in lines[index : end + 1])
        definitions.append(Definition("::".join(context), index + 1, loc))
    return definitions


def index_definitions(definitions: list[Definition], source: str) -> dict[str, Definition]:
    result: dict[str, Definition] = {}
    for definition in definitions:
        if definition.name in result:
            raise ValueError(f"duplicate {source} definition: {definition.name}")
        result[definition.name] = definition
    return result


def selected_loc(index: dict[str, Definition], names: tuple[str, ...], source: str) -> int:
    missing = [name for name in names if name not in index]
    if missing:
        raise ValueError(f"missing {source} definitions: {', '.join(missing)}")
    return sum(index[name].loc for name in names)


def fetch_verus() -> str:
    request = urllib.request.Request(
        VERUS_URL,
        headers={"User-Agent": "Aeneas-DoublyLinkedList-LOC-report"},
    )
    with urllib.request.urlopen(request, timeout=30) as response:
        data = response.read()
    digest = hashlib.sha256(data).hexdigest()
    if digest != VERUS_SHA256:
        raise ValueError(
            f"Verus source checksum mismatch: expected {VERUS_SHA256}, got {digest}"
        )
    return data.decode("utf-8")


def format_number(value: int) -> str:
    return str(value) if value else "-"


def format_lean_loc(executable: int, specification: int, bold: bool = False) -> str:
    value = f"{executable + specification} ({executable}, {specification})"
    return f"**{value}**" if bold else value


def split_lean_example(text: str) -> tuple[str, str]:
    """Split the example into its executable half and its specification half."""
    lines = text.split("\n")
    marks = [i for i, line in enumerate(lines) if line.startswith(LEAN_SPEC_MARKER)]
    if len(marks) != 1:
        raise ValueError(
            f"expected exactly one {LEAN_SPEC_MARKER!r} header in "
            f"{LEAN_EXAMPLE.name}, found {len(marks)}"
        )
    return "\n".join(lines[: marks[0]]), "\n".join(lines[marks[0] :])


def render_report(verus_text: str) -> str:
    verus_defs = rust_definitions(verus_text)
    lean_exec_text, lean_spec_text = split_lean_example(
        LEAN_EXAMPLE.read_text(encoding="utf-8")
    )
    lean_exec_defs = lean_definitions(lean_exec_text)
    lean_lib_defs = lean_definitions(LEAN_LIB.read_text(encoding="utf-8"))
    lean_spec_defs = lean_definitions(lean_spec_text)

    verus = index_definitions(verus_defs, "Verus")
    lean_exec = index_definitions(lean_exec_defs, "Lean executable")
    lean_spec = index_definitions(lean_spec_defs, "Lean specification")

    rows: list[str] = []
    mapped_verus: set[str] = set()
    mapped_exec: set[str] = set()
    mapped_spec: set[str] = set()
    for comparison in COMPARISONS:
        for names, mapped, source in (
            (comparison.verus, mapped_verus, "Verus"),
            (comparison.lean_exec, mapped_exec, "Lean executable"),
            (comparison.lean_spec, mapped_spec, "Lean specification"),
        ):
            duplicates = mapped.intersection(names)
            if duplicates:
                raise ValueError(
                    f"definitions mapped more than once for {source}: "
                    f"{', '.join(sorted(duplicates))}"
                )
            mapped.update(names)
        executable_loc = selected_loc(
            lean_exec,
            comparison.lean_exec,
            "Lean executable",
        )
        specification_loc = selected_loc(
            lean_spec,
            comparison.lean_spec,
            "Lean specification",
        )
        rows.append(
            "| "
            + " | ".join(
                (
                    comparison.label,
                    format_number(selected_loc(verus, comparison.verus, "Verus")),
                    format_lean_loc(executable_loc, specification_loc),
                )
            )
            + " |"
        )

    def total(definitions: list[Definition]) -> int:
        return sum(definition.loc for definition in definitions)

    def unmapped(
        definitions: dict[str, Definition],
        mapped: set[str],
    ) -> tuple[int, int]:
        remaining = [definition for name, definition in definitions.items() if name not in mapped]
        return declaration_count(remaining), total(remaining)

    verus_unmapped = unmapped(verus, mapped_verus)
    exec_unmapped = unmapped(lean_exec, mapped_exec)
    spec_unmapped = unmapped(lean_spec, mapped_spec)
    rows.append(
        "| Other support declarations | "
        f"{format_number(verus_unmapped[1])} | "
        f"{format_lean_loc(exec_unmapped[1], spec_unmapped[1])} |"
    )
    rows.append(
        "| **Total** | "
        f"**{total(verus_defs)}** | "
        f"{format_lean_loc(total(lean_exec_defs), total(lean_spec_defs), bold=True)} |"
    )

    source_link = (
        "https://github.com/verus-lang/verus/blob/"
        f"{VERUS_COMMIT}/examples/doubly_linked.rs"
    )
    return "\n".join(
        (
            REPORT_BEGIN,
            "",
            f"Pinned Verus source: [`{VERUS_COMMIT[:12]}`]({source_link}) "
            f"(SHA-256 `{VERUS_SHA256}`).",
            "",
            "| Source | Declarations | Relevant LOC |",
            "|---|---:|---:|",
            f"| Verus | {declaration_count(verus_defs)} | {total(verus_defs)} |",
            f"| Lean executable definitions | {declaration_count(lean_exec_defs)} | "
            f"{total(lean_exec_defs)} |",
            "| Lean ghost state, specifications and proofs | "
            f"{declaration_count(lean_spec_defs)} | {total(lean_spec_defs)} |",
            f"| **Lean example total** | "
            f"**{declaration_count(lean_exec_defs) + declaration_count(lean_spec_defs)}** | "
            f"**{total(lean_exec_defs) + total(lean_spec_defs)}** |",
            f"| `vstd` equivalent, generic and reusable (`VerusStd.lean`) | "
            f"{declaration_count(lean_lib_defs)} | {total(lean_lib_defs)} |",
            f"| Lean grand total | "
            f"{declaration_count(lean_exec_defs) + declaration_count(lean_spec_defs) + declaration_count(lean_lib_defs)} | "
            f"{total(lean_exec_defs) + total(lean_spec_defs) + total(lean_lib_defs)} |",
            "",
            "| Definition or semantic group | Verus | Lean (executable, spec/proof) |",
            "|---|---:|---:|",
            *rows,
            "",
            f"`VerusStd.lean` ({declaration_count(lean_lib_defs)} declarations, "
            f"{total(lean_lib_defs)} lines) is not compared declaration by "
            "declaration: it is the generic sequence and permission-map layer "
            "that Verus obtains from `vstd`, it does not mention the "
            "doubly-linked list, and each of its declarations names its `vstd` "
            "counterpart in its doc comment.",
            "",
            '"Other support declarations" contains '
            f"{verus_unmapped[0]} Verus, {exec_unmapped[0]} Lean executable, and "
            f"{spec_unmapped[0]} Lean specification/proof declarations not assigned "
            "to a direct cross-language correspondence above, together with the "
            "`attribute` commands that configure the automation.",
            "",
            REPORT_END,
        )
    )


def update_readme(report: str, check: bool) -> int:
    original = README.read_text(encoding="utf-8")
    pattern = re.compile(
        re.escape(REPORT_BEGIN) + r".*?" + re.escape(REPORT_END),
        re.DOTALL,
    )
    if not pattern.search(original):
        raise ValueError(f"generated report markers are missing from {README}")
    updated = pattern.sub(report, original)
    if check:
        if updated != original:
            print(f"{README} is stale; run {Path(__file__).name}", file=sys.stderr)
            return 1
        return 0
    README.write_text(updated, encoding="utf-8")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check",
        action="store_true",
        help="fail if README.md does not contain the generated report",
    )
    parser.add_argument(
        "--stdout",
        action="store_true",
        help="print the generated report instead of updating README.md",
    )
    args = parser.parse_args()

    report = render_report(fetch_verus())
    if args.stdout:
        print(report)
        return 0
    return update_readme(report, args.check)


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, UnicodeError, ValueError) as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(2)
