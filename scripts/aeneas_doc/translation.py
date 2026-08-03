"""
Adapter for Aeneas' `translation.json` (emitted by `aeneas -emit-json`).

`translation.json` is produced by Aeneas itself (see `src/EmitJson.ml`, added in
AeneasVerif/aeneas#1009). It is the single Aeneas-side source of truth connecting
the Lean translation to the original Rust source. This module converts it into the
in-memory dict shape that `generator.py` already consumes, so the rest of the HTML
generator is unchanged.

`translation.json` is intentionally minimal. Compared to the old `-doc-info` JSON it
does NOT carry:
  - the Rust source text (`source_text`)  → we read it from `--rust-src` on demand;
  - the call graph (`callees`)            → dropped (dependency graph is edgeless);
  - Rust visibility (`is_public`)         → approximated by `is_local`
                                            (i.e. "defined in the crate being verified").

Crucially it DOES carry `lean_name` for every declaration, which lets us match Rust
declarations to their Lean `@[step]` theorems exactly (no more fuzzy name matching).

Schema reference: `src/EmitJson.ml` in the aeneas repository.
"""

import json
import os
from pathlib import Path
from typing import Optional


def load_translation(path: str) -> dict:
    """Load a raw `translation.json` file."""
    with open(path) as f:
        return json.load(f)


class _SourceReader:
    """Reads (and caches) Rust source files so we can slice out per-declaration
    snippets by line range. Falls back gracefully when the source is unavailable."""

    def __init__(self, rust_src_dir: Optional[str]):
        self.rust_src_dir = rust_src_dir
        self._cache: dict = {}

    def _read_file(self, file_path: str) -> Optional[list]:
        if file_path in self._cache:
            return self._cache[file_path]
        lines = None
        candidates = []
        if self.rust_src_dir:
            candidates.append(Path(self.rust_src_dir) / file_path)
        candidates.append(Path(file_path))
        for candidate in candidates:
            try:
                if candidate.exists():
                    lines = candidate.read_text().splitlines()
                    break
            except OSError:
                continue
        self._cache[file_path] = lines
        return lines

    def snippet(self, file_path: Optional[str],
                begin_line: Optional[int], end_line: Optional[int]) -> Optional[str]:
        """Return the source text for lines [begin_line, end_line] (1-indexed,
        inclusive), or None if it cannot be read."""
        if not file_path or not begin_line or not end_line:
            return None
        lines = self._read_file(file_path)
        if lines is None:
            return None
        begin = max(1, begin_line)
        end = min(len(lines), end_line)
        if begin > end:
            return None
        return "\n".join(lines[begin - 1:end])


def _name_parts(rust_name: str) -> list:
    """Synthesize the `name` list (used for module / short-name computation) by
    splitting the fully-qualified Rust name on `::`."""
    return [{"kind": "Ident", "name": p} for p in rust_name.split("::") if p]


def _function_to_doc_info(entry: dict, src: _SourceReader,
                          global_rust_names: set) -> dict:
    source = entry.get("source", {})
    file_path = source.get("file")
    begin_line = source.get("begin_line")
    end_line = source.get("end_line")
    is_opaque = entry.get("is_opaque", False)
    rust_name = entry.get("rust_name", "")
    return {
        "def_id": entry["def_id"],
        "name": _name_parts(rust_name),
        "name_pattern": rust_name,
        "lean_name": entry.get("lean_name"),
        "span": {
            "data": {
                "file": file_path,
                "begin_line": begin_line,
                "end_line": end_line,
            }
        },
        "source_text": src.snippet(file_path, begin_line, end_line),
        # translation.json has no visibility info; `is_local` (defined in the
        # crate being verified) is the closest available proxy.
        "is_public": entry.get("is_local", False),
        "is_opaque": is_opaque,
        "has_body": not is_opaque,
        # Global initializers are emitted as ordinary functions; flag the ones
        # whose Rust name coincides with a global so they are shown as constants.
        "is_global_initializer": rust_name in global_rust_names,
        "src": "TopLevel",
        # translation.json deliberately omits the call graph.
        "callees": [],
    }


def _type_to_doc_info(entry: dict, src: _SourceReader) -> dict:
    source = entry.get("source", {})
    file_path = source.get("file")
    begin_line = source.get("begin_line")
    end_line = source.get("end_line")
    rust_name = entry.get("rust_name", "")
    return {
        "def_id": entry["def_id"],
        "name": _name_parts(rust_name),
        "name_pattern": rust_name,
        "lean_name": entry.get("lean_name"),
        "span": {
            "data": {
                "file": file_path,
                "begin_line": begin_line,
                "end_line": end_line,
            }
        },
        "source_text": src.snippet(file_path, begin_line, end_line),
        "is_public": entry.get("is_local", False),
    }


def _global_to_doc_info(entry: dict, src: _SourceReader) -> dict:
    source = entry.get("source", {})
    file_path = source.get("file")
    begin_line = source.get("begin_line")
    end_line = source.get("end_line")
    rust_name = entry.get("rust_name", "")
    return {
        "def_id": entry["def_id"],
        "name": _name_parts(rust_name),
        "name_pattern": rust_name,
        "lean_name": entry.get("lean_name"),
        # NOTE: RustGlobal reads the span via `file_name` / `beg_line` / `end_line`
        # (distinct from the function/type keys), so emit those keys here.
        "span": {
            "data": {
                "file_name": file_path,
                "beg_line": begin_line,
                "end_line": end_line,
            }
        },
        "source_text": src.snippet(file_path, begin_line, end_line),
        "is_public": entry.get("is_local", False),
    }


def load_translation_as_doc_info(path: str,
                                 rust_src_dir: Optional[str] = None) -> dict:
    """Load `translation.json` and convert it into the `doc-info`-shaped dict that
    `generator.py` consumes (functions / types / globals + `crate_name`)."""
    raw = load_translation(path)
    src = _SourceReader(rust_src_dir)

    global_rust_names = {
        g.get("rust_name", "") for g in raw.get("globals", [])
    }

    functions = [
        _function_to_doc_info(f, src, global_rust_names)
        for f in raw.get("functions", [])
    ]
    types = [_type_to_doc_info(t, src) for t in raw.get("types", [])]
    globals_list = [_global_to_doc_info(g, src) for g in raw.get("globals", [])]

    return {
        "crate_name": raw.get("crate", "Unknown Crate"),
        "functions": functions,
        "types": types,
        "globals": globals_list,
    }
