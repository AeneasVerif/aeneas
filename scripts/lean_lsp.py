#!/usr/bin/env python3
"""Query Lean 4 proof goals via the language server.

One-shot mode (starts server, queries, exits):
    python3 lean_lsp.py <file.lean> <line> [col]
    python3 lean_lsp.py <file.lean> diagnostics
    python3 lean_lsp.py <file.lean> errors

Persistent REPL mode (keeps server running for fast incremental queries):
    python3 lean_lsp.py --repl [--json] [--fail-fast]

REPL commands:
    open <file.lean>                    Open a file (waits for elaboration)
    goal <line> [col]                   Query goal at line (1-indexed)
    edit <line> <new_content>           Replace a single line (preserves indent)
    edit_range <start> <end> <content>  Replace lines start..end inclusive (\\n for newlines)
    insert <after_line> <content>       Insert line(s) after given line (\\n for newlines, 0=prepend)
    delete <start> [end]               Delete line(s) (inclusive)
    replace "old" "new"                Find-and-replace unique occurrence (escapes: \" \\ \n \t)
    replace_all "old" "new"            Find-and-replace all occurrences
    batch_start                         Start batch mode (edits deferred, no re-elaboration)
    batch_end                           End batch, send all edits, wait for elaboration
    reread <file.lean>                  Re-read a file from disk and send update
    update                              Re-read current file from disk and send update
    save                                Write in-memory buffer to disk
    diff                                Show unified diff (disk vs in-memory)
    undo                                Revert to previous text state
    diagnostics [line]                  Show all diagnostics, optionally at a specific line
    errors                              Show only errors (severity=1)
    warnings                            Show only warnings (severity=2)
    info <line>                         Show all diagnostics at a specific line
    hover <line> <col>                  Get type/info at position
    complete <line> <col>               Get completions at position
    definition <line> <col>             Go to definition at position
    status                              Show current file status and elaboration state
    logs                                Show Lean server log messages
    sorry                               List all sorry positions in current file
    wait [line]                         Wait for elaboration (up to line, or full file)
    check                               Wait for full elaboration, return all errors/warnings
    next_error                          Wait until a new error appears (or elaboration ends)
    show [start] [end]                  Show current file with line numbers
    grep <pattern> [glob]               Search current file (or project files if glob given)
    search <pattern> [glob]             Search project .lean files (default: **/*.lean)
    cat <file> [start] [end]            Read another file with line numbers
    ls [path]                           List directory contents
    quit                                Exit

Flags:
    --json          Machine-readable JSON output (one JSON object per line on stdout)
    --fail-fast     Exit on first error (useful for scripted usage)

Environment:
    LEAN_PROJECT_ROOT   Override project root (default: auto-detect via lakefile.toml)

Examples:
    python3 lean_lsp.py MyProject/File.lean 246
    python3 lean_lsp.py --repl
    echo -e "open File.lean\\ngoal 42\\nquit" | python3 lean_lsp.py --repl --json
"""

import argparse
import json
import subprocess
import sys
import os
import time
import threading
import re
import glob as glob_mod


def _find_project_root():
    """Find the Lean project root by looking for lakefile.toml/lakefile.lean upward from cwd."""
    d = os.getcwd()
    while True:
        if os.path.exists(os.path.join(d, "lakefile.toml")) or os.path.exists(os.path.join(d, "lakefile.lean")):
            return d
        parent = os.path.dirname(d)
        if parent == d:
            return os.getcwd()
        d = parent


SEV_MAP = {1: "ERROR", 2: "WARN", 3: "INFO", 4: "HINT"}


def _normalize_diag(d):
    """Normalize a raw LSP diagnostic to a consistent format."""
    return {
        "severity": SEV_MAP.get(d.get("severity", 0), "UNKNOWN"),
        "severity_code": d.get("severity", 0),
        "line": d["range"]["start"]["line"] + 1,
        "end_line": d["range"]["end"]["line"] + 1,
        "col": d["range"]["start"]["character"],
        "end_col": d["range"]["end"]["character"],
        "message": d.get("message", ""),
    }


# ---------------------------------------------------------------------------
# Lean LSP client
# ---------------------------------------------------------------------------

class LeanLSP:
    """Low-level Lean 4 language server client over stdio."""

    def __init__(self, project_root):
        self.project_root = project_root
        self.req_id = 0
        self.proc = subprocess.Popen(
            ["lake", "serve"],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            cwd=project_root,
        )
        self.responses = {}
        self.diagnostics = {}
        self.log_messages = []
        self.file_progress = {}
        self.lock = threading.Lock()
        self.reader = threading.Thread(target=self._read_loop, daemon=True)
        self.reader.start()
        self._initialize()
        self.current_uri = None
        self.current_text = None
        self.current_path = None
        self.version = 0

    # --- Low-level transport ---

    def _send(self, msg):
        data = json.dumps(msg).encode()
        header = f"Content-Length: {len(data)}\r\n\r\n".encode()
        self.proc.stdin.write(header + data)
        self.proc.stdin.flush()

    def _read_msg(self):
        headers = {}
        while True:
            line = self.proc.stdout.readline().decode()
            if line == "\r\n" or line == "\n":
                break
            if ":" in line:
                k, v = line.split(":", 1)
                headers[k.strip()] = v.strip()
        length = int(headers.get("Content-Length", 0))
        if length == 0:
            return None
        body = self.proc.stdout.read(length)
        return json.loads(body)

    def _read_loop(self):
        while True:
            try:
                msg = self._read_msg()
                if msg is None:
                    break
                with self.lock:
                    if "id" in msg and "method" not in msg:
                        self.responses[msg["id"]] = msg
                    elif msg.get("method") == "textDocument/publishDiagnostics":
                        uri = msg["params"]["uri"]
                        self.diagnostics[uri] = msg["params"]["diagnostics"]
                    elif msg.get("method") == "window/logMessage":
                        mtype = msg["params"].get("type", 4)
                        message = msg["params"].get("message", "")
                        self.log_messages.append((mtype, message))
                    elif msg.get("method") == "$/lean/fileProgress":
                        uri = msg["params"].get("textDocument", {}).get("uri", "")
                        processing = msg["params"].get("processing", [])
                        self.file_progress[uri] = processing
                    elif msg.get("method") == "window/showMessage":
                        mtype = msg["params"].get("type", 4)
                        message = msg["params"].get("message", "")
                        self.log_messages.append((mtype, f"[showMessage] {message}"))
            except Exception:
                break

    def _request(self, method, params, timeout=120):
        self.req_id += 1
        rid = self.req_id
        self._send({"jsonrpc": "2.0", "id": rid, "method": method, "params": params})
        for _ in range(timeout * 10):
            time.sleep(0.1)
            with self.lock:
                if rid in self.responses:
                    return self.responses.pop(rid)
        return None

    def _notify(self, method, params):
        self._send({"jsonrpc": "2.0", "method": method, "params": params})

    def _initialize(self):
        self._request("initialize", {
            "processId": os.getpid(),
            "rootUri": f"file://{self.project_root}",
            "capabilities": {
                "textDocument": {
                    "hover": {"contentFormat": ["plaintext", "markdown"]},
                    "completion": {"completionItem": {"snippetSupport": False}},
                    "definition": {},
                }
            },
        })
        self._notify("initialized", {})

    # --- Elaboration status ---

    def is_file_ready(self):
        with self.lock:
            if self.current_uri not in self.file_progress:
                return False
            return len(self.file_progress[self.current_uri]) == 0

    def is_ready_until(self, line):
        """Check if elaboration has completed up to (and including) the given line (1-indexed)."""
        with self.lock:
            if self.current_uri not in self.file_progress:
                return False
            processing = self.file_progress[self.current_uri]
            if len(processing) == 0:
                return True  # fully elaborated
            # Find the earliest line still being processed
            earliest = min(r["range"]["start"]["line"] for r in processing)
            # earliest is 0-indexed; line is 1-indexed
            return line <= earliest

    def get_processing_ranges(self):
        with self.lock:
            ranges = self.file_progress.get(self.current_uri, [])
            return [{"start": r["range"]["start"]["line"] + 1,
                      "end": r["range"]["end"]["line"] + 1}
                    for r in ranges]

    def get_file_status(self):
        nlines = len(self.current_text.split("\n")) if self.current_text else 0
        return {
            "file": self.current_path,
            "version": self.version,
            "lines": nlines,
            "ready": self.is_file_ready(),
            "processing_imports": self.is_processing_imports(),
            "processing_ranges": self.get_processing_ranges(),
        }

    def is_processing_imports(self):
        """Check if we're still in the import phase (single range covering from line 1)."""
        with self.lock:
            if self.current_uri not in self.file_progress:
                return True  # no progress yet — assume still loading
            processing = self.file_progress[self.current_uri]
            if len(processing) == 0:
                return False  # fully done
            if len(processing) == 1:
                start = processing[0]["range"]["start"]["line"]
                return start == 0  # 0-indexed line 0 = file start
            return False  # multiple ranges = imports done

    def wait_ready(self, timeout=180):
        """Wait until file elaboration is complete. Returns (ready, elapsed)."""
        t0 = time.time()
        time.sleep(0.5)
        for _ in range(timeout * 10):
            if self.is_file_ready():
                return True, time.time() - t0
            time.sleep(0.1)
        return False, time.time() - t0

    def wait_until(self, line, timeout=180):
        """Wait until elaboration has completed up to the given line. Returns (ready, elapsed)."""
        t0 = time.time()
        time.sleep(0.5)
        for _ in range(timeout * 10):
            if self.is_ready_until(line):
                return True, time.time() - t0
            time.sleep(0.1)
        return False, time.time() - t0

    def wait_for_error(self, timeout=180):
        """Wait until a new error diagnostic appears or elaboration finishes.
        Returns (found_error, errors, elapsed)."""
        t0 = time.time()
        baseline_errors = set()
        for d in self.get_diagnostics(severity=1):
            key = (d["range"]["start"]["line"], d.get("message", ""))
            baseline_errors.add(key)
        time.sleep(0.5)
        for _ in range(timeout * 10):
            current_errors = self.get_diagnostics(severity=1)
            for d in current_errors:
                key = (d["range"]["start"]["line"], d.get("message", ""))
                if key not in baseline_errors:
                    return True, current_errors, time.time() - t0
            if self.is_file_ready():
                return False, current_errors, time.time() - t0
            time.sleep(0.1)
        return False, self.get_diagnostics(severity=1), time.time() - t0

    # --- File operations ---

    def open_file(self, filepath):
        """Open a file and send didOpen to the server. Returns immediately without
        waiting for full elaboration. Use wait_until(line) or wait_ready() to block."""
        abs_path = os.path.join(self.project_root, filepath) if not os.path.isabs(filepath) else filepath
        uri = f"file://{abs_path}"
        with open(abs_path) as f:
            text = f.read()
        self.version = 1
        with self.lock:
            self.file_progress.pop(uri, None)
            self.diagnostics.pop(uri, None)
        self._notify("textDocument/didOpen", {
            "textDocument": {"uri": uri, "languageId": "lean4", "version": self.version, "text": text}
        })
        self.current_uri = uri
        self.current_text = text
        self.current_path = abs_path
        # Brief pause to let the server start processing
        time.sleep(0.5)
        return uri, text

    def send_change(self, new_text):
        """Send a full-document change."""
        self.version += 1
        self.current_text = new_text
        with self.lock:
            self.file_progress.pop(self.current_uri, None)
        self._notify("textDocument/didChange", {
            "textDocument": {"uri": self.current_uri, "version": self.version},
            "contentChanges": [{"text": new_text}]
        })

    # --- Query operations ---

    def get_goal(self, line, col=4, timeout=60):
        """Query proof goal at line (1-indexed), col (0-indexed)."""
        resp = self._request("$/lean/plainGoal", {
            "textDocument": {"uri": self.current_uri},
            "position": {"line": line - 1, "character": col},
        }, timeout=timeout)
        if resp and "result" in resp and resp["result"] is not None:
            return resp["result"].get("goals", [])
        if resp and "error" in resp:
            return [f"[LSP error] {resp['error'].get('message', resp['error'])}"]
        return []

    def get_hover(self, line, col=0, timeout=30):
        """Get hover info (type, docs) at position."""
        resp = self._request("textDocument/hover", {
            "textDocument": {"uri": self.current_uri},
            "position": {"line": line - 1, "character": col},
        }, timeout=timeout)
        if resp and "result" in resp and resp["result"] is not None:
            contents = resp["result"].get("contents", {})
            if isinstance(contents, dict):
                return contents.get("value", "")
            if isinstance(contents, str):
                return contents
            return str(contents)
        if resp and "error" in resp:
            return f"[LSP error] {resp['error'].get('message', resp['error'])}"
        return None

    def get_completions(self, line, col=0, timeout=30):
        """Get completions at position. Returns list of {label, detail, kind}."""
        resp = self._request("textDocument/completion", {
            "textDocument": {"uri": self.current_uri},
            "position": {"line": line - 1, "character": col},
        }, timeout=timeout)
        if resp and "result" in resp and resp["result"] is not None:
            result = resp["result"]
            items = result if isinstance(result, list) else result.get("items", [])
            return [{"label": it.get("label", ""),
                      "detail": it.get("detail", ""),
                      "kind": it.get("kind", 0)}
                    for it in items[:50]]
        return []

    def get_definition(self, line, col=0, timeout=30):
        """Get definition location(s). Returns list of {uri, line, col}."""
        resp = self._request("textDocument/definition", {
            "textDocument": {"uri": self.current_uri},
            "position": {"line": line - 1, "character": col},
        }, timeout=timeout)
        if resp and "result" in resp and resp["result"] is not None:
            result = resp["result"]
            locs = result if isinstance(result, list) else [result]
            out = []
            for loc in locs:
                if "uri" in loc:
                    out.append({
                        "uri": loc["uri"],
                        "line": loc.get("range", {}).get("start", {}).get("line", 0) + 1,
                        "col": loc.get("range", {}).get("start", {}).get("character", 0),
                    })
                elif "targetUri" in loc:
                    out.append({
                        "uri": loc["targetUri"],
                        "line": loc.get("targetRange", {}).get("start", {}).get("line", 0) + 1,
                        "col": loc.get("targetRange", {}).get("start", {}).get("character", 0),
                    })
            return out
        return []

    def get_diagnostics(self, severity=None, line=None):
        """Return diagnostics, optionally filtered by severity (1-4) or line (1-indexed)."""
        with self.lock:
            diags = list(self.diagnostics.get(self.current_uri, []))
        if severity is not None:
            diags = [d for d in diags if d.get("severity") == severity]
        if line is not None:
            diags = [d for d in diags if d["range"]["start"]["line"] + 1 == line]
        return diags

    def get_log_messages(self, clear=False):
        with self.lock:
            msgs = list(self.log_messages)
            if clear:
                self.log_messages.clear()
        return msgs

    def close(self):
        try:
            self._request("shutdown", {}, timeout=5)
            self._notify("exit", {})
            self.proc.terminate()
        except Exception:
            pass


# ---------------------------------------------------------------------------
# Output layer
# ---------------------------------------------------------------------------

class Output:
    """Handles output formatting: JSON (one object per line) or human-readable."""

    def __init__(self, json_mode=False):
        self.json_mode = json_mode
        self.interactive = sys.stdin.isatty() and not json_mode

    def result(self, data):
        """Emit a command result to stdout."""
        if self.json_mode:
            print(json.dumps(data, ensure_ascii=False), flush=True)
        else:
            _print_human(data)
            sys.stdout.flush()

    def info(self, msg):
        """Emit a status/progress message (stderr in JSON/piped mode)."""
        if self.json_mode:
            return
        if self.interactive:
            print(msg, flush=True)
        else:
            print(msg, file=sys.stderr, flush=True)

    def read_command(self):
        """Read next command. Returns None on EOF/interrupt."""
        if self.interactive:
            try:
                return input("lean> ").strip()
            except (EOFError, KeyboardInterrupt):
                return None
        else:
            try:
                line = sys.stdin.readline()
                if not line:
                    return None
                return line.strip()
            except (EOFError, KeyboardInterrupt):
                return None


def _print_human(data):
    """Pretty-print a result dict for human consumption."""
    cmd = data.get("command", "")
    status = data.get("status", "ok")

    if status == "error":
        print(f"Error: {data.get('error', 'unknown')}")
        return

    if cmd == "open":
        print(f"Opened ({data.get('lines', '?')} lines, elaborated in {data.get('elapsed', 0):.1f}s)")
        for s in data.get("sorry_lines", []):
            print(f"  sorry at line {s['line']}: {s['text']}")
        for e in data.get("errors", []):
            print(f"  [{e['severity']}] line {e['line']}: {e['message']}")

    elif cmd == "goal":
        goals = data.get("goals", [])
        if not goals:
            print("  (no goals — proof may be complete, or file still loading)")
        else:
            for i, g in enumerate(goals):
                prefix = f"Goal {i+1}:" if len(goals) > 1 else "Goal:"
                print(f"{prefix}\n{g}")

    elif cmd in ("diagnostics", "errors", "warnings", "info"):
        diags = data.get("diagnostics", [])
        if not diags:
            print(f"  (no {cmd})")
        else:
            print(f"  {len(diags)} result(s):")
            for d in diags:
                print(f"  [{d['severity']}] line {d['line']}: {d['message']}")

    elif cmd == "edit":
        print(f"Line {data.get('line', '?')}: '{data.get('old', '')}' -> '{data.get('new', '')}'")
        _print_elab_human(data)

    elif cmd in ("edit_range", "insert", "delete", "batch_end", "replace", "replace_all"):
        print(data.get("description", cmd))
        _print_elab_human(data)

    elif cmd in ("update", "reread"):
        print(f"Re-read from disk")
        _print_elab_human(data)

    elif cmd == "save":
        print(f"Saved {data.get('file', '?')} ({data.get('lines', '?')} lines)")

    elif cmd == "diff":
        if not data.get("changed"):
            print("No changes (in-memory matches disk)")
        else:
            print(data.get("diff", ""))

    elif cmd == "undo":
        print(data.get("description", "Undone"))
        _print_elab_human(data)

    elif cmd == "status":
        print(f"  File: {data.get('file') or 'none'}")
        print(f"  Version: {data.get('version', 0)}")
        print(f"  Lines: {data.get('lines', 0)}")
        print(f"  Ready: {data.get('ready', False)}")
        pr = data.get("processing_ranges", [])
        if pr:
            print(f"  Processing: {pr}")

    elif cmd == "hover":
        c = data.get("content")
        print(c if c else "  (no information)")

    elif cmd == "complete":
        items = data.get("completions", [])
        if not items:
            print("  (no completions)")
        else:
            for it in items:
                det = f" -- {it['detail']}" if it.get("detail") else ""
                print(f"  {it['label']}{det}")

    elif cmd == "definition":
        locs = data.get("locations", [])
        if not locs:
            print("  (no definition found)")
        else:
            for loc in locs:
                print(f"  {loc.get('uri', '')} line {loc.get('line', '?')}")

    elif cmd == "logs":
        msgs = data.get("messages", [])
        if not msgs:
            print("  (no log messages)")
        else:
            for m in msgs:
                print(f"  [{m.get('level', '?')}] {m.get('message', '')}")

    elif cmd == "sorry":
        items = data.get("sorry_lines", [])
        if not items:
            print("  (no sorry found)")
        else:
            for s in items:
                print(f"  line {s['line']}: {s['text']}")

    elif cmd == "show":
        print(data.get("content", ""))

    elif cmd in ("grep", "search"):
        matches = data.get("matches", [])
        if not matches:
            print(f"  (no matches for '{data.get('pattern', '')}')")
        else:
            for m in matches:
                prefix = f"{m['file']}:" if "file" in m else ""
                print(f"  {prefix}{m['line']}: {m['text']}")
            print(f"  ({len(matches)} match(es))")

    elif cmd == "cat":
        print(data.get("content", ""))

    elif cmd == "ls":
        for e in data.get("entries", []):
            suffix = "/" if e["type"] == "dir" else ""
            print(f"  {e['name']}{suffix}")

    elif cmd == "wait":
        if data.get("ready"):
            print(f"  Ready ({data.get('elapsed', 0):.1f}s)")
            print(f"  {data.get('error_count', 0)} error(s), {data.get('warning_count', 0)} warning(s)")
        else:
            print(f"  Timed out after {data.get('elapsed', 0):.1f}s")

    elif cmd == "help":
        print(data.get("text", ""))

    else:
        print(json.dumps(data, indent=2))


def _print_elab_human(data):
    if data.get("ready"):
        print(f"  Done ({data.get('elapsed', 0):.1f}s)")
        for e in data.get("errors", []):
            print(f"  [{e['severity']}] line {e['line']}: {e['message']}")
    elif "elapsed" in data:
        print(f"  Timed out after {data['elapsed']:.1f}s (elaboration may still be running)")


# ---------------------------------------------------------------------------
# Text editing helpers
# ---------------------------------------------------------------------------

def _get_lines(lsp):
    """Get current text as a list of lines."""
    return lsp.current_text.split("\n") if lsp.current_text else []


def _set_lines(lsp, lines):
    """Join lines back and store (does NOT send to server)."""
    lsp.current_text = "\n".join(lines)


def _send_and_wait(lsp, out, timeout=120):
    """Send current text to server and wait for elaboration. Returns result dict fragment."""
    lsp.send_change(lsp.current_text)
    out.info("Waiting for re-elaboration...")
    ready, elapsed = lsp.wait_ready(timeout=timeout)
    errs = [_normalize_diag(d) for d in lsp.get_diagnostics(severity=1)]
    return {"ready": ready, "elapsed": round(elapsed, 1), "errors": errs,
            "error_count": len(errs)}


def _unescape_content(s):
    r"""Replace literal \\n with newlines."""
    return s.replace("\\n", "\n")


def _parse_quoted_string(s, pos):
    """Parse a double-quoted string starting at s[pos].
    Returns (parsed_string, next_pos) or raises ValueError on error.
    Supports escapes: \\\" \\\\  \\n  \\t"""
    if pos >= len(s) or s[pos] != '"':
        raise ValueError(f"Expected '\"' at position {pos}")
    pos += 1  # skip opening quote
    chars = []
    while pos < len(s):
        ch = s[pos]
        if ch == '\\' and pos + 1 < len(s):
            nxt = s[pos + 1]
            if nxt == '"':
                chars.append('"')
                pos += 2
            elif nxt == '\\':
                chars.append('\\')
                pos += 2
            elif nxt == 'n':
                chars.append('\n')
                pos += 2
            elif nxt == 't':
                chars.append('\t')
                pos += 2
            else:
                # Unknown escape — keep as-is
                chars.append(ch)
                pos += 1
        elif ch == '"':
            return ''.join(chars), pos + 1
        else:
            chars.append(ch)
            pos += 1
    raise ValueError("Unterminated string (missing closing '\"')")


def _parse_two_quoted_strings(args_str):
    """Parse 'replace "old" "new"' arguments.
    Returns (old_str, new_str) or (None, error_message)."""
    if not args_str:
        return None, "Missing arguments"
    s = args_str
    # Skip leading whitespace to find first quote
    pos = 0
    while pos < len(s) and s[pos] == ' ':
        pos += 1
    if pos >= len(s) or s[pos] != '"':
        return None, "Expected '\"' to start first string"
    try:
        old_str, pos = _parse_quoted_string(s, pos)
    except ValueError as e:
        return None, f"Error parsing first string: {e}"
    # Skip whitespace between strings
    while pos < len(s) and s[pos] == ' ':
        pos += 1
    if pos >= len(s) or s[pos] != '"':
        return None, "Expected '\"' to start second string"
    try:
        new_str, pos = _parse_quoted_string(s, pos)
    except ValueError as e:
        return None, f"Error parsing second string: {e}"
    # Check nothing meaningful remains
    tail = s[pos:].strip()
    if tail:
        return None, f"Unexpected content after second string: {tail[:40]}"
    return (old_str, new_str), None


def _find_match_locations(text, pattern):
    """Find all occurrences of pattern in text, return list of {line, context}."""
    matches = []
    start = 0
    lines = text.split('\n')
    while True:
        idx = text.find(pattern, start)
        if idx == -1:
            break
        # Find the line number (1-indexed)
        line_num = text[:idx].count('\n') + 1
        # Get context: the line(s) containing the match
        match_end = idx + len(pattern)
        end_line_num = text[:match_end].count('\n') + 1
        # Show the lines that contain the match
        context_lines = lines[line_num - 1 : end_line_num]
        context = '\n'.join(context_lines)
        # Truncate long contexts
        if len(context) > 120:
            context = context[:120] + "..."
        matches.append({"line": line_num, "context": context})
        start = idx + 1
    return matches


# ---------------------------------------------------------------------------
# REPL command handlers — each returns a result dict
# ---------------------------------------------------------------------------

def _cmd_open(lsp, out, args):
    if not args:
        return {"command": "open", "status": "error", "error": "Usage: open <file.lean>"}
    fp = args[0]
    out.info(f"Opening {fp} (non-blocking — use 'wait [line]' to wait for elaboration)...")
    t0 = time.time()
    try:
        uri, text = lsp.open_file(fp)
    except FileNotFoundError:
        return {"command": "open", "status": "error", "error": f"File not found: {fp}"}
    elapsed = time.time() - t0
    lines = text.split("\n")
    nlines = len(lines)
    sorry_lines = []
    for i, line in enumerate(lines, 1):
        stripped = line.strip()
        if "sorry" in stripped and not stripped.startswith("--") and not stripped.startswith("/-"):
            sorry_lines.append({"line": i, "text": stripped})
    return {"command": "open", "status": "ok", "file": fp, "lines": nlines,
            "elapsed": round(elapsed, 1), "sorry_lines": sorry_lines,
            "ready": lsp.is_file_ready(),
            "processing_imports": lsp.is_processing_imports(),
            "processing_ranges": lsp.get_processing_ranges()}


def _cmd_goal(lsp, out, args):
    if lsp.current_uri is None:
        return {"command": "goal", "status": "error", "error": "No file open"}
    if not args:
        return {"command": "goal", "status": "error", "error": "Usage: goal <line> [col]"}
    line = int(args[0])
    col = int(args[1]) if len(args) > 1 else 4
    nlines = len(_get_lines(lsp))
    if line < 1 or line > nlines:
        return {"command": "goal", "status": "error",
                "error": f"Line {line} out of range (1-{nlines})"}
    t0 = time.time()
    goals = lsp.get_goal(line, col)
    elapsed = time.time() - t0
    return {"command": "goal", "status": "ok", "line": line, "col": col,
            "goals": goals, "elapsed": round(elapsed, 1)}


def _cmd_edit(lsp, out, args_str):
    """Edit a single line. args_str = '<line> <content>'."""
    if lsp.current_text is None:
        return {"command": "edit", "status": "error", "error": "No file open"}
    parts = args_str.split(None, 1) if args_str else []
    if len(parts) < 2:
        return {"command": "edit", "status": "error", "error": "Usage: edit <line> <content>"}
    line_no = int(parts[0])
    new_content = parts[1]
    lines = _get_lines(lsp)
    if line_no < 1 or line_no > len(lines):
        return {"command": "edit", "status": "error",
                "error": f"Line {line_no} out of range (1-{len(lines)})"}
    old_line = lines[line_no - 1]
    indent = len(old_line) - len(old_line.lstrip())
    lines[line_no - 1] = " " * indent + new_content
    _set_lines(lsp, lines)
    result = _send_and_wait(lsp, out)
    result.update({"command": "edit", "status": "ok", "line": line_no,
                    "old": old_line.strip(), "new": new_content.strip()})
    return result


def _cmd_edit_range(lsp, out, args_str):
    """Replace a range of lines. args_str = '<start> <end> <content>'."""
    if lsp.current_text is None:
        return {"command": "edit_range", "status": "error", "error": "No file open"}
    parts = args_str.split(None, 2) if args_str else []
    if len(parts) < 3:
        return {"command": "edit_range", "status": "error",
                "error": "Usage: edit_range <start> <end> <content>"}
    start, end = int(parts[0]), int(parts[1])
    content = _unescape_content(parts[2])
    lines = _get_lines(lsp)
    if start < 1 or end > len(lines) or start > end:
        return {"command": "edit_range", "status": "error",
                "error": f"Range {start}-{end} invalid (file has {len(lines)} lines)"}
    new_lines = content.split("\n")
    lines[start - 1:end] = new_lines
    _set_lines(lsp, lines)
    result = _send_and_wait(lsp, out)
    result.update({"command": "edit_range", "status": "ok",
                    "start": start, "end": end, "new_line_count": len(new_lines),
                    "description": f"Replaced lines {start}-{end} with {len(new_lines)} line(s)"})
    return result


def _cmd_insert(lsp, out, args_str):
    """Insert line(s) after a given line. args_str = '<after_line> <content>'."""
    if lsp.current_text is None:
        return {"command": "insert", "status": "error", "error": "No file open"}
    parts = args_str.split(None, 1) if args_str else []
    if len(parts) < 2:
        return {"command": "insert", "status": "error",
                "error": "Usage: insert <after_line> <content>"}
    after = int(parts[0])
    content = _unescape_content(parts[1])
    lines = _get_lines(lsp)
    if after < 0 or after > len(lines):
        return {"command": "insert", "status": "error",
                "error": f"Line {after} out of range (0-{len(lines)})"}
    new_lines = content.split("\n")
    lines[after:after] = new_lines
    _set_lines(lsp, lines)
    result = _send_and_wait(lsp, out)
    result.update({"command": "insert", "status": "ok",
                    "after": after, "inserted_lines": len(new_lines),
                    "description": f"Inserted {len(new_lines)} line(s) after line {after}"})
    return result


def _cmd_delete(lsp, out, args):
    """Delete line(s). args = ['start'] or ['start', 'end']."""
    if lsp.current_text is None:
        return {"command": "delete", "status": "error", "error": "No file open"}
    if not args:
        return {"command": "delete", "status": "error",
                "error": "Usage: delete <start> [end]"}
    start = int(args[0])
    end = int(args[1]) if len(args) > 1 else start
    lines = _get_lines(lsp)
    if start < 1 or end > len(lines) or start > end:
        return {"command": "delete", "status": "error",
                "error": f"Range {start}-{end} invalid (file has {len(lines)} lines)"}
    del lines[start - 1:end]
    _set_lines(lsp, lines)
    result = _send_and_wait(lsp, out)
    result.update({"command": "delete", "status": "ok",
                    "start": start, "end": end,
                    "deleted_lines": end - start + 1,
                    "description": f"Deleted lines {start}-{end}"})
    return result


def _cmd_replace(lsp, out, args_str, batch=False):
    """Find-and-replace: replace exactly one occurrence of old_str with new_str.
    Syntax: replace "old_str" "new_str"
    Supports escapes: \\\" \\\\  \\n  \\t
    If batch=True, modifies in-memory text only (no re-elaboration)."""
    if lsp.current_text is None:
        return {"command": "replace", "status": "error", "error": "No file open"}
    parsed, err = _parse_two_quoted_strings(args_str)
    if err:
        return {"command": "replace", "status": "error",
                "error": f'Usage: replace "old_text" "new_text"  — {err}'}
    old_str, new_str = parsed
    count = lsp.current_text.count(old_str)
    if count == 0:
        return {"command": "replace", "status": "error",
                "error": "old_text not found in file",
                "old_text": old_str[:80]}
    if count > 1:
        matches = _find_match_locations(lsp.current_text, old_str)
        return {"command": "replace", "status": "error",
                "error": f"old_text found {count} times (must be unique). Add more context to disambiguate.",
                "matches": matches}
    lsp.current_text = lsp.current_text.replace(old_str, new_str, 1)
    if batch:
        return {"command": "replace", "status": "ok",
                "old_text": old_str[:80], "new_text": new_str[:80],
                "batched": True,
                "description": "Replaced 1 occurrence (batched)"}
    result = _send_and_wait(lsp, out)
    result.update({"command": "replace", "status": "ok",
                    "old_text": old_str[:80], "new_text": new_str[:80],
                    "description": "Replaced 1 occurrence"})
    return result


def _cmd_replace_all(lsp, out, args_str, batch=False):
    """Find-and-replace all occurrences of old_str with new_str.
    Syntax: replace_all "old_str" "new_str"
    If batch=True, modifies in-memory text only (no re-elaboration)."""
    if lsp.current_text is None:
        return {"command": "replace_all", "status": "error", "error": "No file open"}
    parsed, err = _parse_two_quoted_strings(args_str)
    if err:
        return {"command": "replace_all", "status": "error",
                "error": f'Usage: replace_all "old_text" "new_text"  — {err}'}
    old_str, new_str = parsed
    count = lsp.current_text.count(old_str)
    if count == 0:
        return {"command": "replace_all", "status": "error",
                "error": "old_text not found in file",
                "old_text": old_str[:80]}
    lsp.current_text = lsp.current_text.replace(old_str, new_str)
    if batch:
        return {"command": "replace_all", "status": "ok",
                "old_text": old_str[:80], "new_text": new_str[:80],
                "replacements": count, "batched": True,
                "description": f"Replaced {count} occurrence(s) (batched)"}
    result = _send_and_wait(lsp, out)
    result.update({"command": "replace_all", "status": "ok",
                    "old_text": old_str[:80], "new_text": new_str[:80],
                    "replacements": count,
                    "description": f"Replaced {count} occurrence(s)"})
    return result


def _cmd_save(lsp, out):
    """Write the current in-memory buffer to disk."""
    if lsp.current_text is None or lsp.current_path is None:
        return {"command": "save", "status": "error", "error": "No file open"}
    try:
        with open(lsp.current_path, 'w') as f:
            f.write(lsp.current_text)
    except OSError as e:
        return {"command": "save", "status": "error", "error": f"Write failed: {e}"}
    out.info(f"Saved {lsp.current_path}")
    return {"command": "save", "status": "ok", "file": lsp.current_path,
            "lines": len(lsp.current_text.split('\n'))}


def _cmd_diff(lsp, out):
    """Show unified diff between the on-disk file and the in-memory buffer."""
    if lsp.current_text is None or lsp.current_path is None:
        return {"command": "diff", "status": "error", "error": "No file open"}
    try:
        with open(lsp.current_path) as f:
            disk_text = f.read()
    except FileNotFoundError:
        return {"command": "diff", "status": "error",
                "error": f"File not found on disk: {lsp.current_path}"}
    if disk_text == lsp.current_text:
        return {"command": "diff", "status": "ok", "changed": False,
                "diff": "", "description": "No changes"}
    import difflib
    disk_lines = disk_text.splitlines(keepends=True)
    mem_lines = lsp.current_text.splitlines(keepends=True)
    diff = difflib.unified_diff(disk_lines, mem_lines,
                                fromfile="disk", tofile="buffer", lineterm="")
    diff_str = '\n'.join(diff)
    return {"command": "diff", "status": "ok", "changed": True,
            "diff": diff_str}


def _cmd_undo(lsp, out, undo_stack):
    """Restore the previous text state from the undo stack and re-elaborate."""
    if lsp.current_text is None:
        return {"command": "undo", "status": "error", "error": "No file open"}
    if not undo_stack:
        return {"command": "undo", "status": "error", "error": "Nothing to undo"}
    lsp.current_text = undo_stack.pop()
    result = _send_and_wait(lsp, out)
    result.update({"command": "undo", "status": "ok",
                    "remaining": len(undo_stack),
                    "description": f"Undone (stack depth: {len(undo_stack)})"})
    return result


def _cmd_diagnostics(lsp, args, severity=None, cmd_name="diagnostics"):
    if lsp.current_uri is None:
        return {"command": cmd_name, "status": "error", "error": "No file open"}
    line_filter = int(args[0]) if args else None
    diags = lsp.get_diagnostics(severity=severity, line=line_filter)
    return {"command": cmd_name, "status": "ok",
            "diagnostics": [_normalize_diag(d) for d in diags],
            "count": len(diags)}


def _cmd_hover(lsp, args):
    if lsp.current_uri is None:
        return {"command": "hover", "status": "error", "error": "No file open"}
    if len(args) < 2:
        return {"command": "hover", "status": "error", "error": "Usage: hover <line> <col>"}
    line, col = int(args[0]), int(args[1])
    content = lsp.get_hover(line, col)
    return {"command": "hover", "status": "ok", "line": line, "col": col,
            "content": content}


def _cmd_complete(lsp, args):
    if lsp.current_uri is None:
        return {"command": "complete", "status": "error", "error": "No file open"}
    if len(args) < 2:
        return {"command": "complete", "status": "error", "error": "Usage: complete <line> <col>"}
    line, col = int(args[0]), int(args[1])
    items = lsp.get_completions(line, col)
    return {"command": "complete", "status": "ok", "line": line, "col": col,
            "completions": items, "count": len(items)}


def _cmd_definition(lsp, args):
    if lsp.current_uri is None:
        return {"command": "definition", "status": "error", "error": "No file open"}
    if len(args) < 2:
        return {"command": "definition", "status": "error",
                "error": "Usage: definition <line> <col>"}
    line, col = int(args[0]), int(args[1])
    locs = lsp.get_definition(line, col)
    return {"command": "definition", "status": "ok", "line": line, "col": col,
            "locations": locs, "count": len(locs)}


def _cmd_status(lsp):
    if lsp.current_uri is None:
        return {"command": "status", "status": "ok", "file": None, "version": 0,
                "lines": 0, "ready": False, "processing_ranges": []}
    s = lsp.get_file_status()
    s["command"] = "status"
    s["status"] = "ok"
    return s


def _cmd_logs(lsp):
    msgs = lsp.get_log_messages(clear=True)
    log_sev = {1: "ERROR", 2: "WARN", 3: "INFO", 4: "LOG"}
    return {"command": "logs", "status": "ok",
            "messages": [{"level": log_sev.get(t, "?"), "message": m}
                         for t, m in msgs],
            "count": len(msgs)}


def _cmd_sorry(lsp):
    if lsp.current_text is None:
        return {"command": "sorry", "status": "error", "error": "No file open"}
    items = []
    for i, line in enumerate(lsp.current_text.split("\n"), 1):
        stripped = line.strip()
        if "sorry" in stripped and not stripped.startswith("--") and not stripped.startswith("/-"):
            items.append({"line": i, "text": stripped})
    return {"command": "sorry", "status": "ok", "sorry_lines": items, "count": len(items)}


def _cmd_wait(lsp, out, args):
    if lsp.current_uri is None:
        return {"command": "wait", "status": "error", "error": "No file open"}
    if args:
        line = int(args[0])
        out.info(f"Waiting for elaboration up to line {line}...")
        ready, elapsed = lsp.wait_until(line, timeout=180)
        errs = [_normalize_diag(d) for d in lsp.get_diagnostics(severity=1)
                if d.get("range", {}).get("start", {}).get("line", 0) < line]
        return {"command": "wait", "status": "ok", "ready": ready,
                "waited_until": line, "elapsed": round(elapsed, 1),
                "error_count": len(errs), "errors": errs}
    else:
        out.info("Waiting for full elaboration...")
        ready, elapsed = lsp.wait_ready(timeout=180)
        errs = lsp.get_diagnostics(severity=1)
        warns = lsp.get_diagnostics(severity=2)
        return {"command": "wait", "status": "ok", "ready": ready,
                "elapsed": round(elapsed, 1),
                "error_count": len(errs), "warning_count": len(warns)}


def _cmd_check(lsp, out):
    """Wait for full elaboration and return all errors and warnings."""
    if lsp.current_uri is None:
        return {"command": "check", "status": "error", "error": "No file open"}
    out.info("Waiting for full elaboration...")
    ready, elapsed = lsp.wait_ready(timeout=180)
    errs = [_normalize_diag(d) for d in lsp.get_diagnostics(severity=1)]
    warns = [_normalize_diag(d) for d in lsp.get_diagnostics(severity=2)]
    return {"command": "check", "status": "ok", "ready": ready,
            "elapsed": round(elapsed, 1),
            "error_count": len(errs), "errors": errs,
            "warning_count": len(warns), "warnings": warns}


def _cmd_next_error(lsp, out):
    """Wait until a new error appears or elaboration finishes with no new errors."""
    if lsp.current_uri is None:
        return {"command": "next_error", "status": "error", "error": "No file open"}
    out.info("Watching for errors...")
    found, errors, elapsed = lsp.wait_for_error(timeout=180)
    norm_errors = [_normalize_diag(d) for d in errors]
    if found:
        return {"command": "next_error", "status": "ok", "found": True,
                "elapsed": round(elapsed, 1),
                "error_count": len(norm_errors), "errors": norm_errors}
    else:
        return {"command": "next_error", "status": "ok", "found": False,
                "elapsed": round(elapsed, 1), "message": "Elaboration finished with no new errors",
                "error_count": len(norm_errors), "errors": norm_errors}


def _cmd_update(lsp, out, args, project_root):
    fp = args[0] if args else lsp.current_path
    cmd_name = "reread" if args else "update"
    if fp is None:
        return {"command": cmd_name, "status": "error", "error": "No file open"}
    abs_path = fp if os.path.isabs(fp) else os.path.join(project_root, fp)
    try:
        with open(abs_path) as f:
            new_text = f.read()
    except FileNotFoundError:
        return {"command": cmd_name, "status": "error", "error": f"File not found: {fp}"}
    lsp.send_change(new_text)
    out.info(f"Re-read {fp} from disk, waiting for re-elaboration...")
    ready, elapsed = lsp.wait_ready(timeout=120)
    errs = [_normalize_diag(d) for d in lsp.get_diagnostics(severity=1)]
    return {"command": cmd_name, "status": "ok", "file": fp,
            "ready": ready, "elapsed": round(elapsed, 1),
            "errors": errs, "error_count": len(errs)}


def _cmd_show(lsp, args_str):
    """Show current file contents with line numbers."""
    if lsp.current_text is None:
        return {"command": "show", "status": "error", "error": "No file open"}
    lines = lsp.current_text.split("\n")
    args = args_str.split() if args_str else []
    start = int(args[0]) if len(args) >= 1 else 1
    end = int(args[1]) if len(args) >= 2 else len(lines)
    start = max(1, min(start, len(lines)))
    end = max(start, min(end, len(lines)))
    output_lines = []
    for i in range(start - 1, end):
        output_lines.append(f"{i+1:>4}. {lines[i]}")
    return {"command": "show", "status": "ok", "start": start, "end": end,
            "total_lines": len(lines), "content": "\n".join(output_lines)}


def _cmd_grep(lsp, args_str, project_root):
    """Search for a pattern in the current file or project files."""
    if not args_str:
        return {"command": "grep", "status": "error",
                "error": "Usage: grep <pattern> [glob]"}
    parts = args_str.split(None, 1)
    pattern = parts[0]
    file_glob = parts[1] if len(parts) > 1 else None

    try:
        regex = re.compile(pattern, re.IGNORECASE)
    except re.error as e:
        return {"command": "grep", "status": "error", "error": f"Invalid regex: {e}"}

    if file_glob is None:
        # Search current file
        if lsp.current_text is None:
            return {"command": "grep", "status": "error", "error": "No file open"}
        matches = []
        for i, line in enumerate(lsp.current_text.split("\n"), 1):
            if regex.search(line):
                matches.append({"line": i, "text": line.strip()})
        return {"command": "grep", "status": "ok", "pattern": pattern,
                "file": lsp.current_path, "matches": matches, "count": len(matches)}
    else:
        # Search project files matching glob
        search_root = project_root
        matched_files = glob_mod.glob(os.path.join(search_root, file_glob), recursive=True)
        matches = []
        for fp in sorted(matched_files):
            try:
                with open(fp) as f:
                    for i, line in enumerate(f, 1):
                        if regex.search(line):
                            rel = os.path.relpath(fp, search_root)
                            matches.append({"file": rel, "line": i, "text": line.strip()})
            except (OSError, UnicodeDecodeError):
                continue
        return {"command": "grep", "status": "ok", "pattern": pattern,
                "glob": file_glob, "matches": matches, "count": len(matches)}


def _cmd_search(lsp, args_str, project_root):
    """Search project files for a pattern. Alias for: grep <pattern> <glob>"""
    if not args_str:
        return {"command": "search", "status": "error",
                "error": "Usage: search <pattern> [glob]  (default glob: **/*.lean)"}
    parts = args_str.split(None, 1)
    pattern = parts[0]
    file_glob = parts[1] if len(parts) > 1 else "**/*.lean"
    return _cmd_grep(lsp, f"{pattern} {file_glob}", project_root)


def _cmd_cat(project_root, args_str):
    """Read another file and display its contents."""
    if not args_str:
        return {"command": "cat", "status": "error", "error": "Usage: cat <file>"}
    parts = args_str.split(None, 1)
    fp = parts[0]
    abs_path = fp if os.path.isabs(fp) else os.path.join(project_root, fp)
    try:
        with open(abs_path) as f:
            text = f.read()
    except FileNotFoundError:
        return {"command": "cat", "status": "error", "error": f"File not found: {fp}"}
    except OSError as e:
        return {"command": "cat", "status": "error", "error": str(e)}
    lines = text.split("\n")
    # Support optional line range: cat <file> [start] [end]
    args = parts[1].split() if len(parts) > 1 else []
    start = int(args[0]) if len(args) >= 1 else 1
    end = int(args[1]) if len(args) >= 2 else len(lines)
    start = max(1, min(start, len(lines)))
    end = max(start, min(end, len(lines)))
    output_lines = []
    for i in range(start - 1, end):
        output_lines.append(f"{i+1:>4}. {lines[i]}")
    return {"command": "cat", "status": "ok", "file": fp,
            "start": start, "end": end, "total_lines": len(lines),
            "content": "\n".join(output_lines)}


def _cmd_ls(project_root, args_str):
    """List directory contents."""
    path = args_str.strip() if args_str else "."
    abs_path = path if os.path.isabs(path) else os.path.join(project_root, path)
    if not os.path.exists(abs_path):
        return {"command": "ls", "status": "error", "error": f"Path not found: {path}"}
    if os.path.isfile(abs_path):
        return {"command": "ls", "status": "ok", "path": path,
                "entries": [{"name": os.path.basename(abs_path), "type": "file"}]}
    entries = []
    try:
        for name in sorted(os.listdir(abs_path)):
            if name.startswith("."):
                continue
            full = os.path.join(abs_path, name)
            entries.append({"name": name, "type": "dir" if os.path.isdir(full) else "file"})
    except OSError as e:
        return {"command": "ls", "status": "error", "error": str(e)}
    return {"command": "ls", "status": "ok", "path": path, "entries": entries,
            "count": len(entries)}


HELP_TEXT = """\
Commands:
  open <file.lean>                    Open file (relative to project root)
  goal <line> [col]                   Query goal at line:col
  edit <line> <content>               Replace line (preserves indent)
  edit_range <start> <end> <content>  Replace lines start..end (\\n for newlines)
  insert <after_line> <content>       Insert after line (\\n for newlines, 0=prepend)
  delete <start> [end]               Delete line(s)
  replace "old" "new"                Find-and-replace unique occurrence (escapes: \" \\ \n \t)
  replace_all "old" "new"            Find-and-replace all occurrences
  batch_start                         Defer edits (no re-elaboration until batch_end)
  batch_end                           Apply deferred edits, wait for elaboration
  update                              Re-read current file from disk
  reread <file.lean>                  Re-read a file from disk
  save                                Write in-memory buffer to disk
  diff                                Show unified diff (disk vs in-memory)
  undo                                Revert to previous text state
  diagnostics [line]                  All diagnostics, optionally at a line
  errors                              Errors only (severity=1)
  warnings                            Warnings only (severity=2)
  info <line>                         All diagnostics at a specific line
  hover <line> <col>                  Type/info at position
  complete <line> <col>               Completions at position
  definition <line> <col>             Go to definition
  status                              File status and elaboration state
  logs                                Server log messages
  sorry                               List sorry positions
  wait [line]                           Wait for elaboration (up to line, or full file)
  check                                 Wait for full elaboration, return all errors/warnings
  next_error                            Wait until a new error appears (or elaboration ends)
  show [start] [end]                  Show current file with line numbers
  grep <pattern> [glob]               Search current file (or project files if glob given)
  search <pattern> [glob]             Search project .lean files (default: **/*.lean)
  cat <file> [start] [end]            Read another file with line numbers
  ls [path]                           List directory contents
  quit                                Exit"""


# ---------------------------------------------------------------------------
# REPL
# ---------------------------------------------------------------------------

def repl_mode(project_root, json_mode=False, fail_fast=False):
    out = Output(json_mode=json_mode)
    out.info(f"Lean 4 LSP REPL — project: {project_root}")
    out.info("Starting lake serve...")
    lsp = LeanLSP(project_root)
    out.info("Ready. Type 'help' for commands.\n")

    batch_mode = False
    batch_text_before = None  # Text snapshot at batch_start for undo
    undo_stack = []  # Stack of previous text states for undo
    exit_code = 0

    while True:
        raw = out.read_command()
        if raw is None:
            break
        if not raw:
            continue

        # Parse command and arguments
        split2 = raw.split(None, 1)
        cmd = split2[0].lower()
        args_str = split2[1] if len(split2) > 1 else ""
        args = args_str.split() if args_str else []

        if cmd in ("quit", "exit"):
            break

        result = None
        # Save text before any potentially mutating command for undo.
        # In batch mode, individual edits don't push — the whole batch
        # is captured at batch_start and pushed at batch_end.
        _MUTATING_CMDS = {"edit", "edit_range", "insert", "delete",
                          "replace", "replace_all", "update", "reread"}
        if cmd == "batch_end":
            text_before = batch_text_before  # Push the pre-batch snapshot
        elif batch_mode:
            text_before = None  # Don't push individual edits in batch
        elif cmd in _MUTATING_CMDS:
            text_before = lsp.current_text
        else:
            text_before = None

        try:
            if cmd == "help":
                result = {"command": "help", "status": "ok", "text": HELP_TEXT}

            elif cmd == "open":
                result = _cmd_open(lsp, out, args)

            elif cmd == "goal":
                result = _cmd_goal(lsp, out, args)

            elif cmd == "edit":
                if batch_mode:
                    # In batch: apply to in-memory text only
                    parts = args_str.split(None, 1) if args_str else []
                    if len(parts) < 2:
                        result = {"command": "edit", "status": "error",
                                  "error": "Usage: edit <line> <content>"}
                    else:
                        line_no = int(parts[0])
                        new_content = parts[1]
                        lines = _get_lines(lsp)
                        if line_no < 1 or line_no > len(lines):
                            result = {"command": "edit", "status": "error",
                                      "error": f"Line {line_no} out of range (1-{len(lines)})"}
                        else:
                            old_line = lines[line_no - 1]
                            indent = len(old_line) - len(old_line.lstrip())
                            lines[line_no - 1] = " " * indent + new_content
                            _set_lines(lsp, lines)
                            result = {"command": "edit", "status": "ok", "line": line_no,
                                      "old": old_line.strip(), "new": new_content.strip(),
                                      "batched": True}
                else:
                    result = _cmd_edit(lsp, out, args_str)

            elif cmd == "edit_range":
                if batch_mode:
                    parts = args_str.split(None, 2) if args_str else []
                    if len(parts) < 3:
                        result = {"command": "edit_range", "status": "error",
                                  "error": "Usage: edit_range <start> <end> <content>"}
                    else:
                        start, end = int(parts[0]), int(parts[1])
                        content = _unescape_content(parts[2])
                        lines = _get_lines(lsp)
                        if start < 1 or end > len(lines) or start > end:
                            result = {"command": "edit_range", "status": "error",
                                      "error": f"Range {start}-{end} invalid"}
                        else:
                            new_lines = content.split("\n")
                            lines[start - 1:end] = new_lines
                            _set_lines(lsp, lines)
                            result = {"command": "edit_range", "status": "ok",
                                      "start": start, "end": end,
                                      "new_line_count": len(new_lines), "batched": True,
                                      "description": f"Replaced lines {start}-{end} (batched)"}
                else:
                    result = _cmd_edit_range(lsp, out, args_str)

            elif cmd == "insert":
                if batch_mode:
                    parts = args_str.split(None, 1) if args_str else []
                    if len(parts) < 2:
                        result = {"command": "insert", "status": "error",
                                  "error": "Usage: insert <after_line> <content>"}
                    else:
                        after = int(parts[0])
                        content = _unescape_content(parts[1])
                        lines = _get_lines(lsp)
                        if after < 0 or after > len(lines):
                            result = {"command": "insert", "status": "error",
                                      "error": f"Line {after} out of range"}
                        else:
                            new_lines = content.split("\n")
                            lines[after:after] = new_lines
                            _set_lines(lsp, lines)
                            result = {"command": "insert", "status": "ok",
                                      "after": after, "inserted_lines": len(new_lines),
                                      "batched": True,
                                      "description": f"Inserted {len(new_lines)} line(s) (batched)"}
                else:
                    result = _cmd_insert(lsp, out, args_str)

            elif cmd == "delete":
                if batch_mode:
                    if not args:
                        result = {"command": "delete", "status": "error",
                                  "error": "Usage: delete <start> [end]"}
                    else:
                        start = int(args[0])
                        end = int(args[1]) if len(args) > 1 else start
                        lines = _get_lines(lsp)
                        if start < 1 or end > len(lines) or start > end:
                            result = {"command": "delete", "status": "error",
                                      "error": f"Range {start}-{end} invalid"}
                        else:
                            del lines[start - 1:end]
                            _set_lines(lsp, lines)
                            result = {"command": "delete", "status": "ok",
                                      "start": start, "end": end,
                                      "deleted_lines": end - start + 1, "batched": True,
                                      "description": f"Deleted lines {start}-{end} (batched)"}
                else:
                    result = _cmd_delete(lsp, out, args)

            elif cmd == "replace":
                result = _cmd_replace(lsp, out, args_str, batch=batch_mode)

            elif cmd == "replace_all":
                result = _cmd_replace_all(lsp, out, args_str, batch=batch_mode)

            elif cmd == "batch_start":
                if batch_mode:
                    result = {"command": "batch_start", "status": "error",
                              "error": "Already in batch mode"}
                elif lsp.current_text is None:
                    result = {"command": "batch_start", "status": "error",
                              "error": "No file open"}
                else:
                    batch_mode = True
                    batch_text_before = lsp.current_text  # Snapshot for undo
                    result = {"command": "batch_start", "status": "ok"}

            elif cmd == "batch_end":
                if not batch_mode:
                    result = {"command": "batch_end", "status": "error",
                              "error": "Not in batch mode"}
                else:
                    batch_mode = False
                    elab = _send_and_wait(lsp, out)
                    elab.update({"command": "batch_end", "status": "ok",
                                 "description": "Batch applied"})
                    result = elab

            elif cmd == "diagnostics":
                result = _cmd_diagnostics(lsp, args)

            elif cmd == "errors":
                result = _cmd_diagnostics(lsp, args, severity=1, cmd_name="errors")

            elif cmd == "warnings":
                result = _cmd_diagnostics(lsp, args, severity=2, cmd_name="warnings")

            elif cmd == "info":
                result = _cmd_diagnostics(lsp, args, cmd_name="info")

            elif cmd == "hover":
                result = _cmd_hover(lsp, args)

            elif cmd == "complete":
                result = _cmd_complete(lsp, args)

            elif cmd == "definition":
                result = _cmd_definition(lsp, args)

            elif cmd == "status":
                result = _cmd_status(lsp)

            elif cmd == "logs":
                result = _cmd_logs(lsp)

            elif cmd == "sorry":
                result = _cmd_sorry(lsp)

            elif cmd == "show":
                result = _cmd_show(lsp, args_str)

            elif cmd == "grep":
                result = _cmd_grep(lsp, args_str, project_root)

            elif cmd == "search":
                result = _cmd_search(lsp, args_str, project_root)

            elif cmd == "cat":
                result = _cmd_cat(project_root, args_str)

            elif cmd == "ls":
                result = _cmd_ls(project_root, args_str)

            elif cmd == "wait":
                result = _cmd_wait(lsp, out, args)

            elif cmd == "check":
                result = _cmd_check(lsp, out)

            elif cmd == "next_error":
                result = _cmd_next_error(lsp, out)

            elif cmd in ("update", "reread"):
                result = _cmd_update(lsp, out, args if cmd == "reread" else [], project_root)

            elif cmd == "save":
                result = _cmd_save(lsp, out)

            elif cmd == "diff":
                result = _cmd_diff(lsp, out)

            elif cmd == "undo":
                result = _cmd_undo(lsp, out, undo_stack)

            else:
                result = {"command": cmd, "status": "error",
                          "error": f"Unknown command: {cmd}. Type 'help' for usage."}

        except ValueError as e:
            result = {"command": cmd, "status": "error",
                      "error": f"Invalid argument: {e}"}
        except Exception as e:
            result = {"command": cmd, "status": "error",
                      "error": f"Unexpected error: {e}"}

        # Push onto undo stack if the text actually changed
        if (text_before is not None
                and result and result.get("status") == "ok"
                and lsp.current_text is not None
                and lsp.current_text != text_before):
            undo_stack.append(text_before)

        if result:
            out.result(result)
            if fail_fast and result.get("status") == "error":
                exit_code = 1
                break

    lsp.close()
    out.info("Bye.")
    return exit_code


# ---------------------------------------------------------------------------
# One-shot mode
# ---------------------------------------------------------------------------

def oneshot_mode(project_root, filepath, query, col=None, json_mode=False):
    out = Output(json_mode=json_mode)
    out.info(f"Opening {filepath}...")
    lsp = LeanLSP(project_root)
    lsp.open_file(filepath)

    if query == "diagnostics":
        lsp.wait_ready(timeout=180)
        result = _cmd_diagnostics(lsp, [])
    elif query == "errors":
        lsp.wait_ready(timeout=180)
        result = _cmd_diagnostics(lsp, [], severity=1, cmd_name="errors")
    elif query == "warnings":
        lsp.wait_ready(timeout=180)
        result = _cmd_diagnostics(lsp, [], severity=2, cmd_name="warnings")
    elif query == "logs":
        lsp.wait_ready(timeout=180)
        result = _cmd_logs(lsp)
    elif query == "sorry":
        result = _cmd_sorry(lsp)
    else:
        line = int(query)
        result = _cmd_goal(lsp, out, [str(line)] + ([str(col)] if col else []))

    out.result(result)
    lsp.close()
    return 1 if result.get("status") == "error" else 0


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description="Query Lean 4 proof goals via the language server.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("--repl", action="store_true",
                        help="Start persistent REPL mode")
    parser.add_argument("--json", action="store_true",
                        help="Machine-readable JSON output")
    parser.add_argument("--fail-fast", action="store_true",
                        help="Exit on first error (REPL mode)")
    parser.add_argument("--project-root",
                        default=os.environ.get("LEAN_PROJECT_ROOT") or _find_project_root(),
                        help="Lean project root (default: auto-detect)")
    parser.add_argument("file", nargs="?", help="Lean file to query")
    parser.add_argument("query", nargs="?",
                        help="Line number, 'diagnostics', 'errors', 'warnings', 'logs', or 'sorry'")
    parser.add_argument("col", nargs="?", type=int, help="Column (0-indexed, default: 4)")

    args = parser.parse_args()

    if args.repl:
        code = repl_mode(args.project_root, json_mode=args.json, fail_fast=args.fail_fast)
        sys.exit(code)
    elif args.file and args.query:
        code = oneshot_mode(args.project_root, args.file, args.query,
                            col=args.col, json_mode=args.json)
        sys.exit(code)
    else:
        parser.print_help()
        sys.exit(1)


if __name__ == "__main__":
    main()
