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
    batch_start                         Start batch mode (edits deferred, no re-elaboration)
    batch_end                           End batch, send all edits, wait for elaboration
    replace <file.lean>                 Re-read a file from disk and send update
    update                              Re-read current file from disk and send update
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
    wait                                Wait for elaboration to finish
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
            "processing_ranges": self.get_processing_ranges(),
        }

    def wait_ready(self, timeout=180):
        """Wait until file elaboration is complete. Returns (ready, elapsed)."""
        t0 = time.time()
        time.sleep(0.5)
        for _ in range(timeout * 10):
            if self.is_file_ready():
                return True, time.time() - t0
            time.sleep(0.1)
        return False, time.time() - t0

    # --- File operations ---

    def open_file(self, filepath):
        """Open a file and wait for elaboration. Returns (uri, text)."""
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
        ready, elapsed = self.wait_ready(timeout=180)
        if not ready:
            for _ in range(60):
                time.sleep(0.5)
                r = self._request("$/lean/plainGoal", {
                    "textDocument": {"uri": uri},
                    "position": {"line": 0, "character": 0},
                }, timeout=5)
                if r is not None:
                    break
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
            print(f"  sorry at line {s}")
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

    elif cmd in ("edit_range", "insert", "delete", "batch_end"):
        print(data.get("description", cmd))
        _print_elab_human(data)

    elif cmd in ("update", "replace"):
        print(f"Re-read from disk")
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


# ---------------------------------------------------------------------------
# REPL command handlers — each returns a result dict
# ---------------------------------------------------------------------------

def _cmd_open(lsp, out, args):
    if not args:
        return {"command": "open", "status": "error", "error": "Usage: open <file.lean>"}
    fp = args[0]
    out.info(f"Opening {fp}...")
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
            sorry_lines.append(i)
    errs = [_normalize_diag(d) for d in lsp.get_diagnostics(severity=1)]
    return {"command": "open", "status": "ok", "file": fp, "lines": nlines,
            "elapsed": round(elapsed, 1), "sorry_lines": sorry_lines,
            "errors": errs, "error_count": len(errs)}


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


def _cmd_wait(lsp, out):
    if lsp.current_uri is None:
        return {"command": "wait", "status": "error", "error": "No file open"}
    out.info("Waiting for elaboration...")
    ready, elapsed = lsp.wait_ready(timeout=180)
    errs = lsp.get_diagnostics(severity=1)
    warns = lsp.get_diagnostics(severity=2)
    return {"command": "wait", "status": "ok", "ready": ready,
            "elapsed": round(elapsed, 1),
            "error_count": len(errs), "warning_count": len(warns)}


def _cmd_update(lsp, out, args, project_root):
    fp = args[0] if args else lsp.current_path
    cmd_name = "replace" if args else "update"
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


HELP_TEXT = """\
Commands:
  open <file.lean>                    Open file (relative to project root)
  goal <line> [col]                   Query goal at line:col
  edit <line> <content>               Replace line (preserves indent)
  edit_range <start> <end> <content>  Replace lines start..end (\\n for newlines)
  insert <after_line> <content>       Insert after line (\\n for newlines, 0=prepend)
  delete <start> [end]               Delete line(s)
  batch_start                         Defer edits (no re-elaboration until batch_end)
  batch_end                           Apply deferred edits, wait for elaboration
  update                              Re-read current file from disk
  replace <file.lean>                 Re-read a file from disk
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
  wait                                Wait for elaboration
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

            elif cmd == "batch_start":
                if batch_mode:
                    result = {"command": "batch_start", "status": "error",
                              "error": "Already in batch mode"}
                elif lsp.current_text is None:
                    result = {"command": "batch_start", "status": "error",
                              "error": "No file open"}
                else:
                    batch_mode = True
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

            elif cmd == "wait":
                result = _cmd_wait(lsp, out)

            elif cmd in ("update", "replace"):
                result = _cmd_update(lsp, out, args if cmd == "replace" else [], project_root)

            else:
                result = {"command": cmd, "status": "error",
                          "error": f"Unknown command: {cmd}. Type 'help' for usage."}

        except ValueError as e:
            result = {"command": cmd, "status": "error",
                      "error": f"Invalid argument: {e}"}
        except Exception as e:
            result = {"command": cmd, "status": "error",
                      "error": f"Unexpected error: {e}"}

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
