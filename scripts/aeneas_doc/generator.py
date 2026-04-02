"""
Aeneas Verification Documentation Generator.

Reads:
  1. doc-info JSON from Aeneas (Rust-side inventory)
  2. lean-doc JSON from AeneasDocExtract (Lean-side step theorems)
  3. Rust and Lean source files

Produces: a self-contained static HTML site showing verification status.
"""

import json
import os
import shutil
import html as html_module
from pathlib import Path
from collections import defaultdict
from typing import Optional

# ---------------------------------------------------------------------------
# Data model
# ---------------------------------------------------------------------------

STATUS_VERIFIED = "verified"
STATUS_VERIFIED_UNVERIFIED_DEPS = "verified_unverified_deps"
STATUS_PARTIAL = "partially_verified"
STATUS_SPECIFIED = "specified"
STATUS_UNVERIFIED = "unverified"
STATUS_EXTERNAL = "external"

STATUS_LABELS = {
    STATUS_VERIFIED: ("Verified", "✓", "#28a745", "verified"),
    STATUS_VERIFIED_UNVERIFIED_DEPS: ("Verified (unverified deps)", "✓⚠", None, "verified-unverified-deps"),
    STATUS_PARTIAL: ("Partially verified", "◐", "#007bff", "partial"),
    STATUS_SPECIFIED: ("Specified", "○", "#ffc107", "specified"),
    STATUS_UNVERIFIED: ("Unverified", "✗", "#dc3545", "unverified"),
    STATUS_EXTERNAL: ("Axiomatized", "⚠", "#6f42c1", "external"),
}


class RustFunction:
    """A Rust function extracted from LLBC doc-info."""

    def __init__(self, data: dict):
        self.def_id = data["def_id"]
        self.name_parts = data["name"]
        self.name_pattern = data["name_pattern"]
        self.span = data.get("span")
        self.source_text = data.get("source_text")
        self.is_public = data.get("is_public", False)
        self.is_opaque = data.get("is_opaque", False)
        self.has_body = data.get("has_body", True)
        self.is_global_init = data.get("is_global_initializer")
        self.src = data.get("src", "TopLevel")
        self.callee_ids: list = data.get("callees", [])

        # Computed
        self.module = self._compute_module()
        self.short_name = self._compute_short_name()
        self.display_name = self.name_pattern
        self.rust_path = self.name_pattern.replace("::", ".")

        # Lean-side info (filled by matcher)
        self.step_theorems: list = []
        self.lean_defs: list = []  # list of LeanDefinition
        self.status = STATUS_UNVERIFIED

    def _compute_module(self) -> str:
        parts = [p["name"] for p in self.name_parts if p["kind"] == "Ident"]
        if len(parts) >= 2:
            return "::".join(parts[:-1])
        return "(root)"

    def _compute_short_name(self) -> str:
        parts = [p["name"] for p in self.name_parts if p["kind"] == "Ident"]
        return parts[-1] if parts else self.name_pattern

    @property
    def file_path(self) -> Optional[str]:
        if self.span and self.span.get("data"):
            return self.span["data"].get("file")
        return None

    @property
    def line_range(self) -> Optional[tuple]:
        if self.span and self.span.get("data"):
            d = self.span["data"]
            return (d.get("begin_line", 0), d.get("end_line", 0))
        return None

    @property
    def line_count(self) -> int:
        r = self.line_range
        if r:
            return max(1, r[1] - r[0] + 1)
        return 0

    @property
    def slug(self) -> str:
        return self.name_pattern.replace("::", ".").replace(" ", "_")


class StepTheorem:
    """A Lean step theorem from the doc extractor."""

    def __init__(self, data: dict):
        self.function_name = data["function"]
        self.theorem_name = data["theorem"]
        self.kind = data.get("kind", "theorem")  # "theorem" or "axiom"
        self.is_private = data.get("is_private", False)
        self.sorry_status = data["sorry_status"]
        self.statement = data["statement"]
        self.annotated_statement = data.get("annotated_statement")
        self.spec_binders = data.get("spec_binders")       # [{name, type, annotated_type}]
        self.spec_body = data.get("spec_body")
        self.annotated_spec_body = data.get("annotated_spec_body")


class LeanDefinition:
    """A Lean definition from the doc extractor (function, type, etc.)."""

    def __init__(self, data: dict):
        self.name: str = data["name"]
        self.kind: str = data.get("kind", "def")
        self.type_signature: str = data.get("type_signature", "")
        self.annotated_type_signature: Optional[list] = data.get("annotated_type_signature")
        self.annotated_body: Optional[list] = data.get("annotated_body")
        self.binders: Optional[list] = data.get("binders")
        self.return_type: Optional[dict] = data.get("return_type")
        self.rust_name: Optional[str] = data.get("rust_name")
        self.rust_source: Optional[dict] = data.get("rust_source")
        self.lean_source: Optional[dict] = data.get("lean_source")
        self.module: str = data.get("module", "")
        self.docstring: str = data.get("docstring", "")

        # Filled by matcher
        self.step_theorems: list = []
        # Cross-link to RustFunction (filled during mapping)
        self.rust_fn: Optional['RustFunction'] = None

    @property
    def slug(self) -> str:
        return self.name.replace(".", "_")

    @property
    def display_name(self) -> str:
        return self.name


class RustType:
    """A Rust type extracted from LLBC doc-info."""

    def __init__(self, data: dict):
        self.def_id = data["def_id"]
        self.name_parts = data["name"]
        self.name_pattern = data["name_pattern"]
        self.kind = data.get("kind", "unknown")
        self.is_public = data.get("is_public", False)
        self.span = data.get("span")
        self.source_text = data.get("source_text")

    @property
    def display_name(self) -> str:
        return self.name_pattern

    @property
    def short_name(self) -> str:
        parts = [p["name"] for p in self.name_parts if p["kind"] == "Ident"]
        return parts[-1] if parts else self.name_pattern

    @property
    def module(self) -> str:
        parts = [p["name"] for p in self.name_parts if p["kind"] == "Ident"]
        if len(parts) >= 2:
            return "::".join(parts[:-1])
        return "(root)"


# ---------------------------------------------------------------------------
# Data loading
# ---------------------------------------------------------------------------

def load_doc_info(path: str) -> dict:
    """Load the LLBC doc-info JSON."""
    with open(path) as f:
        return json.load(f)


def load_lean_doc(path: str) -> dict:
    """Load the Lean doc extractor JSON."""
    with open(path) as f:
        return json.load(f)


def parse_functions(doc_info: dict) -> list:
    """Parse functions from doc-info.
    Excludes trait method declarations (TraitDeclItem) — these are just
    interface signatures, not real functions to verify or axiomatize."""
    return [RustFunction(f) for f in doc_info.get("functions", [])
            if f.get("src") != "TraitDeclItem"]


def parse_types(doc_info: dict) -> list:
    """Parse types from doc-info."""
    return [RustType(t) for t in doc_info.get("types", [])]


class RustGlobal:
    """A Rust global constant/static extracted from LLBC doc-info."""

    def __init__(self, data: dict):
        self.def_id = data["def_id"]
        self.name_parts = data["name"]
        self.name_pattern = data["name_pattern"]
        self.is_public = data.get("is_public", False)
        self.span = data.get("span")
        self.source_text = data.get("source_text")

        # Computed
        self.step_theorems: list = []
        self.lean_defs: list = []
        self.status = STATUS_UNVERIFIED

    @property
    def display_name(self) -> str:
        return self.name_pattern

    @property
    def short_name(self) -> str:
        parts = [p["name"] for p in self.name_parts if p["kind"] == "Ident"]
        return parts[-1] if parts else self.name_pattern

    @property
    def module(self) -> str:
        parts = [p["name"] for p in self.name_parts if p["kind"] == "Ident"]
        if len(parts) >= 2:
            return "::".join(parts[:-1])
        return "(root)"

    @property
    def slug(self) -> str:
        return self.name_pattern.replace("::", ".").replace(" ", "_")

    @property
    def file_path(self) -> Optional[str]:
        if self.span and self.span.get("data"):
            return self.span["data"].get("file_name")
        return None

    @property
    def line_range(self) -> Optional[tuple]:
        if self.span and self.span.get("data"):
            d = self.span["data"]
            return (d.get("beg_line"), d.get("end_line"))
        return None


def parse_globals(doc_info: dict) -> list:
    """Parse globals (constants/statics) from doc-info."""
    return [RustGlobal(g) for g in doc_info.get("globals", [])]


def parse_step_theorems(lean_doc: dict) -> list:
    """Parse step theorems from lean-doc, filtering out private theorems."""
    all_thms = [StepTheorem(t) for t in lean_doc.get("theorems", [])]
    # Filter out private theorems — they are implementation details
    return [t for t in all_thms if not t.is_private]


def parse_lean_definitions(lean_doc: dict) -> list:
    """Parse Lean definitions from lean-doc."""
    return [LeanDefinition(d) for d in lean_doc.get("definitions", [])]


# ---------------------------------------------------------------------------
# Matcher: Rust functions ↔ Lean step theorems
# ---------------------------------------------------------------------------

def match_functions_to_theorems(functions: list, theorems: list):
    """Match each function to its step theorem(s) and set verification status."""
    # Build lookup: Lean function name → theorems
    thm_by_fun = defaultdict(list)
    for thm in theorems:
        thm_by_fun[thm.function_name].append(thm)

    # Build suffix index: short_name → [full keys] for O(1) suffix lookup
    thm_by_suffix = defaultdict(list)
    for key in thm_by_fun:
        short = key.rsplit(".", 1)[-1]
        thm_by_suffix[short].append(key)

    for fn in functions:
        # External/opaque functions get special status
        if fn.is_opaque or not fn.has_body:
            fn.status = STATUS_EXTERNAL
            # Still check if they have specs
            matched = _find_theorems_for(fn, thm_by_fun, thm_by_suffix)
            fn.step_theorems = matched
            continue

        matched = _find_theorems_for(fn, thm_by_fun, thm_by_suffix)
        fn.step_theorems = matched

        if not matched:
            fn.status = STATUS_UNVERIFIED
        else:
            # Separate axioms from theorems
            axiom_specs = [t for t in matched if t.kind == "axiom"]
            theorem_specs = [t for t in matched if t.kind != "axiom"]

            if not theorem_specs and axiom_specs:
                # Only axiom specs — treat as axiomatized
                fn.status = STATUS_EXTERNAL
            else:
                # Determine status from theorem-kind specs (ignore axioms)
                specs_for_status = theorem_specs if theorem_specs else matched
                statuses = {t.sorry_status for t in specs_for_status}
                if all(s == "verified" for s in statuses):
                    fn.status = STATUS_VERIFIED
                elif all(s == "specified" for s in statuses):
                    fn.status = STATUS_SPECIFIED
                else:
                    fn.status = STATUS_PARTIAL


def _find_theorems_for(fn: 'RustFunction', thm_by_fun: dict,
                       thm_by_suffix: dict) -> list:
    """Find step theorems matching a Rust function."""
    # Strategy 1: exact match on name_pattern converted to Lean-style
    lean_name = fn.name_pattern.replace("::", ".")
    if lean_name in thm_by_fun:
        return thm_by_fun[lean_name]

    # Strategy 2: try with crate name stripped
    parts = fn.name_pattern.split("::")
    if len(parts) > 1:
        without_crate = ".".join(parts[1:])
        if without_crate in thm_by_fun:
            return thm_by_fun[without_crate]

    # Strategy 3: suffix match via pre-built index (O(1) lookup)
    for key in thm_by_suffix.get(fn.short_name, []):
        if key in thm_by_fun:
            return thm_by_fun[key]

    return []


def match_globals_to_theorems(globals_list: list, theorems: list):
    """Match each global constant to its step theorem(s) and set status.

    Uses the same matching logic as functions (_find_theorems_for).
    """
    thm_by_fun = defaultdict(list)
    for thm in theorems:
        thm_by_fun[thm.function_name].append(thm)
    thm_by_suffix = defaultdict(list)
    for key in thm_by_fun:
        short = key.rsplit(".", 1)[-1]
        thm_by_suffix[short].append(key)

    for g in globals_list:
        matched = _find_theorems_for(g, thm_by_fun, thm_by_suffix)
        g.step_theorems = matched
        if not matched:
            g.status = STATUS_UNVERIFIED
        else:
            axiom_specs = [t for t in matched if t.kind == "axiom"]
            theorem_specs = [t for t in matched if t.kind != "axiom"]
            if not theorem_specs and axiom_specs:
                g.status = STATUS_EXTERNAL
            else:
                specs = theorem_specs if theorem_specs else matched
                statuses = {t.sorry_status for t in specs}
                if all(s == "verified" for s in statuses):
                    g.status = STATUS_VERIFIED
                elif all(s == "specified" for s in statuses):
                    g.status = STATUS_SPECIFIED
                else:
                    g.status = STATUS_PARTIAL


def _mark_verified_with_unverified_deps(functions: list):
    """Downgrade 'verified' functions that transitively depend on unverified code.

    A function is downgraded to STATUS_VERIFIED_UNVERIFIED_DEPS if it is
    currently STATUS_VERIFIED but transitively calls a function whose status is
    STATUS_PARTIAL, STATUS_SPECIFIED, or STATUS_UNVERIFIED (i.e., not verified
    and not external/axiomatized).
    """
    UNVERIFIED_STATUSES = {STATUS_PARTIAL, STATUS_SPECIFIED, STATUS_UNVERIFIED}

    by_id = {fn.def_id: fn for fn in functions}

    # Cache: def_id → True if the function (transitively) has an unverified dep
    _cache: dict = {}

    def has_unverified_dep(def_id: int, visiting: set) -> bool:
        if def_id in _cache:
            return _cache[def_id]
        if def_id in visiting:
            # Cycle — treat as no unverified dep on this path
            return False
        fn = by_id.get(def_id)
        if fn is None:
            return False
        # If this callee itself is unverified, yes
        if fn.status in UNVERIFIED_STATUSES:
            _cache[def_id] = True
            return True
        # If external/axiom, it's trusted — not an unverified dep
        if fn.status == STATUS_EXTERNAL:
            _cache[def_id] = False
            return False
        # Recurse into callees
        visiting.add(def_id)
        result = any(has_unverified_dep(cid, visiting) for cid in fn.callee_ids)
        visiting.discard(def_id)
        _cache[def_id] = result
        return result

    for fn in functions:
        if fn.status == STATUS_VERIFIED:
            if any(has_unverified_dep(cid, set()) for cid in fn.callee_ids):
                fn.status = STATUS_VERIFIED_UNVERIFIED_DEPS


# ---------------------------------------------------------------------------
# Statistics
# ---------------------------------------------------------------------------

class VerificationStats:
    """Verification statistics for a set of functions."""

    def __init__(self, functions: list, label: str = ""):
        self.label = label
        self.total = 0
        self.public_total = 0
        self.counts = defaultdict(int)
        self.public_counts = defaultdict(int)
        self.lines_by_status = defaultdict(int)
        self.total_lines = 0

        for fn in functions:
            self.total += 1
            self.counts[fn.status] += 1
            lc = fn.line_count
            self.total_lines += lc
            self.lines_by_status[fn.status] += lc
            if fn.is_public:
                self.public_total += 1
                self.public_counts[fn.status] += 1

    def pct(self, status: str) -> float:
        if self.total == 0:
            return 0.0
        return 100.0 * self.counts[status] / self.total

    def line_pct(self, status: str) -> float:
        if self.total_lines == 0:
            return 0.0
        return 100.0 * self.lines_by_status[status] / self.total_lines

    @property
    def verified_pct(self) -> float:
        return self.pct(STATUS_VERIFIED)

    @property
    def progress_pct(self) -> float:
        """Verified + verified-with-unverified-deps + partially verified percentage."""
        if self.total == 0:
            return 0.0
        n = (self.counts[STATUS_VERIFIED]
             + self.counts[STATUS_VERIFIED_UNVERIFIED_DEPS]
             + self.counts[STATUS_PARTIAL])
        return 100.0 * n / self.total


# ---------------------------------------------------------------------------
# HTML rendering
# ---------------------------------------------------------------------------

STATIC_DIR = Path(__file__).parent / "static"

# Set by generate_docs() so all pages can reference it
_CRATE_TITLE = "Verification Docs"


def _esc(s: str) -> str:
    """HTML-escape a string."""
    return html_module.escape(str(s))


_STRIPE_BG = (
    "repeating-linear-gradient(135deg,"
    "#28a745,#28a745 4px,#007bff 4px,#007bff 8px)"
)


def _badge_html(status: str) -> str:
    label, icon, color, css_class = STATUS_LABELS.get(
        status, ("Unknown", "?", "#999", "unknown")
    )
    if status == STATUS_VERIFIED_UNVERIFIED_DEPS:
        bg_style = f"background:{_STRIPE_BG}"
    else:
        bg_style = f"background-color:{color}"
    return (
        f'<span class="badge badge-{css_class}" '
        f'style="{bg_style};color:#fff;padding:2px 8px;'
        f'border-radius:4px;font-size:0.85em" title="{label}">'
        f'{icon} {label}</span>'
    )


def _progress_bar(stats: VerificationStats) -> str:
    """Render a stacked progress bar."""
    segments = []
    order = [STATUS_VERIFIED, STATUS_VERIFIED_UNVERIFIED_DEPS, STATUS_PARTIAL,
             STATUS_SPECIFIED, STATUS_UNVERIFIED]
    for s in order:
        pct = stats.pct(s)
        if pct > 0:
            _, _, color, _ = STATUS_LABELS[s]
            if s == STATUS_VERIFIED_UNVERIFIED_DEPS:
                bg = _STRIPE_BG
            else:
                bg = color
            segments.append(
                f'<div style="width:{pct:.1f}%;background:{bg};height:100%'
                f';display:inline-block" title="{STATUS_LABELS[s][0]}: '
                f'{stats.counts[s]} ({pct:.1f}%)"></div>'
            )
    return (
        '<div style="width:100%;height:20px;background:#eee;border-radius:4px'
        ';overflow:hidden;display:flex">'
        + "".join(segments) +
        '</div>'
    )


def _stats_table(stats: VerificationStats) -> str:
    """Render statistics as an HTML table."""
    rows = []
    for s in [STATUS_VERIFIED, STATUS_VERIFIED_UNVERIFIED_DEPS, STATUS_PARTIAL,
              STATUS_SPECIFIED, STATUS_UNVERIFIED]:
        label, icon, color, _ = STATUS_LABELS[s]
        count = stats.counts[s]
        pct = stats.pct(s)
        lines = stats.lines_by_status[s]
        lpct = stats.line_pct(s)
        pub_count = stats.public_counts[s]
        if s == STATUS_VERIFIED_UNVERIFIED_DEPS:
            icon_html = f'<span style="background:{_STRIPE_BG};-webkit-background-clip:text;-webkit-text-fill-color:transparent">{icon}</span>'
        else:
            icon_html = f'<span style="color:{color}">{icon}</span>'
        rows.append(
            f'<tr>'
            f'<td>{icon_html} {label}</td>'
            f'<td style="text-align:right">{count}</td>'
            f'<td style="text-align:right">{pct:.1f}%</td>'
            f'<td style="text-align:right">{lines}</td>'
            f'<td style="text-align:right">{lpct:.1f}%</td>'
            f'<td style="text-align:right">{pub_count}</td>'
            f'</tr>'
        )
    return f'''
    <table class="stats-table">
      <thead>
        <tr>
          <th>Status</th><th>Functions</th><th>%</th>
          <th>Lines</th><th>%</th><th>Public</th>
        </tr>
      </thead>
      <tbody>{"".join(rows)}</tbody>
      <tfoot>
        <tr style="font-weight:bold">
          <td>Total</td>
          <td style="text-align:right">{stats.total}</td>
          <td></td>
          <td style="text-align:right">{stats.total_lines}</td>
          <td></td>
          <td style="text-align:right">{stats.public_total}</td>
        </tr>
      </tfoot>
    </table>'''


def _page_header(title: str, breadcrumbs: list = None, depth: int = 0) -> str:
    """Generate page header with nav."""
    root = "../" * depth if depth > 0 else "./"
    bc_html = ""
    if breadcrumbs:
        parts = []
        for label, href in breadcrumbs:
            if href:
                parts.append(f'<a href="{root}{href}">{_esc(label)}</a>')
            else:
                parts.append(f'<span>{_esc(label)}</span>')
        bc_html = ' &rsaquo; '.join(parts)

    return f'''<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>{_esc(title)}</title>
  <link rel="stylesheet" href="{root}static/github.min.css">
  <link rel="stylesheet" href="{root}static/style.css">
</head>
<body>
<nav class="top-nav">
  <a href="{root}index.html" class="nav-home">{_esc(_CRATE_TITLE)}</a>
  {f'<span class="breadcrumbs">{bc_html}</span>' if bc_html else ''}
</nav>
<main>
<h1>{_esc(title)}</h1>
'''


def _page_footer(depth: int = 0) -> str:
    root = "../" * depth if depth > 0 else "./"
    return f'''
</main>
<script src="{root}static/highlight.min.js"></script>
<script src="{root}static/rust.min.js"></script>
<script src="{root}static/lean.min.js"></script>
<script>
// Highlight non-annotated code blocks
document.querySelectorAll('pre:not(.lean-annotated) > code[class*="language-"]').forEach(function(el) {{
  hljs.highlightElement(el);
}});
// Source pages: highlight hidden block, distribute into per-line table cells
(function() {{
  var src = document.getElementById('hljs-source');
  if (!src) return;
  var code = src.querySelector('code');
  if (code) {{
    hljs.highlightElement(code);
    var lines = code.innerHTML.split('\\n');
    for (var i = 0; i < lines.length; i++) {{
      var cell = document.getElementById('LC' + (i + 1));
      if (cell) cell.innerHTML = lines[i];
    }}
  }}
  src.remove();
}})();
</script>
<script src="{root}static/search.js"></script>
</body>
</html>'''


def _theorem_links(theorems: list, lean_map: dict = None,
                   link_prefix: str = "", fn_slug: str = "") -> str:
    """Render theorem names as clickable links.

    Links to the Lean definition page if available, otherwise to the
    function's own page #spec section.
    """
    if not theorems:
        return ""
    parts = []
    for thm in theorems:
        ld = lean_map.get(thm.function_name) if lean_map else None
        if ld:
            href = f"{link_prefix}lean/{ld.slug}.html#spec"
        elif fn_slug:
            href = f"{link_prefix}fn/{fn_slug}.html#spec"
        else:
            href = ""
        if href:
            parts.append(f'<a href="{href}">{_esc(thm.theorem_name)}</a>')
        else:
            parts.append(_esc(thm.theorem_name))
    return ", ".join(parts)


def _render_theorem_card(thm: 'StepTheorem', known_fns: dict = None,
                         depth: int = 1, lean_map: dict = None,
                         link_prefix: str = "", fn_slug: str = "") -> str:
    """Render a single theorem card (used in function and Lean definition pages)."""
    sorry_badge = _badge_html(
        STATUS_VERIFIED if thm.sorry_status == "verified"
        else STATUS_SPECIFIED if thm.sorry_status == "specified"
        else STATUS_PARTIAL
    )
    # Make theorem name clickable if we can find its Lean page
    lm = lean_map or {}
    ld = lm.get(thm.function_name)
    if ld:
        thm_name_html = (f'<a href="{link_prefix}lean/{ld.slug}.html#spec">'
                         f'{_esc(thm.theorem_name)}</a>')
    elif fn_slug:
        thm_name_html = (f'<a href="{link_prefix}fn/{fn_slug}.html#spec">'
                         f'{_esc(thm.theorem_name)}</a>')
    else:
        thm_name_html = _esc(thm.theorem_name)
    return f'''
    <div class="theorem-card">
      <div class="theorem-header">
        <code class="thm-name">{thm_name_html}</code>
        {sorry_badge}
      </div>
      <div class="theorem-statement">
        {_annotated_statement_block(thm, known_fns=known_fns, depth=depth)}
      </div>
    </div>
    '''


def _render_theorem_sections(theorems: list, known_fns: dict = None,
                             depth: int = 1, lean_map: dict = None,
                             link_prefix: str = "", fn_slug: str = "") -> str:
    """Render theorem sections, splitting into Specifications and Axioms."""
    if not theorems:
        return '<p class="no-spec">No specification theorem found.</p>'

    axiom_thms = [t for t in theorems if t.kind == "axiom"]
    spec_thms = [t for t in theorems if t.kind != "axiom"]

    html = ""
    if spec_thms:
        html += '<h2 id="spec">Specifications</h2>'
        for thm in spec_thms:
            html += _render_theorem_card(thm, known_fns=known_fns, depth=depth,
                                         lean_map=lean_map, link_prefix=link_prefix,
                                         fn_slug=fn_slug)
    if axiom_thms:
        html += '<h2 id="axioms">Axioms</h2>'
        for thm in axiom_thms:
            html += _render_theorem_card(thm, known_fns=known_fns, depth=depth,
                                         lean_map=lean_map, link_prefix=link_prefix,
                                         fn_slug=fn_slug)
    return html


def _lean_model_links(fn: 'RustFunction', rust_to_lean: dict = None,
                      link_prefix: str = "") -> str:
    """Render clickable Lean model name(s) for a Rust function, or '—' if none."""
    r2l = rust_to_lean or {}
    lds = r2l.get(fn.name_pattern, [])
    if lds:
        return ", ".join(
            f'<a href="{link_prefix}lean/{ld.slug}.html">{_esc(ld.name)}</a>'
            for ld in lds
        )
    return "—"


def _function_row(fn: 'RustFunction', link_prefix: str = "",
                  show_vis: bool = True, lean_map: dict = None,
                  rust_to_lean: dict = None) -> str:
    """Render one row in a function listing table."""
    badge = _badge_html(fn.status)
    name_link = f'<a href="{link_prefix}fn/{fn.slug}.html">{_esc(fn.display_name)}</a>'
    vis_col = f'<td>{"pub" if fn.is_public else ""}</td>' if show_vis else ""
    thm_col = _theorem_links(fn.step_theorems, lean_map, link_prefix,
                             fn_slug=fn.slug) or "—"
    lean_col = _lean_model_links(fn, rust_to_lean, link_prefix)
    pub_attr = "true" if fn.is_public else "false"
    return (
        f'<tr data-public="{pub_attr}">'
        f'<td>{name_link}</td>'
        f'{vis_col}'
        f'<td>{badge}</td>'
        f'<td>{lean_col}</td>'
        f'<td class="thm-name">{thm_col}</td>'
        f'</tr>'
    )


def _global_row(g: 'RustGlobal', link_prefix: str = "",
                show_vis: bool = True, lean_map: dict = None,
                rust_to_lean: dict = None) -> str:
    """Render one row in a constants listing table (same layout as function rows)."""
    badge = _badge_html(g.status)
    name_link = f'<a href="{link_prefix}fn/{g.slug}.html">{_esc(g.display_name)}</a>'
    vis_col = f'<td>{"pub" if g.is_public else ""}</td>' if show_vis else ""
    thm_col = _theorem_links(g.step_theorems, lean_map, link_prefix,
                             fn_slug=g.slug) or "—"
    lean_col = _lean_model_links(g, rust_to_lean, link_prefix)
    pub_attr = "true" if g.is_public else "false"
    return (
        f'<tr data-public="{pub_attr}">'
        f'<td>{name_link}</td>'
        f'{vis_col}'
        f'<td>{badge}</td>'
        f'<td>{lean_col}</td>'
        f'<td class="thm-name">{thm_col}</td>'
        f'</tr>'
    )


def _source_block(code: str, lang: str = "rust") -> str:
    """Render a syntax-highlighted source code block."""
    return (
        f'<pre><code class="language-{lang}">{_esc(code)}</code></pre>'
    )


def _source_block_with_lines(code: str, lang: str = "rust") -> str:
    """Render a source block with per-line anchors and syntax highlighting.

    Uses a per-row table for perfect line-number alignment.  A hidden <code>
    block holds the full source for highlight.js to process; the page footer
    script distributes highlighted HTML back into each table row.
    """
    lines = code.split("\n")
    rows = []
    for i, line in enumerate(lines, 1):
        rows.append(
            f'<tr><td id="L{i}" class="line-num">'
            f'<a href="#L{i}">{i}</a></td>'
            f'<td class="line-code" id="LC{i}">{_esc(line)}</td></tr>'
        )
    # Hidden element for highlight.js to process
    hidden_code = (
        f'<pre style="position:absolute;left:-9999px" id="hljs-source">'
        f'<code class="language-{lang}">{_esc(code)}</code></pre>'
    )
    return (
        '<div class="source-viewer-inner">'
        f'<table class="source-table">{"".join(rows)}</table>'
        f'{hidden_code}'
        '</div>'
    )


def _resolve_lean_ident_href(ident: str, known_fns: dict,
                            constructor_of: str = None) -> str:
    """Resolve a Lean identifier to a link URL.

    Returns empty string if no link can be determined.
    If constructor_of is provided (parent type name), use that for linking.
    """
    # Check if it's a function/type in our doc (by slug)
    if ident in known_fns:
        return known_fns[ident]
    # Also try stripping the crate prefix for project definitions
    parts = ident.split(".")
    if len(parts) > 1:
        without_prefix = ".".join(parts[1:])
        if without_prefix in known_fns:
            return known_fns[without_prefix]
    # If this is a constructor, link to the parent type definition
    if constructor_of:
        if constructor_of in known_fns:
            return known_fns[constructor_of]
        ctor_parts = constructor_of.split(".")
        if len(ctor_parts) > 1:
            without_prefix = ".".join(ctor_parts[1:])
            if without_prefix in known_fns:
                return known_fns[without_prefix]
    return ""


def _render_annotated_html(annotated: list, known_fns: dict,
                          current_fn_lean_name: str = None,
                          inline: bool = False) -> str:
    """Walk structured annotated JSON and emit HTML with links baked in.

    The annotated JSON is an array of:
      - strings (plain text)
      - dicts with "ident" (qualified name) and "children" (nested annotated array)

    Text nodes get minimal Lean keyword/operator highlighting via CSS classes.
    Ident nodes become <a> (if linkable) or <span> (tooltip only).

    If inline=True, returns just the inner HTML without <pre>/<code> wrapper.
    """
    import re

    # Lean keywords and operators to highlight in text nodes
    _LEAN_KW = {
        'def', 'theorem', 'lemma', 'where', 'do', 'let', 'if', 'then', 'else',
        'match', 'with', 'fun', 'return', 'by', 'sorry', 'have', 'show',
        'structure', 'inductive', 'class', 'instance', 'open', 'variable',
        'section', 'namespace', 'end', 'import', 'private', 'protected',
        'noncomputable', 'partial', 'unsafe', 'mutual', 'axiom', 'opaque',
        'abbrev', 'example', 'deriving', 'extends', 'in', 'at', 'for',
    }
    # Token regex: word | operator/symbol | whitespace | other
    _TOKEN_RE = re.compile(
        r'([A-Za-z_][A-Za-z0-9_]*'  # identifiers/keywords
        r'|[0-9]+'                    # numbers
        r'|[⦃⦄⟨⟩→←↑↓∀∃∧∨¬≤≥≠·×⊢⊣λΣΠ]'  # unicode operators
        r'|:=|=>|<\||>\||&&|\|\||::|\.\.)'  # multi-char operators
    )

    def _highlight_text(text: str) -> str:
        """Apply minimal syntax highlighting to a plain text fragment."""
        result = []
        last = 0
        for m in _TOKEN_RE.finditer(text):
            # Emit any text before this match as-is
            if m.start() > last:
                result.append(_esc(text[last:m.start()]))
            tok = m.group()
            if tok in _LEAN_KW:
                result.append(f'<span class="lk">{_esc(tok)}</span>')
            elif tok[0].isdigit():
                result.append(f'<span class="ln">{_esc(tok)}</span>')
            elif tok in '⦃⦄⟨⟩→←∀∃∧∨¬≤≥≠·×⊢⊣λΣΠ↑↓' or tok in (':=', '=>'):
                result.append(f'<span class="lo">{_esc(tok)}</span>')
            else:
                result.append(_esc(tok))
            last = m.end()
        if last < len(text):
            result.append(_esc(text[last:]))
        return "".join(result)

    def _render_node(node) -> str:
        if isinstance(node, str):
            return _highlight_text(node)
        if isinstance(node, dict) and "ident" in node:
            ident = node["ident"]
            constructor_of = node.get("constructor_of")
            children_html = "".join(_render_node(c) for c in node.get("children", []))
            # Skip self-references (the function being specified)
            if current_fn_lean_name and ident == current_fn_lean_name:
                return children_html
            href = _resolve_lean_ident_href(ident, known_fns or {},
                                            constructor_of=constructor_of)
            if href:
                return (f'<a class="lean-ident" href="{_esc(href)}" '
                        f'title="{_esc(ident)}">{children_html}</a>')
            else:
                return (f'<span class="lean-ident" '
                        f'title="{_esc(ident)}">{children_html}</span>')
        return ""

    inner = "".join(_render_node(n) for n in annotated)
    if inline:
        return inner
    return f'<pre class="lean-annotated"><code>{inner}</code></pre>'


def _annotated_statement_block(thm, known_fns: dict = None, depth: int = 1,
                               current_fn_lean_name: str = None) -> str:
    """Render a theorem's annotated statement as HTML with links baked in.

    If decomposed binders are available, renders in context/body format
    with binders above a separator and the WP body below.
    """
    kf = known_fns or {}

    # New decomposed format: binders + separator + body
    if thm.spec_binders and thm.annotated_spec_body:
        binder_lines = []
        for b in thm.spec_binders:
            name = _esc(b["name"])
            type_html = _render_annotated_html(
                b["annotated_type"], kf, inline=True,
                current_fn_lean_name=current_fn_lean_name)
            binder_lines.append(
                f'<span class="spec-binder-name">{name}</span>'
                f' : {type_html}')
        body_html = _render_annotated_html(
            thm.annotated_spec_body, kf, inline=True,
            current_fn_lean_name=current_fn_lean_name)
        binders_block = "\n".join(binder_lines)
        # Use a wrapper div instead of putting block elements inside <code>
        return (
            f'<div class="spec-decomposed">'
            f'<pre class="spec-context"><code>{binders_block}\n</code></pre>'
            f'<hr class="spec-sep">'
            f'<pre class="spec-body"><code>{body_html}</code></pre>'
            f'</div>'
        )

    # Fallback: flat annotated statement
    if thm.annotated_statement:
        return _render_annotated_html(
            thm.annotated_statement, kf,
            current_fn_lean_name=current_fn_lean_name)
    return _source_block(thm.statement, "lean")


def _strip_lean_docstring(lines: list) -> list:
    """Strip /-- ... -/ docstring from the beginning of a list of source lines."""
    # Find the end of the docstring block
    in_docstring = False
    result_start = 0
    for i, line in enumerate(lines):
        stripped = line.strip()
        if i == 0 and stripped.startswith("/--"):
            in_docstring = True
        if in_docstring:
            if "-/" in stripped:
                result_start = i + 1
                break
        else:
            break
    # Also skip leading blank lines after docstring
    while result_start < len(lines) and not lines[result_start].strip():
        result_start += 1
    return lines[result_start:] if result_start > 0 else lines


def _annotated_lean_block(text: str, known_fns: dict,
                         annotated: list = None) -> str:
    """Render a Lean code block with clickable identifiers.

    If `annotated` (structured JSON from the Lean extractor) is provided,
    uses _render_annotated_html for exact, server-side link generation.
    Otherwise falls back to text-scanning for known identifiers.
    """
    if annotated:
        return _render_annotated_html(annotated, known_fns)

    import re
    if not known_fns:
        return _source_block(text, "lean")

    # Fallback: scan text for known identifiers and produce annotated-style JSON
    sorted_fns = sorted(known_fns.keys(), key=len, reverse=True)
    pattern_parts = [re.escape(fn) for fn in sorted_fns]
    combined = '|'.join(pattern_parts)
    pattern = re.compile(
        r'(?<![A-Za-z0-9_.])(' + combined + r')(?![A-Za-z0-9_.])')

    synthetic = []
    last = 0
    for m in pattern.finditer(text):
        if m.start() > last:
            synthetic.append(text[last:m.start()])
        ident_name = m.group(1)
        synthetic.append({"ident": ident_name, "children": [m.group(1)]})
        last = m.end()
    if last < len(text):
        synthetic.append(text[last:])

    if any(isinstance(n, dict) for n in synthetic):
        return _render_annotated_html(synthetic, known_fns)
    return _source_block(text, "lean")



# ---------------------------------------------------------------------------
# Page generators
# ---------------------------------------------------------------------------

def generate_index(crate_name: str, functions: list, types: list,
                   stats: VerificationStats, output_dir: Path,
                   rust_to_lean: dict = None, errors: list = None,
                   lean_map: dict = None):
    """Generate the index.html page."""
    # Group functions by module, excluding external-only modules
    modules = defaultdict(list)
    for fn in functions:
        modules[fn.module].append(fn)

    # Build hierarchical module tree (only local modules)
    local_modules = {
        name: fns for name, fns in modules.items()
        if any(not (f.is_opaque or not f.has_body) for f in fns)
    }

    # Build a proper hierarchical tree with arbitrary depth.
    # Each node: {"fns": [...], "children": {child_name: node, ...}}
    def _build_tree(module_names):
        tree = {}  # top-level token → subtree node
        for mod_name in sorted(module_names):
            parts = mod_name.split("::")
            # Navigate/create the tree path
            current_children = tree
            for part in parts:
                if part not in current_children:
                    current_children[part] = {"_fns": [], "_children": {}}
                node = current_children[part]
                current_children = node["_children"]
            # `node` is now the leaf node for this module
            node["_fns"] = local_modules[mod_name]
        return tree

    tree = _build_tree(local_modules.keys())

    def _collect_all_fns(node):
        """Recursively collect all functions under a tree node."""
        fns = list(node.get("_fns", []))
        for child_node in node.get("_children", {}).values():
            fns.extend(_collect_all_fns(child_node))
        return fns

    def _render_module_tree(node, prefix_parts, depth=0, parent_expanded=True):
        """Recursively render a module tree as table rows."""
        html = ""
        children = node.get("_children", {})
        for child_name in sorted(children.keys()):
            child_node = children[child_name]
            full_parts = prefix_parts + [child_name]
            full_name = "::".join(full_parts)
            all_child_fns = _collect_all_fns(child_node)
            child_stats = VerificationStats(
                [f for f in all_child_fns if f.status != STATUS_EXTERNAL], full_name)
            count = len(all_child_fns)
            verified = child_stats.counts[STATUS_VERIFIED] + child_stats.counts[STATUS_VERIFIED_UNVERIFIED_DEPS]
            slug = full_name.replace("::", ".")
            link = f'<a href="mod/{slug}.html">{_esc(full_name)}</a>'
            has_children = bool(child_node.get("_children"))

            # The crate root (depth 0) is always expanded to show level-1 modules
            is_expanded = (depth == 0)
            indent = 16 + 16 * max(depth, 0)
            display = "" if parent_expanded else ' style="display:none"'

            if has_children:
                arrow = "▾" if is_expanded else "▸"
                expanded_cls = " expanded" if is_expanded else ""
                html += (
                    f'<tr class="parent-module mod-row{expanded_cls}"'
                    f' data-mod="{slug}" data-depth="{depth}"'
                    f'{display}'
                    f' onclick="toggleMod(this)">'
                    f'<td style="padding-left:{indent}px">{link} '
                    f'<span class="expand-arrow">{arrow}</span></td>'
                    f'<td>{count}</td>'
                    f'<td>{verified}/{count}</td>'
                    f'<td style="width:200px">{_progress_bar(child_stats)}</td></tr>'
                )
                html += _render_module_tree(child_node, full_parts, depth + 1,
                                            parent_expanded=is_expanded and parent_expanded)
            else:
                html += (
                    f'<tr class="mod-row" data-mod="{slug}" data-depth="{depth}"'
                    f'{display}>'
                    f'<td style="padding-left:{indent}px">{link}</td>'
                    f'<td>{count}</td>'
                    f'<td>{verified}/{count}</td>'
                    f'<td style="width:200px">{_progress_bar(child_stats)}</td></tr>'
                )
        return html

    # Start rendering from the tree root; depth 0 = crate root, expanded
    root_node = {"_fns": [], "_children": tree}
    module_html = _render_module_tree(root_node, [], depth=0, parent_expanded=True)

    # External functions summary
    externals = [f for f in functions if f.status == STATUS_EXTERNAL]

    content = _page_header(f"{crate_name} — Verification Dashboard")
    content += '''
    <div class="search-box">
      <input type="text" id="search-input" placeholder="Search functions, types..." autocomplete="off">
      <div id="search-results"></div>
    </div>
    '''
    content += f'''
    <section class="overview">
      <h2>Overview</h2>
      {_progress_bar(stats)}
      <p style="margin-top:8px">
        <strong>{stats.counts[STATUS_VERIFIED]}</strong> verified,
        <strong>{stats.counts[STATUS_VERIFIED_UNVERIFIED_DEPS]}</strong> verified (unverified deps),
        <strong>{stats.counts[STATUS_PARTIAL]}</strong> partially verified,
        <strong>{stats.counts[STATUS_SPECIFIED]}</strong> specified,
        <strong>{stats.counts[STATUS_UNVERIFIED]}</strong> unverified
        — out of <strong>{stats.total}</strong> functions
        (+ <strong>{len(externals)}</strong> <a href="external.html">external/axiomatized</a>)
      </p>
      {_stats_table(stats)}
    </section>
    '''

    content += f'''
    <section class="legend-box">
      <h2>⚠ About Verification Status</h2>
      <p>This documentation is generated automatically by matching Rust functions
         to their Lean models and proof theorems. The verification statuses are
         <strong>approximative</strong> — always review the theorem statements
         and proofs manually.</p>
      <dl class="status-legend">
        <dt>{_badge_html(STATUS_VERIFIED)} Verified</dt>
        <dd>A <code>@[step]</code> theorem exists for this function and its proof
            is complete (no <code>sorry</code>). This does <strong>not</strong>
            guarantee the theorem is correct — a human must review the theorem
            statement (both the preconditions and the postcondition) to check
            that it actually captures the intended specification.</dd>
        <dt>{_badge_html(STATUS_VERIFIED_UNVERIFIED_DEPS)} Verified (unverified deps)</dt>
        <dd>This function has a complete proof, but it transitively depends on
            one or more functions that are <em>not fully verified</em> (partially
            verified, specified only, or unverified). The proof chain is
            incomplete.</dd>
        <dt>{_badge_html(STATUS_PARTIAL)} Partially verified</dt>
        <dd>A theorem exists and its proof has been started, but still contains
            some <code>sorry</code> placeholders. Parts of the proof are filled
            in.</dd>
        <dt>{_badge_html(STATUS_SPECIFIED)} Specified</dt>
        <dd>A theorem exists (the specification has been written), but the proof
            has not been started — the proof body is entirely
            <code>sorry</code>.</dd>
        <dt>{_badge_html(STATUS_UNVERIFIED)} Unverified</dt>
        <dd>No matching theorem was found for this function. Either the function
            has not been specified yet, or the visualizer failed to link it to
            its Lean model.</dd>
        <dt>{_badge_html(STATUS_EXTERNAL)} Axiomatized</dt>
        <dd>This function comes from outside the crate (e.g., the Rust standard
            library, intrinsic operations). Its behavior is modeled by a
            hand-written Lean definition and axiomatized — the model is
            <strong>assumed correct without proof</strong>. See the
            <a href="external.html">list of axioms and models</a> that the
            verification relies on.</dd>
      </dl>
    </section>
    '''

    content += f'''
    <section>
      <h2>Modules</h2>
      <table class="data-table" id="module-table">
        <colgroup><col class="col-mod"><col class="col-count"><col class="col-count"><col class="col-prog"></colgroup>
        <thead><tr><th>Module</th><th>Functions</th><th>Verified</th><th>Progress</th></tr></thead>
        <tbody>{module_html}</tbody>
      </table>
      <script>
        function toggleMod(row) {{
          var expanded = row.classList.toggle('expanded');
          var arrow = row.querySelector('.expand-arrow');
          if (arrow) arrow.textContent = expanded ? '▾' : '▸';
          var parentMod = row.getAttribute('data-mod');
          var parentDepth = parseInt(row.getAttribute('data-depth'));
          // Walk subsequent rows
          var next = row.nextElementSibling;
          while (next && next.classList.contains('mod-row')) {{
            var d = parseInt(next.getAttribute('data-depth'));
            if (d <= parentDepth) break;  // sibling or ancestor
            if (d === parentDepth + 1) {{
              // Direct child — toggle visibility
              next.style.display = expanded ? '' : 'none';
              // If collapsing, also collapse nested children
              if (!expanded && next.classList.contains('expanded')) {{
                next.classList.remove('expanded');
                var sa = next.querySelector('.expand-arrow');
                if (sa) sa.textContent = '▸';
              }}
            }} else {{
              // Deeper descendant — hide when collapsing
              if (!expanded) next.style.display = 'none';
            }}
            next = next.nextElementSibling;
          }}
        }}
      </script>
    </section>
    '''

    # Public functions table (no Vis column — it's obvious from the name)
    public_fns = [f for f in functions if f.is_public and f.status != STATUS_EXTERNAL]
    lm = lean_map or {}
    if public_fns:
        pub_rows = ""
        for fn in sorted(public_fns, key=lambda f: f.display_name):
            badge = _badge_html(fn.status)
            name_link = f'<a href="fn/{fn.slug}.html">{_esc(fn.display_name)}</a>'
            thm_col = _theorem_links(fn.step_theorems, lm, fn_slug=fn.slug) or "—"
            lean_col = _lean_model_links(fn, rust_to_lean)
            pub_rows += (
                f'<tr>'
                f'<td>{name_link}</td>'
                f'<td>{badge}</td>'
                f'<td>{lean_col}</td>'
                f'<td class="thm-name">{thm_col}</td>'
                f'</tr>'
            )
        content += f'''
    <section>
      <h2>Public Functions ({len(public_fns)})</h2>
      <table class="data-table">
        <colgroup><col class="col-name"><col class="col-status"><col class="col-lean"><col class="col-thm"></colgroup>
        <thead><tr><th>Function</th><th>Status</th><th>Lean Model</th><th>Theorem</th></tr></thead>
        <tbody>{pub_rows}</tbody>
      </table>
    </section>
    '''

    if externals:
        content += f'''
    <section>
      <h2>External / Axiomatized Functions ({len(externals)})</h2>
      <p><a href="external.html">View all external functions →</a></p>
    </section>
    '''

    content += '''
    <section>
      <h2>Dependency Graph</h2>
      <p><a href="graph.html">View the interactive function dependency graph →</a></p>
    </section>
    '''

    # Diagnostics / errors section
    diag_errors = errors or []
    if diag_errors:
        error_rows = "".join(
            f'<li class="diag-error">{_esc(e)}</li>' for e in diag_errors
        )
        content += f'''
    <section class="diagnostics">
      <h2>⚠ Diagnostics ({len(diag_errors)})</h2>
      <p>The following issues were detected during documentation generation.
         They may indicate bugs in the visualizer or missing Lean models.</p>
      <ul class="diag-list">{error_rows}</ul>
    </section>
    '''

    content += _page_footer()
    (output_dir / "index.html").write_text(content)


def generate_module_page(mod_name: str, functions: list,
                         types: list, output_dir: Path,
                         lean_map: dict = None, type_lean_map: dict = None,
                         rust_to_lean: dict = None,
                         globals_list: list = None):
    """Generate a module page."""
    mod_dir = output_dir / "mod"
    mod_dir.mkdir(parents=True, exist_ok=True)

    stats = VerificationStats(functions, mod_name)
    slug = mod_name.replace("::", ".")

    fn_rows = "".join(
        _function_row(fn, link_prefix="../", lean_map=lean_map,
                      rust_to_lean=rust_to_lean)
        for fn in sorted(functions, key=lambda f: f.short_name)
    )

    tl = type_lean_map or {}
    type_rows = ""
    for t in sorted(types, key=lambda x: x.short_name):
        ld = tl.get(t.name_pattern)
        name_cell = (f'<a href="../lean/{ld.slug}.html">{_esc(t.display_name)}</a>'
                     if ld else _esc(t.display_name))
        type_rows += (
            f'<tr><td>{name_cell}</td>'
            f'<td>{_esc(t.kind)}</td>'
            f'<td>{"pub" if t.is_public else ""}</td></tr>'
        )

    content = _page_header(
        f"Module: {mod_name}",
        breadcrumbs=[("Index", "index.html"), (mod_name, None)],
        depth=1
    )
    content += f'''
    {_progress_bar(stats)}
    {_stats_table(stats)}

    <h2>Functions</h2>
    <label style="margin-bottom:8px;display:inline-block;cursor:pointer">
      <input type="checkbox" id="only-public" onchange="
        document.querySelectorAll('#fn-table tbody tr').forEach(r =>
          r.style.display = this.checked && r.dataset.public === 'false' ? 'none' : '')
      "> Only public
    </label>
    <table class="data-table" id="fn-table">
      <colgroup><col class="col-name"><col class="col-vis"><col class="col-status"><col class="col-lean"><col class="col-thm"></colgroup>
      <thead><tr><th>Function</th><th>Vis</th><th>Status</th><th>Lean Model</th><th>Theorem</th></tr></thead>
      <tbody>{fn_rows}</tbody>
    </table>
    '''

    if type_rows:
        content += f'''
    <h2>Types</h2>
    <table class="data-table">
      <colgroup><col style="width:60%"><col style="width:20%"><col style="width:20%"></colgroup>
      <thead><tr><th>Type</th><th>Kind</th><th>Vis</th></tr></thead>
      <tbody>{type_rows}</tbody>
    </table>
    '''

    # Constants/globals for this module (already includes submodules)
    mod_globals = globals_list or []
    if mod_globals:
        global_rows = "".join(
            _global_row(g, link_prefix="../", lean_map=lean_map,
                        rust_to_lean=rust_to_lean)
            for g in sorted(mod_globals, key=lambda x: x.short_name)
        )
        content += f'''
    <h2>Constants</h2>
    <table class="data-table">
      <colgroup><col class="col-name"><col class="col-vis"><col class="col-status"><col class="col-lean"><col class="col-thm"></colgroup>
      <thead><tr><th>Constant</th><th>Vis</th><th>Status</th><th>Lean Model</th><th>Theorem</th></tr></thead>
      <tbody>{global_rows}</tbody>
    </table>
    '''

    content += _page_footer(depth=1)
    (mod_dir / f"{slug}.html").write_text(content)


def generate_function_page(fn: 'RustFunction', output_dir: Path,
                           known_fns: dict = None,
                           lean_defs: list = None,
                           lean_map: dict = None):
    """Generate a per-function detail page."""
    fn_dir = output_dir / "fn"
    fn_dir.mkdir(parents=True, exist_ok=True)
    lean_defs = lean_defs or []

    content = _page_header(
        fn.display_name,
        breadcrumbs=[
            ("Index", "index.html"),
            (fn.module, f"mod/{fn.module.replace('::', '.')}.html"),
            (fn.short_name, None),
        ],
        depth=1,
    )

    content += f'''
    <div class="fn-header">
      {_badge_html(fn.status)}
      <span class="fn-visibility">{"pub " if fn.is_public else ""}</span>
      <code class="fn-name">{_esc(fn.display_name)}</code>
    </div>
    '''

    # Lean model cross-link(s)
    if lean_defs:
        if len(lean_defs) == 1:
            ld = lean_defs[0]
            content += f'<p class="cross-link">Lean model: <a href="../lean/{ld.slug}.html">{_esc(ld.name)}</a></p>'
        else:
            links = ", ".join(
                f'<a href="../lean/{ld.slug}.html">{_esc(ld.name)}</a>'
                for ld in lean_defs
            )
            content += f'<p class="cross-link">Lean models: {links}</p>'

    # Source location
    if fn.file_path and fn.line_range:
        begin, end = fn.line_range
        src_link = f"../source/rust/{fn.file_path.replace('/', '_')}.html#L{begin}"
        content += f'<p class="src-link">Source: <a href="{src_link}">{_esc(fn.file_path)}:{begin}-{end}</a></p>'

    # Rust source
    if fn.source_text:
        content += f'''
    <h2>Rust Source</h2>
    <details open>
      <summary>View source</summary>
      {_source_block(fn.source_text, "rust")}
    </details>
    '''

    # Step theorems (no fn_slug — we're already on this function's page)
    content += _render_theorem_sections(fn.step_theorems, known_fns=known_fns,
                                         depth=1, lean_map=lean_map,
                                         link_prefix="../")

    content += _page_footer(depth=1)
    (fn_dir / f"{fn.slug}.html").write_text(content)


def generate_global_page(g: 'RustGlobal', output_dir: Path,
                         known_fns: dict = None,
                         lean_defs: list = None,
                         lean_map: dict = None):
    """Generate a per-constant detail page (same layout as function pages)."""
    fn_dir = output_dir / "fn"
    fn_dir.mkdir(parents=True, exist_ok=True)
    lean_defs = lean_defs or []

    content = _page_header(
        g.display_name,
        breadcrumbs=[
            ("Index", "index.html"),
            (g.module, f"mod/{g.module.replace('::', '.')}.html"),
            (g.short_name, None),
        ],
        depth=1,
    )

    content += f'''
    <div class="fn-header">
      {_badge_html(g.status)}
      <span class="fn-visibility">{"pub " if g.is_public else ""}</span>
      <code class="fn-name">{_esc(g.display_name)}</code>
      <span style="color:#888;margin-left:8px">(constant)</span>
    </div>
    '''

    # Lean model cross-link(s)
    if lean_defs:
        if len(lean_defs) == 1:
            ld = lean_defs[0]
            content += f'<p class="cross-link">Lean model: <a href="../lean/{ld.slug}.html">{_esc(ld.name)}</a></p>'
        else:
            links = ", ".join(
                f'<a href="../lean/{ld.slug}.html">{_esc(ld.name)}</a>'
                for ld in lean_defs
            )
            content += f'<p class="cross-link">Lean models: {links}</p>'

    # Source location
    if g.file_path and g.line_range:
        begin, end = g.line_range
        src_link = f"../source/rust/{g.file_path.replace('/', '_')}.html#L{begin}"
        content += f'<p class="src-link">Source: <a href="{src_link}">{_esc(g.file_path)}:{begin}-{end}</a></p>'

    # Rust source
    if g.source_text:
        content += f'''
    <h2>Rust Source</h2>
    <details open>
      <summary>View source</summary>
      {_source_block(g.source_text, "rust")}
    </details>
    '''

    # Step theorems
    content += _render_theorem_sections(g.step_theorems, known_fns=known_fns,
                                         depth=1, lean_map=lean_map,
                                         link_prefix="../")

    content += _page_footer(depth=1)
    (fn_dir / f"{g.slug}.html").write_text(content)


def generate_external_page(functions: list, output_dir: Path,
                           lean_map: dict = None, known_fns: dict = None,
                           rust_to_lean: dict = None):
    """Generate the external/axiomatized functions page."""
    externals = [f for f in functions if f.status == STATUS_EXTERNAL]

    rows = ""
    spec_details = ""
    for fn in sorted(externals, key=lambda f: f.display_name):
        name_link = f'<a href="fn/{fn.slug}.html">{_esc(fn.display_name)}</a>'
        has_spec = "Yes" if fn.step_theorems else "No"
        thm_col = _theorem_links(fn.step_theorems, lean_map, fn_slug=fn.slug) or "—"
        lean_col = _lean_model_links(fn, rust_to_lean)
        rows += (
            f'<tr><td>{name_link}</td>'
            f'<td>{"pub" if fn.is_public else ""}</td>'
            f'<td>{has_spec}</td>'
            f'<td>{lean_col}</td>'
            f'<td class="thm-name">{thm_col}</td>'
            f'</tr>'
        )
        # Collect theorem statements for display below the table
        if fn.step_theorems:
            for thm in fn.step_theorems:
                sorry_badge = _badge_html(
                    STATUS_VERIFIED if thm.sorry_status == "verified"
                    else STATUS_SPECIFIED if thm.sorry_status == "specified"
                    else STATUS_PARTIAL
                )
                stmt_html = _annotated_statement_block(thm, known_fns=known_fns)
                spec_details += f'''
    <div class="theorem-card">
      <div class="theorem-header">
        <code class="thm-name">{_esc(thm.theorem_name)}</code>
        {sorry_badge}
        <span class="cross-link" style="margin-left:8px">for <a href="fn/{fn.slug}.html">{_esc(fn.display_name)}</a></span>
      </div>
      <details>
        <summary>View statement</summary>
        <div class="theorem-statement">{stmt_html}</div>
      </details>
    </div>
    '''

    content = _page_header(
        "External / Axiomatized Functions",
        breadcrumbs=[("Index", "index.html"), ("External", None)],
    )
    content += f'''
    <p>These functions are opaque (have no body in the LLBC translation). They are
    axiomatized — their behavior is assumed, not proved. Any specification theorem
    for these functions is an axiom that must be trusted.</p>

    <table class="data-table">
      <colgroup><col class="col-name"><col class="col-vis"><col class="col-status"><col class="col-lean"><col class="col-thm"></colgroup>
      <thead><tr><th>Function</th><th>Vis</th><th>Has Spec</th><th>Lean Model</th><th>Theorem</th></tr></thead>
      <tbody>{rows}</tbody>
    </table>
    '''

    if spec_details:
        content += f'''
    <h2>Axiomatized Specifications</h2>
    <p>These theorem statements are assumed (axioms) — they constrain the behavior
    of external functions but are not machine-checked proofs.</p>
    {spec_details}
    '''

    content += _page_footer()
    (output_dir / "external.html").write_text(content)


def generate_source_pages(functions: list, rust_src_dir: Optional[str],
                          output_dir: Path):
    """Generate source viewer pages for Rust files."""
    src_dir = output_dir / "source" / "rust"
    src_dir.mkdir(parents=True, exist_ok=True)

    # Collect all referenced files
    files = set()
    for fn in functions:
        if fn.file_path:
            files.add(fn.file_path)

    for file_path in sorted(files):
        # Try to read the file
        source = None
        if rust_src_dir:
            # Try relative to rust_src_dir
            candidates = [
                Path(rust_src_dir) / file_path,
                Path(file_path),
            ]
            for candidate in candidates:
                if candidate.exists():
                    source = candidate.read_text()
                    break

        if source is None:
            # Reconstruct from function source_text (imperfect but useful)
            source = f"// Source file: {file_path}\n// (Full source not available)\n"

        slug = file_path.replace("/", "_")

        content = _page_header(
            file_path,
            breadcrumbs=[("Index", "index.html"), ("Source", None), (file_path, None)],
            depth=2,
        )
        content += f'''
    <div class="source-viewer">
      {_source_block_with_lines(source, "rust")}
    </div>
    '''
        content += _page_footer(depth=2)
        (src_dir / f"{slug}.html").write_text(content)


def generate_lean_page(lean_def: 'LeanDefinition', output_dir: Path,
                       known_fns: dict = None, rust_fn_map: dict = None,
                       lean_src_dir: str = None):
    """Generate a per-Lean-definition detail page."""
    lean_dir = output_dir / "lean"
    lean_dir.mkdir(parents=True, exist_ok=True)

    kind_label = {
        "def": "Definition",
        "inductive": "Inductive Type",
        "structure": "Structure",
        "abbreviation": "Abbreviation",
        "opaque": "Opaque",
        "axiom": "Axiom",
    }.get(lean_def.kind, lean_def.kind.capitalize())

    content = _page_header(
        lean_def.display_name,
        breadcrumbs=[
            ("Index", "index.html"),
            ("Lean", None),
            (lean_def.name, None),
        ],
        depth=1,
    )

    content += f'''
    <div class="fn-header">
      <span class="lean-kind-badge">{_esc(kind_label)}</span>
      <code class="fn-name">{_esc(lean_def.name)}</code>
    </div>
    '''

    # Signature block with binder-by-binder rendering when available
    kind_kw = lean_def.kind if lean_def.kind in ("def", "inductive", "structure",
        "opaque", "axiom", "abbrev") else "def"
    if lean_def.binders is not None and lean_def.return_type is not None:
        # Build natural header: def name {T : Type} (l : CList T) : ReturnType
        sig_parts: list = [f'<span class="kw">{_esc(kind_kw)}</span> {_esc(lean_def.name)}']
        for b in lean_def.binders:
            bname = _esc(b["name"])
            btype_html = _render_annotated_html(b["annotated_type"], known_fns or {}, inline=True)
            if b.get("inst_implicit"):
                sig_parts.append(f' [{bname} : {btype_html}]')
            elif b.get("implicit"):
                sig_parts.append(f' {{{bname} : {btype_html}}}')
            else:
                sig_parts.append(f' ({bname} : {btype_html})')
        ret_html = _render_annotated_html(lean_def.return_type["annotated_type"],
                                          known_fns or {}, inline=True)
        sig_parts.append(f' : {ret_html}')
        sig_html = f'<pre class="lean-annotated">{"".join(sig_parts)}</pre>'
        content += f'''
    <h2>Signature</h2>
    {sig_html}
    '''
    elif lean_def.type_signature:
        # Fallback: "def name : full_type" (flat)
        if lean_def.annotated_type_signature:
            sig_annotated = [f"{kind_kw} {lean_def.name} : "] + lean_def.annotated_type_signature
            sig_html = _render_annotated_html(sig_annotated, known_fns or {})
        else:
            sig_html = _annotated_lean_block(
                f"{kind_kw} {lean_def.name} : {lean_def.type_signature}",
                known_fns or {})
        content += f'''
    <h2>Signature</h2>
    {sig_html}
    '''

    # Rust counterpart link — make the Rust name itself clickable
    if lean_def.rust_name:
        if lean_def.rust_fn:
            content += f'''
    <p class="cross-link">Implements: <a href="../fn/{lean_def.rust_fn.slug}.html"><code>{_esc(lean_def.rust_name)}</code></a></p>
    '''
        else:
            content += f'''
    <p class="cross-link">Implements: <code>{_esc(lean_def.rust_name)}</code></p>
    '''

    # Lean source location
    if lean_def.lean_source:
        ls = lean_def.lean_source
        begin = ls.get("begin_line", 0)
        end = ls.get("end_line", 0)
        module_file = lean_def.module.replace(".", "/") + ".lean"
        src_slug = module_file.replace("/", "_")
        src_link = f"../source/lean/{src_slug}.html#L{begin}"
        content += f'<p class="src-link">Source: <a href="{src_link}">{_esc(module_file)}:{begin}-{end}</a></p>'

    # Lean definition body — show natural def header + annotated body with
    # clickable identifiers.  Fall back to source file.
    if lean_def.annotated_body:
        # Build header: def name {T} (l : CList T) : RetType :=
        header_parts: list = [f'<span class="kw">{_esc(kind_kw)}</span> {_esc(lean_def.name)}']
        if lean_def.binders is not None:
            for b in lean_def.binders:
                bname = _esc(b["name"])
                btype_html = _render_annotated_html(b["annotated_type"], known_fns or {}, inline=True)
                if b.get("inst_implicit"):
                    header_parts.append(f' [{bname} : {btype_html}]')
                elif b.get("implicit"):
                    header_parts.append(f' {{{bname} : {btype_html}}}')
                else:
                    header_parts.append(f' ({bname} : {btype_html})')
        if lean_def.return_type is not None:
            ret_html = _render_annotated_html(lean_def.return_type["annotated_type"],
                                              known_fns or {}, inline=True)
            header_parts.append(f' : {ret_html}')
        header_parts.append(f' :=')
        body_html = _render_annotated_html(lean_def.annotated_body, known_fns or {}, inline=True)
        full_def_html = (
            f'<pre class="lean-annotated">{"".join(header_parts)}\n'
            f'  {body_html}</pre>'
        )
        content += f'''
    <h2>Definition</h2>
    <details open>
      <summary>View definition</summary>
      {full_def_html}
    </details>
    '''
    elif lean_def.lean_source and lean_src_dir:
        ls = lean_def.lean_source
        begin = ls.get("begin_line", 1)
        end = ls.get("end_line", begin)
        module_file = lean_def.module.replace(".", "/") + ".lean"
        src_path = Path(lean_src_dir) / module_file
        if src_path.exists():
            all_lines = src_path.read_text().split("\n")
            body_lines = all_lines[max(0, begin - 1):end]
            body_lines = _strip_lean_docstring(body_lines)
            body_text = "\n".join(body_lines)
            if body_text.strip():
                content += f'''
    <h2>Definition</h2>
    <details open>
      <summary>View definition</summary>
      {_annotated_lean_block(body_text, known_fns or {})}
    </details>
    '''

    # Step theorems
    content += _render_theorem_sections(lean_def.step_theorems, known_fns=known_fns, depth=1)

    content += _page_footer(depth=1)
    (lean_dir / f"{lean_def.slug}.html").write_text(content)


def generate_lean_source_pages(lean_definitions: list, lean_src_dir: Optional[str],
                               output_dir: Path):
    """Generate source viewer pages for Lean files."""
    src_dir = output_dir / "source" / "lean"
    src_dir.mkdir(parents=True, exist_ok=True)

    # Collect all referenced Lean modules
    modules = set()
    for ld in lean_definitions:
        if ld.module:
            modules.add(ld.module)

    for module in sorted(modules):
        module_file = module.replace(".", "/") + ".lean"
        source = None
        if lean_src_dir:
            candidate = Path(lean_src_dir) / module_file
            if candidate.exists():
                source = candidate.read_text()

        if source is None:
            source = f"-- Lean module: {module}\n-- (Full source not available)\n"

        slug = module_file.replace("/", "_")

        content = _page_header(
            module_file,
            breadcrumbs=[("Index", "index.html"), ("Lean Source", None),
                         (module_file, None)],
            depth=2,
        )
        content += f'''
    <div class="source-viewer">
      {_source_block_with_lines(source, "lean")}
    </div>
    '''
        content += _page_footer(depth=2)
        (src_dir / f"{slug}.html").write_text(content)


# ---------------------------------------------------------------------------
# CSS
# ---------------------------------------------------------------------------

CUSTOM_CSS = '''
/* Aeneas Verification Docs */
:root {
  --bg: #fff;
  --fg: #24292e;
  --border: #e1e4e8;
  --bg-secondary: #f6f8fa;
  --link: #0366d6;
}
* { box-sizing: border-box; }
body {
  font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Helvetica, Arial, sans-serif;
  color: var(--fg);
  background: var(--bg);
  margin: 0;
  padding: 0;
  line-height: 1.5;
}
.top-nav {
  background: var(--bg-secondary);
  border-bottom: 1px solid var(--border);
  padding: 8px 24px;
  display: flex;
  align-items: center;
  gap: 12px;
}
.nav-home {
  font-weight: 600;
  color: var(--fg);
  text-decoration: none;
}
.breadcrumbs { color: #586069; font-size: 0.9em; }
.breadcrumbs a { color: var(--link); text-decoration: none; }
main {
  width: 80%;
  max-width: 1600px;
  margin: 0 auto;
  padding: 24px;
}
h1 { border-bottom: 1px solid var(--border); padding-bottom: 8px; }
h2 { margin-top: 32px; }
a { color: var(--link); text-decoration: none; }
a:hover { text-decoration: underline; }

.data-table {
  width: 100%;
  border-collapse: collapse;
  margin: 12px 0;
  table-layout: fixed;
}
.data-table th, .data-table td {
  border: 1px solid var(--border);
  padding: 6px 12px;
  text-align: left;
  overflow-wrap: break-word;
  word-break: break-word;
}
/* Column width hints (applied via colgroup in HTML) */
.col-name   { width: 32%; }
.col-status { width: 13%; }
.col-lean   { width: 27%; }
.col-thm    { width: 23%; }
.col-vis    { width: 5%; }
.col-mod    { width: 40%; }
.col-count  { width: 10%; }
.col-prog   { width: 25%; }
.data-table th {
  background: var(--bg-secondary);
  font-weight: 600;
}
.data-table tr:hover { background: #f0f4f8; }
.stats-table {
  border-collapse: collapse;
  margin: 12px auto;
}
.stats-table th, .stats-table td {
  border: 1px solid var(--border);
  padding: 4px 12px;
}
.stats-table th { background: var(--bg-secondary); }

.badge {
  display: inline-block;
  font-size: 0.85em;
  padding: 2px 8px;
  border-radius: 4px;
  color: #fff;
}

.fn-header {
  display: flex;
  align-items: center;
  gap: 12px;
  margin: 16px 0;
}
.fn-name { font-size: 1.2em; }
.fn-visibility { color: #6a737d; }
.src-link { color: #586069; font-size: 0.9em; }
.cross-link { color: #586069; font-size: 0.95em; margin: 4px 0; }
.cross-link a { color: var(--link); }
.cross-link code { background: var(--bg-secondary); padding: 1px 4px; border-radius: 3px; }
.no-spec { color: #dc3545; font-style: italic; }
.lean-kind-badge {
  background: #e8eef4;
  color: #24292e;
  padding: 2px 10px;
  border-radius: 4px;
  font-size: 0.85em;
  font-weight: 600;
}

.theorem-card {
  border: 1px solid var(--border);
  border-radius: 6px;
  margin: 12px 0;
  overflow: hidden;
}
.theorem-header {
  background: var(--bg-secondary);
  padding: 8px 16px;
  display: flex;
  align-items: center;
  gap: 12px;
  border-bottom: 1px solid var(--border);
}
.theorem-statement { padding: 0; }
.theorem-statement pre {
  margin: 0;
  border-radius: 0;
}
/* Decomposed spec: binders above separator, body below */
.spec-decomposed { font-family: 'SFMono-Regular',Consolas,'Liberation Mono',Menlo,monospace; }
.spec-decomposed pre { margin: 0; border: none; border-radius: 0; padding: 8px 16px; }
.spec-context code { opacity: 0.85; }
.spec-binder-name { color: #953800; font-weight: 600; }
hr.spec-sep {
  border: none;
  border-top: 1px solid #8b949e;
  margin: 4px 16px;
}
.spec-body code { font-weight: 500; }
.thm-name { font-family: monospace; font-size: 0.9em; }

/* Clickable Lean identifiers in annotated statements */
a.lean-ident {
  color: #0969da !important;
  text-decoration: underline !important;
  text-decoration-style: dotted !important;
  cursor: pointer !important;
}
a.lean-ident:hover {
  text-decoration-style: solid !important;
  background-color: rgba(9, 105, 218, 0.12);
}
span.lean-ident {
  color: #0550ae !important;
  cursor: help;
}
span.lean-ident:hover {
  background-color: rgba(5, 80, 174, 0.08);
}

/* Server-side Lean syntax highlighting classes */
.lean-annotated { background: #f6f8fa; border: 1px solid #d0d7de; border-radius: 6px; padding: 12px; overflow-x: auto; }
.lean-annotated code { background: transparent; padding: 0; }
.lean-annotated .lk { color: #8959a8; }  /* keywords: ∀, fun, do, let... */
.lean-annotated .ln { color: #f5871f; }  /* number literals */
.lean-annotated .lo { color: #3e999f; }  /* operators: →, ⦃, ⦄, ↑ */

details summary {
  cursor: pointer;
  padding: 4px 0;
  color: var(--link);
}
pre code {
  font-size: 0.875em;
}
.source-viewer pre {
  max-height: none;
}
.source-viewer-inner { overflow-x: auto; }
.source-table {
  border-collapse: collapse;
  width: 100%;
  border: 1px solid var(--border);
  border-radius: 6px;
  overflow: hidden;
  font-size: 13px;
  line-height: 20px;
  font-family: 'SFMono-Regular', Consolas, 'Liberation Mono', Menlo, monospace;
}
.source-table td { padding: 0; vertical-align: top; }
.line-num {
  width: 1px;
  min-width: 50px;
  white-space: nowrap;
  text-align: right;
  user-select: none;
  background: #f6f8fa;
  border-right: 1px solid var(--border);
  padding: 0 10px;
}
.line-num a {
  color: #8b949e;
  text-decoration: none;
  display: block;
}
.line-num a:hover { color: var(--link); }
.line-num:target, .line-num:target a {
  background: #fff8c5;
  color: #24292e;
  font-weight: bold;
}
.line-code { padding-left: 16px !important; white-space: pre; }

/* Diagnostics */
.diagnostics {
  border: 2px solid #f0ad4e;
  border-radius: 8px;
  padding: 16px 24px;
  margin-top: 32px;
  background: #fff8e6;
}
.diagnostics h2 { color: #856404; margin-top: 8px; }
.diag-list { margin: 8px 0; padding-left: 20px; }
.diag-error { color: #856404; margin: 4px 0; }

/* Legend / status explanation */
.legend-box {
  border: 1px solid var(--border);
  border-radius: 8px;
  padding: 16px 24px;
  margin-top: 24px;
  background: #f8f9fa;
}
.legend-box h2 { margin-top: 8px; font-size: 1.1em; }
.status-legend { margin: 12px 0 0 0; }
.status-legend dt {
  margin-top: 10px;
  font-weight: 600;
  display: flex;
  align-items: center;
  gap: 6px;
}
.status-legend dd {
  margin: 4px 0 0 28px;
  color: #555;
  line-height: 1.5;
}

/* Search */
.search-box {
  position: relative;
  margin: 16px 0;
}
#search-input {
  width: 100%;
  padding: 8px 12px;
  border: 1px solid var(--border);
  border-radius: 6px;
  font-size: 1em;
}
#search-input:focus { outline: 2px solid var(--link); }
#search-results {
  position: absolute;
  top: 100%;
  left: 0;
  right: 0;
  background: var(--bg);
  border: 1px solid var(--border);
  border-top: none;
  border-radius: 0 0 6px 6px;
  z-index: 10;
  max-height: 400px;
  overflow-y: auto;
  display: none;
}
#search-results:not(:empty) { display: block; }
.search-item {
  padding: 6px 12px;
  border-bottom: 1px solid var(--border);
}
.search-item:hover { background: var(--bg-secondary); }
.search-item a { font-weight: 500; }
.search-kind { color: #586069; font-size: 0.85em; margin-left: 8px; }
.search-status {
  font-size: 0.8em; padding: 1px 6px; border-radius: 3px; color: #fff;
}
.search-status-verified { background: #28a745; }
.search-status-verified_unverified_deps {
  background: ''' + _STRIPE_BG + ''';
}
.search-status-partially_verified { background: #007bff; }
.search-status-specified { background: #ffc107; color: #333; }
.search-status-unverified { background: #dc3545; }
.search-status-external { background: #6f42c1; }
.search-no-results { padding: 8px 12px; color: #586069; }

/* Collapsible module tree */
.parent-module { cursor: pointer; }
.parent-module:hover { background: var(--bg-secondary); }
.expand-arrow { font-size: 0.8em; color: #586069; transition: transform 0.15s; }
.parent-module.expanded .expand-arrow { transform: rotate(90deg); }
.child-module td:first-child { font-size: 0.95em; }
'''


# ---------------------------------------------------------------------------
# Dependency graph page
# ---------------------------------------------------------------------------

def generate_graph_page(functions: list, output_dir: Path):
    """Generate an interactive dependency graph page using D3.js."""
    # Build def_id → function lookup
    id_to_fn = {fn.def_id: fn for fn in functions}

    # Build nodes and edges
    nodes = []
    edges = []
    fn_ids_in_graph = set()

    for fn in functions:
        fn_ids_in_graph.add(fn.def_id)

    for fn in functions:
        slug = fn.rust_path
        _, _, color, _ = STATUS_LABELS.get(fn.status, ("?", "?", "#999", "unknown"))
        if fn.status == STATUS_VERIFIED_UNVERIFIED_DEPS:
            color = "url(#stripe-pattern)"
        nodes.append({
            "id": fn.def_id,
            "name": fn.short_name,
            "full_name": fn.name_pattern,
            "status": fn.status,
            "color": color,
            "is_public": fn.is_public,
            "url": f"fn/{slug}.html",
            "theorem": fn.step_theorems[0].theorem_name if fn.step_theorems else None,
        })
        for callee_id in fn.callee_ids:
            if callee_id in fn_ids_in_graph:
                edges.append({"source": fn.def_id, "target": callee_id})

    import json as json_mod
    graph_data = json_mod.dumps({"nodes": nodes, "links": edges})

    content = _page_header("Dependency Graph",
        breadcrumbs=[("Index", "index.html"), ("Dependency Graph", None)])

    content += f'''
    <section>
      <h2>Function Dependency Graph</h2>
      <p style="color:#586069;margin-bottom:8px">
        Nodes are functions, edges are call dependencies.
        Color indicates verification status.
        Hover for details, click to navigate. Drag nodes, scroll to zoom.
      </p>
      <div style="margin-bottom:8px">
        <label><input type="checkbox" id="filter-local"> Local only (hide external)</label>
        <label style="margin-left:16px"><input type="checkbox" id="filter-public"> Public only</label>
      </div>
      <div id="graph-container" style="border:1px solid var(--border);border-radius:8px;
           background:#fafbfc;position:relative;width:100%;height:600px;overflow:hidden">
        <svg id="graph-svg" width="100%" height="100%"></svg>
      </div>
      <div id="graph-tooltip" style="position:fixed;padding:8px 12px;background:#24292e;
           color:#fff;border-radius:6px;font-size:0.85em;pointer-events:none;opacity:0;
           max-width:400px;z-index:1000;line-height:1.4;white-space:pre-wrap"></div>
    </section>
    '''

    content += f'''
    <script src="static/d3.v7.min.js"></script>
    <script>
    (function() {{
      const data = {graph_data};
      const container = document.getElementById("graph-container");
      const svg = d3.select("#graph-svg");
      const tooltip = document.getElementById("graph-tooltip");
      const width = container.clientWidth;
      const height = container.clientHeight;

      // Filters
      const filterLocal = document.getElementById("filter-local");
      const filterPublic = document.getElementById("filter-public");

      function getVisibleData() {{
        let nodes = data.nodes;
        if (filterLocal.checked) nodes = nodes.filter(n => n.status !== "external");
        if (filterPublic.checked) nodes = nodes.filter(n => n.is_public);
        const nodeIds = new Set(nodes.map(n => n.id));
        const links = data.links.filter(l => nodeIds.has(l.source.id ?? l.source) && nodeIds.has(l.target.id ?? l.target));
        return {{ nodes, links }};
      }}

      let sim, linkSel, nodeSel, labelSel, gMain;

      // Arrow marker
      const defs = svg.append("defs");
      defs.append("marker")
        .attr("id", "arrow").attr("viewBox", "0 -5 10 10")
        .attr("refX", 26).attr("refY", 0)
        .attr("markerWidth", 6).attr("markerHeight", 6)
        .attr("orient", "auto")
        .append("path").attr("d", "M0,-5L10,0L0,5")
        .attr("fill", "#999");

      // Diagonal stripe pattern for "verified with unverified deps"
      const pat = defs.append("pattern")
        .attr("id", "stripe-pattern")
        .attr("width", 8).attr("height", 8)
        .attr("patternUnits", "userSpaceOnUse")
        .attr("patternTransform", "rotate(-45)");
      pat.append("rect").attr("width", 4).attr("height", 8).attr("fill", "#28a745");
      pat.append("rect").attr("x", 4).attr("width", 4).attr("height", 8).attr("fill", "#007bff");

      // Zoom
      const zoom = d3.zoom().scaleExtent([0.1, 5]).on("zoom", e => {{
        gMain.attr("transform", e.transform);
      }});
      svg.call(zoom);
      gMain = svg.append("g");

      function render() {{
        const {{ nodes, links }} = getVisibleData();
        gMain.selectAll("*").remove();

        linkSel = gMain.append("g").selectAll("line")
          .data(links).enter().append("line")
          .attr("stroke", "#bbb").attr("stroke-width", 1.5)
          .attr("marker-end", "url(#arrow)");

        const nodeG = gMain.append("g").selectAll("g")
          .data(nodes).enter().append("g").attr("cursor", "pointer");

        nodeSel = nodeG.append("circle")
          .attr("r", d => d.is_public ? 16 : 11)
          .attr("fill", d => d.color)
          .attr("stroke", d => d.is_public ? "#24292e" : "none")
          .attr("stroke-width", 2);

        labelSel = nodeG.append("text")
          .text(d => d.full_name)
          .attr("dx", 18).attr("dy", 5)
          .attr("font-size", "14px").attr("fill", "#24292e")
          .attr("font-weight", d => d.is_public ? "600" : "400");

        // Tooltip
        nodeG.on("mouseover", (e, d) => {{
          let html = d.full_name + "\\nStatus: " + d.status;
          if (d.theorem) html += "\\nTheorem: " + d.theorem;
          tooltip.textContent = html;
          tooltip.style.opacity = "0.95";
        }}).on("mousemove", (e) => {{
          tooltip.style.left = (e.clientX + 12) + "px";
          tooltip.style.top = (e.clientY - 10) + "px";
        }}).on("mouseout", () => {{
          tooltip.style.opacity = "0";
        }}).on("click", (e, d) => {{
          window.location.href = d.url;
        }});

        // Drag
        nodeG.call(d3.drag()
          .on("start", (e, d) => {{ if (!e.active) sim.alphaTarget(0.3).restart(); d.fx = d.x; d.fy = d.y; }})
          .on("drag", (e, d) => {{ d.fx = e.x; d.fy = e.y; }})
          .on("end", (e, d) => {{ if (!e.active) sim.alphaTarget(0); d.fx = null; d.fy = null; }})
        );

        // Simulation
        sim = d3.forceSimulation(nodes)
          .force("link", d3.forceLink(links).id(d => d.id).distance(60))
          .force("charge", d3.forceManyBody().strength(-120))
          .force("center", d3.forceCenter(width / 2, height / 2))
          .force("collide", d3.forceCollide(50))
          .on("tick", () => {{
            linkSel
              .attr("x1", d => d.source.x).attr("y1", d => d.source.y)
              .attr("x2", d => d.target.x).attr("y2", d => d.target.y);
            nodeG.attr("transform", d => `translate(${{d.x}},${{d.y}})`);
          }})
          .on("end", () => {{
            // Zoom-to-fit once simulation settles
            const bounds = gMain.node().getBBox();
            if (bounds.width === 0 || bounds.height === 0) return;
            const pad = 40;
            const scale = Math.min(
              width / (bounds.width + pad * 2),
              height / (bounds.height + pad * 2),
              2
            );
            const tx = width / 2 - (bounds.x + bounds.width / 2) * scale;
            const ty = height / 2 - (bounds.y + bounds.height / 2) * scale;
            svg.transition().duration(500).call(
              zoom.transform,
              d3.zoomIdentity.translate(tx, ty).scale(scale)
            );
          }});
      }}

      render();
      filterLocal.addEventListener("change", render);
      filterPublic.addEventListener("change", render);
    }})();
    </script>
    '''

    content += _page_footer()
    (output_dir / "graph.html").write_text(content)


# ---------------------------------------------------------------------------
# Main generator
# ---------------------------------------------------------------------------

def generate_docs(
    doc_info_path: str,
    lean_doc_path: Optional[str],
    rust_src_dir: Optional[str],
    output_dir: str,
    title: Optional[str] = None,
    lean_src_dir: Optional[str] = None,
):
    """Generate the complete documentation site."""
    out = Path(output_dir)
    out.mkdir(parents=True, exist_ok=True)

    # Load data
    doc_info = load_doc_info(doc_info_path)
    crate_name = title or doc_info.get("crate_name", "Unknown Crate")

    global _CRATE_TITLE
    _CRATE_TITLE = f"{crate_name} — Verification Dashboard"

    functions = parse_functions(doc_info)
    types = parse_types(doc_info)
    globals_list = parse_globals(doc_info)

    # Load Lean data if available
    theorems = []
    lean_definitions = []
    if lean_doc_path and os.path.exists(lean_doc_path):
        lean_doc = load_lean_doc(lean_doc_path)
        theorems = parse_step_theorems(lean_doc)
        lean_definitions = parse_lean_definitions(lean_doc)

    # Match Rust functions ↔ step theorems (sets fn.status and fn.step_theorems)
    match_functions_to_theorems(functions, theorems)

    # Match globals ↔ step theorems
    match_globals_to_theorems(globals_list, theorems)

    # Downgrade verified functions with unverified transitive dependencies
    _mark_verified_with_unverified_deps(functions)

    # Filter out uninteresting functions (global initializers are shown as
    # constants, not functions)
    functions = [
        f for f in functions
        if f.name_pattern and f.name_pattern != "UNIT_METADATA"
        and not f.is_global_init
    ]

    # --- Build Rust ↔ Lean mapping ---
    errors = []
    rust_to_lean = defaultdict(list)  # rust_name_pattern → [LeanDefinition, ...]
    lean_to_rust = {}   # lean_name → rust_name_pattern
    rust_fn_map = {}    # rust_name_pattern → RustFunction

    for fn in functions:
        rust_fn_map[fn.name_pattern] = fn
    for g in globals_list:
        rust_fn_map[g.name_pattern] = g

    for ld in lean_definitions:
        if not ld.rust_name:
            continue
        rust_to_lean[ld.rust_name].append(ld)
        lean_to_rust[ld.name] = ld.rust_name

        # Cross-link
        if ld.rust_name in rust_fn_map:
            ld.rust_fn = rust_fn_map[ld.rust_name]

    # Build a normalized lookup: Lean's rust_name uses "for" syntax for trait impls
    # while LLBC uses angle brackets. Normalize both for matching.
    import re
    def _normalize_rust_name(name: str) -> str:
        """Normalize trait impl syntax: {T<U>} → {T for U}"""
        # Pattern: {path::Trait<Type>}
        def _repl(m):
            inner = m.group(1)
            # Find the angle-bracket args
            angle_match = re.search(r'<(.+?)>$', inner)
            if angle_match:
                base = inner[:angle_match.start()]
                args = angle_match.group(1)
                return '{' + base + ' for ' + args + '}'
            return m.group(0)
        return re.sub(r'\{([^}]+)\}', _repl, name)

    lean_rust_names_norm = defaultdict(list)  # normalized_rust_name → [LeanDefinition, ...]
    for ld in lean_definitions:
        if ld.rust_name:
            lean_rust_names_norm[_normalize_rust_name(ld.rust_name)].append(ld)

    # Check for unmatched local Rust functions
    for fn in functions:
        is_local = not (fn.is_opaque or not fn.has_body)
        is_external_module = any(
            fn.name_pattern.startswith(p)
            for p in ("core::", "alloc::", "std::")
        )
        if is_local and not is_external_module and fn.name_pattern not in rust_to_lean:
            # Try normalized matching
            norm = _normalize_rust_name(fn.name_pattern)
            if norm in lean_rust_names_norm:
                for ld in lean_rust_names_norm[norm]:
                    rust_to_lean[fn.name_pattern].append(ld)
                    if fn.name_pattern in rust_fn_map:
                        ld.rust_fn = rust_fn_map[fn.name_pattern]
            else:
                errors.append(
                    f"Unmatched: Rust function '{fn.name_pattern}' has no Lean model"
                )

    # Match step theorems → Lean definitions
    thm_by_fun = defaultdict(list)
    for thm in theorems:
        thm_by_fun[thm.function_name].append(thm)

    for ld in lean_definitions:
        if ld.name in thm_by_fun:
            ld.step_theorems = thm_by_fun[ld.name]

    # Populate fn.lean_defs and collect all step_theorems across all Lean defs
    for fn in functions:
        lds = rust_to_lean.get(fn.name_pattern, [])
        fn.lean_defs = lds
        # Collect theorems from all Lean defs for this function
        all_thms = []
        for ld in lds:
            all_thms.extend(ld.step_theorems)
        if all_thms:
            fn.step_theorems = all_thms

    # Recompute status now that we have complete theorem lists
    for fn in functions:
        if fn.is_opaque or not fn.has_body:
            fn.status = STATUS_EXTERNAL
        elif not fn.step_theorems:
            fn.status = STATUS_UNVERIFIED
        else:
            statuses = {t.sorry_status for t in fn.step_theorems}
            if all(s == "verified" for s in statuses):
                fn.status = STATUS_VERIFIED
            elif all(s == "specified" for s in statuses):
                fn.status = STATUS_SPECIFIED
            else:
                fn.status = STATUS_PARTIAL

    # Compute stats (exclude external/axiomatized functions)
    local_functions = [f for f in functions if f.status != STATUS_EXTERNAL]
    stats = VerificationStats(local_functions, crate_name)

    # Copy static assets
    static_out = out / "static"
    if static_out.exists():
        shutil.rmtree(static_out)
    shutil.copytree(STATIC_DIR, static_out)

    # Write custom CSS
    (static_out / "style.css").write_text(CUSTOM_CSS)

    # Build known_fns map for clickable Lean identifiers.
    # Maps Lean name → relative URL from fn/ or lean/ pages (sibling depth=1).
    # Lean definitions get lean/ pages; idents link there.
    known_fns = {}
    for ld in lean_definitions:
        known_fns[ld.name] = f"{ld.slug}.html"
        # Also without first component for matching (e.g., "mod_add" → full page)
        parts = ld.name.split(".")
        if len(parts) > 1:
            without_prefix = ".".join(parts[1:])
            if without_prefix not in known_fns:
                known_fns[without_prefix] = f"{ld.slug}.html"

    # Build lean_map: Lean function name → LeanDefinition (for theorem links)
    lean_map = {ld.name: ld for ld in lean_definitions}

    # Build type_lean_map: Rust type name_pattern → LeanDefinition
    type_lean_map = {}
    for ld in lean_definitions:
        if ld.kind in ("inductive", "structure") and ld.rust_name:
            type_lean_map[ld.rust_name] = ld

    # Generate pages
    generate_index(crate_name, functions, types, stats, out,
                   rust_to_lean=rust_to_lean, errors=errors, lean_map=lean_map)
    generate_external_page(functions, out, lean_map=lean_map, known_fns=known_fns,
                           rust_to_lean=rust_to_lean)

    # Module pages — each module page includes functions from all submodules
    modules = defaultdict(list)
    for fn in functions:
        modules[fn.module].append(fn)

    for mod_name in modules:
        # Collect all functions in this module and its submodules
        mod_prefix = mod_name + "::"
        all_mod_fns = [fn for fn in functions
                       if fn.module == mod_name or fn.module.startswith(mod_prefix)]
        all_mod_types = [t for t in types
                         if t.module == mod_name or t.module.startswith(mod_prefix)]
        all_mod_globals = [g for g in globals_list
                           if g.module == mod_name or g.module.startswith(mod_prefix)]
        generate_module_page(mod_name, all_mod_fns, all_mod_types, out,
                             lean_map=lean_map, type_lean_map=type_lean_map,
                             rust_to_lean=rust_to_lean,
                             globals_list=all_mod_globals)

    # Function pages (with Lean model cross-link)
    fn_known_fns = {k: f"../lean/{v}" for k, v in known_fns.items()}
    for fn in functions:
        lds = rust_to_lean.get(fn.name_pattern, [])
        generate_function_page(fn, out, known_fns=fn_known_fns, lean_defs=lds,
                               lean_map=lean_map)

    # Global/constant pages
    for g in globals_list:
        lds = rust_to_lean.get(g.name_pattern, [])
        generate_global_page(g, out, known_fns=fn_known_fns, lean_defs=lds,
                             lean_map=lean_map)

    # Lean definition pages
    # known_fns links from lean/ pages stay as-is (sibling)
    for ld in lean_definitions:
        generate_lean_page(ld, out, known_fns=known_fns, rust_fn_map=rust_fn_map,
                          lean_src_dir=lean_src_dir)

    # Source pages
    generate_source_pages(functions, rust_src_dir, out)
    generate_lean_source_pages(lean_definitions, lean_src_dir, out)

    # Dependency graph page
    generate_graph_page(functions, out)

    # Search index (includes Lean definitions)
    generate_search_index(functions, types, theorems, out,
                          lean_definitions=lean_definitions,
                          type_lean_map=type_lean_map)

    print(f"Generated documentation in {out}/")
    print(f"  {len(functions)} functions, {len(types)} types, {len(globals_list)} globals, {len(theorems)} theorems")
    print(f"  {len(lean_definitions)} Lean definitions")
    if errors:
        print(f"  ⚠ {len(errors)} diagnostic issues (see index.html)")
    print(f"  Open {out / 'index.html'} in a browser")


def generate_search_index(functions: list, types: list,
                          theorems: list, output_dir: Path,
                          lean_definitions: list = None,
                          type_lean_map: dict = None):
    """Generate a JSON search index embedded in search JS (no fetch needed)."""
    tl = type_lean_map or {}
    entries = []
    for fn in functions:
        entries.append({
            "name": fn.display_name,
            "kind": "function",
            "status": fn.status,
            "module": fn.module,
            "url": f"fn/{fn.slug}.html",
            "public": fn.is_public,
        })
    for t in types:
        ld = tl.get(t.name_pattern)
        entries.append({
            "name": t.display_name,
            "kind": "type",
            "status": "",
            "module": t.module,
            "url": f"lean/{ld.slug}.html" if ld else "",
            "public": t.is_public,
        })
    for ld in (lean_definitions or []):
        entries.append({
            "name": ld.name,
            "kind": f"lean {ld.kind}",
            "status": "",
            "module": ld.module,
            "url": f"lean/{ld.slug}.html",
            "public": True,
        })

    # Embed the search data directly in JS (avoids fetch, works with file://)
    search_js = f'''
// Simple client-side search for Aeneas verification docs
(function() {{
  var searchData = {json.dumps(entries)};
  var searchInput = document.getElementById('search-input');
  var searchResults = document.getElementById('search-results');
  if (!searchInput || !searchResults) return;

  searchInput.addEventListener('input', function() {{
    var q = this.value.toLowerCase().trim();
    if (q.length < 2) {{ searchResults.innerHTML = ''; return; }}

    var matches = searchData.filter(function(e) {{
      return e.name.toLowerCase().indexOf(q) !== -1;
    }}).slice(0, 20);

    if (matches.length === 0) {{
      searchResults.innerHTML = '<div class="search-no-results">No results</div>';
      return;
    }}

    searchResults.innerHTML = matches.map(function(e) {{
      var badge = e.status ? '<span class="search-status search-status-' + e.status + '">' +
        e.status.replace('_', ' ') + '</span>' : '';
      var link = e.url ? '<a href="' + e.url + '">' + e.name + '</a>' : e.name;
      return '<div class="search-item">' + link + ' ' + badge +
        '<span class="search-kind">' + e.kind + '</span></div>';
    }}).join('');
  }});
}})();
'''
    (output_dir / "static" / "search.js").write_text(search_js)
