#!/usr/bin/env python3
"""Maintenance tool for the GraphCanonizationProofs theorem index.

Usage:
  GenerateTheoremIndexes.py rewrite [--with-line-numbers]

`rewrite` regenerates the four index files from the Lean source + the existing
indices. What it does, per the current requirements:

  1. **Discovery.** Every named source declaration (theorem/lemma/def, plus
     infrastructure: structure/class/inductive/abbrev/axiom/named instance)
     is ensured to have a row in the table for its file, creating the `##
     <path>` section + table header if none exists. (Anonymous `instance` /
     `example` have no identifier and are skipped.)
  2. **Line column** (`--with-line-numbers`): a `start-end` source range
     covering the declaration's header (doc comment / attributes) and body.
  3. **Description** is hand-written and preserved verbatim.
  4. **Notes** are computed from source for every row — the infrastructure
     kind, `noncomputable`, and `@[…]` attributes; `private` is omitted
     (encoded by the public/private split). Semantic annotations belong in
     Description, not Notes.
  5. **Four files** (active|archive × public|private) are read, merged, and
     re-split: a row migrates between files when its decl's archive/visibility
     status changes, carrying its description.

Tracked vs. conceptual rows. A row that carries a Line cell is *tracked* and is
refreshed. A 3-cell row (no Line — a def shown with its args, or several decls
in one cell, e.g. `AutGroup adj` / `orbitMk / orbitMk_eq_iff`) is *conceptual*
and kept verbatim; it still *covers* its decls (matched by last name-segment)
so discovery does not duplicate them.

Prose between tables — `### …` sub-headers, per-file descriptions, the intro
note, the Legend — is passed through untouched and never moved between files
(structure: TableHeader → rows → [ignored prose] → TableHeader → rows → …).

Source-scan scope: all `.lean` files under `GraphCanonizationProofs/`,
excluding `.lake/`. Files under `Archive/...` are *archived*; else *active*.
"""
from __future__ import annotations

import argparse
import re
from collections import defaultdict
from pathlib import Path

# ---------------------------------------------------------------------------
# Repo / file layout
# ---------------------------------------------------------------------------
REPO_ROOT = Path(__file__).resolve().parent.parent
ROOT = REPO_ROOT / "GraphCanonizationProofs"

# The four index files: active|archive × public|private. Archived indices live
# next to the archived Lean source under `Archive/`.
ACTIVE_PUBLIC_INDEX = ROOT / "PublicTheoremIndex.md"
ACTIVE_PRIVATE_INDEX = ROOT / "PrivateTheoremIndex.md"
ARCHIVE_PUBLIC_INDEX = ROOT / "Archive" / "PublicTheoremIndex.md"
ARCHIVE_PRIVATE_INDEX = ROOT / "Archive" / "PrivateTheoremIndex.md"

# A source path is considered archived iff it sits anywhere under `Archive/`
# (relative to ROOT). The four-file layout pivots on this.
ARCHIVE_PREFIX = "Archive/"


def is_archived_path(path_str: str) -> bool:
    """True if the given source-relative path lives under `Archive/`."""
    if not path_str:
        return False
    return path_str.replace("\\", "/").startswith(ARCHIVE_PREFIX)


# Directory components excluded from the source scan — build artefacts and
# package caches we don't want to walk.
EXCLUDED_DIRS = {".lake"}


# ---------------------------------------------------------------------------
# Lean source parser
# ---------------------------------------------------------------------------
# Declaration keywords we index. Includes infrastructure kinds
# (`structure`/`class`/`inductive`/`abbrev`/`axiom`/named `instance`) so that
# infra "shows up" even if only with a simple line number — anonymous
# `instance`/`example` have no identifier and are intentionally skipped.
DECL_LINE_RE = re.compile(
    r"^\s*"
    r"((?:@\[[^\]]*\]\s*)*)"
    r"((?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*)"
    r"(theorem|lemma|def|instance|abbrev|structure|class|inductive|axiom)"
    r"\s+([^\s:({\[]+)",
    re.UNICODE,
)
ATTR_RE = re.compile(r"@\[[^\]]*\]")


def strip_comments(body: str) -> str:
    """Strip Lean block (nesting-aware) and line comments."""
    out: list[str] = []
    i, n, depth = 0, len(body), 0
    while i < n:
        two = body[i:i + 2]
        if two == "/-":
            depth += 1
            i += 2
        elif two == "-/" and depth > 0:
            depth -= 1
            i += 2
        elif depth > 0:
            i += 1
        elif two == "--":
            while i < n and body[i] != "\n":
                i += 1
        else:
            out.append(body[i])
            i += 1
    return "".join(out)


def _classify_lines(text: str) -> list[str]:
    """Per-line classification used by header-range detection.

    Returns a list of tags, one per line (split on '\\n'). Tags:
      - 'blank' : empty / whitespace-only line.
      - 'attr'  : top-level attribute line (`@[simp]`, `@[ext]`, ...).
      - 'doc'   : a line inside or making up a `/-- ... -/` doc comment.
      - 'sect'  : a line inside or making up a `/-! ... -/` section comment.
      - 'cmt'   : a line inside any other `/- ... -/` block comment.
      - 'code'  : anything else (regular Lean source).

    Doc-comment classification powers header-range expansion: when walking
    back from a declaration line to find the start of its header, we
    include contiguous `attr` and `doc` lines and stop at the first
    blank / sect / cmt / code line.
    """
    lines = text.split("\n")
    kinds: list[str] = []
    block_depth = 0
    block_kind: str | None = None  # 'doc' | 'sect' | 'cmt'
    for line in lines:
        stripped = line.strip()
        if block_depth > 0:
            kind = block_kind or "cmt"
        elif not stripped:
            kind = "blank"
        elif stripped.startswith("@["):
            # `@[simp] theorem foo := ...` is a declaration line (the
            # attribute lives on the keyword's own line). Only treat the
            # line as a pure attribute when no decl keyword follows on
            # the same line — otherwise the next decl's header walkback
            # would incorrectly absorb this declaration's header.
            kind = "code" if DECL_LINE_RE.match(line) else "attr"
        elif stripped.startswith("/--"):
            kind = "doc"
        elif stripped.startswith("/-!"):
            kind = "sect"
        elif stripped.startswith("/-"):
            kind = "cmt"
        else:
            kind = "code"

        # Advance block_depth / block_kind across this line's open/close
        # markers so the *next* line's classification is correct.
        i = 0
        while i < len(line):
            two = line[i:i + 2]
            three = line[i:i + 3]
            if two == "/-":
                if block_depth == 0:
                    if three == "/--":
                        block_kind = "doc"
                    elif three == "/-!":
                        block_kind = "sect"
                    else:
                        block_kind = "cmt"
                block_depth += 1
                i += 2
            elif two == "-/" and block_depth > 0:
                block_depth -= 1
                if block_depth == 0:
                    block_kind = None
                i += 2
            elif two == "--" and block_depth == 0:
                break  # rest of line is a Lean line comment
            else:
                i += 1
        kinds.append(kind)
    return kinds


_TERMINATOR_RE = re.compile(r"^\s*(namespace|end|section)\b")
_ANON_INSTANCE_RE = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*instance\s*[:({\[]")


def _is_decl_terminator(line: str) -> bool:
    """A line that should not be folded into the *preceding* declaration's
    end_line. Used by the walk-forward end-finder so that an inductive's
    range stops at the next `namespace`/`end`/`section`/anonymous-instance
    line rather than absorbing sibling code into the range."""
    if _TERMINATOR_RE.match(line):
        return True
    # Anonymous `instance : Foo := ...` lines: the explicit-declaration
    # parser skips these (no identifier follows the keyword), so they
    # would otherwise be silently attributed to the previous decl.
    if _ANON_INSTANCE_RE.match(line):
        return True
    return False


def parse_lean_file(path: Path) -> list[dict]:
    """Return list of declarations.

    Each entry has keys:
      - name        : declaration identifier.
      - line        : 1-indexed line of the declaration keyword
                      (theorem/def/lemma/...). Same as the historical
                      `line` field.
      - header_start: 1-indexed line where the declaration's *header*
                      starts — the first contiguous attached attribute or
                      doc-comment line above `line`, falling back to
                      `line` itself when there are none.
      - end_line    : 1-indexed last line of the declaration's body
                      (excluding trailing blank lines and the next
                      declaration's header).
      - is_private  : has the `private` modifier on the keyword line.
      - is_simp     : has the `@[simp]` attribute on the keyword line.
      - body        : full text from the declaration keyword to the next
                      declaration's header_start (unchanged semantics).
    """
    text = path.read_text()
    lines = text.split("\n")
    line_kinds = _classify_lines(text)

    decls: list[dict] = []
    for i, line in enumerate(lines):
        # Don't treat declarations inside any kind of block comment as real.
        if line_kinds[i] in ("doc", "sect", "cmt"):
            continue
        m = DECL_LINE_RE.match(line)
        if not m:
            continue
        attrs, modifiers, kind, name = m.groups()
        if not (name[0].isalpha() or name[0] == "_"):
            continue
        decls.append({
            "name": name,
            "kind": kind,
            "attrs": ATTR_RE.findall(attrs or ""),
            "line": i + 1,           # 1-indexed
            "_line_idx": i,
            "is_private": bool(re.search(r"\bprivate\b", modifiers)),
            "is_noncomputable": bool(re.search(r"\bnoncomputable\b", modifiers)),
            "is_simp": "@[simp" in (attrs or ""),
        })

    # Pass 1: header_start (depends only on the lines above each decl).
    header_starts: list[int] = []  # 0-indexed
    for d in decls:
        h = d["_line_idx"] - 1
        while h >= 0 and line_kinds[h] in ("attr", "doc"):
            h -= 1
        header_starts.append(h + 1)

    # Pass 2: end_line + body. Each decl owns the lines from its
    # `_line_idx` up to the *next* decl's header_start, exclusive. The
    # end_line is the last source line that actually belongs to the
    # declaration — we walk forward and stop at the first structural
    # marker (namespace/end/section/section comment/anonymous instance),
    # so a declaration's range is not padded with sibling namespace
    # housekeeping or skipped anonymous instances.
    for j, d in enumerate(decls):
        next_hs = header_starts[j + 1] if j + 1 < len(decls) else len(lines)
        e = d["_line_idx"]
        for k in range(d["_line_idx"] + 1, next_hs):
            if line_kinds[k] == "sect":
                break
            stripped_k = lines[k].strip()
            if not stripped_k:
                continue
            if _is_decl_terminator(lines[k]):
                break
            e = k
        d["header_start"] = header_starts[j] + 1  # 1-indexed
        d["end_line"] = e + 1                     # 1-indexed
        d["body"] = "\n".join(lines[d["_line_idx"]:next_hs])
        del d["_line_idx"]
    return decls


def _iter_lean_files() -> list[Path]:
    """All .lean files under ROOT, skipping `.lake/` build/package trees.

    Era-agnostic: scans both active locations (e.g. `ChainDescent.lean`) and
    archived ones (e.g. `Archive/V4/FullCorrectness/...`).
    """
    out: list[Path] = []
    for path in ROOT.rglob("*.lean"):
        rel = path.relative_to(ROOT)
        if any(part in EXCLUDED_DIRS for part in rel.parts):
            continue
        out.append(path)
    return sorted(out)


def parse_all_lean() -> dict[str, dict]:
    """name -> {path, line, is_private, is_simp, body, stripped_body}."""
    out: dict[str, dict] = {}
    for path in _iter_lean_files():
        for d in parse_lean_file(path):
            d["path"] = path.relative_to(ROOT)
            d["stripped_body"] = strip_comments(d["body"])
            out[d["name"]] = d
    return out

# ---------------------------------------------------------------------------
# Source-name resolution
#
# The Lean parser stores *unqualified* names ("trivial"), but an index row may
# display a namespace-qualified name ("LayerChain.trivial") or a definition
# with its arguments ("AutGroup adj") or several decls in one cell
# ("orbitMk / orbitMk_eq_iff"). We resolve a row to its source decl(s) by
# matching identifier tokens on their final `.`-segment.
# ---------------------------------------------------------------------------
# Split a Name cell into identifier tokens. We split on separators rather than
# match a character class, because Lean identifiers contain unicode (σ, τ,
# subscripts) and `!`/`?` that a `[A-Za-z…]` class would truncate.
_TOKEN_SEP_RE = re.compile(r"[\s/,]+")


def build_last_segment_index(source: dict[str, dict]) -> dict[str, list[str]]:
    """`last segment` -> list of source decl names sharing it."""
    by_last: dict[str, list[str]] = defaultdict(list)
    for name in source:
        by_last[name.split(".")[-1]].append(name)
    return by_last


def resolve_token(token: str, source: dict[str, dict],
                  by_last: dict[str, list[str]]) -> str | None:
    """Resolve one identifier token to a single source decl name, or None.
    Exact name wins; otherwise an *unambiguous* last-segment match."""
    if token in source:
        return token
    cands = by_last.get(token.split(".")[-1], [])
    return cands[0] if len(cands) == 1 else None


def row_decl_tokens(name_cell: str) -> list[str]:
    """Identifier tokens in a row's Name cell — handles `foo adj`, `foo / bar`,
    and unicode names (`comparePathSegments_σ_equivariant`)."""
    return [t for t in _TOKEN_SEP_RE.split(name_cell.replace("`", " ").strip()) if t]


def resolve_row(name_cell: str, source: dict[str, dict],
                by_last: dict[str, list[str]]) -> str | None:
    """The decl a (tracked) row is *about*: its first resolvable token."""
    for tok in row_decl_tokens(name_cell):
        d = resolve_token(tok, source, by_last)
        if d is not None:
            return d
    return None


# ---------------------------------------------------------------------------
# Notes (computed from the source declaration, for every row)
#
# The infrastructure kind, `noncomputable`, and `@[…]` attributes; `private`
# is omitted (encoded by the public/private split). Notes is fully derived —
# any semantic annotation a row used to carry in Notes belongs in Description.
# ---------------------------------------------------------------------------
_KIND_NOTE = {
    "def": "Definition", "structure": "Structure", "inductive": "Inductive",
    "class": "Class", "abbrev": "`abbrev`", "axiom": "axiom", "instance": "Instance",
}


def compute_notes(decl: dict) -> str:
    parts: list[str] = []
    k = _KIND_NOTE.get(decl["kind"])
    if k:
        parts.append(k)
    if decl.get("is_noncomputable"):
        parts.append("`noncomputable`")
    parts += [f"`{a}`" for a in decl.get("attrs", [])]
    return ", ".join(parts) if parts else "—"


# ---------------------------------------------------------------------------
# Markdown index layout (prose + rows, captured for lossless re-render)
#
# A file is `preamble` (everything before the first `## …` header) plus an
# ordered list of sections. Each section keeps its items in order; an item is
# either a verbatim prose line or a data row. Anything that is not a data row
# — section headers, `### …` sub-headers, descriptions, table headers and
# separators, blank lines — is prose and is passed through untouched. Prose is
# never moved between files.
# ---------------------------------------------------------------------------
SECTION_RE = re.compile(r"^##\s+(.+?)\s*$")
LINE_CELL_RE = re.compile(r"^(?:\d+(?:\s*[-–]\s*\d+)?|—|-)$")


def split_row(line: str) -> list[str] | None:
    """Split a markdown table row on `|`, ignoring pipes inside backtick spans
    and escaped `\\|`."""
    if not line.startswith("|") or not line.rstrip().endswith("|"):
        return None
    inner = line.rstrip()[1:-1]
    cells: list[str] = []
    buf: list[str] = []
    in_tick = False
    i = 0
    while i < len(inner):
        ch = inner[i]
        if ch == "\\" and i + 1 < len(inner) and inner[i + 1] == "|":
            buf.append("|")
            i += 2
            continue
        if ch == "`":
            in_tick = not in_tick
            buf.append(ch)
        elif ch == "|" and not in_tick:
            cells.append("".join(buf).strip())
            buf = []
        else:
            buf.append(ch)
        i += 1
    cells.append("".join(buf).strip())
    return cells


def _is_data_row(cells: list[str] | None) -> bool:
    return bool(cells and len(cells) >= 3 and cells[0].startswith("`")
                and cells[0].strip("`").strip() != "Name")


def parse_index_layout(path: Path) -> dict:
    """Capture a file as {"preamble": [str], "sections": [section]}.

    section = {"header": str, "path": str, "items": [item]}
    item    = ("prose", raw_line)
            | ("row", {name, raw, description, notes, tracked})

    A row is `tracked` iff it carries a Line cell (≥4 cells with a line-range
    2nd cell). Tracked rows are refreshed on re-render; 3-cell *conceptual*
    rows (a def shown with its args, or several decls in one cell) are kept
    verbatim.
    """
    if not path.exists():
        return {"preamble": [], "sections": []}
    preamble: list[str] = []
    sections: list[dict] = []
    cur: dict | None = None
    for line in path.read_text().splitlines():
        m_sec = SECTION_RE.match(line)
        if m_sec:
            cur = {"header": line, "path": m_sec.group(1).strip(), "items": []}
            sections.append(cur)
            continue
        if cur is None:
            preamble.append(line)
            continue
        cells = split_row(line)
        if _is_data_row(cells):
            tracked = len(cells) >= 4 and bool(LINE_CELL_RE.match(cells[1].strip("` ").strip()))
            cur["items"].append(("row", {
                "name": cells[0].strip().strip("`").strip(),
                "raw": line,
                "description": cells[-2],
                "notes": cells[-1],
                "tracked": tracked,
            }))
        else:
            cur["items"].append(("prose", line))
    return {"preamble": preamble, "sections": sections}


# ---------------------------------------------------------------------------
# Rendering
# ---------------------------------------------------------------------------
def render_line(info: dict) -> str:
    start = info.get("header_start") or info.get("line")
    end = info.get("end_line") or info.get("line")
    if start is None:
        return "—"
    if end is None or end == start:
        return str(start)
    return f"{start}-{end}"


def table_header(with_line_numbers: bool) -> list[str]:
    headers = ["Name"] + (["Line"] if with_line_numbers else []) + ["Description", "Notes"]
    return [
        "| " + " | ".join(headers) + " |",
        "|" + "|".join("-" * (len(h) + 2) for h in headers) + "|",
    ]


def _emit_row(name: str, line_cell: str | None, description: str, notes: str,
              with_line_numbers: bool) -> str:
    cells = [f"`{name}`"]
    if with_line_numbers:
        cells.append(line_cell or "—")
    cells += [description or "—", notes or "—"]
    return "| " + " | ".join(cells) + " |"


def render_tracked_row(decl: str, source: dict, row: dict, with_line_numbers: bool) -> str:
    # Refresh the Line column and recompute Notes from source; keep the
    # hand-written Description (Notes is now derived — see compute_notes).
    info = source[decl]
    return _emit_row(row["name"], render_line(info), row["description"],
                     compute_notes(info), with_line_numbers)


def render_new_row(decl: str, source: dict, global_desc: dict, with_line_numbers: bool) -> str:
    info = source[decl]
    return _emit_row(decl, render_line(info), global_desc.get(decl, "—"),
                     compute_notes(info), with_line_numbers)


_INDEX_TITLES = {
    ("active", False): "Public Theorem Index — GraphCanonizationProofs",
    ("active", True): "Private Theorem Index — GraphCanonizationProofs",
    ("archive", False): "Archived Public Theorem Index — GraphCanonizationProofs",
    ("archive", True): "Archived Private Theorem Index — GraphCanonizationProofs",
}
_INDEX_DESCRIPTIONS = {
    ("active", False): "Index of public Lean theorems, lemmas, and definitions in the GraphCanonizationProofs project (active source), grouped by source file path. Archived counterparts live in `Archive/PublicTheoremIndex.md`.",
    ("active", True): "Index of private Lean theorems, lemmas, and definitions in the GraphCanonizationProofs project (active source), grouped by source file path. Archived counterparts live in `Archive/PrivateTheoremIndex.md`.",
    ("archive", False): "Index of public Lean theorems, lemmas, and definitions in the archived (`Archive/...`) portion of the project. Active counterparts live in `../PublicTheoremIndex.md`.",
    ("archive", True): "Index of private Lean theorems, lemmas, and definitions in the archived (`Archive/...`) portion of the project. Active counterparts live in `../PrivateTheoremIndex.md`.",
}
_INDEX_PATHS = {
    ("active", False): ACTIVE_PUBLIC_INDEX,
    ("active", True): ACTIVE_PRIVATE_INDEX,
    ("archive", False): ARCHIVE_PUBLIC_INDEX,
    ("archive", True): ARCHIVE_PRIVATE_INDEX,
}


def default_preamble(key: tuple[str, bool], with_line_numbers: bool) -> list[str]:
    out = [f"# {_INDEX_TITLES[key]}", "", _INDEX_DESCRIPTIONS[key], "", "## Legend", ""]
    if with_line_numbers:
        out.append("- **Line**: Source-line range `start-end` covering the declaration's header (attached doc comment / attributes) and its full body. Collapses to a single number when the declaration occupies one line.")
    out += [
        "- **Description**: A short description of what the theorem proves.",
        "- **Notes**: infrastructure kind, `noncomputable`, and `@[…]` attributes (computed from source).",
        "",
    ]
    return out


def render_layout(layout: dict, key: tuple[str, bool], source: dict,
                  by_last: dict, bucket_decls: set[str], bucket_of: dict,
                  global_desc: dict, new_by_section: dict[str, list[str]],
                  with_line_numbers: bool, orphans: list[str]) -> str:
    out: list[str] = list(layout["preamble"]) if layout["preamble"] \
        else default_preamble(key, with_line_numbers)

    def _hs(decl: str) -> int:
        return source[decl].get("header_start") or source[decl].get("line") or 0

    emitted_sections: set[str] = set()
    for sec in layout["sections"]:
        out.append(sec["header"])
        emitted_sections.add(sec["path"])
        pending = sorted(new_by_section.get(sec["path"], []), key=_hs)
        pi = 0

        def _flush(limit: int, _p=pending) -> None:
            nonlocal pi
            while pi < len(_p) and _hs(_p[pi]) <= limit:
                out.append(render_new_row(_p[pi], source, global_desc, with_line_numbers))
                pi += 1

        for item in sec["items"]:
            if item[0] == "prose":
                out.append(item[1])
                continue
            row = item[1]
            if not row["tracked"]:
                out.append(row["raw"])            # conceptual → verbatim
                continue
            decl = resolve_row(row["name"], source, by_last)
            if decl is None:
                out.append(row["raw"])            # unresolved → keep (report)
                orphans.append(row["name"])
                continue
            if bucket_of[decl] != key:
                continue                          # migrated to another file → drop here
            _flush(_hs(decl))
            out.append(render_tracked_row(decl, source, row, with_line_numbers))
        while pi < len(pending):
            out.append(render_new_row(pending[pi], source, global_desc, with_line_numbers))
            pi += 1

    # Files with new decls but no existing section: append a fresh section.
    for sec_path in sorted(new_by_section):
        if sec_path in emitted_sections or not sec_path:
            continue
        out += [f"## {sec_path}", ""]
        out += table_header(with_line_numbers)
        for decl in sorted(new_by_section[sec_path], key=_hs):
            out.append(render_new_row(decl, source, global_desc, with_line_numbers))
        out.append("")

    return "\n".join(out).rstrip() + "\n"


# ---------------------------------------------------------------------------
# `rewrite` command
# ---------------------------------------------------------------------------
def cmd_rewrite(args: argparse.Namespace) -> None:
    source = parse_all_lean()
    by_last = build_last_segment_index(source)

    def bucket_of_decl(decl: str) -> tuple[str, bool]:
        info = source[decl]
        archived = is_archived_path(str(info["path"]))
        return ("archive" if archived else "active", bool(info["is_private"]))

    bucket_of = {d: bucket_of_decl(d) for d in source}

    # Parse all four existing files once.
    layouts = {key: parse_index_layout(path) for key, path in _INDEX_PATHS.items()}

    # Global description map (preserved across active↔archive / visibility moves):
    # a decl's hand-written description, taken from whichever file currently rows it.
    global_desc: dict[str, str] = {}
    for layout in layouts.values():
        for sec in layout["sections"]:
            for item in sec["items"]:
                if item[0] != "row":
                    continue
                decl = resolve_row(item[1]["name"], source, by_last)
                if decl is not None and item[1].get("description") not in (None, "", "—"):
                    global_desc.setdefault(decl, item[1]["description"])

    orphans: list[str] = []
    for key, path in _INDEX_PATHS.items():
        layout = layouts[key]
        bucket_decls = {d for d in source if bucket_of[d] == key}
        # Decls already represented in THIS file (by any covering row).
        covered: set[str] = set()
        for sec in layout["sections"]:
            for item in sec["items"]:
                if item[0] != "row":
                    continue
                for tok in row_decl_tokens(item[1]["name"]):
                    d = resolve_token(tok, source, by_last)
                    if d is not None:
                        covered.add(d)
        new_by_section: dict[str, list[str]] = defaultdict(list)
        for d in bucket_decls:
            if d not in covered:
                new_by_section[str(source[d]["path"])].append(d)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(render_layout(
            layout, key, source, by_last, bucket_decls, bucket_of,
            global_desc, new_by_section, args.with_line_numbers, orphans))
        added = sum(len(v) for v in new_by_section.values())
        print(f"Wrote {path.relative_to(REPO_ROOT)} "
              f"({len(bucket_decls)} decls, {added} newly added)")

    if orphans:
        print(f"\n{len(orphans)} tracked row(s) with no matching source decl "
              f"(kept verbatim — delete by hand if stale):")
        for o in sorted(set(orphans)):
            print(f"    {o}")


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------
def main() -> None:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sp = parser.add_subparsers(dest="command", required=True)
    p_rw = sp.add_parser("rewrite", help="Regenerate the four index files.")
    p_rw.add_argument("--with-line-numbers", action="store_true",
                      help="Include the 'Line' column (header + body source range).")
    p_rw.set_defaults(func=cmd_rewrite)
    args = parser.parse_args()
    args.func(args)


if __name__ == "__main__":
    main()
