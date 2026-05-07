#!/usr/bin/env python3
"""Invert the Uses column of TheoremIndex.md into Used By, and drop the Uses column."""

import re
import sys
from pathlib import Path

PATH = Path("/workspace/GraphCanonizationProofs/TheoremIndex.md")

text = PATH.read_text()
lines = text.splitlines(keepends=True)

# Identify table rows. Each table has a header `| Name | Uses | Used By | Description | Notes |`,
# a separator `|---|---|---|---|---|`, then data rows. We only touch lines that look like
# 5-cell table rows.

HEADER_RE = re.compile(r"^\|\s*Name\s*\|\s*Uses\s*\|\s*Used By\s*\|\s*Description\s*\|\s*Notes\s*\|\s*$")
SEP_RE = re.compile(r"^\|\s*-+\s*\|\s*-+\s*\|\s*-+\s*\|\s*-+\s*\|\s*-+\s*\|\s*$")
ROW_RE = re.compile(r"^\|(.+)\|\s*$")

def split_cells(line: str):
    # strip leading/trailing | and split. Cells should never contain literal | here.
    inner = line.rstrip("\n").strip()
    if not inner.startswith("|") or not inner.endswith("|"):
        return None
    parts = inner.strip("|").split("|")
    return [p.strip() for p in parts]

# First pass: collect entries to build inverse map.
entries = []  # list of dicts: {line, name, name_clean, uses_names, description, notes}

for i, line in enumerate(lines):
    if HEADER_RE.match(line) or SEP_RE.match(line):
        continue
    cells = split_cells(line)
    if cells is None or len(cells) != 5:
        continue
    name, uses, used_by, description, notes = cells
    if name == "Name":
        # any header that didn't match HEADER_RE due to spacing
        continue
    name_clean = name.strip("`")
    uses_names = re.findall(r"`([^`]+)`", uses)
    entries.append({
        "line": i,
        "name": name,
        "name_clean": name_clean,
        "uses_names": uses_names,
        "description": description,
        "notes": notes,
    })

# Build inverse: for each referenced declaration, which entries name it in Uses?
used_by_map: dict[str, set[str]] = {}
all_names = {e["name_clean"] for e in entries}
external_refs = set()

for e in entries:
    for u in e["uses_names"]:
        if u not in all_names:
            external_refs.add(u)
            continue
        used_by_map.setdefault(u, set()).add(e["name_clean"])

# Second pass: rewrite each entry line, dropping the Uses column.
new_lines = list(lines)
for e in entries:
    used_by = sorted(used_by_map.get(e["name_clean"], set()))
    if used_by:
        used_by_str = ", ".join(f"`{n}`" for n in used_by)
    else:
        used_by_str = "—"
    new_lines[e["line"]] = (
        f"| {e['name']} | {used_by_str} | {e['description']} | {e['notes']} |\n"
    )

# Rewrite headers + separators (drop the Uses column).
for i, line in enumerate(lines):
    if HEADER_RE.match(line):
        new_lines[i] = "| Name | Used By | Description | Notes |\n"
    elif SEP_RE.match(line):
        new_lines[i] = "|------|---------|-------------|-------|\n"

# Update the Legend: drop the Uses bullet.
out = "".join(new_lines)
out = out.replace(
    "- **Uses**: Theorems/definitions directly referenced in this theorem's proof\n",
    "",
)

PATH.write_text(out)

# Report.
print(f"Entries processed: {len(entries)}")
print(f"Inverse map size:  {len(used_by_map)}")
print(f"External refs (referenced but not declared in index): {len(external_refs)}")
if external_refs:
    print("Examples:", sorted(external_refs)[:20])
