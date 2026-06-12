 #!/usr/bin/env python3
"""Make a pdf2txt-extracted text file greppable, in place.

WHY THIS EXISTS
---------------
`pdf2txt` (PyMuPDF) output is NOT greppable as-is, for two reasons:
  1. It contains embedded NUL bytes (`\\x00`). `grep` treats any file with a NUL
     as *binary* and silently refuses to print matches (returns exit 1, no count)
     — this is the real cause of the "grep finds nothing" trap, NOT the locale.
     `LC_ALL=C grep` fails for the same reason. (The `setlocale: LC_ALL` warnings
     in this environment are noise, unrelated to the failure.)
  2. It uses Unicode ligatures inside words — e.g. "conﬁguration" (ﬁ = "fi"),
     "diﬀerent" (ﬀ = "ff"). So even after NUL stripping, `grep configuration`
     would MISS "conﬁguration". NFKC normalization decomposes these to ASCII.

This script does both: strips NUL, NFKC-normalizes. Non-ASCII math symbols that
carry meaning (← domination arrow, ̸= etc.) are preserved — they do not
break grep (only NUL did), and they matter for reading the source.

USAGE
  python3 scripts/clean-extracted-text.py <file.txt> [<file2.txt> ...]   # in place
  pdf2txt paper.pdf > /tmp/paper.txt && python3 scripts/clean-extracted-text.py /tmp/paper.txt

ALWAYS run this on a fresh pdf2txt extraction, or `grep`/`rg` will silently find
nothing on it.
"""
import sys
import unicodedata


def clean(path: str) -> None:
    raw = open(path, encoding="utf-8", errors="replace").read()
    out = unicodedata.normalize("NFKC", raw.replace("\x00", ""))
    open(path, "w", encoding="utf-8").write(out)
    print(f"cleaned {path}: stripped NUL + NFKC-normalized ({len(out)} chars)")


if __name__ == "__main__":
    if len(sys.argv) < 2:
        sys.exit("usage: clean-extracted-text.py <file.txt> [<file2.txt> ...]")
    for p in sys.argv[1:]:
        clean(p)
