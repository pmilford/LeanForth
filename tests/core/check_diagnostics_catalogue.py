#!/usr/bin/env python3
"""The diagnostic catalogue in docs/programming/DIAGNOSTICS.md matches the
code: every row of its table (except code 0, "no diagnostic") gives a code
and printed name that src/core/diagnostics.fs's catalogue table holds, in
the same order, and the table lists every code the Forth catalogue has.
Run from the repository root; GFORTH names Gforth (default: gforth).
Test-only; prints one line and exits 0 when they match, 1 otherwise."""
import os
import re
import subprocess
import sys

DOC = "docs/programming/DIAGNOSTICS.md"
# Print each catalogue entry as "code<TAB>name", up to the closing entry.
DUMP = (
    ": dump ( -- ) lf-diag-catalogue begin dup lf-diag-entry-code dup lf-diag-none <>"
    " while 0 .r 9 emit dup lf-diag-entry-name type cr lf-diag-entry-next repeat 2drop ;"
    " dump bye"
)


def forth_catalogue(gforth):
    run = subprocess.run([gforth, "src/core/diagnostics.fs", "-e", DUMP],
                         stdin=subprocess.DEVNULL, capture_output=True, text=True,
                         timeout=120, check=True)
    rows = [line.split("\t") for line in run.stdout.splitlines() if "\t" in line]
    return [(int(code), name) for code, name in rows]


def doc_catalogue(path):
    rows = []
    for line in open(path, encoding="utf-8"):
        match = re.match(r"\|\s*(\d+)\s*\|\s*([^|]*?)\s*\|", line)
        if match and match.group(1) != "0":
            rows.append((int(match.group(1)), match.group(2)))
    return rows


def main():
    forth = forth_catalogue(os.environ.get("GFORTH", "gforth"))
    doc = doc_catalogue(DOC)
    if not forth or forth != doc:
        print(f"diagnostic catalogue: {DOC} and src/core/diagnostics.fs differ")
        for row in sorted(set(forth) ^ set(doc)):
            where = "code only" if row in forth else "docs only"
            print(f"  {where}: {row[0]} {row[1]}")
        if set(forth) == set(doc):
            print("  same entries, different order")
        return 1
    print(f"diagnostic catalogue: {len(forth)} codes, documentation and code agree")
    return 0


sys.exit(main())
