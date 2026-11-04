#!/usr/bin/env python3
"""The derivation log's rule catalogue in docs/programming/DERIVATION_LOG.md
matches the code (ADR 0013 L1): every row of the catalogue table gives a
code, the rule's name and the kinds of its a, b and out, as
src/core/derivation-log.fs's catalogue holds them, in the same order, and
the table lists every rule the Forth catalogue has.
Run from the repository root; GFORTH names Gforth (default: gforth).
Test-only; prints one line and exits 0 when they match, 1 otherwise."""
import os
import re
import subprocess
import sys

DOC = "docs/programming/DERIVATION_LOG.md"
KINDS = {0: "none", 1: "term", 2: "level", 3: "number"}
# Print each catalogue entry as "code<TAB>name<TAB>kinds", up to code 0.
DUMP = (
    ": dump ( -- ) lf-log-catalogue begin dup lf-log-entry-code ?dup while"
    " 0 .r 9 emit dup lf-log-entry-name type 9 emit dup lf-log-entry-kinds 0 .r cr"
    " lf-log-entry-next repeat drop ; dump bye"
)


def forth_catalogue(gforth):
    run = subprocess.run([gforth, "src/core/derivation-log.fs", "-e", DUMP],
                         stdin=subprocess.DEVNULL, capture_output=True, text=True,
                         timeout=120, check=True)
    rows = []
    for line in run.stdout.splitlines():
        parts = line.split("\t")
        if len(parts) == 3:
            kinds = int(parts[2])
            names = tuple(KINDS[(kinds >> shift) & 3] for shift in (0, 2, 4))
            rows.append((int(parts[0]), parts[1]) + names)
    return rows


def doc_catalogue(path):
    rows = []
    pattern = (r"\|\s*(\d+)\s*\|\s*`([a-z-]+)`\s*\|\s*(\w+)\s*\|\s*(\w+)\s*\|\s*(\w+)\s*\|")
    for line in open(path, encoding="utf-8"):
        match = re.match(pattern, line)
        if match:
            rows.append((int(match.group(1)),) + match.groups()[1:])
    return rows


def main():
    forth = forth_catalogue(os.environ.get("GFORTH", "gforth"))
    doc = doc_catalogue(DOC)
    if not forth or forth != doc:
        print(f"derivation log catalogue: {DOC} and src/core/derivation-log.fs differ")
        for row in sorted(set(forth) ^ set(doc)):
            where = "code only" if row in forth else "docs only"
            print(f"  {where}: {row}")
        if set(forth) == set(doc):
            print("  same entries, different order")
        return 1
    print(f"derivation log catalogue: {len(forth)} rules, documentation and code agree")
    return 0


if __name__ == "__main__":
    sys.exit(main())
