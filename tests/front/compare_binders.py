#!/usr/bin/env python3
"""Binder names and binder information of LeanForth's generated definitions
against pinned Lean's environment (plan row FE6; review fe6a M1;
tests/front/constructions-init.sh).

Usage: compare_binders.py LEAN.txt FORTH.txt
  LEAN.txt   tests/reference/constructions-binders.lean's output: one line
             per definition, name, tab, the type's binders, tab, the value's
  FORTH.txt  tests/front/constructions-init.fs's output; its "sig " lines
             are the same for each definition LeanForth built
Prints, per construction (casesOn, recOn, ctorIdx), how many built
definitions have exactly Lean's binder names and information in type and
value, how many differ (and in what: names only, or information too), and
how many Lean's environment lacks; then the first differing names. Always
exits 0 unless a file is malformed: the caller pins the counts.
"""
import sys

KINDS = ("casesOn", "recOn", "ctorIdx")


def read_lean(path):
    table = {}
    with open(path, encoding="utf-8") as f:
        for line in f:
            parts = line.rstrip("\n").split("\t")
            if len(parts) != 3:
                raise SystemExit(f"{path}: malformed line: {line!r}")
            table[parts[0]] = (parts[1], parts[2])
    return table


def read_forth(path):
    rows = []
    with open(path, encoding="utf-8") as f:
        for line in f:
            if line.startswith("sig "):
                parts = line[4:].rstrip("\n").split("\t")
                if len(parts) != 3:
                    raise SystemExit(f"{path}: malformed line: {line!r}")
                rows.append(parts)
    return rows


def infos(sig):
    return [b.rsplit(":", 1)[-1] for b in sig.split()]


def main(argv):
    if len(argv) != 3:
        raise SystemExit(__doc__)
    lean = read_lean(argv[1])
    counts = {k: [0, 0, 0, 0] for k in KINDS}   # exact, names only, information, missing
    examples = []
    for name, ty, val in read_forth(argv[2]):
        kind = name.rsplit(".", 1)[-1]
        row = counts[kind]
        if name not in lean:
            row[3] += 1
            continue
        lty, lval = lean[name]
        if (ty, val) == (lty, lval):
            row[0] += 1
        elif infos(ty) == infos(lty) and infos(val) == infos(lval):
            row[1] += 1
            examples.append(f"names {name}")
        else:
            row[2] += 1
            examples.append(f"information {name}")
    for kind in KINDS:
        exact, names, info, missing = counts[kind]
        print(f"binders {kind} exact {exact} names-differ {names} information-differs {info}"
              f" not-in-lean {missing}")
    for line in examples[:20]:
        print(f"  differs: {line}")


if __name__ == "__main__":
    main(sys.argv)
