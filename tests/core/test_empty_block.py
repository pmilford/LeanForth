#!/usr/bin/env python3
"""Empty inductive blocks (plan task 5.2.1a; ADR 0016 amendment 1): an
inductive record with no type, constructor or recursor is staged as one
declaration that the block check rejects as Lean's kernel does
(emptyBlock, diagnostic 78, step 4), and the file goes on; a block record
with no type but with constructors or recursors stays malformed, the file
invalid. Each file is the committed Bool export
(tests/core/check-block-cases/replay-bool.original.ndjson) with empty
records put before, between or after its lines (an empty record uses no
name or expression, so nothing is renumbered), checked by LeanForth
(tests/core/inductive-table.fs). Needs GFORTH. Test-only."""
import os
import subprocess
import sys
import tempfile
TEST_LIMIT = int(os.environ.get("TEST_TIMEOUT", "1800"))  # seconds; make exports it

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
BOOL = os.path.join(ROOT, "tests/core/check-block-cases/replay-bool.original.ndjson")
DRIVER = os.path.join(ROOT, "tests/core/inductive-table.fs")
EMPTY = '{"inductive":{"ctors":[],"recs":[],"types":[]}}\n'
CTOR_ONLY = ('{"inductive":{"ctors":[{"cidx":0,"induct":1,"isUnsafe":false,"levelParams":[],'
             '"name":3,"numFields":0,"numParams":0,"type":1}],"recs":[],"types":[]}}\n')


def cases(bool_lines):
    meta, rest = bool_lines[0], bool_lines[1:]
    block = next(i for i, line in enumerate(rest) if line.startswith('{"inductive"'))
    return [
        # name, lines, expected per declaration (name, outcome), or "invalid" for the feed
        ("empty block first", [meta, EMPTY] + rest,
         [("", "rejected"), ("IE.B", "ok"), ("IE.B.false", "ok"), ("IE.B.true", "ok"),
          ("IE.B.rec", "ok")]),
        ("two empty blocks around the Bool block",
         [meta] + rest[:block] + [EMPTY, rest[block], EMPTY] + rest[block + 1:],
         [("", "rejected"), ("IE.B", "ok"), ("IE.B.false", "ok"), ("IE.B.true", "ok"),
          ("IE.B.rec", "ok"), ("", "rejected")]),
        ("no type but a constructor", [meta] + rest[:block] + [CTOR_ONLY], "invalid"),
    ]


def run(gforth, paths, folder):
    script = os.path.join(folder, "run.fs")
    with open(script, "w", encoding="utf-8") as out:
        out.write(f"include {DRIVER}\n")
        out.writelines(f's" {p}" table-case\n' for p in paths)
        out.write("bye\n")
    result = subprocess.run([gforth, script], stdin=subprocess.DEVNULL, capture_output=True,
                            text=True, timeout=TEST_LIMIT)
    found, current, checks = [], [], {}
    for line in result.stdout.splitlines():
        part = line.split("\t")
        if part[0] == "feed":
            current = part[1]
        elif part[0] == "check":
            checks[int(part[1])] = (int(part[2]), int(part[3]))
        elif part[0] == "decl":
            current.append((part[2], part[3], checks.get(int(part[1]))))
        elif part[0] == "case-end":
            found.append(current)
            current, checks = [], {}
    if len(found) != len(paths):
        sys.stdout.write(result.stdout + result.stderr)
    return found


def main():
    gforth = os.environ.get("GFORTH", "gforth")
    with open(BOOL, encoding="utf-8") as bool_file:
        bool_lines = bool_file.readlines()
    all_cases = cases(bool_lines)
    with tempfile.TemporaryDirectory() as folder:
        paths = []
        for k, (_, lines, _) in enumerate(all_cases):
            paths.append(os.path.join(folder, f"case{k}.ndjson"))
            with open(paths[-1], "w", encoding="utf-8") as out:
                out.writelines(lines)
        found = run(gforth, paths, folder)
    failures = 0
    for (name, _, expected), got in zip(all_cases, found):
        if expected == "invalid":
            ok = got == "invalid"
        else:
            ok = [(n, o) for n, o, _ in got] == expected and all(
                c == (78, 4) for n, _, c in got if n == "")
        failures += not ok
        print(f"{name}: {'ok' if ok else 'DIFFERENCE'} {got}")
    if len(found) != len(all_cases):
        failures += 1
        print("empty-block: Gforth did not check every file")
    print(f"empty-block: {len(all_cases) - failures} of {len(all_cases)} as required")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
