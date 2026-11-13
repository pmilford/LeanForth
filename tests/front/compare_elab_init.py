#!/usr/bin/env python3
"""Compare the elaboration data of Init with pinned Lean (tests/front/elab-init.sh).

Usage: python3 tests/front/compare_elab_init.py FINISH LEAN FORTH DATA

FINISH is scripts/export_elab.py's summary line (records written and left
out, by kind), LEAN the lines of tests/reference/elab-data-counts.lean,
FORTH those of tests/front/elab-init.fs, DATA the elaboration data. Holds
when, for every kind, Lean's count equals the records written plus those
left out, and LeanForth read exactly the records written; when the
reducibility statuses LeanForth found equal the file's, and Lean's add up
to its count; when Lean's samples equal LeanForth's line for line; and
when every line of DATA is valid under schemas/elab-data-1.schema.json.
Prints the counts compared; exit status 1 and the differences otherwise.
"""
import collections
import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tests/support"))
from schema_subset import Validator, load_strict  # noqa: E402

KINDS = ("instance", "default_instance", "reducibility", "eliminator")


def pairs(text):
    """{name: number} of the lines "name number"."""
    return {m[1]: int(m[2]) for m in re.finditer(r"^(\S+(?: \S+)?) (\d+)$", text, re.M)}


def main(finish, lean, forth, data):
    summary = open(finish).read()
    written = {k: int(n) for n, k in re.findall(r"(\d+) (\w+)", summary.split(";")[0])}
    left = {k: int(n) for n, k in re.findall(r"(\d+) (\w+)", summary.split(":")[-1])}
    lean_text, forth_text = open(lean).read(), open(forth).read()
    lean_counts, forth_counts = pairs(lean_text), pairs(forth_text)
    statuses = collections.Counter(json.loads(line)["reducibility"]["status"]
                                   for line in open(data, encoding="utf-8")
                                   if line.startswith('{"reducibility"'))
    problems = []
    for kind in KINDS:
        if lean_counts.get(kind) != written.get(kind, -1) + left.get(kind, -1):
            problems.append(f"{kind}: Lean {lean_counts.get(kind)}, written {written.get(kind)} "
                            f"+ left out {left.get(kind)}")
        if forth_counts.get(kind) != written.get(kind):
            problems.append(f"{kind}: LeanForth read {forth_counts.get(kind)}, "
                            f"written {written.get(kind)}")
    for status, count in statuses.items():
        if forth_counts.get(f"status {status}") != count:
            problems.append(f"status {status}: LeanForth {forth_counts.get(f'status {status}')}, "
                            f"file {count}")
    lean_statuses = sum(n for k, n in lean_counts.items() if k.startswith("status "))
    if lean_statuses != lean_counts.get("reducibility"):
        problems.append(f"Lean's statuses add up to {lean_statuses}")
    lean_samples = sorted(line for line in lean_text.splitlines() if line.startswith("sample"))
    forth_samples = sorted(line for line in forth_text.splitlines() if line.startswith("sample"))
    if lean_samples != forth_samples or len(lean_samples) < 6:
        problems.append(f"samples differ: Lean {lean_samples}, LeanForth {forth_samples}")
    validator = Validator(load_strict((ROOT / "schemas/elab-data-1.schema.json").read_text()))
    for number, line in enumerate(open(data, encoding="utf-8"), 1):
        problems += [f"line {number}: {e}" for e in validator.errors(load_strict(line))]
    if problems:
        print("\n".join(problems))
        return 1
    print("Init: " + ", ".join(f"{k} {lean_counts[k]} = {written[k]} written + {left[k]} left out"
                               for k in KINDS)
          + f"; LeanForth read all {sum(written.values())} and the same "
          f"{len(statuses)} statuses and {len(lean_samples)} samples as pinned Lean")
    return 0


if __name__ == "__main__":
    sys.exit(main(*sys.argv[1:]))
