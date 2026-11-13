#!/usr/bin/env python3
"""Compare the elaboration data of Init with pinned Lean (tests/front/elab-init.sh).

Usage: python3 tests/front/compare_elab_init.py FINISH LEAN FORTH DATA ORDER

FINISH is scripts/export_elab.py's summary line (records written and left
out, by kind), LEAN the lines of tests/reference/elab-data-counts.lean,
FORTH those of tests/front/elab-init.fs, DATA the elaboration data and
ORDER the lines of tests/reference/elab-instance-order.lean. Holds when,
for every kind, Lean's count equals the records written plus those left
out (for instances: the instance and instance_left_out records written
plus the values left out), and LeanForth read exactly the records
written; when the reducibility statuses LeanForth found equal the file's,
and Lean's add up to its count; when Lean's samples equal LeanForth's
line for line; when every line of DATA is valid under
schemas/elab-data-2.schema.json; and when, for every goal of ORDER, the
data's ranks give Lean's getUnify order (the values under the goal's root
key in rank order, kept to the ones getUnify found) and the data's
priorities give Lean's getInstances order from it (a stable sort by
priority, the erased ones dropped). Prints the counts compared; exit
status 1 and the differences otherwise.
"""
import collections
import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tests/support"))
from schema_subset import Validator, load_strict  # noqa: E402

# Lean's counts against the records written (+ those left out).
LEAN_KINDS = {"class": ("class",), "instance": ("instance", "instance_left_out"),
              "default_instance": ("default_instance",), "reducibility": ("reducibility",),
              "eliminator": ("eliminator",), "tag": ("tag",)}
KINDS = ("class", "instance", "instance_left_out", "default_instance", "reducibility",
         "eliminator", "tag")


def pairs(text):
    """{name: number} of the lines "name number"."""
    return {m[1]: int(m[2]) for m in re.finditer(r"^(\S+(?: \S+)?) (\d+)$", text, re.M)}


def dotted(name):
    return ".".join(str(part) for part in name)


def tree_values(data):
    """Every value of the instance tree in the data: (name, root, rank,
    priority, erased), the instance and instance_left_out records."""
    values = []
    for line in open(data, encoding="utf-8"):
        record = json.loads(line)
        kind, body = next(iter(record.items()))
        if kind in ("instance", "instance_left_out"):
            values.append((dotted(body["name"]), json.dumps(body["keys"][0], sort_keys=True),
                           body["rank"], body["priority"], body.get("reason") == "erased"))
    return values


def order_problems(order, data):
    """The goals of ORDER whose Lean orders the data's ranks and priorities
    do not give, and the number of goals."""
    values = tree_values(data)
    by_name = {v[0]: v for v in values}
    lean = {}
    for kind, goal, names in re.findall(r"^(unify|instances) (.+?): ?(.*)$", open(order).read(),
                                        re.M):
        lean.setdefault(goal, {})[kind] = names.split()
    problems = []
    for goal, found in lean.items():
        unified = found["unify"]
        roots = {by_name[n][1] for n in unified if n in by_name}
        if len(roots) != 1 or any(n not in by_name for n in unified):
            problems.append(f"{goal}: getUnify's {unified} are not values of one root")
            continue
        root = roots.pop()
        ranked = sorted((v for v in values if v[1] == root and v[0] in unified),
                        key=lambda v: v[2])
        if [v[0] for v in ranked] != unified:
            problems.append(f"{goal}: ranks give {[v[0] for v in ranked]}, Lean {unified}")
        tried = [v[0] for v in sorted(ranked, key=lambda v: v[3]) if not v[4]]
        if tried != found["instances"]:
            problems.append(f"{goal}: priorities give {tried}, Lean {found['instances']}")
    return problems, len(lean)


def main(finish, lean, forth, data, order):
    summary = open(finish).read()
    written = {k: int(n) for n, k in re.findall(r"(\d+) (\w+)", summary.split(";")[0])}
    left = {k: int(n) for n, k in re.findall(r"(\d+) (\w+)", summary.split(":")[-1])}
    lean_text, forth_text = open(lean).read(), open(forth).read()
    lean_counts, forth_counts = pairs(lean_text), pairs(forth_text)
    statuses = collections.Counter(json.loads(line)["reducibility"]["status"]
                                   for line in open(data, encoding="utf-8")
                                   if line.startswith('{"reducibility"'))
    problems = []
    for kind, kinds in LEAN_KINDS.items():
        total = sum(written.get(k, -1) for k in kinds) + left.get(kind, -1)
        if lean_counts.get(kind) != total:
            problems.append(f"{kind}: Lean {lean_counts.get(kind)}, written "
                            f"{[written.get(k) for k in kinds]} + left out {left.get(kind)}")
    for kind in KINDS:
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
    if lean_samples != forth_samples or len(lean_samples) < 9:
        problems.append(f"samples differ: Lean {lean_samples}, LeanForth {forth_samples}")
    validator = Validator(load_strict((ROOT / "schemas/elab-data-2.schema.json").read_text()))
    for number, line in enumerate(open(data, encoding="utf-8"), 1):
        problems += [f"line {number}: {e}" for e in validator.errors(load_strict(line))]
    order_found, goals = order_problems(order, data)
    problems += order_found
    if problems:
        print("\n".join(problems))
        return 1
    print("Init: " + ", ".join(f"{k} {lean_counts[k]}" for k in LEAN_KINDS)
          + f" (Lean) = written + left out; LeanForth read all {sum(written.values())} and the "
          f"same {len(statuses)} statuses and {len(lean_samples)} samples as pinned Lean; "
          f"the ranks and priorities give Lean's candidate order for all {goals} goals")
    return 0


if __name__ == "__main__":
    sys.exit(main(*sys.argv[1:]))
