#!/usr/bin/env python3
"""The block check's constructor capacity (plan task 5.2.1a; review rvI21
B1): an export with an enumeration E of N constructors (no recursor, which
Lean's replay accepts, ADR 0015 B4), then the committed Bool block of
tests/core/check-block-cases/replay-bool.original.ndjson with its indices
renumbered, is checked by LeanForth (tests/core/inductive-table.fs).

  N = 512, the capacity (lf-ind-ctor-capacity): E accepted, Bool accepted;
  N = 513: E full, every member, before anything is written for its
    constructors; Bool still accepted;
  N = 1600: the same, at once (the capacity used not to be enforced: such
    a block wrote past its state record, the next blocks became invalid,
    and one run hung).

The generator follows the reviewer's probe (.claude/work/rvI21/make_enum.py).
Needs GFORTH. Test-only."""
import json
import os
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
BOOL = os.path.join(ROOT, "tests/core/check-block-cases/replay-bool.original.ndjson")
DRIVER = os.path.join(ROOT, "tests/core/inductive-table.fs")
META = {"meta": {"exporter": {"name": "lean4export", "version": "3.1.0"},
                 "format": {"version": "3.1.0"},
                 "lean": {"githash": "eb6cafb7290e8bd5f2937522d8d804f58f02bafc",
                          "version": "4.35.0"}}}


def enumeration(n):
    """E : Type with n constructors c0 .. c(n-1), no recursor."""
    records = [META, {"in": 1, "str": {"pre": 0, "str": "E"}}]
    records += [{"in": 2 + j, "str": {"pre": 1, "str": f"c{j}"}} for j in range(n)]
    records += [{"il": 1, "succ": 0}, {"ie": 0, "sort": 1},
                {"const": {"name": 1, "us": []}, "ie": 1}]
    ctors = [{"cidx": j, "induct": 1, "isUnsafe": False, "levelParams": [], "name": 2 + j,
              "numFields": 0, "numParams": 0, "type": 1} for j in range(n)]
    types = [{"all": [1], "ctors": [2 + j for j in range(n)], "isRec": False,
              "isReflexive": False, "isUnsafe": False, "levelParams": [], "name": 1,
              "numIndices": 0, "numNested": 0, "numParams": 0, "type": 0}]
    records.append({"inductive": {"ctors": ctors, "recs": [], "types": types}})
    return records, 2 + n


class Renumber:
    """The Bool file's records with its name, level and expression indices
    moved past those already used."""

    def __init__(self, names):
        self.names, self.levels, self.exprs = {0: 0}, {0: 0}, {}
        self.next = {"in": names, "il": 2, "ie": 2}

    def fresh(self, kind, table, old):
        table[old] = self.next[kind]
        self.next[kind] += 1
        return table[old]

    def record(self, r):
        r = json.loads(json.dumps(r))
        if "in" in r:
            r["in"] = self.fresh("in", self.names, r["in"])
            part = r.get("str") or r.get("num")
            part["pre"] = self.names[part["pre"]]
        elif "il" in r:
            r["il"] = self.fresh("il", self.levels, r["il"])
            if "succ" in r:
                r["succ"] = self.levels[r["succ"]]
            if "param" in r:
                r["param"] = self.names[r["param"]]
        elif "ie" in r:
            r["ie"] = self.fresh("ie", self.exprs, r["ie"])
            self.expression(r)
        elif "inductive" in r:
            self.block(r["inductive"])
        return r

    def expression(self, r):
        if "sort" in r:
            r["sort"] = self.levels[r["sort"]]
        if "const" in r:
            r["const"]["name"] = self.names[r["const"]["name"]]
            r["const"]["us"] = [self.levels[u] for u in r["const"]["us"]]
        if "app" in r:
            r["app"]["fn"] = self.exprs[r["app"]["fn"]]
            r["app"]["arg"] = self.exprs[r["app"]["arg"]]
        for binder in ("forallE", "lam"):
            if binder in r:
                b = r[binder]
                b["type"], b["body"] = self.exprs[b["type"]], self.exprs[b["body"]]
                b["name"] = self.names[b["name"]]

    def block(self, b):
        n, e = self.names, self.exprs
        for c in b["ctors"]:
            c["name"], c["induct"], c["type"] = n[c["name"]], n[c["induct"]], e[c["type"]]
        for t in b["types"]:
            t["name"], t["type"] = n[t["name"]], e[t["type"]]
            t["all"], t["ctors"] = [n[x] for x in t["all"]], [n[x] for x in t["ctors"]]
        for q in b["recs"]:
            q["name"], q["type"] = n[q["name"]], e[q["type"]]
            q["all"], q["levelParams"] = [n[x] for x in q["all"]], [n[x] for x in q["levelParams"]]
            for rule in q["rules"]:
                rule["ctor"], rule["rhs"] = n[rule["ctor"]], e[rule["rhs"]]


def export(n, path):
    records, names = enumeration(n)
    with open(BOOL, encoding="utf-8") as bool_file:
        rest = [json.loads(line) for line in bool_file if line.strip()][1:]
    renumber = Renumber(names)
    records += [renumber.record(r) for r in rest]
    with open(path, "w", encoding="utf-8") as out:
        for r in records:
            out.write(json.dumps(r, separators=(",", ":"), sort_keys=True) + "\n")


def outcomes(gforth, paths, folder):
    script = os.path.join(folder, "run.fs")
    with open(script, "w", encoding="utf-8") as out:
        out.write(f"include {DRIVER}\n")
        out.writelines(f's" {p}" table-case\n' for p in paths)
        out.write("bye\n")
    run = subprocess.run([gforth, script], stdin=subprocess.DEVNULL, capture_output=True,
                         text=True, timeout=300)
    cases, current = [], {}
    for line in run.stdout.splitlines():
        part = line.split("\t")
        if part[0] == "decl":
            current.setdefault(part[2].split(".")[0], set()).add(part[3])
        elif part[0] == "case-end":
            cases.append(current)
            current = {}
    if len(cases) != len(paths):
        sys.stdout.write(run.stdout + run.stderr)
    return cases


def main():
    gforth = os.environ.get("GFORTH", "gforth")
    want = {512: "ok", 513: "full", 1600: "full"}
    with tempfile.TemporaryDirectory() as folder:
        paths = []
        for n in want:
            paths.append(os.path.join(folder, f"enum{n}.ndjson"))
            export(n, paths[-1])
        cases = outcomes(gforth, paths, folder)
    failures = 0
    for (n, e_outcome), case in zip(want.items(), cases):
        ok = case.get("E") == {e_outcome} and case.get("IE") == {"ok"}
        failures += not ok
        print(f"{n} constructors: E {sorted(case.get('E', []))}, then Bool"
              f" {sorted(case.get('IE', []))}{'' if ok else '  DIFFERENCE'}")
    if len(cases) != len(want):
        failures += 1
        print("block-capacity: Gforth did not check every file")
    print(f"block-capacity: {len(want) - failures} of {len(want)} as required")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
