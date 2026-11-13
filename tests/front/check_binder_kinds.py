#!/usr/bin/env python3
"""Binder kinds of the export against pinned Lean's (plan S1,
docs/design/S1_INTERFACE.md §4; branch s1-meta).

The front end reads a library constant's binder kinds from the export's
binder tags (src/front/lib-decode.fs, lf-tier-kinds; meta-env.fs,
lf-menv-kinds). Lean's exporter shares expressions equal up to binder
information (review fe6a M1), so a declaration's type there may show
another term's kinds. This compares, for every declaration of Init, each
binder of its type in pre-order (binder, domain, body; function,
argument; a let's type, value and body) with pinned Lean's environment
(tests/reference/binder-kinds.lean, getConstInfo), and reports how many
declarations and binders differ, over all of Init and over the
declarations S1 reads (S1_DECLS). The target is 0 on S1's; a declaration
that differs answers unsupported where its kinds are read, by the list
§4 ships in the elaboration data.

Usage: check_binder_kinds.py [--export INIT.ndjson] [--lean LEAN.txt]
  --export  Init exported by the pinned leanexport (its SHA-256 checked);
            default: made here with $LEAN's leanexport
  --lean    binder-kinds.lean's output; default: run here with $LEAN
Exits 1 when a declaration S1 reads differs or the export is not the
pinned one, 0 otherwise (the Init count is reported, not pinned).
"""
import argparse
import array
import hashlib
import json
import os
import pathlib
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[2]
INIT_SHA = "c1b2071a6d2132ace8c4711499f078aab2117d925213d5a222a1fe843a59a179"
S1_DECLS = ["Eq", "Eq.refl", "HAdd", "HAdd.hAdd", "HAdd.mk", "OfNat", "OfNat.ofNat",
            "OfNat.mk", "Add", "Add.add", "Add.mk", "instHAdd", "instAddNat",
            "instOfNatNat", "Nat", "Nat.add"]
INFO = {"default": 0, "implicit": 1, "strictImplicit": 2, "instImplicit": 3}
# Expression kinds kept: 0 other, 1 binder, 2 application, 3 let, 4 one child.
BINDER, APP, LET, ONE = 1, 2, 3, 4


class Exprs:
    """The export's expressions, only what a walk over binders needs."""

    def __init__(self):
        self.kind = array.array("b")
        self.info = array.array("b")
        self.a = array.array("q")
        self.b = array.array("q")
        self.c = array.array("q")

    def put(self, i, kind, info=0, a=-1, b=-1, c=-1):
        while len(self.kind) <= i:
            for arr in (self.kind, self.info):
                arr.append(0)
            for arr in (self.a, self.b, self.c):
                arr.append(-1)
        self.kind[i], self.info[i] = kind, info
        self.a[i], self.b[i], self.c[i] = a, b, c

    def binders(self, root):
        out, stack = [], [root]
        while stack:
            e = stack.pop()
            k = self.kind[e]
            if k == BINDER:
                out.append(self.info[e])
                stack += [self.b[e], self.a[e]]
            elif k == APP:
                stack += [self.b[e], self.a[e]]
            elif k == LET:
                stack += [self.c[e], self.b[e], self.a[e]]
            elif k == ONE:
                stack.append(self.a[e])
        return out


def read_export(path):
    names, exprs, decls = {0: ""}, Exprs(), {}
    with open(path, encoding="utf-8") as f:
        for line in f:
            r = json.loads(line)
            if "in" in r:
                part = r.get("str") or r.get("num")
                pre = names[part["pre"]]
                text = part["str"] if "str" in r else str(part["i"])
                names[r["in"]] = f"{pre}.{text}" if pre else text
            elif "ie" in r:
                read_expr(r, exprs)
            elif "inductive" in r:
                ind = r["inductive"]
                for d in ind["types"] + ind["ctors"] + ind["recs"]:
                    decls[names[d["name"]]] = d["type"]
            else:
                for key in ("def", "thm", "axiom", "opaque", "quot"):
                    if key in r:
                        decls[names[r[key]["name"]]] = r[key]["type"]
    return exprs, decls


def read_expr(r, exprs):
    i = r["ie"]
    for key in ("forallE", "lam"):
        if key in r:
            x = r[key]
            exprs.put(i, BINDER, INFO[x["binderInfo"]], x["type"], x["body"])
            return
    if "app" in r:
        exprs.put(i, APP, 0, r["app"]["fn"], r["app"]["arg"])
    elif "letE" in r:
        x = r["letE"]
        exprs.put(i, LET, 0, x["type"], x["value"], x["body"])
    elif "mdata" in r:
        exprs.put(i, ONE, 0, r["mdata"]["expr"])
    elif "proj" in r:
        exprs.put(i, ONE, 0, r["proj"]["struct"])
    else:
        exprs.put(i, 0)


def read_lean(path):
    table = {}
    with open(path, encoding="utf-8") as f:
        for line in f:
            line = line.rstrip("\n")
            if not line:
                continue
            name, _, codes = line.rpartition("\t")
            table[name] = [int(c) for c in codes.split()]
    return table


def lean_tool(name):
    lean = os.environ.get("LEAN", "lean")
    prefix = subprocess.run([lean, "--print-prefix"], capture_output=True, text=True,
                            check=True).stdout.strip()
    return lean, pathlib.Path(prefix) / "bin" / name


def make_export(work):
    lean, leanexport = lean_tool("leanexport")
    path = work / "init.ndjson"
    env = dict(os.environ, PATH=f"{leanexport.parent}:{os.environ.get('PATH', '')}")
    with open(path, "wb") as out:
        subprocess.run([str(leanexport), "Init"], stdout=out, check=True, env=env)
    return path


def make_lean(work):
    lean, _ = lean_tool("lean")
    path = work / "lean.txt"
    with open(path, "wb") as out:
        subprocess.run([lean, str(ROOT / "tests/reference/binder-kinds.lean")], stdout=out,
                       check=True, cwd=ROOT)
    return path


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for block in iter(lambda: f.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


def compare(exprs, decls, lean, names):
    decl_diff = binder_diff = both = 0
    first = []
    for name in names:
        if name not in decls or name not in lean:
            continue
        both += 1
        got, want = exprs.binders(decls[name]), lean[name]
        bad = sum(1 for g, w in zip(got, want) if g != w) + abs(len(got) - len(want))
        if bad:
            decl_diff += 1
            binder_diff += bad
            if len(first) < 5:
                first.append(name)
    return both, decl_diff, binder_diff, first


def main(argv):
    p = argparse.ArgumentParser()
    p.add_argument("--export")
    p.add_argument("--lean")
    args = p.parse_args(argv)
    with tempfile.TemporaryDirectory() as tmp:
        work = pathlib.Path(tmp)
        export = pathlib.Path(args.export) if args.export else make_export(work)
        if sha256(export) != INIT_SHA:
            print(f"{export}: not the pinned Init export", file=sys.stderr)
            return 1
        lean = read_lean(args.lean if args.lean else make_lean(work))
        exprs, decls = read_export(export)
    only_export = len(set(decls) - set(lean))
    only_lean = len(set(lean) - set(decls))
    n, d, b, first = compare(exprs, decls, lean, sorted(decls))
    s1n, s1d, s1b, s1first = compare(exprs, decls, lean, S1_DECLS)
    print(f"binder kinds, export against pinned Lean: Init {n} declarations compared "
          f"({only_export} only in the export, {only_lean} only in Lean's environment), "
          f"{d} differ in {b} binders{' (first: ' + ', '.join(first) + ')' if first else ''}; "
          f"S1's {s1n} of {len(S1_DECLS)} declarations: {s1d} differ in {s1b} binders"
          f"{' (' + ', '.join(s1first) + ')' if s1first else ''}")
    return 1 if s1d or s1n != len(S1_DECLS) else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
