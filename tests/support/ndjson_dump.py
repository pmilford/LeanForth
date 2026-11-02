"""Test oracle: print every record of a lean4export 3.1.0 NDJSON file in the
canonical text form of tests/core/ndjson-dump.fs, using Python's json module.

This is an independent second reader for differential tests of the Forth
reader (src/import/ndjson.fs). It assumes a valid export; with --check it
also checks, independently of the Forth code, that record indices are dense
and in order and that every reference names an earlier record, and fails
otherwise. The Forth reader's other fail-closed checks are tested
separately. Untrusted, development only.
Usage: python3 tests/support/ndjson_dump.py [--check] FILE
"""

import json
import sys

BINDER = {"default": 0, "implicit": 1, "strictImplicit": 2, "instImplicit": 3}
SAFETY = {"safe": 0, "unsafe": 1, "partial": 2}
QUOT = {"type": 0, "ctor": 1, "lift": 2, "ind": 3}


def text(s):
    return s.encode("utf-8").hex().upper() if s else "-"


def flag(b):
    return "1" if b else "0"


def lst(xs):
    return "[" + ",".join(str(x) for x in xs) + "]"


def hints(h):
    if isinstance(h, dict):
        return f"2 {h['regular']}"
    return {"opaque": "0 0", "abbrev": "1 0"}[h]


def decl(d):
    return f"{d['name']} {lst(d['levelParams'])} {d['type']}"


def rule(r):
    return f"{r['ctor']}:{r['nfields']}:{r['rhs']}"


def expression(o):
    i = o["ie"]
    kind = next(k for k in o if k != "ie")
    v = o[kind]
    if kind in ("bvar", "sort"):
        rest = f"{v}"
    elif kind == "const":
        rest = f"{v['name']} {lst(v['us'])}"
    elif kind == "app":
        rest = f"{v['fn']} {v['arg']}"
    elif kind in ("lam", "forallE"):
        rest = f"{v['name']} {v['type']} {v['body']} {BINDER[v['binderInfo']]}"
    elif kind == "letE":
        rest = f"{v['name']} {v['type']} {v['value']} {v['body']} {flag(v['nondep'])}"
    elif kind == "proj":
        rest = f"{v['typeName']} {v['idx']} {v['struct']}"
    elif kind == "natVal":
        rest = v
    elif kind == "strVal":
        rest = text(v)
    else:  # mdata
        rest = f"{v['expr']}"
    return [f"expr.{kind} {i} {rest}"]


def level(o):
    i = o["il"]
    kind = next(k for k in o if k != "il")
    v = o[kind]
    rest = f"{v[0]} {v[1]}" if kind in ("max", "imax") else f"{v}"
    return [f"level.{kind} {i} {rest}"]


def name(o):
    i = o["in"]
    if "str" in o:
        return [f"name.str {i} {o['str']['pre']} {text(o['str']['str'])}"]
    return [f"name.num {i} {o['num']['pre']} {o['num']['i']}"]


def inductive(n, d):
    out = [f"decl.inductive {n} {len(d['types'])} {len(d['ctors'])} {len(d['recs'])}"]
    for j, t in enumerate(d["types"]):
        out.append(f"ind.type {j} {decl(t)} {t['numParams']} {t['numIndices']} {lst(t['all'])} "
                   f"{lst(t['ctors'])} {t['numNested']} {flag(t['isRec'])} {flag(t['isUnsafe'])} "
                   f"{flag(t['isReflexive'])}")
    for j, c in enumerate(d["ctors"]):
        out.append(f"ind.ctor {j} {decl(c)} {c['induct']} {c['cidx']} {c['numParams']} "
                   f"{c['numFields']} {flag(c['isUnsafe'])}")
    for j, r in enumerate(d["recs"]):
        out.append(f"ind.rec {j} {decl(r)} {lst(r['all'])} {r['numParams']} {r['numIndices']} "
                   f"{r['numMotives']} {r['numMinors']} {flag(r['k'])} {flag(r['isUnsafe'])} "
                   f"[{','.join(rule(x) for x in r['rules'])}]")
    return out


def declaration(n, o):
    kind = next(iter(o))
    d = o[kind]
    if kind == "inductive":
        return inductive(n, d)
    head = f"decl.{kind} {n} {decl(d)}"
    if kind == "axiom":
        return [f"{head} {flag(d['isUnsafe'])}"]
    if kind == "def":
        return [f"{head} {d['value']} {hints(d['hints'])} {SAFETY[d['safety']]} {lst(d['all'])}"]
    if kind == "thm":
        return [f"{head} {d['value']} {lst(d['all'])}"]
    if kind == "opaque":
        return [f"{head} {d['value']} {flag(d['isUnsafe'])} {lst(d['all'])}"]
    return [f"{head} {QUOT[d['kind']]}"]  # quot


def meta(o):
    m = o["meta"]
    return [f"meta 0 {text(m['exporter']['name'])} {text(m['exporter']['version'])} "
            f"{text(m['lean']['githash'])} {text(m['lean']['version'])} {text(m['format']['version'])}"]


class Counts:
    """Records so far, for --check: names and levels count their implicit 0."""

    def __init__(self):
        self.names, self.levels, self.exprs = 1, 1, 0


def check_refs(o, c):
    """Raise ValueError unless the record's own index is the next one and every
    reference names an earlier record. Independent of the Forth reader's code."""
    def below(value, count, what):
        if type(value) is not int or not 0 <= value < count:
            raise ValueError(f"bad {what} reference {value!r}")

    def names(xs):
        for x in xs:
            below(x, c.names, "name")

    def decl_refs(d):
        below(d["name"], c.names, "name")
        names(d["levelParams"])
        below(d["type"], c.exprs, "expression")

    if "meta" in o:
        return
    if "in" in o:
        if o["in"] != c.names:
            raise ValueError("name index out of order")
        below(next(v for k, v in o.items() if k != "in")["pre"], c.names, "name")
        c.names += 1
    elif "il" in o:
        if o["il"] != c.levels:
            raise ValueError("level index out of order")
        kind = next(k for k in o if k != "il")
        v = o[kind]
        for x in (v if isinstance(v, list) else [v]):
            below(x, c.names if kind == "param" else c.levels, kind)
        c.levels += 1
    elif "ie" in o:
        if o["ie"] != c.exprs:
            raise ValueError("expression index out of order")
        kind = next(k for k in o if k != "ie")
        v = o[kind]
        refs = {"sort": [], "const": [], "app": ["fn", "arg"], "lam": ["type", "body"],
                "forallE": ["type", "body"], "letE": ["type", "value", "body"],
                "proj": ["struct"], "mdata": ["expr"]}.get(kind, [])
        for key in refs:
            below(v[key], c.exprs, "expression")
        if kind == "sort":
            below(v, c.levels, "level")
        if kind == "const":
            below(v["name"], c.names, "name")
            for u in v["us"]:
                below(u, c.levels, "level")
        if kind in ("lam", "forallE", "letE"):
            below(v["name"], c.names, "name")
        if kind == "proj":
            below(v["typeName"], c.names, "name")
        c.exprs += 1
    else:
        d = o[next(iter(o))]
        if "types" in d:
            for t in d["types"]:
                decl_refs(t)
                names(t["all"])
                names(t["ctors"])
            for k in d["ctors"]:
                decl_refs(k)
                below(k["induct"], c.names, "name")
            for r in d["recs"]:
                decl_refs(r)
                names(r["all"])
                for rule in r["rules"]:
                    below(rule["ctor"], c.names, "name")
                    below(rule["rhs"], c.exprs, "expression")
        else:
            decl_refs(d)
            if "value" in d:
                below(d["value"], c.exprs, "expression")
            names(d.get("all", []))


def main():
    decls = 0
    out = sys.stdout
    check = sys.argv[1] == "--check"
    counts = Counts()
    with open(sys.argv[-1], "rb") as f:
        for raw in f:
            o = json.loads(raw.decode("utf-8"))
            if check:
                check_refs(o, counts)
            if "meta" in o:
                lines = meta(o)
            elif "ie" in o:
                lines = expression(o)
            elif "in" in o:
                lines = name(o)
            elif "il" in o:
                lines = level(o)
            else:
                lines = declaration(decls, o)
                decls += 1
            for line in lines:
                out.write(line + "\n")
    out.write("ok\n")


if __name__ == "__main__":
    main()
