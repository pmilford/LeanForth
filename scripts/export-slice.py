#!/usr/bin/env python3
"""Cut the smallest Lean export that holds some declarations.

    python3 -I scripts/export-slice.py EXPORT NAME... > SLICE

EXPORT is a lean4export 3.1.0 NDJSON file (the format `leanforth check`
reads, docs/development/NDJSON_READER.md). SLICE holds, in the original
order and with the original header line, the named declarations and
everything their checking needs: every declaration whose constant occurs in
a type or value (transitively), the whole inductive block of any inductive
type, constructor or recursor named, and the names, universe levels and
expressions those declarations use. It also holds the declarations the
LeanForth checker looks up by name itself (Nat, Bool, Char, List, String,
Eq, Quot, propext, Classical.choice, Quot.sound; src/kernel/env-schedule.fs,
lf-sch-builtins), those the export has. Records keep their original indices,
so the slice has gaps; Lean's own reader (Export.Parse) and LeanForth's take
any natural numbers in any order. Re-running one failing root of a library
in seconds is the purpose: slice it once, check the slice.

NAME is a declaration's name as Lean prints it, `Nat.add_comm`; a component
with a dot or a space is written in «», a numeric component as digits.
Several NAMEs make one slice. A name the export does not declare is an
error (exit 2, nothing written). A slice has no manifest, so check it with
`leanforth check --no-manifest SLICE`.

Three passes over EXPORT, each sequential: (1) the tables of names, levels
and expressions as compact arrays (about 13 bytes per expression, 12 per
name, 9 per level) and the byte offset of every declaration; (2) the
closure, reading only the declarations it needs, by offset; (3) the copy.
Python standard library only; memory is a few GB for a library the size of
Mathlib (6 GB file, about 100 million expressions), under 100 MB for Init.
Untrusted development tool: the slice is checked by the checkers, and a
slice's verdicts are its own, not the whole export's.
"""

import json
import re
import sys
from array import array

NONE = 0xFFFFFFFF
# Expression kinds in the arrays.
BVAR, SORT, CONST, APP, LAM, PI, LET, PROJ, NAT, STR, MDATA = range(11)
EXPR_KIND = {"bvar": BVAR, "sort": SORT, "const": CONST, "app": APP, "lam": LAM,
             "forallE": PI, "letE": LET, "proj": PROJ, "natVal": NAT, "strVal": STR,
             "mdata": MDATA}
SUCC, MAX, IMAX, PARAM = 1, 2, 3, 4
# The names the LeanForth checker looks up itself (lf-sch-builtins).
BUILTINS = ["Nat", "Nat.zero", "Nat.succ", "Bool", "Bool.true", "Bool.false", "Char",
            "Char.ofNat", "List", "List.nil", "List.cons", "String", "String.mk",
            "String.ofList", "Eq", "Eq.refl", "Quot", "Quot.mk", "Quot.lift", "Quot.ind",
            "propext", "Classical.choice", "Quot.sound"]
DECL_KINDS = ("axiom", "def", "thm", "opaque", "quot", "inductive")
# In a declaration's JSON: what an integer under each key refers to.
NAME_KEYS = {"name", "induct", "ctor", "typeName"}
NAME_LISTS = {"levelParams", "all", "ctors"}
EXPR_KEYS = {"type", "value", "rhs"}


class SliceError(Exception):
    """A problem with the export or the request: message, exit code."""

    def __init__(self, message, code=2):
        super().__init__(message)
        self.code = code


def split_name(text):
    """Components of a printed name: «» quotes, digits for numbers."""
    parts, cur, quoted, plain = [], "", False, True
    for ch in text:
        if ch == "«":
            quoted, plain = True, False
        elif ch == "»":
            quoted = False
        elif ch == "." and not quoted:
            parts.append((cur, plain))
            cur, plain = "", True
        else:
            cur += ch
    parts.append((cur, plain))
    if any(p == "" for p, _ in parts):
        raise SliceError("not a name: " + text)
    return [(1, int(p)) if plain and p.isdigit() else (0, p) for p, plain in parts]


def name_hash(parent, kind, comp):
    return hash((parent, kind, comp)) & 0xFFFFFFFFFFFFFFFF


def text_hash(text):
    h = 0
    for kind, comp in split_name(text):
        h = name_hash(h, kind, comp)
    return h


class Tables:
    """What pass 1 learns: the tables, and where each declaration is."""

    def __init__(self, wanted):
        self.wanted = wanted                 # name hash -> printed name
        self.found = {}                      # printed name -> name ids
        self.np, self.nh = array("I", [0]), array("Q", [0])
        self.lk, self.la, self.lb = array("B", [0]), array("I", [0]), array("I", [0])
        self.ek, self.ea = array("B"), array("I")
        self.eb, self.ec, self.ulist = array("I"), array("I"), array("I")
        self.letbody = {}
        self.declof = array("I", [NONE])     # per name: its declaration, or NONE
        self.offsets = array("Q")            # per declaration: its line's offset
        self.header = b""


def need_sequential(index, count, family):
    if index != count:
        raise SliceError(f"{family} index {index} out of order: this tool needs the "
                         f"indices lean4export writes, one more each time", 3)


def read_name(t, obj):
    index = obj["in"]
    need_sequential(index, len(t.np), "name")
    if "str" in obj:
        pre, kind, comp = obj["str"]["pre"], 0, obj["str"]["str"]
    else:
        pre, kind, comp = obj["num"]["pre"], 1, obj["num"]["i"]
    h = name_hash(t.nh[pre], kind, comp)
    t.np.append(pre)
    t.nh.append(h)
    t.declof.append(NONE)
    if h in t.wanted:
        t.found.setdefault(t.wanted[h], []).append(index)


def read_level(t, obj):
    index = obj["il"]
    need_sequential(index, len(t.lk), "level")
    for key in ("succ", "max", "imax", "param"):
        if key in obj:
            v = obj[key]
            break
    kind = {"succ": SUCC, "max": MAX, "imax": IMAX, "param": PARAM}[key]
    a, b = (v[0], v[1]) if kind in (MAX, IMAX) else (v, 0)
    t.lk.append(kind)
    t.la.append(a)
    t.lb.append(b)


def read_expr(t, obj):
    index = obj["ie"]
    need_sequential(index, len(t.ek), "expression")
    for key, v in obj.items():
        if key != "ie":
            break
    kind = EXPR_KIND[key]
    a = b = c = 0
    if kind == SORT:
        a = v
    elif kind == CONST:
        a, b, c = v["name"], len(t.ulist), len(v["us"])
        t.ulist.extend(v["us"])
    elif kind == APP:
        a, b = v["fn"], v["arg"]
    elif kind in (LAM, PI):
        a, b, c = v["name"], v["type"], v["body"]
    elif kind == LET:
        a, b, c = v["name"], v["type"], v["value"]
        t.letbody[index] = v["body"]
    elif kind == PROJ:
        a, b = v["typeName"], v["struct"]
    elif kind == MDATA:
        a = v["expr"]
    t.ek.append(kind)
    t.ea.append(a)
    t.eb.append(b)
    t.ec.append(c)


def declared_names(obj):
    """The names a declaration record declares."""
    kind, body = next(iter(obj.items()))
    if kind == "inductive":
        return [x["name"] for part in ("types", "ctors", "recs") for x in body[part]]
    return [body["name"]]


def read_declaration(t, obj, offset):
    kind = next(iter(obj))
    if kind not in DECL_KINDS:
        raise SliceError(f"unknown record kind {kind!r}", 3)
    d = len(t.offsets)
    t.offsets.append(offset)
    for n in declared_names(obj):
        if n >= len(t.declof):
            raise SliceError("a declaration names a name not yet given", 3)
        t.declof[n] = d


def pass_one(path, wanted):
    t = Tables(wanted)
    offset = 0
    with open(path, "rb") as f:
        for number, line in enumerate(f, 1):
            obj = json.loads(line)
            if number == 1:
                if "meta" not in obj:
                    raise SliceError("the first line is not the metadata record", 3)
                t.header = line
            elif "in" in obj:
                read_name(t, obj)
            elif "il" in obj:
                read_level(t, obj)
            elif "ie" in obj:
                read_expr(t, obj)
            else:
                read_declaration(t, obj, offset)
            offset += len(line)
    return t


class Closure:
    """Pass 2: the records a set of declarations needs."""

    def __init__(self, t, path):
        self.t = t
        self.f = open(path, "rb")
        self.need_n = bytearray(len(t.np))
        self.need_l = bytearray(len(t.lk))
        self.need_e = bytearray(len(t.ek))
        self.need_d = bytearray(len(t.offsets))
        self.todo = []                       # declarations not yet read

    def name(self, n):
        np, need = self.t.np, self.need_n
        while n and not need[n]:
            need[n] = 1
            n = np[n]

    def level(self, root):
        t, need, stack = self.t, self.need_l, [root]
        while stack:
            u = stack.pop()
            if u == 0 or need[u]:
                continue
            need[u] = 1
            kind = t.lk[u]
            if kind == PARAM:
                self.name(t.la[u])
            elif kind == SUCC:
                stack.append(t.la[u])
            else:
                stack.extend((t.la[u], t.lb[u]))

    def constant(self, n):
        self.name(n)
        d = self.t.declof[n]
        if d != NONE and not self.need_d[d]:
            self.need_d[d] = 1
            self.todo.append(d)

    def expr(self, root):
        t, need, stack = self.t, self.need_e, [root]
        ek, ea, eb, ec = t.ek, t.ea, t.eb, t.ec
        while stack:
            u = stack.pop()
            if need[u]:
                continue
            need[u] = 1
            k = ek[u]
            if k == APP:
                stack.extend((ea[u], eb[u]))
            elif k == LAM or k == PI:
                self.name(ea[u])
                stack.extend((eb[u], ec[u]))
            elif k == CONST:
                self.constant(ea[u])
                for i in range(eb[u], eb[u] + ec[u]):
                    self.level(t.ulist[i])
            elif k == SORT:
                self.level(ea[u])
            elif k == LET:
                self.name(ea[u])
                stack.extend((eb[u], ec[u], t.letbody[u]))
            elif k == PROJ:
                self.name(ea[u])
                stack.append(eb[u])
            elif k == MDATA:
                stack.append(ea[u])

    def refs(self, key, value):
        """Walk a declaration's JSON: names under name keys, expressions under
        expression keys; other numbers (counts, flags) name nothing."""
        if isinstance(value, dict):
            for k, v in value.items():
                self.refs(k, v)
        elif isinstance(value, list):
            for v in value:
                if isinstance(v, int) and key in NAME_LISTS:
                    self.name(v)
                else:
                    self.refs(key, v)
        elif isinstance(value, int) and not isinstance(value, bool):
            if key in NAME_KEYS:
                self.name(value)
            elif key in EXPR_KEYS:
                self.expr(value)

    def read(self, d):
        self.f.seek(self.t.offsets[d])
        self.refs("", json.loads(self.f.readline()))

    def run(self, roots):
        for d in roots:
            if not self.need_d[d]:
                self.need_d[d] = 1
                self.todo.append(d)
        while self.todo:
            self.read(self.todo.pop())
        self.f.close()


FAMILY = re.compile(rb'^\{"(in|il|ie)":(\d+),|,"(in|il|ie)":(\d+)\}$')


def pass_three(path, c, out):
    kept = {"in": c.need_n, "il": c.need_l, "ie": c.need_e}
    lines = decls = 0
    with open(path, "rb") as f:
        out.write(f.readline())
        for line in f:
            m = FAMILY.search(line.rstrip(b"\n"))
            if m:
                fam, index = (m.group(1), m.group(2)) if m.group(1) else (m.group(3), m.group(4))
                keep = kept[fam.decode()][int(index)]
            else:
                keep = c.need_d[decls]
                decls += 1
            if keep:
                out.write(line)
                lines += 1
    return lines, decls


def find_ids(t, names):
    ids = []
    for text in names:
        found = [n for n in t.found.get(text, []) if t.declof[n] != NONE]
        if not found:
            raise SliceError(f"{text}: not declared in the export")
        ids.extend(t.declof[n] for n in found)
    return ids


def slice_export(path, names, out):
    wanted = {text_hash(text): text for text in names + BUILTINS}
    t = pass_one(path, wanted)
    roots = find_ids(t, names)
    roots += [t.declof[n] for text in BUILTINS for n in t.found.get(text, [])
              if t.declof[n] != NONE]
    c = Closure(t, path)
    c.run(sorted(set(roots)))
    lines, _ = pass_three(path, c, out)
    return sum(c.need_d), len(t.offsets), lines


def main(argv):
    if len(argv) < 3:
        sys.stderr.write("usage: export-slice.py EXPORT NAME... > SLICE\n")
        return 4
    try:
        kept, total, lines = slice_export(argv[1], argv[2:], sys.stdout.buffer)
    except SliceError as e:
        sys.stderr.write(f"export-slice: {e}\n")
        return e.code
    except OSError as e:
        sys.stderr.write(f"export-slice: {e}\n")
        return 4
    sys.stderr.write(f"export-slice: {kept} of {total} declarations, {lines + 1} lines\n")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
