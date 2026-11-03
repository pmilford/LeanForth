"""Strict test oracle for the Forth NDJSON reader (src/import/ndjson.fs).

An independent second reader of lean4export 3.1.0 NDJSON as
docs/development/NDJSON_READER.md specifies it, written from that document,
not from the Forth code. oracle(data) returns (dump, result): dump is the
list of records the Forth reader must hand over, in the text form of
tests/core/ndjson-dump.fs, and result is "ok" or (outcomes, line), the set
of outcomes the reader may report and the line it must report them at.
Records before a failing line are handed over; nothing of the failing line
is (an inductive block is checked whole).

Strict where Python's json module is lenient: NaN and Infinity, lone
surrogates and duplicate keys are invalid; numbers keep their text, so
integers of any length work. Limits follow the reader: lines of at most
LINE_LIMIT bytes, JSON nested at most DEPTH deep, at most TOKENS JSON
tokens on one line, and natural number fields at most MAXN (64-bit cells).
Development only, untrusted. Adapted from the independent review of
2026-11-02 (docs/development/NDJSON_READER.md, "Evidence").
"""

import json

MAXN = 2**63 - 1
DEPTH = 64
TOKENS = 65536
LINE_LIMIT = 64 * 1024 * 1024
U32 = 4294967295
INVALID, FULL, UNSUPPORTED = "invalid", "full", "unsupported"
PINNED = ("lean4export", "3.1.0", "3.1.0", "4.35.0", "eb6cafb7290e8bd5f2937522d8d804f58f02bafc")
BINDER = {"default": 0, "implicit": 1, "strictImplicit": 2, "instImplicit": 3}
SAFETY = {"safe": 0, "unsafe": 1, "partial": 2}
QUOT = {"type": 0, "ctor": 1, "lift": 2, "ind": 3}
HINTS = {"opaque": 0, "abbrev": 1}


class Obj:
    """A JSON object with its members in order, duplicates kept."""

    def __init__(self, pairs):
        self.pairs = pairs

    def keys(self):
        return [k for k, _ in self.pairs]

    def get(self, key):
        return next(v for k, v in self.pairs if k == key)


class JInt:
    def __init__(self, text):
        self.text = text


class JReal:
    def __init__(self, text):
        self.text = text


class Fail(Exception):
    def __init__(self, outcomes):
        super().__init__(outcomes)
        self.outcomes = set(outcomes)


def no_constant(name):
    raise ValueError("not JSON: " + name)


def items(v):
    if isinstance(v, Obj):
        return [x for _, x in v.pairs]
    return v if isinstance(v, list) else []


def depth(v):
    inner = [depth(x) for x in items(v)]
    return 1 + max(inner + [0]) if isinstance(v, (Obj, list)) else 0


def tokens(v):
    """JSON tokens: one per value, plus one per object key."""
    keys = len(v.pairs) if isinstance(v, Obj) else 0
    return 1 + keys + sum(tokens(x) for x in items(v))


def check_strings(v):
    """Raise UnicodeError for a lone surrogate in a string or key."""
    if isinstance(v, str):
        v.encode("utf-8")
    for key in (v.keys() if isinstance(v, Obj) else []):
        key.encode("utf-8")
    for x in items(v):
        check_strings(x)


def raw_depth(line):
    """Bracket nesting of a line that may not be JSON, skipping strings."""
    level = most = 0
    inside = escaped = False
    for c in line:
        if inside:
            if escaped:
                escaped = False
            elif c == 0x5C:
                escaped = True
            elif c == 0x22:
                inside = False
        elif c == 0x22:
            inside = True
        elif c in (0x5B, 0x7B):
            level += 1
            most = max(most, level)
        elif c in (0x5D, 0x7D):
            level -= 1
    return most


def parse_line(line):
    if len(line) > LINE_LIMIT:
        raise Fail([FULL])
    if b"\r" in line or line.startswith(b"\xef\xbb\xbf"):
        raise Fail([INVALID])
    # A text that is not JSON may hit a limit before its error is found.
    limits = [FULL] if raw_depth(line) > DEPTH or len(line) > TOKENS else []
    try:
        v = json.loads(line.decode("utf-8"), object_pairs_hook=Obj, parse_int=JInt,
                       parse_float=JReal, parse_constant=no_constant)
        check_strings(v)
    except (ValueError, UnicodeError, RecursionError):
        raise Fail([INVALID] + limits)
    if depth(v) > DEPTH or tokens(v) > TOKENS:
        raise Fail([FULL])
    return v


class Collect:
    """Evaluate every field check of a record; collect all failure outcomes,
    since the reader may meet the fields in any order."""

    def __init__(self):
        self.outcomes = set()

    def __call__(self, check, *args):
        try:
            return check(*args)
        except Fail as e:
            self.outcomes |= e.outcomes
            return None

    def done(self):
        if self.outcomes:
            raise Fail(self.outcomes)


def natural_text(v):
    if not isinstance(v, JInt):
        return None
    if v.text == "-0":
        return "0"
    return None if v.text.startswith("-") else v.text


def value_of(text):
    return int(text) if len(text) < 40 else MAXN + 1


def nat(v):
    t = natural_text(v)
    if t is None:
        raise Fail([INVALID])
    if value_of(t) > MAXN:
        raise Fail([FULL])
    return value_of(t)


def ref(v, count, named=False):
    t = natural_text(v)
    if t is None or not 0 <= value_of(t) < count or (named and value_of(t) == 0):
        raise Fail([INVALID])
    return value_of(t)


def boolean(v):
    if v is True or v is False:
        return v
    raise Fail([INVALID])


def text(v):
    if not isinstance(v, str):
        raise Fail([INVALID])
    return v


def digits(v):
    t = natural_text(v)
    if t is None:
        raise Fail([INVALID])
    return t


def natlit(v):
    s = text(v)
    if s == "" or any(c not in "0123456789" for c in s) or (len(s) > 1 and s[0] == "0"):
        raise Fail([INVALID])
    return s


def choice(v, table):
    s = text(v)
    if s not in table:
        raise Fail([INVALID])
    return table[s]


def height(v):
    t = natural_text(v)
    if t is None or len(t) > 10 or int(t) > U32:
        raise Fail([INVALID])
    return int(t)


def array(v):
    if not isinstance(v, list):
        raise Fail([INVALID])
    return v


def shape(v, keys):
    if not isinstance(v, Obj):
        raise Fail([INVALID])
    found = v.keys()
    if len(found) != len(keys) or set(found) != set(keys):
        raise Fail([INVALID])
    return {k: v.get(k) for k in keys}


def refs(c, v, count, named):
    xs = c(array, v)
    return None if xs is None else [c(ref, x, count, named) for x in xs]


def hexed(s):
    return s.encode("utf-8").hex().upper() if s else "-"


def flag(b):
    return "1" if b else "0"


def listed(xs):
    return "[" + ",".join(str(x) for x in (xs or [])) + "]"


class State:
    def __init__(self):
        self.names, self.levels, self.exprs, self.decls, self.metas = 1, 1, 0, 0, 0


def name_record(kind, v, st, i):
    keys = {"str": ["pre", "str"], "num": ["pre", "i"]}
    if kind not in keys:
        raise Fail([INVALID])
    c = Collect()
    f = c(shape, v, keys[kind])
    c.done()
    pre = c(ref, f["pre"], st.names)
    part = c(text, f["str"]) if kind == "str" else c(digits, f["i"])
    c.done()
    return [f"name.str {i} {pre} {hexed(part)}" if kind == "str" else f"name.num {i} {pre} {part}"]


def level_record(kind, v, st, i):
    c = Collect()
    if kind == "succ":
        x = c(ref, v, st.levels)
    elif kind in ("max", "imax"):
        if not isinstance(v, list) or len(v) != 2:
            raise Fail([INVALID])
        x = f"{c(ref, v[0], st.levels)} {c(ref, v[1], st.levels)}"
    elif kind == "param":
        x = c(ref, v, st.names, True)
    else:
        raise Fail([INVALID])
    c.done()
    return [f"level.{kind} {i} {x}"]


EXPR_KEYS = {"const": ["name", "us"], "app": ["fn", "arg"],
             "lam": ["name", "type", "body", "binderInfo"],
             "forallE": ["name", "type", "body", "binderInfo"],
             "letE": ["name", "type", "value", "body", "nondep"],
             "proj": ["typeName", "idx", "struct"], "mdata": ["expr", "data"]}


def expr_record(kind, v, st, i):
    c = Collect()
    E, N, L = st.exprs, st.names, st.levels
    scalar = {"bvar": lambda: c(nat, v), "sort": lambda: c(ref, v, L),
              "natVal": lambda: c(natlit, v), "strVal": lambda: hexed(c(text, v) or "")}
    if kind in scalar:
        x = scalar[kind]()
        c.done()
        return [f"expr.{kind} {i} {x}"]
    if kind not in EXPR_KEYS:
        raise Fail([INVALID])
    f = c(shape, v, EXPR_KEYS[kind])
    c.done()
    if kind == "const":
        rest = f"{c(ref, f['name'], N, True)} {listed(refs(c, f['us'], L, False))}"
    elif kind == "app":
        rest = f"{c(ref, f['fn'], E)} {c(ref, f['arg'], E)}"
    elif kind in ("lam", "forallE"):
        rest = (f"{c(ref, f['name'], N)} {c(ref, f['type'], E)} {c(ref, f['body'], E)} "
                f"{c(choice, f['binderInfo'], BINDER)}")
    elif kind == "letE":
        rest = (f"{c(ref, f['name'], N)} {c(ref, f['type'], E)} {c(ref, f['value'], E)} "
                f"{c(ref, f['body'], E)} {flag(c(boolean, f['nondep']))}")
    elif kind == "proj":
        rest = f"{c(ref, f['typeName'], N, True)} {c(nat, f['idx'])} {c(ref, f['struct'], E)}"
    else:
        rest = f"{c(ref, f['expr'], E)}"
        if not isinstance(f["data"], Obj):
            c.outcomes.add(INVALID)
    c.done()
    return [f"expr.{kind} {i} {rest}"]


def decl_head(c, f, st):
    name = c(ref, f["name"], st.names, True)
    params = refs(c, f["levelParams"], st.names, True)
    return f"{name} {listed(params)} {c(ref, f['type'], st.exprs)}"


TYPE_KEYS = ["name", "levelParams", "type", "numParams", "numIndices", "all", "ctors",
             "numNested", "isRec", "isUnsafe", "isReflexive"]
CTOR_KEYS = ["name", "levelParams", "type", "induct", "cidx", "numParams", "numFields", "isUnsafe"]
REC_KEYS = ["name", "levelParams", "type", "all", "numParams", "numIndices", "numMotives",
            "numMinors", "rules", "k", "isUnsafe"]
DECL_KEYS = {"axiom": ["name", "levelParams", "type", "isUnsafe"],
             "def": ["name", "levelParams", "type", "value", "hints", "safety", "all"],
             "thm": ["name", "levelParams", "type", "value", "all"],
             "opaque": ["name", "levelParams", "type", "value", "isUnsafe", "all"],
             "quot": ["name", "levelParams", "type", "kind"],
             "inductive": ["types", "ctors", "recs"]}


def ind_type(c, g, st, j):
    head = decl_head(c, g, st)
    nums = [c(nat, g[k]) for k in ("numParams", "numIndices")]
    names = [refs(c, g[k], st.names, True) for k in ("all", "ctors")]
    nested = c(nat, g["numNested"])
    flags = [flag(c(boolean, g[k])) for k in ("isRec", "isUnsafe", "isReflexive")]
    return (f"ind.type {j} {head} {nums[0]} {nums[1]} {listed(names[0])} {listed(names[1])} "
            f"{nested} {' '.join(flags)}")


def ind_ctor(c, g, st, j):
    head = decl_head(c, g, st)
    induct = c(ref, g["induct"], st.names, True)
    nums = [c(nat, g[k]) for k in ("cidx", "numParams", "numFields")]
    unsafe = flag(c(boolean, g["isUnsafe"]))
    return f"ind.ctor {j} {head} {induct} {nums[0]} {nums[1]} {nums[2]} {unsafe}"


def ind_rec(c, g, st, j):
    head = decl_head(c, g, st)
    names = refs(c, g["all"], st.names, True)
    nums = [c(nat, g[k]) for k in ("numParams", "numIndices", "numMotives", "numMinors")]
    rules = []
    for r in c(array, g["rules"]) or []:
        q = c(shape, r, ["ctor", "nfields", "rhs"])
        if q is not None:
            rules.append(f"{c(ref, q['ctor'], st.names, True)}:{c(nat, q['nfields'])}:"
                         f"{c(ref, q['rhs'], st.exprs)}")
    k, unsafe = c(boolean, g["k"]), c(boolean, g["isUnsafe"])
    return (f"ind.rec {j} {head} {listed(names)} {' '.join(str(x) for x in nums)} "
            f"{flag(k)} {flag(unsafe)} [{','.join(rules)}]")


def inductive(c, f, st, n):
    types, ctors, recs = c(array, f["types"]), c(array, f["ctors"]), c(array, f["recs"])
    if types is not None and len(types) == 0:
        c.outcomes.add(INVALID)
    out = []
    for elements, keys, element in ((types, TYPE_KEYS, ind_type), (ctors, CTOR_KEYS, ind_ctor),
                                    (recs, REC_KEYS, ind_rec)):
        for j, x in enumerate(elements or []):
            g = c(shape, x, keys)
            if g is not None:
                out.append(element(c, g, st, j))
    c.done()
    return [f"decl.inductive {n} {len(types)} {len(ctors)} {len(recs)}"] + out


def decl_record(kind, v, st, n):
    if kind not in DECL_KEYS:
        raise Fail([INVALID])
    c = Collect()
    f = c(shape, v, DECL_KEYS[kind])
    c.done()
    if kind == "inductive":
        return inductive(c, f, st, n)
    head = f"decl.{kind} {n} {decl_head(c, f, st)}"
    value = c(ref, f["value"], st.exprs) if "value" in f else None
    if kind == "axiom":
        rest = flag(c(boolean, f["isUnsafe"]))
    elif kind == "def":
        hints = f["hints"]
        if isinstance(hints, Obj):
            g = c(shape, hints, ["regular"])
            hint = f"2 {c(height, g['regular'])}" if g is not None else None
        else:
            hint = f"{c(choice, hints, HINTS)} 0"
        rest = (f"{value} {hint} {c(choice, f['safety'], SAFETY)} "
                f"{listed(refs(c, f['all'], st.names, True))}")
    elif kind == "thm":
        rest = f"{value} {listed(refs(c, f['all'], st.names, True))}"
    elif kind == "opaque":
        rest = (f"{value} {flag(c(boolean, f['isUnsafe']))} "
                f"{listed(refs(c, f['all'], st.names, True))}")
    else:
        rest = f"{c(choice, f['kind'], QUOT)}"
    c.done()
    return [f"{head} {rest}"]


def meta_record(v):
    c = Collect()
    f = c(shape, v, ["exporter", "lean", "format"])
    c.done()
    parts = [c(shape, f["exporter"], ["name", "version"]),
             c(shape, f["lean"], ["githash", "version"]), c(shape, f["format"], ["version"])]
    values = [c(text, part[k]) for part in parts if part is not None for k in part]
    c.done()
    exporter, exporter_version, githash, lean_version, format_version = values
    if (exporter, exporter_version, format_version, lean_version, githash) != PINNED:
        raise Fail([UNSUPPORTED])
    return ["meta 0 " + " ".join(hexed(s) for s in values)]


FAMILIES = {"ie": ("exprs", expr_record), "in": ("names", name_record),
            "il": ("levels", level_record)}


def record(v, st):
    if not isinstance(v, Obj):
        raise Fail([INVALID])
    keys = v.keys()
    if st.metas == 0:
        if keys != ["meta"]:
            raise Fail([INVALID])
        out = meta_record(v.get("meta"))
        st.metas += 1
        return out
    family = [k for k in ("ie", "in", "il") if k in keys]
    if family:
        counter, decode = FAMILIES[family[0]]
        index = natural_text(v.get(family[0]))
        others = [k for k in keys if k != family[0]]
        if len(keys) != 2 or len(others) != 1 or index is None \
                or value_of(index) != getattr(st, counter):
            raise Fail([INVALID])
        kind = others[0]
        out = decode(kind, v.get(kind), st, getattr(st, counter))
        setattr(st, counter, getattr(st, counter) + 1)
        return out
    if "meta" in keys or len(keys) != 1:
        raise Fail([INVALID])
    out = decl_record(keys[0], v.get(keys[0]), st, st.decls)
    st.decls += 1
    return out


def oracle(data):
    """(dump, "ok" | (outcomes, line)) for the bytes of an export file."""
    st = State()
    parts = data.split(b"\n")
    complete, tail = parts[:-1], parts[-1]
    dump = []
    for n, line in enumerate(complete, 1):
        try:
            dump += record(parse_line(line), st)
        except Fail as e:
            return dump, (e.outcomes, n)
    if tail:
        return dump, ({FULL} if len(tail) > LINE_LIMIT else {INVALID}, len(complete) + 1)
    if st.metas == 0 or st.decls == 0:
        return dump, ({INVALID}, len(complete))
    return dump, "ok"
