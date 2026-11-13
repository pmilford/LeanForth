#!/usr/bin/env python3
"""Verification-condition generator v0 for the program IR (task 2.5.5).

Usage (from the repository root):
  python3 scripts/program_vc.py --out FILE.lean --summary FILE.json CONTRACT...

UNTRUSTED. It reads a word's IR (the reader's text form, version 0.1) and a
contract (docs/programming/PROGRAM_VC.md) and writes one Lean file:

- a verbatim copy of the IR semantics of tests/reference/program-ir.lean;
- the program, translated from the IR text into Lean terms;
- the contract's postcondition as a Lean predicate `post`;
- one obligation per path through the word (symbolic execution: IF splits
  a path, calls are followed, constants are evaluated): under the path's
  conditions, `post` holds of the stack the path leaves, or, for a path
  that fails (underflow, a division outside the model, ...), the path
  cannot be taken; each with a proof script;
- `contract`, the contract itself as a statement about `callWord` on the
  IR semantics, proved by splitting on the same conditions and running the
  IR in Lean on each path;
- or, when the generator finds inputs that break the contract, instead a
  theorem `refuted`: Lean evaluates the IR on those inputs and proves the
  contract false.

Lean checks everything; the generator only proposes. A wrong generator
can make Lean fail (an unprovable obligation, a proof that does not
check), never make it accept a false contract, because `contract` is
stated against the IR semantics itself, not against the generator's
symbolic results. Loops (BEGIN ... WHILE ... REPEAT) need invariants
(IR version 1, task 4.4.1) and make a word unsupported here, as do
recursion and stack effects deeper than the declared inputs.

The summary (JSON) lists, per contract, its status (discharged, refuted or
unsupported), the obligations with plain-text statements and theorem
names, and the counterexample of a refuted contract. A status of
discharged means only "Lean is expected to prove these"; whether it did is
what `make reference-program-vc` checks.
"""
import argparse
import hashlib
import itertools
import json
from pathlib import Path
import re
import sys
import unicodedata

GENERATOR_VERSION = "0.1"
MODEL = "tests/reference/program-ir.lean"
# The literals v0 accepts: those that fit every cell width (Cells.fits_*).
SMALL_LITERALS = (-1, 0, 1)


def model_ranges(lines):
    """The copied parts of the model, by anchors: the semantics (cells to the
    ir_simp tactic) and the IR text printer (Prim.word to render, the
    lowest version that fits included)."""
    def at(prefix):
        for i, line in enumerate(lines):
            if line.startswith(prefix):
                return i + 1
        raise Malformed(f"{MODEL}: no line starting {prefix!r}")

    def last_before_blank(start):
        i = start
        while lines[i].strip():
            i += 1
        return i

    part3 = at("-- Part 3. The six example words")
    prelude_end = max(i for i in range(1, part3) if lines[i - 1].strip())
    return (at("/-- A host cell of"), prelude_end), \
        (at("def Prim.word"), last_before_blank(at("def render ")))

RESERVED = re.compile(r"(c|fuel|tail|rs|out|g|h|this|[fhp][0-9]+|pre[0-9]+)$")
CELL_BITS = 64               # counterexamples are searched and refuted on 64-bit cells
CMIN, CMAX = -(1 << (CELL_BITS - 1)), (1 << (CELL_BITS - 1)) - 1


class Unsupported(Exception):
    """The word or contract is outside what v0 handles."""


class Malformed(Exception):
    """The IR text or contract is not well formed."""


class Limit(Exception):
    """A limit given to the generator was reached (scripts/program_verify.py's
    --paths-limit and --search-limit): code is paths-limit or search-limit."""

    def __init__(self, code, message):
        super().__init__(message)
        self.code = code


# Limits leanforth verify gives (plan 8.4.1b; None: unbounded, as generate()):
# paths double with each IF, and the counterexample search tries
# len(CANDIDATES) ** inputs combinations (12^5 = 248,832 for five inputs).
PATHS_LIMIT = 256
SEARCH_LIMIT = 250_000


# Text from a contract or an IR file never enters the generated Lean file as
# code: only the expression parser's output does (lean() below). The
# contract's statement does not enter it at all (it stays in the summary).
# Names and paths enter only inside comments and string literals, so each must
# be unable to end or open a Lean comment (-/ and /-; Lean's block comments
# nest), and a name or path inside a string unable to end it or escape (" and
# \); and no text may hold control, format or separator characters (Unicode
# Cc, Cf, Cs, Zl, Zp), which could hide what it says. Review B1 of the verify
# design (2026-11-13): a statement holding `-/ macro_rules ... /--` made Lean
# accept a false contract.
HIDDEN = ("Cc", "Cf", "Cs", "Zl", "Zp")


def checked_text(text, what, quoted=False):
    """text, or Malformed when it could change the generated Lean file (see above)."""
    bad = [d for d in ("-/", "/-") + (('"', "\\") if quoted else ()) if d in text]
    hidden = [f"U+{ord(ch):04X}" for ch in text if unicodedata.category(ch) in HIDDEN]
    if bad or hidden:
        raise Malformed(f"{what} holds {', '.join(bad + hidden[:3])}, which the generated "
                        "Lean file cannot hold safely: refused")
    return text


# ---------------------------------------------------------------- the IR text

PRIM_NAMES = {
    "dup": "dup", "drop": "drop", "swap": "swap", "over": "over", "nip": "nip",
    "tuck": "tuck", "rot": "rot", "2dup": "twoDup", "2drop": "twoDrop", ">r": "toR",
    "r>": "fromR", "r@": "rFetch", "+": "add", "-": "sub", "*": "mul", "/": "div",
    "mod": "mod", "negate": "negate", "abs": "abs", "1+": "onePlus", "1-": "oneMinus",
    "=": "eq", "<>": "ne", "<": "lt", ">": "gt", "0=": "zeroEq", "0<>": "zeroNe",
    "0<": "zeroLt", "0>": "zeroGt", "and": "and", "or": "or", "xor": "xor",
    "invert": "invert", "rshift": "rshift", "max": "max", "min": "min", "true": "true",
    "false": "false",
}


def ir_tokens(line):
    words = line.split()
    if words and words[-1].startswith("@"):
        words = words[:-1]
    return words


def parse_block(lines, i):
    """Instructions from lines[i:] up to a line that ends the block."""
    body = []
    while i < len(lines):
        words = lines[i]
        head = words[0] if words else ""
        if head == "prim" and len(words) == 2 and words[1] in PRIM_NAMES:
            body.append(("prim", words[1]))
        elif head == "lit" and len(words) == 2 and re.fullmatch(r"-?[0-9]+", words[1]):
            body.append(("lit", int(words[1])))
        elif head == "call" and len(words) == 2:
            body.append(("call", checked_text(words[1], "a called name", quoted=True)))
        elif words == ["exit"]:
            body.append(("exit",))
        elif words == ["if"]:
            yes, i = parse_block(lines, i + 1)
            no = []
            if i < len(lines) and lines[i] == ["else"]:
                no, i = parse_block(lines, i + 1)
            if i >= len(lines) or lines[i] != ["then"]:
                raise Malformed("IF without THEN")
            body.append(("if", yes, no))
        elif words == ["begin"]:
            test, i = parse_block(lines, i + 1)
            if i >= len(lines) or lines[i] != ["while"]:
                raise Malformed("BEGIN without WHILE")
            loop, i = parse_block(lines, i + 1)
            if i >= len(lines) or lines[i] != ["repeat"]:
                raise Malformed("WHILE without REPEAT")
            body.append(("loop", test, loop))
        else:
            return body, i
        i += 1
    return body, i


def ir_source(text):
    """The path on the IR text's source line."""
    return text.splitlines()[1].split(" ", 1)[1]


def parse_ir(text):
    """Definitions [(name, kind, body)] in source order."""
    lines = [ir_tokens(line) for line in text.splitlines()]
    if len(lines) < 2 or lines[0] != ["lf-ir", "0.1"] or lines[1][:1] != ["source"]:
        raise Malformed("not IR 0.1 text")
    defs, i = [], 2
    while i < len(lines):
        if len(lines[i]) != 2 or lines[i][0] not in ("word", "constant"):
            raise Malformed(f"unexpected line {i + 1}")
        kind, name = lines[i]
        checked_text(name, f"the name {name!r}", quoted=True)
        body, i = parse_block(lines, i + 1)
        if i >= len(lines) or lines[i] != ["end"]:
            raise Malformed(f"definition {name} not closed")
        defs.append((name, kind, body))
        i += 1
    return defs


def lean_int(n):
    return str(n) if n >= 0 else f"({n})"


def lean_block(body):
    return "[" + ", ".join(lean_instr(i) for i in body) + "]"


def lean_instr(instr):
    kind = instr[0]
    if kind == "prim":
        return f".prim .{PRIM_NAMES[instr[1]]}"
    if kind == "lit":
        return f".lit {lean_int(instr[1])}"
    if kind == "call":
        return f'.call "{instr[1]}"'
    if kind == "exit":
        return ".exit"
    if kind == "if":
        return f".ifElse {lean_block(instr[1])} {lean_block(instr[2])}"
    return f".loop {lean_block(instr[1])} {lean_block(instr[2])}"


# ----------------------------------------------------------- the contract text

TOKEN = re.compile(r"\s*(->|\|\||&&|<>|<=|>=|cell\.max|cell\.min|[A-Za-z_][A-Za-z0-9_]*|"
                   r"[0-9]+|[-+*()<>=!,])")


def lex(text):
    tokens, pos = [], 0
    text = text.rstrip()
    while pos < len(text):
        match = TOKEN.match(text, pos)
        if not match:
            raise Malformed(f"cannot read: {text[pos:]}")
        tokens.append(match.group(1))
        pos = match.end()
    return tokens


class ExprParser:
    """Contract expressions: -> || && ! comparisons + - * unary minus, and
    min(a, b) max(a, b) abs(a) flag(cond) fits(a) cell.max cell.min."""

    def __init__(self, text):
        self.tokens, self.pos = lex(text), 0

    def peek(self):
        return self.tokens[self.pos] if self.pos < len(self.tokens) else None

    def take(self, expected=None):
        token = self.peek()
        if token is None or (expected and token != expected):
            raise Malformed(f"expected {expected or 'more'} in {' '.join(self.tokens)}")
        self.pos += 1
        return token

    def parse(self):
        expr = self.implies()
        if self.peek() is not None:
            raise Malformed(f"unexpected {self.peek()} in {' '.join(self.tokens)}")
        return expr

    def implies(self):
        left = self.disj()
        if self.peek() == "->":
            self.take()
            return ("implies", left, self.implies())
        return left

    def disj(self):
        left = self.conj()
        while self.peek() == "||":
            self.take()
            left = ("or", left, self.conj())
        return left

    def conj(self):
        left = self.negation()
        while self.peek() == "&&":
            self.take()
            left = ("and", left, self.negation())
        return left

    def negation(self):
        if self.peek() == "!":
            self.take()
            return ("not", self.negation())
        return self.comparison()

    def comparison(self):
        left = self.sum()
        if self.peek() in ("=", "<>", "<", "<=", ">", ">="):
            op = self.take()
            return ("cmp", op, left, self.sum())
        return left

    def sum(self):
        left = self.product()
        while self.peek() in ("+", "-"):
            op = self.take()
            left = ("add" if op == "+" else "sub", left, self.product())
        return left

    def product(self):
        left = self.unary()
        while self.peek() == "*":
            self.take()
            left = ("mul", left, self.unary())
        return left

    def unary(self):
        if self.peek() == "-":
            self.take()
            return ("neg", self.unary())
        return self.atom()

    def atom(self):
        token = self.take()
        if token == "(":
            expr = self.implies()
            self.take(")")
            return expr
        if token.isdigit():
            return ("lit", int(token))
        if token == "cell.max":
            return ("cmax",)
        if token == "cell.min":
            return ("cmin",)
        if token in ("true", "false"):
            return ("bool", token == "true")
        if token in ("min", "max", "abs", "flag", "fits"):
            self.take("(")
            args = [self.implies()]
            while self.peek() == ",":
                self.take()
                args.append(self.implies())
            self.take(")")
            if len(args) != (2 if token in ("min", "max") else 1):
                raise Malformed(f"{token} takes {2 if token in ('min', 'max') else 1} argument(s)")
            return ("fn", token, *args)
        if re.fullmatch(r"[a-z][a-z0-9_]*", token):
            return ("var", token)
        raise Malformed(f"unexpected {token}")


def contract_lines(text, path):
    """The contract's lines, split at LF only (a CR just before an LF dropped), or Malformed
    when the file holds a character that would hide a line (review H1, 2026-11-13: Python's
    splitlines also breaks at U+2028, U+2029, NEL, VT, FF, U+001C-U+001E and a lone CR,
    which viewers do not show, so a hidden `pre value < value` made a false contract
    vacuously true): any control character but LF and TAB, a CR not before an LF, and
    format and separator characters (Unicode Cc, Cf, Cs, Zl, Zp)."""
    for number, line in enumerate(text.split("\n"), 1):
        body = line[:-1] if line.endswith("\r") else line
        hidden = [f"U+{ord(ch):04X}" for ch in body
                  if ch != "\t" and unicodedata.category(ch) in HIDDEN]
        if hidden:
            raise Malformed(f"{path}:{number}: the file holds {', '.join(hidden[:3])}, which "
                            "could hide a line: refused")
    return [line[:-1] if line.endswith("\r") else line for line in text.split("\n")]


def contract_scope_problems(contract):
    """Names a contract reads but never binds (review M2): a `pre` line and a guard may read
    only inputs, an ensure line also the results its case names on its out line. In Lean
    an unbound name would be auto-bound (now refused there too) or a global (`default` is
    0 in Int), and either can make a false contract true."""
    inputs, problems = set(contract["inputs"]), []
    for expr in contract["pre"]:
        problems += sorted(variables(expr) - inputs)
    for case in contract["cases"]:
        results = {t for t in case["out"] if out_item(t, inputs)[0] == "unknown"}
        problems += sorted(variables(case["guard"]) - inputs)
        for expr, _ in case["ensure"]:
            problems += sorted(variables(expr) - inputs - results)
    return problems


def variables(expr, found=None):
    """The names an expression reads."""
    found = set() if found is None else found
    if isinstance(expr, tuple):
        if expr[0] == "var":
            found.add(expr[1])
        for part in expr[1:]:
            variables(part, found)
    return found


def read_contract(path):
    """A contract file's text exactly as stored: Python's text mode would turn a lone CR,
    which no viewer shows, into a line break before contract_lines could refuse it."""
    return Path(path).read_bytes().decode("utf-8")


# Lines a contract has at most once: a second one would quietly replace the first.
SINGLE_LINES = ("id", "word", "ir", "stack", "statement", "expect", "inputs")


def parse_contract(text, path):
    contract = {"path": path, "pre": [], "cases": [], "file": None}
    case = None
    for number, raw in enumerate(contract_lines(text, path), 1):
        line = raw.split("#", 1)[0].rstrip() if not raw.lstrip().startswith("statement") else raw
        if not line.strip():
            continue
        if number == 1:
            if line.strip() != "lf-contract 0.1":
                raise Malformed(f"{path}: not a contract 0.1")
            continue
        key, _, rest = line.strip().partition(" ")
        if key in SINGLE_LINES and key in contract:
            raise Malformed(f"{path}:{number}: a second {key} line")
        indented = line.startswith(" ")
        if indented and case is None:
            raise Malformed(f"{path}:{number}: indented line outside a case")
        if key in ("id", "word", "ir", "stack", "statement", "expect"):
            contract[key] = rest.strip()
        elif key == "inputs":
            contract["inputs"] = rest.split()
        elif key == "pre":
            contract["pre"].append(ExprParser(rest).parse())
        elif key == "case":
            case = {"guard": ExprParser(rest).parse(), "out": None, "ensure": [], "text": rest}
            contract["cases"].append(case)
        elif key == "out" and indented:
            case["out"] = rest.split()
        elif key == "ensure" and indented:
            case["ensure"].append((ExprParser(rest).parse(), rest.strip()))
        else:
            raise Malformed(f"{path}:{number}: unknown line {key}")
    for field in ("id", "word", "ir", "stack", "statement", "inputs"):
        if field not in contract:
            raise Malformed(f"{path}: no {field}")
    for name in contract["inputs"]:
        if not re.fullmatch(r"[a-z][a-z0-9_]*", name) or RESERVED.match(name):
            raise Malformed(f"{path}: input name {name} is not allowed")
    if len(set(contract["inputs"])) != len(contract["inputs"]):   # review M1: one would
        raise Malformed(f"{path}: an input named twice")         # shadow the other
    if not contract["cases"]:   # review M3: post would be True
        raise Malformed(f"{path}: no case: the contract would state nothing")
    for case in contract["cases"]:
        if case["out"] is None:
            raise Malformed(f"{path}: a case without out")
    unbound = contract_scope_problems(contract)
    if unbound:
        raise Malformed(f"{path}: reads names that are neither an input nor a result of "
                        f"their case: {', '.join(unbound)}")
    checked_text(path, "the contract's path")
    for field in ("id", "ir", "statement", "stack"):
        checked_text(contract[field], f"{path}: the {field} line")
    checked_text(contract["word"], f"{path}: the word line", quoted=True)
    return contract


# --------------------------------------------------- symbolic values and paths
# Values are tuples: ("lit", n), ("var", name), ("cmax",), ("cmin",),
# ("wrap", e) of ("add"|"sub"|"mul", a, b) or ("neg", a) or ("absraw", a),
# ("div"|"mod", a, b), ("max"|"min", a, b), ("flag", cond), ("bits", op, a, b),
# ("invert", a), ("rshift", a, n). Conditions: ("cmp", op, a, b), ("not", c),
# ("and", c, d), ("or", c, d), ("bool", b), ("bitsok", n).

def negate(cond):
    if cond[0] == "not":
        return cond[1]
    if cond[0] == "bool":
        return ("bool", not cond[1])
    return ("not", cond)


def truth(value):
    """The condition 'value is nonzero', or a constant."""
    if value[0] == "flag":
        return value[1]
    if value[0] == "lit":
        return ("bool", value[1] != 0)
    return ("cmp", "<>", value, ("lit", 0))


def flag_of(cond):
    if cond[0] == "bool":
        return ("lit", -1 if cond[1] else 0)
    return ("flag", cond)


def compare(op, a, b):
    if a[0] == "lit" and b[0] == "lit":
        return flag_of(("bool", evaluate_cond(("cmp", op, a, b), {})))
    return flag_of(("cmp", op, a, b))


class State:
    def __init__(self, conds, data, rets):
        self.conds, self.data, self.rets = conds, data, rets

    def but(self, conds=None, data=None, rets=None):
        return State(self.conds if conds is None else conds,
                     self.data if data is None else data,
                     self.rets if rets is None else rets)


ARITY = {"dup": 1, "drop": 1, "swap": 2, "over": 2, "nip": 2, "tuck": 2, "rot": 3, "2dup": 2,
         "2drop": 2, ">r": 1, "r>": 0, "r@": 0, "+": 2, "-": 2, "*": 2, "/": 2, "mod": 2,
         "negate": 1, "abs": 1, "1+": 1, "1-": 1, "=": 2, "<>": 2, "<": 2, ">": 2, "0=": 1,
         "0<>": 1, "0<": 1, "0>": 1, "and": 2, "or": 2, "xor": 2, "invert": 1, "rshift": 2,
         "max": 2, "min": 2, "true": 0, "false": 0}
CMP = {"=": "=", "<>": "<>", "<": "<", ">": ">"}
ZERO_CMP = {"0=": "=", "0<>": "<>", "0<": "<", "0>": ">"}


def apply_prim(name, args):
    """The values a total primitive leaves, from its inputs (deepest first)."""
    if name == "dup":
        return [args[0], args[0]]
    if name == "drop" or name == "2drop":
        return []
    if name == "swap":
        return [args[1], args[0]]
    if name == "over":
        return [args[0], args[1], args[0]]
    if name == "nip":
        return [args[1]]
    if name == "tuck":
        return [args[1], args[0], args[1]]
    if name == "rot":
        return [args[1], args[2], args[0]]
    if name == "2dup":
        return [args[0], args[1], args[0], args[1]]
    if name in ("+", "-", "*"):
        return [("wrap", ({"+": "add", "-": "sub", "*": "mul"}[name], args[0], args[1]))]
    if name == "negate":
        return [("wrap", ("neg", args[0]))]
    if name == "abs":
        return [("wrap", ("absraw", args[0]))]
    if name == "1+":
        return [("wrap", ("add", args[0], ("lit", 1)))]
    if name == "1-":
        return [("wrap", ("sub", args[0], ("lit", 1)))]
    if name in CMP:
        return [compare(CMP[name], args[0], args[1])]
    if name == "0=" and args[0][0] == "flag":
        return [flag_of(negate(args[0][1]))]
    if name in ZERO_CMP:
        return [compare(ZERO_CMP[name], args[0], ("lit", 0))]
    if name in ("and", "or") and all(a[0] == "flag" for a in args):
        return [("flag", (name, args[0][1], args[1][1]))]
    if name in ("and", "or", "xor"):
        return [("bits", name, args[0], args[1])]
    if name == "invert":
        return [("cmin",)] if args[0] == ("cmax",) else [("invert", args[0])]
    if name in ("max", "min"):
        return [(name, args[0], args[1])]
    if name == "true":
        return [("lit", -1)]
    if name == "false":
        return [("lit", 0)]
    raise AssertionError(name)


class Executor:
    """Symbolic execution of IR 0.1 without loops."""

    def __init__(self, defs, inputs, max_paths=None):
        self.defs = {name: (kind, body) for name, kind, body in defs}
        self.inputs = inputs
        self.depth = 0          # deepest call nesting seen
        self.facts = set()      # side facts the proofs need, such as (1 : Int) < c.bits
        self.max_paths = max_paths

    def bounded(self, paths):
        """paths, unless there are more than max_paths of them."""
        if self.max_paths is not None and len(paths) > self.max_paths:
            raise Limit("paths-limit", f"the word has more than {self.max_paths} paths "
                        "(the path limit)")
        return paths

    def prim(self, name, st):
        arity = ARITY[name]
        if name in ("r>", "r@"):
            if not st.rets:
                return [(st, ("fail", "underflow"))]
            top = st.rets[-1]
            rets = st.rets[:-1] if name == "r>" else st.rets
            return [(st.but(data=st.data + [top], rets=rets), "next")]
        if len(st.data) < arity:
            raise Unsupported("the word reads below its declared inputs")
        args, rest = st.data[len(st.data) - arity:], st.data[:len(st.data) - arity]
        if name == ">r":
            return [(st.but(data=rest, rets=st.rets + [args[0]]), "next")]
        if name in ("/", "mod"):
            return self.partial(st, rest, ("and", ("cmp", "<=", ("lit", 0), args[0]),
                                           ("cmp", "<", ("lit", 0), args[1])),
                                ("div" if name == "/" else "mod", args[0], args[1]))
        if name == "rshift":
            return self.shift(st, rest, args)
        return [(st.but(data=rest + apply_prim(name, args)), "next")]

    def partial(self, st, rest, cond, value):
        cond = simplify(cond)
        if cond == ("bool", True):
            return [(st.but(data=rest + [value]), "next")]
        if cond == ("bool", False):
            return [(st, ("fail", "unmodeled"))]
        return [(st.but(conds=st.conds + [cond], data=rest + [value]), "next"),
                (st.but(conds=st.conds + [negate(cond)]), ("fail", "unmodeled"))]

    def shift(self, st, rest, args):
        x, n = args
        if n[0] == "lit" and 0 <= n[1] <= 1:
            # Every cell has at least two bits (Cells.two_le), so the shift is defined.
            self.facts.add(n[1])
            value = ("cmax",) if (x, n) == (("lit", -1), ("lit", 1)) else ("rshift", x, n)
            return [(st.but(data=rest + [value]), "next")]
        cond = ("and", ("cmp", "<=", ("lit", 0), n), ("bitsok", n))
        return self.partial(st, rest, cond, ("rshift", x, n))

    def block(self, body, st, depth):
        if not body:
            return [(st, "next")]
        out = []
        for st2, outcome in self.instr(body[0], st, depth):
            out += self.block(body[1:], st2, depth) if outcome == "next" else [(st2, outcome)]
            self.bounded(out)
        return out

    def instr(self, instr, st, depth):
        kind = instr[0]
        if kind == "prim":
            return self.prim(instr[1], st)
        if kind == "lit":
            if instr[1] not in SMALL_LITERALS:
                raise Unsupported("a literal outside -1..1 may not fit every cell width")
            return [(st.but(data=st.data + [("lit", instr[1])]), "next")]
        if kind == "exit":
            return [(st, "exit")]
        if kind == "if":
            if not st.data:
                raise Unsupported("the word reads below its declared inputs")
            cond, rest = simplify(truth(st.data[-1])), st.data[:-1]
            out = []
            for branch, c in ((instr[1], cond), (instr[2], negate(cond))):
                if c == ("bool", False):
                    continue
                conds = st.conds if c == ("bool", True) else st.conds + [c]
                out += self.block(branch, st.but(conds=conds, data=rest), depth)
            return out
        if kind == "call":
            return self.call(instr[1], st, depth + 1)
        raise Unsupported("loops need invariants (IR version 1, task 4.4.1)")

    def call(self, name, st, depth):
        if depth > 16:
            raise Unsupported("recursion")
        self.depth = max(self.depth, depth)
        if name not in self.defs:
            return [(st, ("fail", "unknownWord"))]
        kind, body = self.defs[name]
        if kind == "word":
            out = []
            for st2, outcome in self.block(body, st.but(rets=[]), depth):
                if outcome in ("next", "exit"):
                    good = not st2.rets
                    out.append((st2.but(rets=st.rets), "next" if good else ("fail", "unbalanced")))
                else:
                    out.append((st2, outcome))
            return out
        out = []
        for st2, outcome in self.block(body, State(st.conds, [], []), depth):
            if outcome == "next" and len(st2.data) == 1 and not st2.rets:
                out.append((st.but(conds=st2.conds, data=st.data + st2.data), "next"))
            elif outcome == "next" or outcome == "exit":
                out.append((st2, ("fail", "badConstant")))
            else:
                out.append((st2, outcome))
        return out


def simplify(cond):
    if cond[0] == "not":
        inner = simplify(cond[1])
        return negate(inner)
    if cond[0] == "and":
        a, b = simplify(cond[1]), simplify(cond[2])
        if ("bool", False) in (a, b):
            return ("bool", False)
        if a == ("bool", True):
            return b
        if b == ("bool", True):
            return a
        return ("and", a, b)
    if cond[0] == "cmp" and cond[2][0] == "lit" and cond[3][0] == "lit":
        return ("bool", evaluate_cond(cond, {}))
    return cond


# ------------------------------------------------------- concrete evaluation

def wrap(x):
    return (x - CMIN) % (1 << CELL_BITS) + CMIN


def unsigned(x):
    return x + (1 << CELL_BITS) if x < 0 else x


def signed(u):
    return u - (1 << CELL_BITS) if u > CMAX else u


def evaluate(expr, env):
    kind = expr[0]
    if kind == "lit":
        return expr[1]
    if kind == "var":
        return env[expr[1]]
    if kind == "cmax":
        return CMAX
    if kind == "cmin":
        return CMIN
    if kind == "bool":
        return expr[1]
    if kind == "wrap":
        return wrap(evaluate(expr[1], env))
    if kind in ("add", "sub", "mul"):
        a, b = evaluate(expr[1], env), evaluate(expr[2], env)
        return a + b if kind == "add" else a - b if kind == "sub" else a * b
    if kind == "neg":
        return -evaluate(expr[1], env)
    if kind == "absraw":
        return abs(evaluate(expr[1], env))
    if kind == "div":
        return evaluate(expr[1], env) // evaluate(expr[2], env)
    if kind == "mod":
        return evaluate(expr[1], env) % evaluate(expr[2], env)
    if kind in ("max", "min"):
        a, b = evaluate(expr[1], env), evaluate(expr[2], env)
        return (b if a < b else a) if kind == "max" else (a if a < b else b)
    if kind == "flag":
        return -1 if evaluate_cond(expr[1], env) else 0
    if kind == "bits":
        a, b = unsigned(evaluate(expr[2], env)), unsigned(evaluate(expr[3], env))
        return signed({"and": a & b, "or": a | b, "xor": a ^ b}[expr[1]])
    if kind == "invert":
        return -evaluate(expr[1], env) - 1
    if kind == "rshift":
        return signed(unsigned(evaluate(expr[1], env)) >> evaluate(expr[2], env))
    if kind == "fn":
        return evaluate_fn(expr, env)
    return evaluate_cond(expr, env)


def evaluate_fn(expr, env):
    name = expr[1]
    if name == "flag":
        return -1 if evaluate_cond(expr[2], env) else 0
    args = [evaluate(a, env) for a in expr[2:]]
    if name == "min":
        return min(args)
    if name == "max":
        return max(args)
    if name == "abs":
        return abs(args[0])
    return CMIN <= args[0] <= CMAX


def evaluate_cond(cond, env):
    kind = cond[0]
    if kind == "bool":
        return cond[1]
    if kind == "not":
        return not evaluate_cond(cond[1], env)
    if kind == "and":
        return evaluate_cond(cond[1], env) and evaluate_cond(cond[2], env)
    if kind == "or":
        return evaluate_cond(cond[1], env) or evaluate_cond(cond[2], env)
    if kind == "implies":
        return (not evaluate_cond(cond[1], env)) or evaluate_cond(cond[2], env)
    if kind == "bitsok":
        return evaluate(cond[1], env) < CELL_BITS
    if kind == "cmp":
        a, b = evaluate(cond[2], env), evaluate(cond[3], env)
        return {"=": a == b, "<>": a != b, "<": a < b, "<=": a <= b, ">": a > b,
                ">=": a >= b}[cond[1]]
    if kind == "fn":
        return bool(evaluate_fn(cond, env))
    raise AssertionError(kind)


# ------------------------------------------------------------ printing (Lean)

LEAN_OPS = {"=": "=", "<>": "≠", "<": "<", "<=": "≤", ">": ">", ">=": "≥"}


def lean(expr):
    kind = expr[0]
    if kind == "lit":
        return lean_int(expr[1])
    if kind == "var":
        return expr[1]
    if kind == "cmax":
        return "c.max"
    if kind == "cmin":
        return "c.min"
    if kind == "bool":
        return "True" if expr[1] else "False"
    if kind == "wrap":
        return f"c.wrap {paren(expr[1])}"
    if kind in ("add", "sub", "mul"):
        op = {"add": "+", "sub": "-", "mul": "*"}[kind]
        return f"{paren(expr[1])} {op} {paren(expr[2])}"
    if kind == "neg":
        return f"-{paren(expr[1])}"
    if kind == "absraw":
        a = paren(expr[1])
        return f"if {a} < 0 then -{a} else {a}"
    if kind in ("div", "mod"):
        return f"{paren(expr[1])} {'/' if kind == 'div' else '%'} {paren(expr[2])}"
    if kind in ("max", "min"):
        return f"{kind} {paren(expr[1])} {paren(expr[2])}"
    if kind == "flag":
        return f"flag (decide ({lean(expr[1])}))"
    if kind == "bits":
        op = {"and": "&&&", "or": "|||", "xor": "^^^"}[expr[1]]
        return f"bitwise c (· {op} ·) {paren(expr[2])} {paren(expr[3])}"
    if kind == "invert":
        return f"-{paren(expr[1])} - 1"
    if kind == "rshift":
        return f"c.signed (c.unsigned {paren(expr[1])} >>> ({lean(expr[2])}).toNat)"
    if kind == "bitsok":
        return f"{paren(expr[1])} < (c.bits : Int)"
    if kind == "cmp":
        return f"{paren(expr[2])} {LEAN_OPS[expr[1]]} {paren(expr[3])}"
    if kind == "not":
        return f"¬{paren(expr[1])}"
    if kind in ("and", "or", "implies"):
        op = {"and": "∧", "or": "∨", "implies": "→"}[kind]
        return f"{paren(expr[1])} {op} {paren(expr[2])}"
    if kind == "fn":
        name, args = expr[1], expr[2:]
        if name in ("min", "max"):
            return f"{name} {paren(args[0])} {paren(args[1])}"
        if name == "abs":
            a = paren(args[0])
            return f"if {a} < 0 then -{a} else {a}"
        if name == "flag":
            return f"flag (decide ({lean(args[0])}))"
        return f"c.Fits {paren(args[0])}"
    raise AssertionError(kind)


def paren(expr):
    """An expression as an argument: atoms bare, everything else in parentheses."""
    if expr[0] in ("lit", "var", "cmax", "cmin", "bool"):
        return lean(expr)
    return f"({lean(expr)})"


# ------------------------------------------------------------ printing (text)

TEXT_OPS = {"=": "=", "<>": "≠", "<": "<", "<=": "≤", ">": ">", ">=": "≥"}
FLIPPED = {"=": "<>", "<>": "=", "<": ">=", ">=": "<", ">": "<=", "<=": ">"}


def describe_stack(data):
    """A path's output in words, bottom first; the flags TRUE and FALSE named."""
    names = {("lit", -1): "true", ("lit", 0): "false"}
    return ", ".join(names.get(v, text(v)) for v in data) or "nothing"


def text(expr):
    kind = expr[0]
    if kind == "lit":
        return str(expr[1])
    if kind == "var":
        return expr[1]
    if kind in ("cmax", "cmin"):
        return "cell max" if kind == "cmax" else "cell min"
    if kind == "bool":
        return "true" if expr[1] else "false"
    if kind == "wrap":
        return f"wrap({text(expr[1])})"
    if kind in ("add", "sub", "mul"):
        op = {"add": "+", "sub": "-", "mul": "·"}[kind]
        return f"{tparen(expr[1])} {op} {tparen(expr[2])}"
    if kind == "neg":
        return f"-{tparen(expr[1])}"
    if kind == "absraw":
        return f"|{text(expr[1])}|"
    if kind in ("div", "mod"):
        return f"{tparen(expr[1])} {'/' if kind == 'div' else 'mod'} {tparen(expr[2])}"
    if kind in ("max", "min"):
        return f"{kind}({text(expr[1])}, {text(expr[2])})"
    if kind == "flag":
        return f"flag({text(expr[1])})"
    if kind == "bits":
        return f"{tparen(expr[2])} {expr[1]} {tparen(expr[3])}"
    if kind == "invert":
        return f"invert({text(expr[1])})"
    if kind == "rshift":
        return f"{tparen(expr[1])} >> {tparen(expr[2])}"
    if kind == "bitsok":
        return f"{tparen(expr[1])} < cell bits"
    if kind == "cmp":
        return f"{tparen(expr[2])} {TEXT_OPS[expr[1]]} {tparen(expr[3])}"
    if kind == "not" and expr[1][0] == "cmp":
        return text(("cmp", FLIPPED[expr[1][1]], expr[1][2], expr[1][3]))
    if kind == "not":
        return f"not {tparen(expr[1])}"
    if kind in ("and", "or", "implies"):
        op = {"and": "and", "or": "or", "implies": "→"}[kind]
        return f"{tparen(expr[1])} {op} {tparen(expr[2])}"
    if kind == "fn":
        args = ", ".join(text(a) for a in expr[2:])
        return f"{expr[1]}({args})" if expr[1] != "abs" else f"|{args}|"
    raise AssertionError(kind)


def tparen(expr):
    simple = expr[0] in ("lit", "var", "cmax", "cmin", "bool", "max", "min", "flag", "fn",
                         "wrap", "invert", "absraw")
    return text(expr) if simple and not (expr[0] == "lit" and expr[1] < 0) else f"({text(expr)})"


# ------------------------------------------------------------ the obligations

def camel(identifier):
    return "".join(p[:1].upper() + p[1:] for p in re.split(r"[^A-Za-z0-9]+", identifier) if p)


def out_item(token, inputs):
    if token == "true":
        return ("lit", -1)
    if token == "false":
        return ("lit", 0)
    if re.fullmatch(r"-?[0-9]+", token):
        return ("lit", int(token))
    if token in inputs:
        return ("var", token)
    if re.fullmatch(r"[a-z][a-z0-9_]*", token):
        return ("unknown", token)
    raise Malformed(f"bad output item {token}")


def lean_post(contract):
    """The `post` predicate: each case's guard implies its output shape."""
    inputs = contract["inputs"]
    parts = []
    for case in contract["cases"]:
        items = [out_item(t, inputs) for t in case["out"]]
        unknowns = [t[1] for t in items if t[0] == "unknown"]
        shape = "[" + ", ".join(t[1] if t[0] == "unknown" else lean(t) for t in reversed(items)) + "]"
        body = " ∧ ".join([f"out = {shape}"] + [f"({lean(e)})" for e, _ in case["ensure"]])
        for name in reversed(unknowns):
            body = f"∃ {name} : Int, {body}"
        parts.append(f"({lean(case['guard'])} → {body})")
    return " ∧\n    ".join(parts) if parts else "True"


def check_case(case, inputs, values, env):
    """Whether concrete output values satisfy one case (assumed: guard holds)."""
    items = [out_item(t, inputs) for t in case["out"]]
    if len(items) != len(values):
        return False
    bound = dict(env)
    for item, value in zip(items, values):
        if item[0] == "unknown":
            if item[1] in bound and bound[item[1]] != value:
                return False
            bound[item[1]] = value
        elif evaluate(item, env) != value:
            return False
    return all(evaluate_cond(e, bound) for e, _ in case["ensure"])


def post_holds(contract, env, values):
    return all(not evaluate_cond(case["guard"], env)
               or check_case(case, contract["inputs"], values, env)
               for case in contract["cases"])


CANDIDATES = [-3, -2, -1, 0, 1, 2, 3, 10, CMIN, CMIN + 1, CMAX - 1, CMAX]


def candidates(count):
    return itertools.product(CANDIDATES, repeat=count)


def counterexample(contract, paths, max_cases=None, notes=None):
    """The first candidate inputs that break the contract, with the reason, or
    None; a Limit when the search would try more than max_cases of them. When it
    finds none, it adds to notes (a list) what makes the search say little: no
    candidate meets the preconditions, or candidates that no case covers (the
    contract then says nothing about them)."""
    inputs = contract["inputs"]
    cases = len(CANDIDATES) ** len(inputs)
    if max_cases is not None and cases > max_cases:
        raise Limit("search-limit", f"the counterexample search would try {cases:,} input "
                    f"combinations ({len(CANDIDATES)} values for each of {len(inputs)} inputs), "
                    f"more than the search limit {max_cases:,}")
    met, uncovered = 0, []
    for combo in candidates(len(inputs)):
        env = dict(zip(inputs, combo))
        if not all(evaluate_cond(p, env) for p in contract["pre"]):
            continue
        met += 1
        if not any(evaluate_cond(case["guard"], env) for case in contract["cases"]):
            uncovered.append(combo)
        taken = [(st, oc) for st, oc in paths if all(evaluate_cond(c, env) for c in st.conds)]
        if len(taken) != 1:
            raise AssertionError(f"{len(taken)} paths taken for {combo}")
        st, outcome = taken[0]
        if outcome != "next":
            return combo, f"the IR fails ({outcome[1]})"
        values = [evaluate(v, env) for v in st.data]
        if not post_holds(contract, env, values):
            return combo, "the postcondition fails"
    if notes is not None and not met:
        notes.append(f"no candidate meets pre: none of the {cases:,} candidate inputs meets the "
                     "preconditions, so the search tried nothing")
    if notes is not None and uncovered:
        example = ", ".join(f"{x} = {v}" for x, v in zip(inputs, uncovered[0]))
        notes.append(f"inputs no case covers: {len(uncovered):,} of the {met:,} candidates that "
                     f"meet pre, for example {example}; the contract says nothing about them")
    return None


def matches(case, inputs, stack):
    """The number of a case's unknowns if a path's output has the case's shape
    item for item (unknowns match anything; other items must be written the
    same), else None: then the case's guard must contradict the path."""
    items = [out_item(t, inputs) for t in case["out"]]
    if len(items) != len(stack):
        return None
    bound = {}
    for item, value in zip(items, stack):
        if item[0] == "unknown":
            if bound.setdefault(item[1], lean(value)) != lean(value):
                return None
        elif lean(item) != lean(value):
            return None
    return len(bound)


def wraps(expr, found):
    """Every c.wrap term inside expr, innermost first."""
    if isinstance(expr, tuple):
        for part in expr[1:]:
            wraps(part, found)
        if expr[0] == "wrap" and expr not in found:
            found.append(expr)
    return found


# Closing an obligation: unfold cells and flags, drop the list equation a
# witness made trivial, and leave the arithmetic to omega.
CLOSE = ("try simp only [Cells.Fits, flag, decide_eq_true_eq, List.cons.injEq, and_true, "
         "true_and] at *\n    all_goals omega")


class Generator:
    def __init__(self, contract, defs, source, limits=(None, None)):
        self.contract, self.defs, self.source = contract, defs, source
        self.name = camel(contract["id"])
        self.inputs = contract["inputs"]
        self.max_paths, self.max_cases = limits

    def binders(self):
        return " ".join(self.inputs)

    def hyps(self):
        fits = [f"(f{i} : c.Fits {x})" for i, x in enumerate(self.inputs, 1)]
        pre = [f"(pre{i} : {lean(p)})" for i, p in enumerate(self.contract["pre"], 1)]
        return fits + pre

    def hyp_names(self):
        return [f"f{i}" for i in range(1, len(self.inputs) + 1)] + \
            [f"pre{i}" for i in range(1, len(self.contract["pre"]) + 1)]

    def run(self):
        executor = Executor(self.defs, self.inputs, self.max_paths)
        if self.contract["word"] not in executor.defs:
            raise Malformed(f"no word {self.contract['word']} in the IR")
        start = State([], [("var", x) for x in self.inputs], [])
        paths = executor.bounded(executor.call(self.contract["word"], start, 1))
        self.paths, self.fuel, self.facts = paths, executor.depth, sorted(executor.facts)
        self.notes = []
        self.refutation = counterexample(self.contract, paths, self.max_cases, self.notes)
        return self

    def stack_of(self, st):
        """A path's output, top first as the model's lists are."""
        return list(reversed(st.data))

    def output_on(self, combo):
        """What the word does on 64-bit cells with these inputs: the values it
        leaves (bottom first), or the reason its path fails, as text."""
        env = dict(zip(self.inputs, combo))
        for st, outcome in self.paths:
            if all(evaluate_cond(c, env) for c in st.conds):
                if outcome != "next":
                    return f"the IR fails ({outcome[1]})"
                values = [evaluate(v, env) for v in st.data]
                names = {-1: "true", 0: "false"}
                shown = ", ".join(f"{v} ({names[v]})" if v in names else str(v) for v in values)
                return f"the word leaves {shown or 'nothing'} (bottom first)"
        raise AssertionError(f"no path taken for {combo}")

    def obligation_statement(self, k, st, outcome):
        conds = [f"(p{j} : {lean(c)})" for j, c in enumerate(st.conds, 1)]
        head = f"theorem O{k} (c : Cells) ({self.binders()} : Int)"
        goal = "False" if outcome != "next" else \
            f"post c {self.binders()} [{', '.join(lean(v) for v in self.stack_of(st))}]"
        return head, self.hyps() + conds, goal

    def obligation_proof(self, st, outcome):
        lines = ["  have := c.min_eq", "  have := c.max_pos", "  have := c.two_le"]
        for w in wraps(tuple(["path"] + st.conds + st.data), []):
            lines.append(f"  try rw [c.wrap_of_fits (x := {lean(w[1])}) "
                         "(by simp only [Cells.Fits] at *; omega)] at *")
        if outcome != "next":
            return lines + [f"  {CLOSE}"]
        lines.append("  simp only [post]")
        cases = self.contract["cases"]
        if len(cases) > 1:
            lines.append("  refine ⟨" + ", ".join("?_" for _ in cases) + "⟩")
        for case in cases:
            lines.append("  · intro g")
            unknowns = matches(case, self.inputs, st.data)
            if unknowns is None:
                lines.append("    exfalso")
            elif case["ensure"]:
                lines.append("    refine ⟨" + "_, " * unknowns + "rfl, ?_⟩" if unknowns
                             else "    refine ⟨rfl, ?_⟩")
            else:
                lines.append("    exact ⟨" + "_, " * unknowns + "rfl⟩" if unknowns
                             else "    first | rfl | trivial")
                continue
            lines.append(f"    {CLOSE}")
        return lines

    def tree(self, paths, depth=0):
        """The proof of `contract`: split on the paths' conditions in order."""
        if len(paths) == 1 and len(paths[0][1].conds) == depth:
            return self.leaf(*paths[0])
        cond = paths[0][1].conds[depth]
        yes = [p for p in paths if p[1].conds[depth] == cond]
        no = [p for p in paths if p[1].conds[depth] != cond]
        if len(yes) + len(no) != len(paths) or not no:
            raise AssertionError("paths do not form a tree")
        h = f"h{depth + 1}"
        out = [f"by_cases {h} : {lean(cond)}"]
        out += ["· " + line if i == 0 else "  " + line
                for i, line in enumerate(self.tree(yes, depth + 1))]
        out += ["· " + line if i == 0 else "  " + line
                for i, line in enumerate(self.tree(no, depth + 1))]
        return out

    def leaf(self, k, st, outcome):
        args = " ".join(["c", self.binders()] + self.hyp_names() +
                        [f"h{j}" for j in range(1, len(st.conds) + 1)])
        if outcome != "next":
            return [f"exact (O{k} {args}).elim"]
        stack = ", ".join(lean(v) for v in self.stack_of(st))
        return [f"refine ⟨[{stack}], ?_, O{k} {args}⟩", "vc_run program"]

    def input_stack(self):
        return " :: ".join(list(reversed(self.inputs)) + ["tail"])

    def contract_statement(self):
        hyps = "\n    ".join(self.hyps())
        return (f"(c : Cells) (fuel : Nat) ({self.binders()} : Int) (tail rs : List Int)\n"
                f"    {hyps} :\n"
                f"    ∃ out, callWord c program (fuel + {self.fuel}) \"{self.contract['word']}\"\n"
                f"      ⟨{self.input_stack()}, rs⟩ = .next ⟨out ++ tail, rs⟩ ∧\n"
                f"      post c {self.binders()} out")

    def refuted_lines(self):
        combo, reason = self.refutation
        hyps = " → ".join([f"c.Fits {x}" for x in self.inputs] +
                          [lean(p) for p in self.contract["pre"]])
        args = " ".join(lean_int(v) for v in combo)
        proofs = " ".join(["(by vc_fits)"] * len(self.inputs) +
                          ["(by decide)"] * len(self.contract["pre"]))
        return [
            f"/-- The contract is false: on 64-bit cells, with {', '.join(f'{x} = {v}' for x, v in zip(self.inputs, combo))},",
            f"{reason}. -/",
            "theorem refuted : ¬ ∀ (c : Cells) (fuel : Nat) "
            f"({self.binders()} : Int) (tail rs : List Int),",
            f"    {hyps} →",
            f"    ∃ out, callWord c program (fuel + {self.fuel}) \"{self.contract['word']}\"",
            f"      ⟨{self.input_stack()}, rs⟩ = .next ⟨out ++ tail, rs⟩ ∧",
            f"      post c {self.binders()} out := by",
            "  intro h",
            f"  obtain ⟨out, hrun, hpost⟩ := h cells64 0 {args} [] [] {proofs}",
            "  vc_eval program at hrun",
            "  first",
            "  | (subst hrun; simp only [post] at hpost; simp at hpost; try omega)",
            "  | skip",
        ]

    def lean_section(self):
        out = [f"/-! Contract {self.contract['id']} for `{self.contract['word']}`, from "
               f"{self.contract['path']}. -/", f"namespace {self.name}", ""]
        defs = ",\n  ".join(f'("{n}", .{k} {lean_block(b)})' for n, k, b in self.defs)
        out += [f"def program : Program := [\n  {defs}]", "",
                "-- The program printed back in the IR text form, for comparison with the IR.",
                f'#eval IO.print ("vc-program {self.name}\\n" ++ render "{self.source}" program ++ '
                '"vc-program-end\\n")', ""]
        out += ["/-- The postcondition: each case's guard implies its output and its ensures "
                "(the contract's statement is not copied here). -/",
                f"def post (c : Cells) ({self.binders()} : Int) (out : List Int) : Prop :=",
                f"  {lean_post(self.contract)}", ""]
        if self.refutation:
            out += self.refuted_lines()
            names = ["refuted"]
        else:
            names = []
            for k, (st, outcome) in enumerate(self.paths, 1):
                head, hyps, goal = self.obligation_statement(k, st, outcome)
                out.append(head)
                out += [f"    {h}" for h in hyps]
                out.append(f"    : {goal} := by")
                out += self.obligation_proof(st, outcome)
                out.append("")
                names.append(f"O{k}")
            numbered = [(k, st, oc) for k, (st, oc) in enumerate(self.paths, 1)]
            out += ["/-- The contract, on the IR semantics: for every cell width, input "
                    "and stack below. -/",
                    f"theorem contract {self.contract_statement()} := by"]
            out += ["  " + line for line in self.tree(numbered)]
            names.append("contract")
        out += [""] + [f"#print axioms {name}" for name in names]
        out += ["", f"end {self.name}", ""]
        self.theorems = [f"ProgramVC.{self.name}.{n}" for n in names]
        return out

    def summary(self):
        entry = {"id": self.contract["id"], "word": self.contract["word"],
                 "contract": self.contract["path"], "ir": self.contract["ir"],
                 "stackEffect": self.contract["stack"], "statement": self.contract["statement"],
                 "namespace": f"ProgramVC.{self.name}", "fuel": self.fuel,
                 "theorems": self.theorems}
        if self.notes:
            entry["searchNotes"] = self.notes
        if self.refutation:
            combo, reason = self.refutation
            entry["status"] = "refuted"
            entry["counterexample"] = {"inputs": dict(zip(self.inputs, combo)), "reason": reason}
            entry["obligations"] = []
            return entry
        entry["status"] = "discharged"
        entry["obligations"] = []
        for k, (st, outcome) in enumerate(self.paths, 1):
            path = " and ".join(text(c) for c in st.conds) or "always"
            if outcome != "next":
                claim = f"this path, which ends in {outcome[1]}, cannot be taken"
            else:
                claim = (f"the word leaves {describe_stack(st.data)} (bottom first), "
                         "and the postcondition holds")
            entry["obligations"].append({"id": f"O{k}", "path": path, "statement": claim,
                                         "theorem": f"ProgramVC.{self.name}.O{k}"})
        return entry


HEADER = """import Lean

/-
Verification conditions for program IR words, GENERATED by
scripts/program_vc.py (generator {version}) from:
{sources}
Do not edit: regenerate (make test checks that this file is what the
generator writes). Untrusted generator, checked by Lean: every obligation
and every `contract` theorem below is proved by Lean 4.35.0, and the
`contract` theorems are stated against the IR semantics itself, so a wrong
generator can only make this file fail to check. Checked by the Lean
reference, not by LeanForth.

Part 1 copies the IR semantics verbatim from {model} (checked by
tests/program/vc_check.py). Part 2 holds, per contract, the program, the
postcondition `post`, one obligation per path (`O1`, `O2`, ...), and the
contract theorem, or for a contract the generator found false, a theorem
`refuted` that proves it false on concrete inputs.
-/

namespace ProgramIR

-- Part 1. The IR semantics, copied.

-- BEGIN VERBATIM {model} {first}-{last}
"""

COMMON = """-- END VERBATIM

end ProgramIR

-- Part 2. The contracts.

-- Proofs are generated; their binders and simp sets are uniform, not minimal.
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
-- A name the generator did not bind is an error, never an implicit argument (review M2).
set_option autoImplicit false

namespace ProgramVC
open ProgramIR

theorem ir_max (a b : Int) : (if a < b then b else a) = max a b := by omega
theorem ir_min (a b : Int) : (if a < b then a else b) = min a b := by omega
theorem ir_cell_min (c : Cells) : -c.max - 1 = c.min := c.min_eq.symm
theorem ir_shift_one (c : Cells) : (1 : Int) < (c.bits : Int) := by have := c.two_le; omega
theorem ir_not_lt (a b : Int) : (!decide (a < b)) = decide (b ≤ a) := by
  by_cases h : a < b <;> simp [h] <;> omega

/-- The development host's cells, for counterexamples. -/
def cells64 : Cells := ⟨64, by decide⟩

/-- Run IR code on a path: unfold `callWord`, `run` and `step`, decide each
IF by the path's hypotheses, and name the IR's MAX, MIN and constants. -/
macro "vc_run" p:ident : tactic => `(tactic| (simp [callWord, run_call, run_prim, run_lit, run_exit,
  run_if, run_nil, step, lookup, $p:ident, flag_ne_zero, flag_beq_zero, and_flags, or_flags,
  decide_eq_true_eq, ir_max, ir_min, ir_cell_min, ir_shift_one, ir_not_lt,
  Cells.rshift_neg_one, Cells.fits_zero, Cells.fits_one, Cells.fits_neg_one, *]))

/-- Run IR code on concrete inputs on 64-bit cells. -/
macro "vc_eval" p:ident "at" h:ident : tactic => `(tactic| (simp [callWord, run_call, run_prim,
  run_lit, run_exit, run_if, run_nil, step, lookup, $p:ident, flag, bitwise, cells64,
  Cells.wrap, Cells.min, Cells.max, Cells.half, Cells.modulus, Cells.unsigned,
  Cells.signed, Cells.fits_zero, Cells.fits_one, Cells.fits_neg_one] at $h:ident))

/-- A concrete value fits in a 64-bit cell. -/
macro "vc_fits" : tactic => `(tactic| (simp [Cells.Fits, cells64, Cells.min, Cells.max,
  Cells.half]))

"""


def generate(contract_paths):
    """The Lean file and the summary for the contracts at these paths, each
    with the IR file its `ir` line names."""
    items = []
    for path in contract_paths:
        contract = parse_contract(read_contract(path), path)
        items.append((contract, Path(contract["ir"]).read_text(encoding="utf-8")))
    text, summary, _ = generate_parsed(items)
    return text, summary


def generate_parsed(items, limits=(None, None)):
    """The Lean file, the summary and the generators (None for an unsupported
    contract) for (parsed contract, IR text) pairs; limits are the path and
    counterexample-search limits (Limit when one is reached), None for none.
    scripts/program_verify.py passes the IR text the program words wrote and
    the contract text it read, so nothing is read twice."""
    model_lines = Path(MODEL).read_text(encoding="utf-8").splitlines()
    (first, last), printer = model_ranges(model_lines)
    sections, summary, sources, generators = [], [], [], []
    for contract, ir_text in items:
        path = contract["path"]
        checked_text(ir_source(ir_text), f"{contract['ir']}: the source path", quoted=True)
        sources.append(f"  {path} with {contract['ir']} (sha256 "
                       f"{hashlib.sha256(ir_text.encode()).hexdigest()[:16]}...)")
        defs = parse_ir(ir_text)
        try:
            gen = Generator(contract, defs, ir_source(ir_text), limits).run()
        except Unsupported as reason:
            summary.append({"id": contract["id"], "word": contract["word"], "contract": path,
                            "ir": contract["ir"], "status": "unsupported",
                            "reason": str(reason), "obligations": [], "theorems": []})
            generators.append(None)
            continue
        sections += gen.lean_section()
        summary.append(gen.summary())
        generators.append(gen)
    text = HEADER.format(version=GENERATOR_VERSION, sources="\n".join(sources), model=MODEL,
                         first=first, last=last)
    text += "\n".join(model_lines[first - 1:last]) + "\n-- END VERBATIM\n\n"
    text += "-- The IR text printer, copied.\n\n"
    text += f"-- BEGIN VERBATIM {MODEL} {printer[0]}-{printer[1]}\n"
    text += "\n".join(model_lines[printer[0] - 1:printer[1]]) + "\n" + COMMON
    text += "\n".join(sections) + "end ProgramVC\n"
    return text, summary, generators


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("contracts", nargs="+")
    parser.add_argument("--out", required=True)
    parser.add_argument("--summary", required=True)
    args = parser.parse_args()
    try:
        text, summary = generate(args.contracts)
    except Malformed as problem:
        print(f"program_vc: {problem}", file=sys.stderr)
        return 1
    Path(args.out).write_text(text, encoding="utf-8")
    Path(args.summary).write_text(json.dumps({"generator": GENERATOR_VERSION,
                                              "contracts": summary}, indent=2,
                                             ensure_ascii=False) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    sys.exit(main())
