"""Round trip and random programs for the program words (ADR 0019, MiniForth
review recommendation 2).

Usage (from the repository root):
  GFORTH=... python3 tests/program/verify_roundtrip.py [--seed N] [--programs N]

Round trip: each IR file (the four golden files, IR 0.2's included, and
AWKWARD below) is printed back as Forth source, in another layout (calls
and keywords in upper or mixed case, tabs, comments, several instructions
to a line; a version's IR name, show'1, as a name of its own, which gives
the same IR), run in correctness mode by both designs, and must give the
same IR apart from the locations and the source line. AWKWARD uses names
that Gforth 1.0 reads in other syntaxes (->x, "x", forth:dup), names with
odd characters, a name of 31 characters, and Gforth words that Forth-2012
does not define (rdrop, g). Then Forth source that no accepted IR can come
from must be refused: names of vocabulary or Core words (-rot and .s
included), names that read as numbers, a forward call, recursion, a name
the IR gives another version, and output words outside a definition or S"
without TYPE.

Random programs: --programs (default 400) programs from --seed (default
20261103), each with words and constants built from every primitive,
literals (also with leading zeros and of ten digits), calls, IF/ELSE/THEN,
BEGIN/WHILE/REPEAT nested up to three deep, EXIT, comments and random case
and spacing; a fifth of them carry one planted mistake (an unknown word, a
bad literal, a structure out of place, a name too long, a redefinition, a
character outside ASCII ...; a redefinition and the literals $10, 'a' and
2147483648, which IR 0.2 accepts). The mode shift and the separate
vocabulary must write the same lines and give the same verdict on every
one, and today's reader too but for the differences verify_check.py's rules
explain. Finite tests on the Gforth that GFORTH names, not a proof.
"""
import argparse
import os
from pathlib import Path
import random
import re
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tests" / "program"))
import verify_check  # noqa: E402

PRIMS = ("dup drop swap over nip tuck rot 2dup 2drop >r r> r@ + - * / mod negate abs 1+ "
         "1- = <> < > 0= 0<> 0< 0> and or xor invert rshift max min true false").split()
GOLDEN = ["tests/program/ir/clamp.ir", "tests/program/ir/examples.ir",
          "tests/program/ir/all-primitives.ir", "tests/program/ir/ir-0.2.ir",
          "tests/program/ir/sha-words.ir"]
AWKWARD = """lf-ir 0.1
source awkward.fs
constant k7
  lit 7
end
constant ->x
  call k7
  prim negate
end
word "x"
  call k7
  lit 5
  prim +
end
word forth:dup
  call "x"
  if
    call ->x
  else
    lit -2147483647
  then
end
word x:dup
  begin
    prim dup
    lit 0
    prim >
  while
    prim 1-
  repeat
end
word rdrop
  call x:dup
  exit
end
word g
  call rdrop
  call forth:dup
end
word a(b)
  call g
  if
  else
  then
end
word x\\y
  call a(b)
  lit 2147483647
  lit -5
end
word abcdefghijklmnopqrstuvwxyz01234
  call x\\y
end
"""
LOCATION = re.compile(r" @\d+:\d+$")


def mixed(word, rng):
    return "".join(c.upper() if rng.random() < 0.5 else c for c in word)


def to_forth(ir_text, rng):
    """IR text printed back as Forth source in another layout."""
    out, line, kept, pending = [], [], [], None
    for raw in ir_text.splitlines()[2:]:
        text = LOCATION.sub("", raw).strip()
        op, _, arg = text.partition(" ")
        if op == "word":
            if line:
                out.append(" ".join(line))
            line = [":", mixed(arg, rng)]
        elif op == "constant":
            pending = arg
        elif op == "end" and pending is not None:
            out.append("\t".join(kept + ["CONSTANT", mixed(pending, rng)]) + "  \\ constant")
            pending, kept = None, []
        else:
            token = {"prim": arg, "lit": arg, "call": arg, "out": arg}.get(op, op)
            text = op == "out" and arg.startswith('."')
            token = ";" if op == "end" else token if text else mixed(token, rng)
            if op == "lit" and rng.random() < 0.3 and len(token.lstrip("-")) <= 8:
                token = token.replace("-", "-00", 1) if token.startswith("-") else "00" + token
            if pending is not None:
                kept.append(token)
                continue
            line.append(token)
            if rng.random() < 0.15:
                line.append("( note )")
            if op == "end" or rng.random() < 0.3:
                out.append(("\t" if rng.random() < 0.5 else " ").join(line))
                line = []
    if line:
        out.append(" ".join(line))
    return "\n".join(out) + "\n"


def stripped(lines):
    return [LOCATION.sub("", x) for x in lines if not x.startswith("source ")]


REFUSED = [": dup 1 ;", ": DUP 1 ;", ": emit ;", ": 5 7 ;", ": -0 1 ;", ": 1e 1 ;",
           ": $10 1 ;", ": 'a' 1 ;", ": .5 1 ;", "5 constant -1", ": f g ;\n: g 1 ;",
           ": f f ;", ": foo 1 ;\n: FOO'1 2 ;\n: Foo 3 ;", ": -rot 1 ;", ": .s ;",
           ": f 1 . ;\n.", ': f s" x" ;']


def round_trip(gforth):
    rng = random.Random(7)
    entries, wanted = [], []
    for path in GOLDEN:
        wanted.append((path, Path(ROOT / path).read_text(encoding="utf-8")))
    wanted.append(("awkward", AWKWARD))
    for name, ir in wanted:
        entries.append(("texts", to_forth(ir, rng).encode()))
    for text in REFUSED:
        entries.append(("texts", text.encode()))
    with tempfile.TemporaryDirectory() as directory:
        results = verify_check.run_driver(gforth, entries, directory)
    problems = []
    for n, (name, ir) in enumerate(wanted):
        for who in ("NEW", "ALIAS"):
            lines, verdict = results[n][who]
            if verdict[0] != 0 or stripped(lines) != stripped(ir.splitlines()):
                problems.append(f"round trip {name} ({who}): {verdict}\n" +
                                "\n".join(lines[-3:]))
    for n, text in enumerate(REFUSED, len(wanted)):
        for who in ("NEW", "ALIAS"):
            if results[n][who][1][0] == 0:
                problems.append(f"accepted ({who}): {text!r}")
        if results[n]["NEW"] != results[n]["ALIAS"]:
            problems.append(f"the designs differ on {text!r}")
    return problems, len(wanted), len(REFUSED)


# ---------------------------------------------------------- random programs

class Program:
    """A random program printed as Forth, built so that it is accepted unless
    a mistake is planted."""

    def __init__(self, rng):
        self.rng, self.words, self.constants, self.lines = rng, [], [], []

    def name(self):
        stem = self.rng.choice(["w", "lf-x", "q?", "a-b", "z9", "x:y", "p.q"])
        return f"{stem}{len(self.words) + len(self.constants)}"

    def literal(self):
        r = self.rng
        n = r.choice([0, 1, -1, 7, 255, 2147483647, -2147483647, r.randint(-99999, 99999)])
        text = str(n)
        if r.random() < 0.1 and abs(n) < 10 ** 9:
            text = text.replace("-", "-0", 1) if n < 0 else "0" + text
        return text

    def case(self, word):
        r = self.rng.random()
        return word.upper() if r < 0.2 else mixed(word, self.rng) if r < 0.3 else word

    def body(self, depth):
        r, out = self.rng, []
        for _ in range(r.randint(0, 6)):
            k = r.random()
            if k < 0.45:
                out.append(self.case(r.choice(PRIMS)))
            elif k < 0.65:
                out.append(self.literal())
            elif k < 0.75 and (self.words or self.constants):
                out.append(self.case(r.choice(self.words + self.constants)))
            elif k < 0.83 and depth < 3:
                inner = self.body(depth + 1)
                rest = ["ELSE"] + self.body(depth + 1) if r.random() < 0.5 else []
                out += [self.case("if")] + inner + rest + [self.case("then")]
            elif k < 0.9 and depth < 3:
                out += ([self.case("begin")] + self.body(depth + 1) + [self.case("while")] +
                        self.body(depth + 1) + [self.case("repeat")])
            elif k < 0.93:
                out.append(self.case("exit"))
            elif k < 0.96:
                out.append("( a comment )")
        return out

    def constant_body(self):
        r = self.rng
        if self.constants and r.random() < 0.3:
            first = [self.case(r.choice(self.constants))]
        else:
            first = [self.literal()]
        k = r.random()
        if k < 0.3:
            return first + [self.literal(), self.case(r.choice(["+", "-", "*", "max", "and"]))]
        if k < 0.6:
            return first + [self.case(r.choice(["negate", "abs", "1+", "invert", "0="]))]
        return first

    def layout(self, tokens):
        """Tokens over one or more lines, a definition's name kept beside it."""
        lines, line = [], []
        for i, token in enumerate(tokens):
            line.append(token)
            if i > 1 and self.rng.random() < 0.2 and tokens[i - 1] not in (":",):
                lines.append(self.rng.choice([" ", "\t", "  "]).join(line))
                line = []
        if line:
            lines.append(" ".join(line))
        return lines

    def build(self):
        r = self.rng
        for _ in range(r.randint(1, 6)):
            if r.random() < 0.25:
                name = self.name()
                self.lines.append(" ".join(self.constant_body() + [self.case("constant"), name]))
                self.constants.append(name)
            else:
                name = self.name()
                self.lines += self.layout([":", name] + self.body(0) + [";"])
                self.words.append(name)
            if r.random() < 0.2:
                self.lines.append("\\ " + r.choice(["a comment", "bye", ": f ;"]))
        return self

    MISTAKES = ["foo", "$10", "1.", "2147483648", "then", "else", "repeat", "while", ":",
                "constant", "decimal", "until", "@", ">r", "abcdefghijklmnopqrstuvwxyz0123456",
                "(", "exit", "\x01", "\xe9", "-2147483648", "1e", "'a'"]

    def plant(self):
        """One mistake at a random token of a random line."""
        r = self.rng
        i = r.randrange(len(self.lines))
        tokens = self.lines[i].split(" ")
        tokens.insert(r.randint(0, len(tokens)), r.choice(self.MISTAKES))
        self.lines[i] = " ".join(tokens)
        if r.random() < 0.3 and self.words:
            self.lines.append(f": {self.case(r.choice(self.words))} ;")   # a redefinition
        return self

    def text(self):
        return "\n".join(self.lines).encode("latin-1")


def random_programs(gforth, seed, count):
    rng = random.Random(seed)
    texts = []
    for _ in range(count):
        p = Program(rng).build()
        texts.append((p.plant() if rng.random() < 0.2 else p).text())
    with tempfile.TemporaryDirectory() as directory:
        results = verify_check.run_driver(gforth, [("texts", t) for t in texts], directory)
    problems, outcomes, rules = [], {}, {}
    for n, text in enumerate(texts):
        r = results[n]
        outcomes[r["NEW"][1][:2]] = outcomes.get(r["NEW"][1][:2], 0) + 1
        rule = "identical" if r["OLD"] == r["NEW"] else verify_check.intended(r["OLD"], r["NEW"])
        rules[rule] = rules.get(rule, 0) + 1
        if rule is None or r["NEW"] != r["ALIAS"]:
            problems.append(f"program {n} differs:\n{text.decode('latin-1')}\n"
                            f"  old {r['OLD']}\n  new {r['NEW']}\n  alias {r['ALIAS']}")
        if r["depth"] != 0:
            problems.append(f"program {n}: data stack depth {r['depth']}")
    return problems, outcomes, rules


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--seed", type=int, default=20261103)
    parser.add_argument("--programs", type=int, default=400)
    args = parser.parse_args()
    gforth = os.environ.get("GFORTH", "gforth")
    problems, trips, refused = round_trip(gforth)
    random_problems, outcomes, rules = random_programs(gforth, args.seed, args.programs)
    problems += random_problems
    for problem in problems:
        print(problem, file=sys.stderr)
    names = {0: "ok", 1: "invalid", 5: "unsupported", 6: "full"}
    mix = ", ".join(f"{names.get(o, o)}{'' if w == 0 else f' (reason {w})'} {v}"
                    for (o, w), v in sorted(outcomes.items()))
    agree = ", ".join(f"{k or 'unexplained'} {v}" for k, v in sorted(rules.items(),
                                                                       key=str))
    print(f"program words round trip: {trips} IR files identical in both designs, "
          f"{refused} sources refused; {args.programs} random programs (seed {args.seed}; "
          f"{mix}): both designs identical, against today's reader {agree}; "
          f"{len(random_problems)} problems")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
