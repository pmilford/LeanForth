"""Differential tests of src/lib/bigint.fs against Lean 4.35.0's Int.

Usage (from the repository root):
  GFORTH=... python3 tests/lib/bigint_differential.py                # make test
  GFORTH=... LEAN=... python3 tests/lib/bigint_differential.py --lean  # make check
  options: --seed N (default 20261113), --pairs N (random pairs, default 10000)

Without --lean it needs only Gforth and Python 3. It builds integer pairs
(a, b): edge pairs (0, +-1, limb and cell boundaries of 32- and 64-bit
limbs, 2^64 +- 1, 10^19, 2^200, 2^300, Lean's documented examples of /, %
and bmod, bmod's boundary r = m/2 for even and odd m, exact and inexact
divisions by negative divisors) and random pairs from a fixed seed, a
quarter of them a = q b + r. tests/lib/bigint-cases.fs prints one line per
pair, the operands and thirteen results (see there); every line must equal
the one computed by the model below, which follows Lean's definitions
case by case (Init/Data/Int/DivMod/Basic.lean: ediv 73-78, emod 103-105,
bmod 318-323; Gcd.lean 43; Int.pow, natAbs, toNat, sign, compare).

A self-test first shows that the comparison refuses the same lines with one
value changed. Then the header's example runs from a folder outside the project, with
only the files the library requires, and every name the library defines
is checked: exactly the documented interface is visible, the helpers are
not (ADR 0010).

With --lean it also runs pinned Lean on the same pairs: a program reads
them from a string in its own source (so the Lean cache keys on them),
computes the same thirteen results with Lean's own Int operations (the
compiled ones that `#eval` and tactics use) and prints the same lines,
which must equal Forth's and the model's, line for line. Then a sample of
results as `example : (a op b : Int) = r := by decide +kernel`, so that
Lean's kernel computes the operations from their definitions: every one
must be accepted, and every one with r changed rejected. Finite tests, not
a proof.
"""
import argparse
import math
import os
from pathlib import Path
import random
import re
import subprocess
import sys
import tempfile

TEST_LIMIT = int(os.environ.get("TEST_TIMEOUT", "1800"))  # seconds; make exports it
if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)

ROOT = Path(__file__).resolve().parents[2]
RUNNER = ROOT / "tests/lib/bigint-cases.fs"
LIBRARY = ROOT / "src/lib/bigint.fs"
# The files the library requires, directly or through bignum.fs.
REQUIRED = ["bigint.fs", "bignum.fs", "bits.fs", "bounds.fs", "decimal.fs", "outcome.fs",
            "portability.fs", "module.fs"]
PUBLIC = {"bigint-valid?", "bigint-sign", "bigint-magnitude", "bigint-compare", "bigint+",
          "bigint-", "bigint*", "bigint-negate", "bigint-ediv", "bigint-emod", "bigint-bmod",
          "bigint-gcd", "bigint-pow", "bigint-natabs", "bigint-tonat", "nat>bigint",
          "n>bigint", "bigint>n", "decimal>bigint", "bigint>decimal"}
DEFINERS = {":", "constant", "create", "begin-structure", "field:", "+field", "variable",
            "value", "2constant"}


# ---- The model: Lean's definitions, case by case ----------------------------

def nat_div(m, n):
    return m // n if n else 0           # Nat.div: m / 0 = 0


def nat_mod(m, n):
    return m % n if n else m            # Nat.mod: m % 0 = m


def ediv(a, b):
    """Int.ediv: ofNat/ofNat, ofNat/-[n+1], -[m+1]/0, -[m+1]/ofNat (n+1), -[m+1]/-[n+1]."""
    if a >= 0:
        return nat_div(a, b) if b >= 0 else -nat_div(a, -b)
    m = -a - 1
    if b == 0:
        return 0
    if b > 0:
        return -(nat_div(m, b) + 1)     # -[m / succ n +1]
    return nat_div(m, -b) + 1           # ofNat (succ (m / succ n))


def emod(a, b):
    """Int.emod: ofNat m % n = m % natAbs n; -[m+1] % n = subNatNat (natAbs n) (succ (m % natAbs n))."""
    n = abs(b)
    if a >= 0:
        return nat_mod(a, n)
    return n - (nat_mod(-a - 1, n) + 1)


def bmod(x, m):
    """Int.bmod x m (m a Nat): r := x % m; if r < (m + 1) / 2 then r else r - m."""
    r = emod(x, m)
    return r if r < (m + 1) // 2 else r - m


def sign(a):
    return (a > 0) - (a < 0)


def line(a, b):
    """The thirteen results for the pair, after a and b, as tests/lib/bigint-cases.fs prints them."""
    values = [a, b, a + b, a - b, a * b, ediv(a, b), emod(a, b), bmod(a, abs(b)),
              math.gcd(abs(a), abs(b)), abs(a), max(a, 0), -a, sign(a), sign(a - b),
              a ** (abs(b) % 8)]
    return " ".join(str(v) for v in values)


# ---- Cases ------------------------------------------------------------------

def edge_values():
    values = {0, 1, 2, 3, 7, 8, 9, 10 ** 9, 10 ** 19 - 1, 10 ** 19, 10 ** 19 + 1}
    for k in (31, 32, 33, 62, 63, 64, 65, 95, 96, 127, 128, 129, 192, 200, 256, 300):
        values |= {(1 << k) - 1, 1 << k, (1 << k) + 1}
    values |= {(1 << 128) - 1 - (1 << 64), (1 << 192) - 1, 3 ** 150}
    return sorted(values | {-v for v in values})


def edge_divisors():
    values = {0, 1, 2, 3, 6, 7, 8, 9, (1 << 63) - 1, 1 << 63, (1 << 64) - 1, 1 << 64,
              (1 << 64) + 1, 1 << 128, 10 ** 19}
    return sorted(values | {-v for v in values})


def edge_pairs():
    pairs = []
    values, divisors = edge_values(), edge_divisors()
    for a in values:
        for b in divisors:
            pairs += [(a, b), (b, a)]
    # Lean's documented examples (DivMod/Basic.lean 60-70, 90-100, 305-315).
    for a in (12, -12, 7, 0):
        for b in (0, 6, -6, 7, -7, 8, -8, 9, -9):
            pairs.append((a, b))
    # bmod's boundary: x = q m + r with 2r = m - 1, m, m + 1 (r < (m + 1) / 2).
    for m in (1, 2, 3, 4, 5, 6, 7, 8, 9, 1 << 64, (1 << 64) + 1, (1 << 65) + 3, 10 ** 30):
        for r in {m // 2 - 1, m // 2, m // 2 + 1, (m + 1) // 2, 0, m - 1}:
            if 0 <= r < m:
                for q in (0, 1, -1, -3, 1 << 70, -(1 << 70)):
                    pairs += [(q * m + r, m), (q * m + r, -m)]
    # Exact and inexact divisions with every sign.
    for b in (3, 1 << 64, (1 << 64) + 7, 10 ** 25):
        for q in (1, 5, 1 << 64, 10 ** 30):
            for r in (0, 1, b - 1):
                for sa in (1, -1):
                    for sb in (1, -1):
                        pairs.append((sa * (q * b + r), sb * b))
    return pairs


class Random:
    def __init__(self, seed):
        self.rng = random.Random(seed)

    def below(self, n):
        return self.rng.randrange(n)

    def magnitude(self):
        roll = self.below(100)
        if roll < 10:
            return abs(self.rng.choice(edge_values()))
        if roll < 45:
            bits = 1 + self.below(64)
        elif roll < 75:
            bits = 65 + self.below(192)
        elif roll < 95:
            bits = 257 + self.below(768)
        else:
            bits = 1025 + self.below(1024)
        if self.below(4) == 0:                  # all ones: every carry
            return (1 << bits) - 1
        return self.rng.getrandbits(bits)

    def integer(self):
        n = self.magnitude()
        return -n if self.below(2) else n

    def pair(self):
        a, b = self.integer(), self.integer()
        roll = self.below(8)
        if roll < 2 and b:                      # a = q b + r, r of either sign
            a = a * b + self.rng.choice([0, 0, 1, -1, b // 2, -(b // 2), b // 2 + 1])
        elif roll == 2:                         # small divisors
            b = self.rng.choice([1, -1, 2, -2, 3, -3, 7, -7, 8, -8])
        elif roll == 3:
            b = a + self.rng.choice([-1, 0, 1]) if self.below(2) else -a
        return a, b


def pairs_for(seed, count):
    rnd = Random(seed)
    pairs = edge_pairs()
    edges = len(pairs)
    pairs += [rnd.pair() for _ in range(count)]
    return pairs, edges


# ---- Running ----------------------------------------------------------------

def run(command, what, cwd=None):
    done = subprocess.run(command, capture_output=True, text=True, timeout=TEST_LIMIT,
                          stdin=subprocess.DEVNULL, cwd=cwd)
    if done.returncode != 0:
        sys.stderr.write(done.stdout[-2000:] + done.stderr[-2000:])
        raise SystemExit(f"{what} failed (exit {done.returncode})")
    return [l.rstrip() for l in done.stdout.splitlines()]


def forth_lines(gforth, case_file):
    return run([gforth, str(RUNNER), "-e", f's" {case_file}" run-cases bye'], "Gforth")


def compare(name, lines, expected, pairs):
    if len(lines) != len(expected):
        return [f"{name}: {len(lines)} lines for {len(expected)} pairs"]
    bad = []
    for got, want, (a, b) in zip(lines, expected, pairs):
        if got != want:
            bad.append(f"{name}: a={str(a)[:40]} b={str(b)[:40]}:\n    got  {got[:200]}\n"
                       f"    want {want[:200]}")
    return bad


def self_test(lines, pairs):
    """The comparison refuses a known-wrong table: one quotient changed in a
    copy of the lines is reported, and only that line."""
    wrong = list(lines)
    k = len(wrong) // 2
    fields = wrong[k].split()
    fields[5] = str(int(fields[5]) + 1)
    wrong[k] = " ".join(fields)
    found = compare("self-test", wrong, lines, pairs)
    if len(found) != 1 or f"a={str(pairs[k][0])[:40]} " not in found[0]:
        raise SystemExit("the comparison did not refuse a table with one value changed")
    print("Self-test: the comparison refuses the same lines with one quotient changed.")


def source_words(text):
    """The words of Forth source, without \\ comments and ( ) comments."""
    words, skipping = [], False
    for text_line in text.splitlines():
        tokens = text_line.split()
        if "\\" in tokens:
            tokens = tokens[:tokens.index("\\")]
        for token in tokens:
            if skipping:
                skipping = not token.endswith(")")
            elif token == "(":
                skipping = True
            else:
                words.append(token)
    return words


def defined_names(text):
    """{name: public} for every name the library defines; public when defined
    while lf-lib is the compilation word list."""
    words, public, names, compiling = source_words(text), False, {}, False
    for i, word in enumerate(words):
        low = word.lower()
        if low == ";":
            compiling = False
        elif compiling:
            continue
        elif low == "module-open":
            public = False
        elif low == "set-current" and i > 0:
            public = words[i - 1].lower() == "lf-lib"
        elif low in DEFINERS and i + 1 < len(words):
            names[words[i + 1].lower()] = public
            compiling = low == ":"
    return names


def header_example():
    lines = LIBRARY.read_text().splitlines()
    start = next(i for i, l in enumerate(lines) if l.startswith("\\ Example:")) + 1
    end = next(i for i in range(start, len(lines)) if not lines[i].startswith("\\   "))
    return "\n".join(l[4:] for l in lines[start:end]) + "\n"


def standalone(gforth):
    """The header's example, and the interface, from a folder outside the project."""
    with tempfile.TemporaryDirectory() as scratch:
        folder = Path(scratch)
        if folder.resolve().is_relative_to(ROOT.resolve()):
            raise SystemExit("the scratch folder lies inside the project")
        (folder / "lib").mkdir()
        for name in REQUIRED:
            (folder / "lib" / name).write_text((ROOT / "src/lib" / name).read_text())
        (folder / "example.fs").write_text("require lib/bigint.fs\n" + header_example() + "bye\n")
        got = run([gforth, "example.fs"], "the header's example", cwd=folder)
        if " ".join(got).split() != ["-2", "2"]:
            raise SystemExit(f"the header's example printed {got}, not -2 2")
        names = defined_names(LIBRARY.read_text())
        checks = ["require lib/bigint.fs"]
        for name, public in sorted(names.items()):
            test, label = ("0=", "missing") if public else ("", "visible")
            checks.append(f"[defined] {name} {test} [if] .( {label}:{name}) cr [then]")
        (folder / "interface.fs").write_text("\n".join(checks) + "\n.( checked) cr bye\n")
        got = run([gforth, "interface.fs"], "the interface check", cwd=folder)
    public = {name for name, is_public in names.items() if is_public}
    if got != ["checked"] or public != PUBLIC or len(names) < 80:
        raise SystemExit(f"interface: {got[:5]}; public {sorted(public ^ PUBLIC)} differ; "
                         f"{len(names)} names read")
    print(f"The header's example prints -2 2 from a folder outside the project, loading only "
          f"{', '.join(REQUIRED)}; exactly the {len(PUBLIC)} documented words of "
          f"{len(names)} names are visible.")


LEAN_PROGRAM = '''-- Generated by tests/lib/bigint_differential.py: Lean's Int on the pairs below.
def data : String := "{data}"

def cmp (a b : Int) : Int :=
  match compare a b with
  | .lt => -1
  | .eq => 0
  | .gt => 1

def line (a b : Int) : String :=
  s!"{{a}} {{b}} {{a + b}} {{a - b}} {{a * b}} {{a / b}} {{a % b}} {{Int.bmod a b.natAbs}} " ++
  s!"{{Int.gcd a b}} {{a.natAbs}} {{a.toNat}} {{-a}} {{a.sign}} {{cmp a b}} {{a ^ (b.natAbs % 8)}}"

def main : IO Unit := do
  for l in data.splitOn "\\n" do
    match l.splitOn " " with
    | [x, y] =>
      match x.toInt?, y.toInt? with
      | some a, some b => IO.println (line a b)
      | _, _ => IO.println s!"unreadable: {{l}}"
    | _ => pure ()
'''


def lean_lines(lean, directory, pairs):
    data = "\\n".join(f"{a} {b}" for a, b in pairs)
    source = Path(directory) / "BigintLean.lean"
    source.write_text(LEAN_PROGRAM.format(data=data))
    return run([lean, "-DwarningAsError=true", "--run", str(source)], "Lean")


# Equations for the kernel: (Lean text of the left side, the model's value).
KERNEL_OPS = [
    ("({a} : Int) + {b}", lambda a, b: a + b),
    ("({a} : Int) - {b}", lambda a, b: a - b),
    ("({a} : Int) * {b}", lambda a, b: a * b),
    ("({a} : Int) / {b}", ediv),
    ("({a} : Int) % {b}", emod),
    ("Int.bmod {a} {m}", lambda a, b: bmod(a, abs(b))),
    ("(Int.gcd {a} {b} : Int)", lambda a, b: math.gcd(a, b)),
    ("({a} : Int) ^ {e}", lambda a, b: a ** (abs(b) % 8)),
    ("-({a} : Int)", lambda a, b: -a),
    ("(Int.toNat {a} : Int)", lambda a, b: max(a, 0)),
]


def lit(n):
    return f"({n})" if n < 0 else str(n)


def kernel_check(lean, directory, pairs, rng):
    """A sample of pairs, each operation as an equation Lean's kernel decides; then
    every one with its value changed, which the kernel must reject."""
    small = [p for p in pairs if len(str(p[0])) + len(str(p[1])) < 400]
    sample = rng.sample(small, min(30, len(small)))
    rows = []
    for a, b in sample:
        for text, value in KERNEL_OPS:
            left = text.format(a=lit(a), b=lit(b), m=abs(b), e=abs(b) % 8)
            rows.append((left, value(a, b)))

    def equations(change):
        return "".join(f"example : {left} = {lit(value + change)} := by decide +kernel\n"
                       for left, value in rows)
    right = Path(directory) / "BigintKernel.lean"
    right.write_text(equations(0))
    run([lean, "-DwarningAsError=true", str(right)], "Lean (kernel equations)")
    wrong = Path(directory) / "BigintKernelWrong.lean"
    wrong.write_text(equations(1))
    done = subprocess.run([lean, "-DwarningAsError=true", "-DmaxErrors=100000", str(wrong)],
                          capture_output=True, text=True, timeout=TEST_LIMIT)
    refused = r"BigintKernelWrong\.lean:(\d+):\d+: error"
    rejected = {int(m.group(1)) for m in re.finditer(refused, done.stdout + done.stderr)}
    missing = sorted(set(range(1, len(rows) + 1)) - rejected)
    if done.returncode == 0 or missing:
        raise SystemExit(f"Lean's kernel accepted {len(missing)} changed values, lines {missing[:10]}")
    print(f"Lean 4.35.0's kernel (decide +kernel) proves {len(rows)} equations of the model "
          f"({len(KERNEL_OPS)} operations on {len(sample)} pairs) and rejects all {len(rows)} "
          f"with the value changed.")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--seed", type=int, default=20261113)
    parser.add_argument("--pairs", type=int, default=10000)
    parser.add_argument("--lean", action="store_true")
    args = parser.parse_args()
    gforth = os.environ.get("GFORTH", "gforth")
    if "/" in gforth:
        gforth = str(Path(gforth).absolute())
    pairs, edges = pairs_for(args.seed, args.pairs)
    expected = [line(a, b) for a, b in pairs]
    with tempfile.TemporaryDirectory() as directory:
        case_file = Path(directory) / "pairs.txt"
        case_file.write_text("".join(f"{a} {b}\n" for a, b in pairs))
        lines = forth_lines(gforth, case_file)
        bad = compare("Forth against the model", lines, expected, pairs)
        if args.lean:
            lean = lean_lines(os.environ.get("LEAN", "lean"), directory, pairs)
            bad += compare("Forth against Lean", lines, lean, pairs)
            bad += compare("the model against Lean", expected, lean, pairs)
        for item in bad[:10]:
            print("  " + item)
        if bad:
            names = [item.split(":")[0] for item in bad]
            counts = ", ".join(f"{name}: {names.count(name)}" for name in dict.fromkeys(names))
            raise SystemExit(f"differences in {len(pairs)} pairs ({counts})")
        self_test(lines, pairs)
        negative = sum(1 for a, b in pairs if a < 0 or b < 0)
        biggest = max(max(abs(a), abs(b)).bit_length() for a, b in pairs)
        print(f"bigint: {len(pairs)} pairs ({edges} edge, {len(pairs) - edges} random, "
              f"seed {args.seed}; {negative} with a negative operand, up to {biggest} bits), "
              f"13 operations each, equal the model of Lean's definitions"
              + (" and pinned Lean 4.35.0's own Int, line for line." if args.lean else "."))
        if not args.lean:
            standalone(gforth)
        if args.lean:
            kernel_check(os.environ.get("LEAN", "lean"), directory, pairs,
                         random.Random(args.seed + 1))


if __name__ == "__main__":
    main()
