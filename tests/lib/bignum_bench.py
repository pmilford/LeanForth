"""Speed of src/lib/bignum.fs against Python's integers (report only).

Usage (from the repository root):
  python3 tests/lib/bignum_bench.py [--gforth PATH ...] [--seed N]
Default engines: .tools/gforth/bin/gforth and gforth-fast.

For numbers of 10, 100, 1,000 and 10,000 decimal digits (fixed seed) it
times addition, multiplication, division and remainder of a 2n-digit
number by an n-digit one, gcd, a power with an n-digit result, and
decimal reading and printing, with tests/lib/bignum-bench.fs on each
engine and with Python's timeit on the same operands, and prints the
nanoseconds per operation and the ratio Forth / Python. Python's integers
use 30-bit digits, Karatsuba multiplication from about 70 digits, and
quadratic decimal conversion below a few thousand digits (CPython). The
two sides are timed differently (Gforth's utime around a loop; timeit),
so ratios are approximate; nothing here fails on speed.
"""
import argparse
import os
from pathlib import Path
import platform
import random
import subprocess
import sys
import tempfile
import timeit

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)

ROOT = Path(__file__).resolve().parents[2]
BENCH = ROOT / "tests/lib/bignum-bench.fs"
SIZES = [10, 100, 1000, 10000]


def operands(rng, digits):
    def number(d):
        return rng.randrange(10 ** (d - 1), 10 ** d)
    a, b = number(digits), number(digits)
    e = max(1, round(digits / 0.4771))          # 3^e has about `digits` digits
    return [("add", a, b), ("mul", a, b), ("div", number(2 * digits), b),
            ("mod", number(2 * digits), b), ("gcd", a, b), ("pow", 3, e),
            ("parse", a, 0), ("print", a, 0)]


def python_ns(op, a, b):
    text = str(a)
    work = {"add": lambda: a + b, "mul": lambda: a * b, "div": lambda: a // b,
            "mod": lambda: a % b, "gcd": lambda: __import__("math").gcd(a, b),
            "pow": lambda: a ** b, "parse": lambda: int(text), "print": lambda: str(a)}[op]
    timer = timeit.Timer(work)
    count, _ = timer.autorange()
    best = min(timer.repeat(repeat=3, number=count))
    return best / count * 1e9


def forth_ns(gforth, cases):
    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory) / "bench.txt"
        path.write_text("".join(f"{op} {a} {b}\n" for op, a, b in cases))
        done = subprocess.run([gforth, str(BENCH), "-e", f's" {path}" run-bench bye'],
                              capture_output=True, text=True, timeout=3600,
                              stdin=subprocess.DEVNULL)
        if done.returncode != 0:
            raise SystemExit(done.stderr[-2000:])
        return [int(line) for line in done.stdout.split()]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--gforth", action="append")
    parser.add_argument("--seed", type=int, default=20261102)
    args = parser.parse_args()
    engines = args.gforth or [str(ROOT / ".tools/gforth/bin/gforth"),
                              str(ROOT / ".tools/gforth/bin/gforth-fast")]
    rng = random.Random(args.seed)
    cases = [(digits, case) for digits in SIZES for case in operands(rng, digits)]
    timings = {gforth: forth_ns(gforth, [c for _, c in cases]) for gforth in engines}
    print(f"Python {platform.python_version()}; engines: "
          + ", ".join(os.path.basename(g) for g in engines))
    header = ["op", "digits", "python ns"]
    for g in engines:
        header += [f"{os.path.basename(g)} ns", "ratio"]
    print(" | ".join(header))
    for index, (digits, (op, a, b)) in enumerate(cases):
        py = python_ns(op, a, b)
        row = [op, str(digits), f"{py:,.0f}"]
        for g in engines:
            ns = timings[g][index]
            row += [f"{ns:,}", f"{ns / py:,.1f}"]
        print(" | ".join(row))


if __name__ == "__main__":
    main()
