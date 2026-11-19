"""Differential tests of src/lib/bignum.fs against Python's integers and pinned Lean.

Usage (from the repository root):
  GFORTH=... python3 tests/lib/bignum_differential.py                # make test
  GFORTH=... LEAN=... python3 tests/lib/bignum_differential.py --lean  # make check
  options: --seed N (default 20261102), --cases N (random cases, default 24000),
           --no-faults (skip the planted faults)

Without --lean it needs only Gforth and Python 3. It generates the edge
cases (0, 1, limb and cell boundaries of 32- and 64-bit limbs, max-u plus
and minus one, equal operands, very unequal sizes, subtraction below 0,
division by 0, huge shifts and exponents, Knuth's rare add-back case,
gcd of Fibonacci neighbours, results at an arena's bit limit) and random
cases from a fixed seed, runs tests/lib/bignum-cases.fs on all of them and
requires every printed line to equal Python's answer. The expected answers
follow the semantics in the header of src/lib/bignum.fs: Lean's Nat
operations, and "full" exactly when a result has more bits than the
arena's limit. Then it plants faults in a copy of the library (a lost
carry, a wrong borrow, a skipped add-back, ...) and requires each to
change at least one line.

With --lean it also gives a sample of the cases to pinned Lean 4.35.0 as
`example : Nat.op A B = R := by decide +kernel`, which makes Lean's kernel
compute the operation itself (its GMP path, type_checker.cpp reduce_nat):
every one must be accepted, and every one with R changed must be rejected.
Finite tests, not a proof.
"""
import argparse
import math
import os
from pathlib import Path
import random
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import pathlib
import functools
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[2] / "scripts"))
import lean_pin  # noqa: E402  $LEAN or the pinned Lean, refused unrun when an elan proxy
TEST_LIMIT = int(os.environ.get("TEST_TIMEOUT", "1800"))  # seconds; make exports it

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)

ROOT = Path(__file__).resolve().parents[2]
RUNNER = ROOT / "tests/lib/bignum-cases.fs"
LIBRARY = ROOT / "src/lib"
LEAN_BITS = 1 << 30            # the arena's default limit, Lean's 128 MiB
OPS = ["add", "sub", "mul", "div", "mod", "gcd", "and", "or", "xor",
       "shl", "shr", "pow", "beq", "ble", "cmp"]
LEAN_NAMES = {"add": "Nat.add", "sub": "Nat.sub", "mul": "Nat.mul", "div": "Nat.div",
              "mod": "Nat.mod", "gcd": "Nat.gcd", "and": "Nat.land", "or": "Nat.lor",
              "xor": "Nat.xor", "shl": "Nat.shiftLeft", "shr": "Nat.shiftRight",
              "pow": "Nat.pow", "beq": "Nat.beq", "ble": "Nat.ble"}

# Faults planted in a copy of src/lib/bignum.fs: (what, text, replacement).
# Each text occurs exactly once in the module.
FAULTS = [
    ("carry out of a limb addition lost",
     "over i + @ 0 rot 0 d+ i @ 0 d+ swap i ! cell +loop nip ;",
     "over i + @ 0 rot 0 d+ i @ 0 d+ drop 0 swap i ! cell +loop nip ;"),
    ("addition starts with a carry of 1 (off by one)",
     "limbs-paired 0 -rot ?do over i + @ 0 rot 0 d+ i @ 0 d+",
     "limbs-paired 1 -rot ?do over i + @ 0 rot 0 d+ i @ 0 d+"),
    ("borrow of a limb subtraction ignored",
     "i @ 0 2swap d- swap i ! negate cell +loop nip ;",
     "i @ 0 2swap d- swap i ! drop 0 cell +loop nip ;"),
    ("borrow not passed on to higher limbs",
     "dup 0= if leave then i @ 0 rot 0 d-",
     "leave i @ 0 rot 0 d-"),
    ("multiply-accumulate drops the product's high limb",
     "i @ 0 tuck d+ 2over i + @ um* d+ swap i !",
     "i @ 0 tuck d+ 2over i + @ um* drop 0 d+ swap i !"),
    ("Karatsuba: a1 b1 not subtracted from the middle term",
     "2dup r@ kara-high 2swap vector-! drop",
     ""),
    ("Karatsuba: the carry out of a0 + a1 lost",
     "r@ kara-h swap r> kara-hi 1+ vector+! drop",
     "r@ kara-h swap r> kara-hi vector+! drop"),
    ("Karatsuba: a short tail's rows lose the tail's top limb",
     "dup tail-size over chunks-frame school",
     "dup tail-size 1- over chunks-frame school"),
    ("Karatsuba: a long tail's product added at limb 0, not at the tail's place",
     "r@ tail-limb cells r@ chunks-r +!",
     ""),
    ("Knuth D: the add-back step skipped",
     "if window+! r> 1- else 2drop r> then",
     "if 2drop r> else 2drop r> then"),
    ("Knuth D: qhat is B - 2 instead of B - 1 when u2 = v1",
     "-1 over division-qhat !",
     "-2 over division-qhat !"),
    ("Knuth D: the remainder is not scaled back",
     "2dup 2>r limbs/1! drop",
     "2dup 2>r 2drop drop"),
    ("Lehmer: quotients used without checking that they agree",
     "over = if true else drop false then ;",
     "drop true ;"),
    ("Lehmer: one cofactor's sign wrong",
     "swap negate r@ euclid-v @ swap r> euclid-u @ ;",
     "swap r@ euclid-v @ swap r> euclid-u @ ;"),
    ("decimal output: one digit too few per chunk",
     "chunk-digits 0 do 1 chars - swap",
     "chunk-digits 1 do 1 chars - swap"),
    ("decimal output: no room for the top chunk's leading zeros, which overwrite the number",
     ": text-cells ( big -- n ) big-bits 3 / chunk-digits + chars",
     ": text-cells ( big -- n ) big-bits 3 / 1+ chars"),
    ("left shift by a limb count ignores the bit remainder",
     "1 swap lshift swap big-vector r> swap limbs*row! r> ;",
     "drop 1 swap big-vector r> swap limbs*row! r> ;"),
    ("right shift loses the bits crossing limbs",
     "1 swap lshift r> r@ big-limbs swap limbs/1! drop r> ;",
     "drop 1 r> r@ big-limbs swap limbs/1! drop r> ;"),
    ("power: odd exponents lose a factor",
     ">r 1 and 0= if drop 0 then",
     ">r drop drop 0"),
    ("normalization drops at most one leading zero limb",
     "begin dup top-zero? while -1 over +! repeat ;",
     "dup top-zero? if -1 over +! then ;"),
    ("limit check off by one",
     ": big-fits? ( big arena -- flag ) arena-limit @ swap big-bits < 0= ;",
     ": big-fits? ( big arena -- flag ) arena-limit @ 1+ swap big-bits < 0= ;"),
    ("comparison of equal-size numbers looks at the top limb only",
     "swap limb-order dup if leave then back-cell +loop nip ;",
     "swap limb-order leave back-cell +loop nip ;"),
]


def bits(n):
    return n.bit_length()


def expect(op, a, b, limit):
    """The line tests/lib/bignum-cases.fs must print."""
    if op == "limit":
        return "limit"
    if bits(a) > limit:
        return "full"
    if op == "dec":
        return str(a)
    if bits(b) > limit:
        return "full"
    if op in ("beq", "ble"):
        return "true" if (a == b if op == "beq" else a <= b) else "false"
    if op == "cmp":
        return str((a > b) - (a < b))
    if op == "shl":
        if a == 0:
            return "0"
        if bits(a) + b > limit:
            return "full"
        r = a << b
    elif op == "pow":
        if b == 0:
            r = 1
        elif a <= 1:
            r = a
        elif (bits(a) - 1) * b + 1 > limit:
            return "full"
        else:
            r = a ** b
    else:
        r = {"add": lambda: a + b, "sub": lambda: max(a - b, 0), "mul": lambda: a * b,
             "div": lambda: a // b if b else 0, "mod": lambda: a % b if b else a,
             "gcd": lambda: math.gcd(a, b), "and": lambda: a & b, "or": lambda: a | b,
             "xor": lambda: a ^ b, "shr": lambda: a >> b}[op]()
    return "full" if bits(r) > limit else str(r)


class Cases:
    def __init__(self, seed):
        self.rng = random.Random(seed)
        self.items = []         # (op, a, b, limit)
        self.limit = LEAN_BITS

    def add(self, op, a, b=0):
        self.items.append((op, a, b, self.limit))

    def set_limit(self, n):
        self.limit = n
        self.items.append(("limit", n, 0, n))

    def bits(self, n):
        return self.rng.getrandbits(n) if n > 0 else 0

    def below(self, n):
        return self.rng.getrandbits(max(n.bit_length() + 8, 8)) % n

    def digits(self):
        """A digit count: mostly small, sometimes up to 10,000."""
        roll = self.below(1000)
        if roll < 500:
            return 1 + self.below(40)
        if roll < 800:
            return 40 + self.below(160)
        if roll < 950:
            return 200 + self.below(800)
        if roll < 990:
            return 1000 + self.below(2000)
        return 5000 + self.below(5001)

    def number(self):
        """A random number of a random size, or a special value."""
        roll = self.below(100)
        if roll < 15:
            return self.rng.choice(SPECIAL)
        if roll < 30:
            n = self.rng.choice([31, 32, 33, 63, 64, 65, 95, 96, 97, 127, 128, 129,
                                 191, 192, 193, 255, 256, 257, 511, 512, 513])
            return self.bits(n) | (1 << (n - 1))
        d = self.digits()
        return self.below(10 ** d) if d > 1 else self.below(10)

    def shift(self):
        roll = self.below(100)
        if roll < 60:
            return self.below(300)
        if roll < 85:
            return self.rng.choice([0, 1, 31, 32, 33, 63, 64, 65, 127, 128, 129, 1000, 4096])
        if roll < 95:
            return self.below(5000)
        return self.rng.choice([1 << 64, (1 << 64) + 5, (1 << 64) - 1, 10 ** 30, 1 << 200])


SPECIAL = sorted({0, 1, 2, 3, 9, 10, 255, 256, 10 ** 9, 10 ** 9 - 1, 10 ** 18, 10 ** 19 - 1,
                  10 ** 19, 10 ** 19 + 1, 10 ** 38, 10 ** 38 - 1}
                 | {(1 << k) + d for k in (31, 32, 33, 63, 64, 65, 96, 127, 128, 129, 192, 256)
                    for d in (-1, 0, 1)}
                 | {((1 << 64) ** n - 1) for n in (2, 3, 5)}
                 | {((1 << 32) ** n - 1) for n in (2, 3, 5)}
                 | {(1 << (64 * n)) + 1 for n in (1, 2, 4)})


def add_back_cases(cases):
    """Divisions where the estimate from the top three limbs is one too
    large: u = q * (v1 B^2 + v0 B) with v's low limb B - 1, so q * v > u.
    Built for B = 2^32 and 2^64."""
    for limb in (32, 64):
        base = 1 << limb
        for _ in range(12):
            v1 = (1 << (limb - 1)) | cases.bits(limb - 1)
            v0 = cases.bits(limb)
            v = v1 * base * base + v0 * base + (base - 1)
            q = (1 << (limb - 1)) | cases.bits(limb - 1)
            u = q * (v1 * base * base + v0 * base)
            low = cases.bits(limb * cases.below(3))
            for op in ("div", "mod"):
                cases.add(op, u, v)
                cases.add(op, u * base ** 2 + low % base ** 2, v * base ** 2 + low % base)


def top_equal_cases(cases):
    """Divisions where a window's top limb equals v's top limb, so the
    first estimate is B - 1: the quotient has limbs B - 1."""
    for limb in (32, 64):
        base = 1 << limb
        for _ in range(12):
            v = ((1 << (limb - 1)) | cases.bits(limb - 1)) * base + cases.bits(limb)
            q = (base - 1) * base + (base - 1 - cases.below(3))
            r = cases.below(v)
            for op in ("div", "mod"):
                cases.add(op, q * v + r, v)
                cases.add(op, (base ** 3 - 1) * v + r, v)


def karatsuba_cases(cases):
    """Products around the Karatsuba threshold (48 limbs) and its levels,
    equal and unequal sizes, random limbs and all-ones limbs (every
    carry), as 64-bit limb counts. A longer factor is cut into chunks of
    the shorter one's size; the tail left over goes by rows below 48
    limbs (49 by 1000: a tail of 20; 95 by 142: 47) and otherwise turns
    the job round (100 by 160: a tail of 60, then 40 by rows; 96 by 144:
    48, then none; 1000 by 1049: 49, then 20; 144 by 233: 89, then 55,
    then 34, Fibonacci sizes, so two turns)."""
    sizes = [(47, 47), (47, 48), (48, 48), (49, 49), (63, 64), (95, 96), (96, 96), (97, 97),
             (100, 100), (127, 129), (48, 100), (49, 1000), (200, 64), (64, 200), (145, 49),
             (191, 193), (520, 520), (513, 1027), (95, 142), (100, 160), (96, 144),
             (1000, 1049), (144, 233)]
    for n1, n2 in sizes:
        a = (1 << (64 * n1 - 1)) | cases.bits(64 * n1 - 1)
        b = (1 << (64 * n2 - 1)) | cases.bits(64 * n2 - 1)
        cases.add("mul", a, b)
        cases.add("mul", (1 << (64 * n1)) - 1, (1 << (64 * n2)) - 1)
        cases.add("pow", a, 2)


def edge_cases(cases):
    ops = OPS + ["dec"]
    for a in SPECIAL:
        cases.add("dec", a)
        for b in (0, 1, 2, 64, 65, (1 << 64) - 1, 1 << 64):
            for op in ("add", "sub", "mul", "div", "mod", "gcd", "and", "or", "xor", "cmp",
                       "beq", "ble"):
                cases.add(op, a, b)
                cases.add(op, b, a)
    for op in ops:
        for a in (0, 1, (1 << 64) - 1, 1 << 64, 10 ** 100):
            cases.add(op, a, a)
    # Text forms: leading zeros.
    for a in (0, 1, 10 ** 19, (1 << 64) - 1):
        cases.items.append(("dec0", a, 0, cases.limit))
    # Very unequal sizes.
    for _ in range(40):
        big, small = cases.bits(64 * (20 + cases.below(100))) | 1, cases.bits(1 + cases.below(130)) | 1
        for op in ("add", "sub", "mul", "div", "mod", "gcd", "and", "or", "xor", "cmp"):
            cases.add(op, big, small)
            cases.add(op, small, big)
    # gcd: common factors, Fibonacci neighbours, powers of two, equal.
    fib = [0, 1]
    while len(fib) < 3000:
        fib.append(fib[-1] + fib[-2])
    for n in (2, 3, 50, 93, 94, 95, 186, 187, 500, 1000, 2999):
        cases.add("gcd", fib[n], fib[n - 1])
        cases.add("gcd", fib[n - 1], fib[n])
    for _ in range(60):
        g = cases.number() | 1
        x, y = cases.number(), cases.number()
        cases.add("gcd", g * x, g * y)
        cases.add("gcd", (g << cases.below(200)) * x, g * y)
    for k in (0, 1, 63, 64, 65, 200):
        cases.add("gcd", 1 << k, 1 << (k + 7))
    # Shifts and powers at their edges.
    for a in (0, 1, 3, (1 << 64) - 1, 10 ** 40):
        for s in (0, 1, 63, 64, 65, 128, 129, 1000, (1 << 64) - 1, 1 << 64, 10 ** 30):
            cases.add("shl", a, s)
            cases.add("shr", a, s)
    for a in (0, 1, 2, 3, 10, (1 << 64) - 1, 1 << 64):
        for e in (0, 1, 2, 3, 63, 64, 65, 100, (1 << 64) - 1, 1 << 64, 10 ** 30):
            cases.add("pow", a, e)
    cases.add("pow", 2, LEAN_BITS)              # 2^30 + 1 bits: refused before computing
    cases.add("shl", 1, LEAN_BITS)
    add_back_cases(cases)
    top_equal_cases(cases)
    karatsuba_cases(cases)


def limit_cases(cases):
    """Results on both sides of a small limit, for every operation."""
    for limit in (0, 1, 64, 65, 200, 256):
        cases.set_limit(limit)
        for _ in range(40):
            a = cases.bits(cases.below(limit + 3) + 1)
            b = cases.bits(cases.below(limit + 3) + 1)
            for op in ("dec", "add", "sub", "mul", "and", "or", "xor", "gcd", "div", "mod"):
                cases.add(op, a, b)
            cases.add("shl", a, cases.below(limit + 2))
            cases.add("pow", a % 1000, cases.below(80))
        top = (1 << limit) - 1 if limit else 0
        for op in ("add", "mul", "shl", "pow"):
            cases.add(op, top, 1)
            cases.add(op, top, 0)
            cases.add(op, 1, top)
        cases.add("dec", top)
        cases.add("dec", top + 1)
        cases.add("dec", 10 ** (limit // 3 + 2))
    cases.set_limit(LEAN_BITS)


def random_cases(cases, count):
    for _ in range(count):
        op = cases.rng.choice(OPS + ["dec"])
        a = cases.number()
        if op in ("shl", "shr"):
            b = cases.shift()
        elif op == "pow":
            a = a % (10 ** (1 + cases.below(30)))
            limit_bits = 40000
            b = cases.below(limit_bits // max(bits(a), 1) + 2)
        elif op in ("beq", "ble", "cmp") and cases.below(3) == 0:
            b = a + cases.rng.choice([-1, 0, 0, 1]) if a else a
        elif op in ("div", "mod", "gcd") and cases.below(4) == 0:
            b = cases.number()
            a = a * b + cases.below(b + 1)
        else:
            b = cases.number()
        cases.add(op, a, b)


def case_line(op, a, b):
    if op == "limit":
        return f"limit {a}"
    if op == "dec":
        return f"dec {a}"
    if op == "dec0":
        return f"dec 000{a}"
    return f"{op} {a} {b}"


def run(command):
    done = subprocess.run(command, capture_output=True, text=True, timeout=TEST_LIMIT,
                          stdin=subprocess.DEVNULL)
    if done.returncode != 0:
        sys.stderr.write(done.stdout[-2000:] + done.stderr[-2000:])
        raise SystemExit(f"command failed: {' '.join(map(str, command[:3]))} ...")
    return done.stdout.splitlines()


def forth_lines(gforth, case_file, preload=None):
    phrase = f's" {case_file}" run-cases bye'
    command = [gforth] + ([str(preload)] if preload else []) + [str(RUNNER), "-e", phrase]
    return run(command)


def compare(lines, expected, items):
    if len(lines) != len(expected):
        return [f"{len(lines)} lines for {len(expected)} cases"]
    bad = []
    for line, want, item in zip(lines, expected, items):
        if line != want:
            op, a, b, _ = item
            bad.append(f"{case_line(op, a, b)[:120]}: got {line[:60]}, want {want[:60]}")
    return bad


def first_difference(command, expected, seconds):
    """Run command and stop it at its first output line that differs from
    expected: that line's number (from 1), len(expected) + 1 when it printed
    fewer lines or failed, or 0 when every line was right. A changed library
    may loop once its numbers are wrong, so the run is stopped there (its
    whole process group, which is only this child's) or after seconds."""
    child = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                             stdin=subprocess.DEVNULL, text=True, start_new_session=True)
    timer = threading.Timer(seconds, os.killpg, (child.pid, signal.SIGKILL))
    timer.start()
    try:
        count = 0
        for count, line in enumerate(child.stdout, 1):
            if count > len(expected) or line.rstrip("\n") != expected[count - 1]:
                return count
        return 0 if child.wait() == 0 and count == len(expected) else len(expected) + 1
    finally:
        timer.cancel()
        if child.poll() is None:
            os.killpg(child.pid, signal.SIGKILL)
        child.wait()


def planted(gforth, directory, case_file, expected):
    source = (LIBRARY / "bignum.fs").read_text()
    caught = 0
    for what, text, change in FAULTS:
        if source.count(text) != 1:
            raise SystemExit(f"fault text not found once: {what}")
        copy = Path(directory) / "lib-copy"
        if copy.exists():
            shutil.rmtree(copy)
        shutil.copytree(LIBRARY, copy)
        (copy / "bignum.fs").write_text(source.replace(text, change))
        line = first_difference([gforth, str(copy / "bignum.fs"), str(RUNNER), "-e",
                                 f's" {case_file}" run-cases bye'], expected, 120)
        how = f"case {line} differs" if 0 < line <= len(expected) else "the run failed"
        print(f"  planted fault {'caught' if line else 'MISSED'} ({how}): {what}")
        caught += line > 0
    return caught


def lean_computes(op, a, b):
    """False where Lean's kernel refuses with an exception instead of
    computing (type_checker.cpp get_count_arg): an exponent above 2^32 - 1,
    whatever the base, and such a shift of a nonzero value. The library
    computes 0^e and 1^e there; refusing is the kernel integration's job."""
    if op == "pow":
        return b < (1 << 32)
    if op == "shl":
        return a == 0 or b < (1 << 32)
    return True


def lean_check(lean, directory, items, results, rng):
    """A sample of the cases, as kernel-decided equations; then the same with
    every right-hand side changed, which Lean must reject one by one."""
    sample = []
    for (op, a, b, limit), result in zip(items, results):
        small = len(str(a)) + len(str(b)) + len(result) < 25000
        if op in LEAN_NAMES and limit == LEAN_BITS and result != "full" and small \
                and lean_computes(op, a, b):
            sample.append((op, a, b, result))
    rng.shuffle(sample)
    by_op = {}
    for case in sample:
        by_op.setdefault(case[0], []).append(case)
    chosen = [c for op in sorted(by_op) for c in by_op[op][:70]]
    big = [c for c in sample if len(str(c[1])) > 3000][:12]
    chosen += [c for c in big if c not in chosen]

    def equation(op, a, b, result, wrong=False):
        if result in ("true", "false"):
            value = {"true": "false", "false": "true"}[result] if wrong else result
        else:
            value = str(int(result) + 1) if wrong else result
        return f"example : {LEAN_NAMES[op]} {a} {b} = {value} := by decide +kernel\n"

    right = Path(directory) / "BignumRight.lean"
    right.write_text("".join(equation(*c) for c in chosen))
    done = subprocess.run([lean, "-DwarningAsError=true", str(right)], capture_output=True,
                          text=True, timeout=TEST_LIMIT)
    if done.returncode != 0:
        sys.stderr.write((done.stdout + done.stderr)[-3000:])
        raise SystemExit("Lean rejected a value the library computed")
    wrong = Path(directory) / "BignumWrong.lean"
    wrong.write_text("".join(equation(*c, wrong=True) for c in chosen))
    done = subprocess.run([lean, "-DwarningAsError=true", "-DmaxErrors=100000", str(wrong)],
                          capture_output=True, text=True, timeout=TEST_LIMIT)
    # decide reports the proposition false, or (for Nat.pow) the kernel
    # refuses the proof term itself; either is Lean rejecting that line.
    refused = (r"BignumWrong\.lean:(\d+):\d+: error: (?:Tactic `decide` proved that the "
               r"proposition|\(kernel\) application type mismatch)")
    rejected = {int(m.group(1)) for m in re.finditer(refused, done.stdout + done.stderr)}
    if done.returncode == 0 or rejected != set(range(1, len(chosen) + 1)):
        missing = sorted(set(range(1, len(chosen) + 1)) - rejected)
        output = done.stdout + done.stderr
        if missing:
            at = output.find(f"BignumWrong.lean:{missing[0]}:")
            sys.stderr.write(output[at:at + 600] if at >= 0 else output[-600:])
        raise SystemExit(f"Lean accepted {len(missing)} changed values, on lines {missing[:10]}")
    ops = sorted({c[0] for c in chosen})
    print(f"Lean 4.35.0's kernel (decide +kernel) agrees on {len(chosen)} cases "
          f"({len(ops)} operations, {len(big)} of more than 3,000 digits) "
          f"and rejects all {len(chosen)} with the result changed.")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--seed", type=int, default=20261102)
    parser.add_argument("--cases", type=int, default=24000)
    parser.add_argument("--lean", action="store_true")
    parser.add_argument("--no-faults", action="store_true")
    args = parser.parse_args()
    gforth = os.environ.get("GFORTH", "gforth")
    cases = Cases(args.seed)
    edge_cases(cases)
    limit_cases(cases)
    edges = len(cases.items)
    random_cases(cases, args.cases)
    items = cases.items
    expected = [expect("dec" if op == "dec0" else op, a, b, limit) for op, a, b, limit in items]
    with tempfile.TemporaryDirectory() as directory:
        case_file = Path(directory) / "cases.txt"
        case_file.write_text("".join(case_line(op, a, b) + "\n" for op, a, b, _ in items))
        lines = forth_lines(gforth, case_file)
        bad = compare(lines, expected, items)
        for line in bad[:20]:
            print("  " + line)
        if bad:
            raise SystemExit(f"{len(bad)} of {len(items)} cases differ from Python")
        counts = {}
        for op, *_ in items:
            counts[op] = counts.get(op, 0) + 1
        full = sum(1 for e in expected if e == "full")
        print(f"bignum: {len(items)} cases ({edges} edge, {len(items) - edges} random, "
              f"seed {args.seed}; {full} full) equal Python's integers: "
              + ", ".join(f"{op} {counts[op]}" for op in sorted(counts)))
        if not args.no_faults:
            fault_items = items[:edges]
            fault_file = Path(directory) / "fault-cases.txt"
            fault_file.write_text("".join(case_line(op, a, b) + "\n"
                                          for op, a, b, _ in fault_items))
            caught = planted(gforth, directory, fault_file, expected[:edges])
            if caught != len(FAULTS):
                raise SystemExit(f"only {caught} of {len(FAULTS)} planted faults caught")
            print(f"All {len(FAULTS)} planted faults were caught by the {edges} edge cases.")
        if args.lean:
            lean_check(lean_pin.pinned_lean(), directory, items, lines,
                       random.Random(args.seed + 1))


if __name__ == "__main__":
    main()
