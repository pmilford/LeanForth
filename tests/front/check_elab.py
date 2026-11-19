#!/usr/bin/env python3
"""The elaborator against pinned Lean (plan S1; src/front/elab-pending.fs,
elab-app.fs, elab-term.fs, elab-decl.fs; docs/design/S1_INTERFACE.md 11).

1. tests/front/s1-now.lf through `bin/leanforth check --env
   tests/front/s1-slice.ndjson --elab-data ...`: exit 0, every theorem
   accepted (S1's t : 0 + 0 = 0 by rfl among them), its #check lines
   printed as pinned Lean prints them (tests/front/s1-now.golden, the
   output of tests/front/s1-now.lean) except the printer gaps listed
   below; and the theorems' types and values, dumped by
   tests/front/elab-dump.fs, equal pinned Lean's node for node (the
   golden's S-expression lines).
2. S1's files (docs/design/S1_INTERFACE.md 11): s1-check.lf prints
   0 + 0 = 0 : Prop and exits 0 with nothing checked by the kernel;
   s1-rfl.lf is accepted, its t node for node the golden's t; the wrong
   twin s1-rfl-wrong.lf fails at by-rfl with Lean's message (exit 4).
3. --elab-fuel 3: exhausted, error 138, exit 3; its misuses refused (exit
   4); a text of only #check lines exits 0 with "nothing checked by the
   kernel"; #check inside a declaration is error 140 (exit 4).
4. MF2's rule: elaboration data with a wrong instance record under the
   root only a text's second theorem queries: the first theorem alone
   exits 0; both stop at the second (exit 4, error 115 naming the record).
A harness self-test first checks that a changed golden line is told apart.
With --lean: pinned Lean writes the golden again (--write-golden keeps
it) and it must be unchanged; the S1 twins give the answers above:
s1-check.lean prints 0 + 0 = 0 : Prop, s1-rfl.lean is accepted,
s1-rfl-wrong.lean fails with "Tactic `rfl` failed"; and pinned Lean's
isDefEq.delta trace unfolds outParam in the C17 and C1 statements as
often as LeanForth's golden traces (tests/front/s1-c17.trace,
s1-c1.trace) do: none and three times.

Usage: GFORTH=... python3 tests/front/check_elab.py
       LEAN=... GFORTH=... python3 tests/front/check_elab.py --lean [--write-golden]
"""
import os
import pathlib
import subprocess
import sys
import tempfile
import functools
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[2] / "scripts"))
import lean_pin  # noqa: E402  $LEAN or the pinned Lean, refused unrun when an elan proxy


@functools.lru_cache(maxsize=None)
def lean():
    """The Lean to run: scripts/lean_pin.py's pinned_lean ($LEAN, else this
    checkout's pinned toolchain), refused before it runs when it is an elan
    proxy or not Lean 4.35.0 (Forth review of reuse-b, finding 4)."""
    return lean_pin.pinned_lean()


ROOT = pathlib.Path(__file__).resolve().parent.parent.parent
GFORTH = os.environ.get("GFORTH", "gforth")
LIMIT = 600
SLICE = "tests/front/s1-slice.ndjson"
DATA = "tests/front/s1-slice.elab.ndjson"
NOW = "tests/front/s1-now.lf"
NOW_LEAN = "tests/front/s1-now.lean"
GOLDEN = ROOT / "tests/front/s1-now.golden"
THEOREMS = ["zero_eq", "zero_eq_term", "self_eq", "succ_eq", "succ_eq_exact", "t",
            "zero_eq_zero", "two_add_two", "add_self"]
# LeanForth's printer shows an implicit argument with @ where its binder's
# kind is not known (present/term-printer.fs; plan 8.6): the term is the
# same, the elaborated declarations are compared node for node.
PRINTER_GAPS = {"@Eq.refl Nat Nat.zero : Nat.zero = Nat.zero":
                "Eq.refl Nat.zero : Nat.zero = Nat.zero"}
# The S1 files, their Lean twins, the exit code and what both print.
RFL_WRONG = ("Tactic `rfl` failed: The left-hand side\n  0 + 0\nis not definitionally equal "
             "to the right-hand side\n  1\n\n\u22a2 0 + 0 = 1")
S1_FILES = [("tests/front/s1-check.lf", "tests/front/s1-check.lean", 0, "0 + 0 = 0 : Prop"),
            ("tests/front/s1-rfl.lf", "tests/front/s1-rfl.lean", 0, ""),
            ("tests/front/s1-rfl-wrong.lf", "tests/front/s1-rfl-wrong.lean", 4, RFL_WRONG)]
# The statements of C17 and C1 (tests/front/elab.fs's golden traces) and
# how often pinned Lean's lazy delta unfolds outParam in each.
DELTA = [("axiom c17 : 0 + 0 = 0", "tests/front/s1-c17.trace"),
         ("axiom c1 (n : Nat) : 0 + n = n", "tests/front/s1-c1.trace")]


class Failure(Exception):
    pass


def run(args, **kw):
    return subprocess.run(args, cwd=ROOT, stdin=subprocess.DEVNULL, capture_output=True,
                          text=True, timeout=LIMIT, env=dict(os.environ, GFORTH=GFORTH), **kw)


def check(path, *extra):
    done = run(["bin/leanforth", "check", "--env", SLICE, "--elab-data", DATA, *extra, path])
    return done.returncode, done.stdout + done.stderr


def dump(path):
    done = run([GFORTH, "tests/front/elab-dump.fs", "-e", f's" {path}" elab-dump bye'])
    if done.returncode != 0:
        raise Failure(f"elab-dump.fs {path}: exit {done.returncode}\n{done.stdout}{done.stderr}")
    return [line for line in done.stdout.splitlines() if " type " in line or " value " in line]


def golden():
    return GOLDEN.read_text(encoding="utf-8").splitlines()


def checks_of(lines):
    return [line for line in lines if " : " in line and " type " not in line
            and " value " not in line]


def terms_of(lines):
    return [line for line in lines if " type (" in line or " value (" in line]


def differ(got, want):
    if got == want:
        return None
    for i, (g, w) in enumerate(zip(got, want)):
        if g != w:
            return f"line {i + 1}:\n  LeanForth: {g}\n  Lean:      {w}"
    return f"{len(got)} lines, Lean has {len(want)}"


def self_test(want):
    wrong = list(want)
    wrong[0] = wrong[0].replace("Nat.zero", "Nat.succ", 1)
    if differ(wrong, want) is None:
        raise Failure("harness self-test: a changed line is not told apart")


def check_now(want):
    code, out = check(NOW)
    if code != 0:
        raise Failure(f"{NOW}: exit {code}\n{out}")
    for name in THEOREMS:
        if f"{name}: accepted" not in out:
            raise Failure(f"{NOW}: {name} not accepted\n{out}")
    printed = [PRINTER_GAPS.get(line, line) for line in checks_of(out.splitlines())]
    bad = differ(printed, checks_of(want))
    if bad:
        raise Failure(f"{NOW}: #check lines differ from pinned Lean's, {bad}")
    bad = differ(dump(NOW), terms_of(want))
    if bad:
        raise Failure(f"{NOW}: elaborated terms differ from pinned Lean's, {bad}")


def check_s1(want):
    for path, _, exit_code, said in S1_FILES:
        code, out = check(path)
        if code != exit_code or said not in out:
            raise Failure(f"{path}: exit {code}, expected {exit_code} with {said!r}\n{out}")
    code, out = check("tests/front/s1-check.lf")
    if "nothing checked by the kernel" not in out:
        raise Failure(f"s1-check.lf: the kernel checked something\n{out}")
    code, out = check("tests/front/s1-rfl.lf")
    if "t: accepted" not in out:
        raise Failure(f"s1-rfl.lf: t not accepted\n{out}")
    mine = [line for line in terms_of(want) if line.startswith("t ")]
    bad = differ(dump("tests/front/s1-rfl.lf"), mine)
    if bad or len(mine) != 2:
        raise Failure(f"s1-rfl.lf: t differs from pinned Lean's, {bad}")


def check_limits():
    code, out = check(NOW, "--elab-fuel", "3")
    if code != 3 or "error 138 at" not in out:
        raise Failure(f"--elab-fuel 3: exit {code}, expected 3 with error 138\n{out}")
    with tempfile.TemporaryDirectory() as work:
        only = pathlib.Path(work) / "only.lf"
        only.write_text("Nat.zero Nat.zero = #check\n", encoding="utf-8")
        code, out = check(str(only))
        if code != 0 or "nothing checked by the kernel" not in out:
            raise Failure(f"#check only: exit {code}\n{out}")
        inside = pathlib.Path(work) / "inside.lf"
        inside.write_text("theorem m Nat.zero Nat.zero = #check\nNat.zero Nat.zero = := by by-rfl "
                          "end m\n", encoding="utf-8")
        code, out = check(str(inside))
        if code != 4 or "error 140 at" not in out or "expected term" not in out:
            raise Failure(f"#check inside a declaration: exit {code}, expected 4 with 140\n{out}")
    for args, said in MISUSES:
        done = run(["bin/leanforth", "check", *args])
        if done.returncode != 4 or said not in done.stdout + done.stderr:
            raise Failure(f"leanforth check {' '.join(args)}: exit {done.returncode}, "
                          f"expected 4 with {said!r}\n{done.stdout}{done.stderr}")


# MF2's rule (docs/design/MATHLIB_FRONT.md 3): instance records are checked
# when first needed. tests/front/mul-wrong.elab.ndjson holds a wrong record
# (instMulNat, its class Add, filed under Mul's root) under the root only the
# second theorem queries: the first theorem alone is accepted (exit 0); the
# file with both stops at the second (exit 4) with the data error naming the
# record, and no theorem of the text is reported accepted.
REFUSED_DATA = "tests/front/mul-wrong.elab.ndjson"
REFUSED_ENV = "tests/front/whnf-slice.ndjson"
FIRST = "theorem t1\n  Nat explicit: n\n  Nat explicit: m\n  n m + n m + =\n:= by\n  by-rfl\nend t1\n"
SECOND = "theorem t2\n  Nat explicit: n\n  Nat explicit: m\n  n m * n m * =\n:= by\n  by-rfl\nend t2\n"
REFUSED = ("error 115 at line:col 14:1 (token `end`): elaboration data refused: an instance is "
           "filed under another root key than its class")


def refused_run(path):
    done = run(["bin/leanforth", "check", "--env", REFUSED_ENV, "--elab-data", REFUSED_DATA, path])
    return done.returncode, done.stdout + done.stderr


def check_refused():
    with tempfile.TemporaryDirectory() as work:
        first = pathlib.Path(work) / "first.lf"
        first.write_text(FIRST, encoding="utf-8")
        code, out = refused_run(str(first))
        if code != 0 or "t1: accepted" not in out:
            raise Failure(f"the first theorem alone on {REFUSED_DATA}: exit {code}, expected 0\n{out}")
        both = pathlib.Path(work) / "both.lf"
        both.write_text(FIRST + SECOND, encoding="utf-8")
        code, out = refused_run(str(both))
        named = REFUSED in out and "\n  instMulNat" in out
        if code != 4 or not named or ": accepted" in out:
            raise Failure(f"both theorems on {REFUSED_DATA}: exit {code}, expected 4 with "
                          f"{REFUSED!r} naming instMulNat and nothing accepted\n{out}")


# --elab-fuel's misuses: each refused before anything runs (exit 4).
MISUSES = (
    (["--elab-fuel", "5", SLICE], "--elab-fuel goes only with a LeanForth text (FILE.lf)"),
    (["--env", SLICE, "--elab-fuel", "x5", NOW], "not an elaboration fuel amount: x5"),
    (["--env", SLICE, "--elab-fuel", "9007199254740992", NOW],
     "an elaboration fuel above 9007199254740991: 9007199254740992"),
    (["--env", SLICE, NOW, "--elab-fuel"], "an option without its value: --elab-fuel"),
)


def lean(path):
    done = run([lean(), "-j", "2", "-DwarningAsError=true", path])
    return done.returncode, done.stdout + done.stderr


def check_lean(write):
    code, out = lean(NOW_LEAN)
    if code != 0:
        raise Failure(f"{NOW_LEAN}: exit {code}\n{out}")
    if write:
        GOLDEN.write_text(out, encoding="utf-8")
    elif out.splitlines() != golden():
        raise Failure(f"{NOW_LEAN}: pinned Lean's output is not {GOLDEN.name}")
    for _, twin, exit_code, said in S1_FILES:
        code, out = lean(twin)
        if said not in out or (code == 0) != (exit_code == 0):
            raise Failure(f"{twin}: exit {code}, expected {said!r}\n{out}")
    with tempfile.TemporaryDirectory() as work:
        for statement, trace in DELTA:
            probe = pathlib.Path(work) / "delta.lean"
            probe.write_text(f"set_option trace.Meta.isDefEq.delta true\n{statement}\n",
                             encoding="utf-8")
            code, out = lean(str(probe))
            theirs = out.count("unfoldLeft] outParam")
            ours = (ROOT / trace).read_text(encoding="utf-8").count("unfold outParam")
            if code != 0 or theirs != ours:
                raise Failure(f"{statement}: pinned Lean unfolds outParam {theirs} times, "
                              f"{trace} {ours} (exit {code})\n{out}")


def main():
    want = golden()
    self_test(want)
    if "--lean" in sys.argv:
        check_lean("--write-golden" in sys.argv)
        print(f"check_elab --lean: {NOW_LEAN} gives {GOLDEN.name}; the S1 twins give "
              f"the S1 files' answers; outParam unfolded in C17 and C1 as the golden traces "
              f"say; harness self-test passed")
        return
    check_now(want)
    check_s1(want)
    check_limits()
    check_refused()
    print(f"check_elab: {NOW}: {len(THEOREMS)} theorems accepted, their terms equal pinned "
          f"Lean's node for node, #check lines as Lean's ({len(PRINTER_GAPS)} printer gap); "
          f"{len(S1_FILES)} S1 files as Lean's (s1-rfl.lf's t node for node); --elab-fuel, "
          f"#check-only and #check-inside exits; a record refused at the second theorem's "
          f"query, the first alone accepted; harness self-test passed")


if __name__ == "__main__":
    try:
        main()
    except (Failure, subprocess.TimeoutExpired) as exc:
        print(f"check_elab: {exc}", file=sys.stderr)
        sys.exit(1)
