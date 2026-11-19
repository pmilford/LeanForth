#!/usr/bin/env python3
"""The proof set's showcase (scripts/showcase-steps.sh and showcase-steps-format.py), so it
cannot break silently again (done check 2026-11-18-s2.md: it exited 1 and printed no steps).

1. The script on its default files and S2's slice of Init: exit 0 and its output equal to
   tests/front/showcase.golden (reviewed by reading it; --write writes it again). Every
   theorem of the golden has a verdict "accepted; axioms: none", and every tactic theorem
   its statement and steps.
2. A file whose check stops (tests/front/s2w-rw-definition.lf, rewriting by a definition,
   error 99): the script exits 1 and shows the error and exit 2.
3. The formatter fails closed: a step-log line that is not JSON, or a step without its
   source, exits 1; a wrong usage exits 1.
A self-test first checks that a changed golden line is told apart.

Usage: GFORTH=... python3 tests/front/check_showcase.py [--write]
"""
import os
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent.parent
GOLDEN = ROOT / "tests/front/showcase.golden"
SCRIPT = "scripts/showcase-steps.sh"
FORMAT = "scripts/showcase-steps-format.py"
LIMIT = int(os.environ.get("TEST_TIMEOUT", "600"))
failures = []


def check(flag, what):
    if not flag:
        failures.append(what)
        print(f"FAIL: {what}")


def run(argv, stdin=""):
    done = subprocess.run(argv, cwd=ROOT, input=stdin, capture_output=True, text=True, timeout=LIMIT)
    return done.returncode, done.stdout, done.stderr


def differs(got, want):
    """The first line where GOT and WANT differ, or None."""
    a, b = got.splitlines(), want.splitlines()
    for n, (x, y) in enumerate(zip(a, b), 1):
        if x != y:
            return f"line {n}: got {x!r}, golden {y!r}"
    return None if len(a) == len(b) else f"{len(a)} lines, golden {len(b)}"


def golden_part(write):
    status, out, err = run(["bash", SCRIPT])
    check(status == 0, f"{SCRIPT} on the slice: exit {status}; {err.strip()[-300:]}")
    if write:
        GOLDEN.write_text(out)
        print(f"wrote {GOLDEN.relative_to(ROOT)}")
    want = GOLDEN.read_text()
    check(differs(want + "x", want) is not None, "self-test: a changed golden line is told apart")
    problem = differs(out, want)
    check(problem is None, f"the output differs from {GOLDEN.name}: {problem}")
    verdicts = [line for line in out.splitlines() if line.startswith("  Verdict: ")]
    check(len(verdicts) == 15, f"15 theorems shown, got {len(verdicts)}")
    check(all(line.endswith(": accepted; axioms: none") for line in verdicts),
          "every theorem accepted with no axiom")
    tactic = out.count("  Steps (")
    check(tactic == 14 and out.count("  Statement, as Lean prints the first goal:") == tactic,
          f"14 tactic theorems, each with its statement; got {tactic}")


def stopped_part():
    status, out, _ = run(["bash", SCRIPT, "tests/front/s2w-rw-definition.lf"])
    check(status == 1, f"a file whose check stops: script exit 1, got {status}")
    check("error 99 at line:col 8:3 (token `by-rw[`)" in out and "--- exit 2" in out,
          "the stopped file's error and exit 2 are shown")
    check("Verdict: none (the run stopped before it)" in out, "a theorem with no verdict says so")


def formatter_part():
    lf = "tests/front/s1-rfl.lf"
    head = ('{"tactic_steps":{"axioms":[],"cut":false,"declaration":"t",'
            '"format":"leanforth-tactic-steps","format_version":1,"open_parts":0,"steps":1}}\n')
    for name, text in (("a line that is not JSON", head + "{not json\n"),
                       ("a step without its source",
                        head + '{"goal_before":"⊢ 0 = 0","goals_after":[],"parent":0,"step":1,'
                               '"tactic":"rfl","word":"by-rfl"}\n')):
        status, _, err = run([sys.executable, FORMAT, lf, "0"], text)
        check(status == 1 and "malformed" in err, f"the formatter refuses {name}: exit {status}")
    status, _, _ = run([sys.executable, FORMAT, lf])
    check(status == 1, f"the formatter refuses a wrong usage: exit {status}")


def main():
    write = sys.argv[1:] == ["--write"]
    if sys.argv[1:] and not write:
        print(__doc__.split("Usage: ")[1].strip())
        return 2
    golden_part(write)
    stopped_part()
    formatter_part()
    if failures:
        print(f"check_showcase: {len(failures)} failed")
        return 1
    print("check_showcase: all tests passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
