#!/usr/bin/env python3
"""The proof set's showcase (scripts/showcase-steps.sh and showcase-steps-format.py), so it
cannot break silently again (done check 2026-11-18-s2.md: it exited 1 and printed no steps).

1. The script on its default files and S2's slice of Init: exit 0 and its output equal to
   tests/front/showcase.golden (reviewed by reading it; --write writes it again). Every
   theorem of the golden has a verdict "accepted; axioms: none", and every tactic theorem
   its statement and steps, and every theorem the same theorem in Lean (from
   tests/front/lean-twins.json) or "no Lean twin recorded"; no label says Lean did the work.
2. A file whose check stops (tests/front/s2w-rw-definition.lf, rewriting by a definition,
   error 99): the script exits 1 and shows the error and exit 2.
3. The formatter fails closed: a step-log line that is not JSON, or a step without its
   source, exits 1; a wrong usage exits 1.
A self-test first checks that a changed golden line is told apart.

Usage: GFORTH=... python3 tests/front/check_showcase.py [--write]
"""
import os
import pathlib
import re
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
    lines = out.splitlines()
    theorems = [n for n, line in enumerate(lines) if line.startswith("Theorem ")]
    check(len(theorems) == 15, f"15 theorems shown, got {len(theorems)}")
    verdicts = [lines[n + 2] for n, line in enumerate(lines)
                if line.startswith("D. The verdict of LeanForth's kernel")]
    check(len(verdicts) == 15 and all(line.endswith(": accepted; axioms: none") for line in verdicts),
          f"every theorem accepted with no axiom; got {len(verdicts)} verdicts")
    for part in ("A. The proof in LeanForth", "B. The same proof in Lean", "C. What LeanForth did",
                 "D. The verdict of LeanForth's kernel"):
        check(sum(line.startswith(part) for line in lines) == 15, f"each theorem has its part {part[:2]}")
    tactic = out.count("\\ The statement of A as LeanForth read it. This is the first goal:")
    check(tactic == 14 and out.count("\\ step 1 (") == tactic, f"14 tactic theorems, each with its statement; got {tactic}")
    twins = out.count("-- copied from tests/front/")
    noted = out.count("no test compares it with Lean yet")
    check(twins == 14 and noted == 1 and "no Lean twin is recorded" not in out,
          f"each theorem shows its Lean form (14 twins, 1 from its file's note): got {twins}, {noted}")
    check(out.count("Not LeanForth's output; Lean is not run") == 15, "the Lean part says it is not LeanForth's output")
    check("[Lean:" not in out and "as Lean prints" not in out, "no label says Lean did the work")
    check(not any(re.match(r"\s+\d+\s+(\||theorem|:=|end)\b", line) for line in lines),
          "no line number is mixed into the LeanForth text")
    explained = [line for line in lines if re.match(r"\s*(After|Goal|The goal|First|Then|Step \d)", line)]
    check(not explained, f"explanations are comments on the right, not lines of their own: {explained[:1]}")


def stopped_part():
    status, out, _ = run(["bash", SCRIPT, "tests/front/s2w-rw-definition.lf"])
    check(status == 1, f"a file whose check stops: script exit 1, got {status}")
    check("error 99 at line:col 8:3 (token `by-rw[`)" in out and "    exit status 2" in out,
          "the stopped file's error and exit status 2 are shown")
    check("\\ None: the run stopped before the kernel was given this theorem." in out,
          "a theorem with no verdict says so")


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
