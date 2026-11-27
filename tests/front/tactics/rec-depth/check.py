#!/usr/bin/env python3
"""The runner's bound on Lean's recursion depth, end to end (re-check of the Forth review of
small-tactics-1, finding 1; src/front/tactic-run.fs's lf-tac-depth-most). Plain: u-rd-try.lf
(36 by-try around 126 by-iterate), u-rd-have.lf (40 nested by-have-by:, no iterate) and
u-rd-wr.lf (119 nested by-with-reducible) through bin/leanforth check against decide's slice
of Init: exit 2, error 99, never accepted (the
harness of tests/front/tactics/tactic_check.py). With --lean: pinned Lean accepts every
theorem of rec-depth.lean, the deepest nesting of each block it takes, and refuses every
theorem of rec-depth-wrong.lean, one level deeper, with "maximum recursion depth has been
reached". The unit tests on both sides of LeanForth's bound are test.fs's.

Usage: GFORTH=... python3 tests/front/tactics/rec-depth/check.py
       LEAN=... python3 tests/front/tactics/rec-depth/check.py --lean"""
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "tests/front/tactics"))
import tactic_check  # noqa: E402

s2 = tactic_check.s2
D = "tests/front/tactics/rec-depth/"
ENV = tactic_check.Env("tests/front/decide-slice.ndjson", "tests/front/decide-slice.elab.ndjson",
                       "decide-dump")
UNSUPPORTED = [(D + "u-rd-try.lf", 99, "not supported yet"),
               (D + "u-rd-have.lf", 99, "not supported yet"),
               (D + "u-rd-wr.lf", 99, "not supported yet")]
DEPTH = "maximum recursion depth has been reached"


def theorems(path):
    """The theorems of a twin file, with their first lines."""
    lines = (ROOT / path).read_text(encoding="utf-8").splitlines()
    return [(number, match.group(1)) for number, line in enumerate(lines, 1)
            for match in [re.match(r"theorem (\S+)", line)] if match]


def failed(path, out):
    """Each theorem of path that an error of Lean's out names, with that error."""
    names = theorems(path)
    errors = {}
    for match in re.finditer(r":(\d+):\d+: error: (.*)", out):
        name = [n for line, n in names if line <= int(match.group(1))][-1]
        errors.setdefault(name, match.group(2))
    return names, errors


def check_lean():
    good, bad = D + "rec-depth.lean", D + "rec-depth-wrong.lean"
    done, wrong = s2.run_many([[s2.lean_binary(), source] for source in (good, bad)])
    if done.returncode != 0:
        raise tactic_check.Failure(f"{good}: exit {done.returncode}\n{done.stdout}{done.stderr}")
    names, errors = failed(bad, wrong.stdout + wrong.stderr)
    others = [n for _, n in names if not errors.get(n, "").startswith(DEPTH)]
    if wrong.returncode == 0 or others:
        raise tactic_check.Failure(f"{bad}: exit {wrong.returncode}, not refused so: {others}")
    return len(theorems(good)), len(names)


def main():
    try:
        if "--lean" in sys.argv:
            good, bad = check_lean()
            print(f"rec-depth --lean: pinned Lean accepts the {good} theorems of rec-depth.lean "
                  f"and refuses the {bad} of rec-depth-wrong.lean with {DEPTH!r}")
            return
        tactic_check.check_refused([], UNSUPPORTED, ENV)
        print(f"rec-depth: {len(UNSUPPORTED)} not supported yet (exit 2, error 99)")
    except tactic_check.Failure as exc:
        print(f"rec-depth: {exc}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
