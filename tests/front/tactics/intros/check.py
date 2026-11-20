#!/usr/bin/env python3
"""by-intros end to end against pinned Lean (plan row TB1; src/front/tactics/intros.fs,
src/front/meta-tactic/goal.fs's lf-goal-intros): the harness and its usage are
tests/front/tactics/tactic_check.py's. Also by-intro and by-intros on implicit and
strict-implicit binders, which no LeanForth text can state yet: implicit.fs builds the goals,
introduces and closes them with the tactics' goal words, and prints each term and its lambdas'
binder kinds, which must equal pinned Lean's lines of goal-layer.golden (in_implicit, in_strict,
is_implicit)."""
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "tests/front"))
sys.path.insert(0, str(ROOT / "tests/front/tactics"))
import check_s2 as s2  # noqa: E402
import tactic_check  # noqa: E402

D = "tests/front/tactics/intros/"
FILES = [(D + "is-or.lf", ["is_or"]), (D + "is-none.lf", ["is_none"])]
WRONG = [(D + "w-is-not.lf", 381, "Tactic `assumption` failed", "\na b : Nat\n⊢ ¬a = b")]
UNSUPPORTED = []
IMPLICIT = ["in_implicit", "in_strict", "is_implicit"]


def implicit(want):
    """implicit.fs's lines against pinned Lean's, three per theorem."""
    done = s2.run([s2.GFORTH, D + "implicit.fs"])
    lines = [line for line in done.stdout.splitlines() if tactic_check.DUMPED.match(line)]
    if done.returncode != 0 or len(lines) != 3 * len(IMPLICIT):
        raise tactic_check.Failure(f"implicit.fs: exit {done.returncode}\n{done.stdout}{done.stderr}")
    for line in lines:
        key = " ".join(line.split(" ", 2)[:2])
        if key.split()[0] not in IMPLICIT or want.get(key) != line:
            raise tactic_check.Failure(f"implicit.fs: {key} differs from pinned Lean's:\n"
                                       f"  LeanForth: {line}\n  Lean:      {want.get(key)}")
    return (f"{len(IMPLICIT)} goals with implicit and strict-implicit binders introduced as "
            f"pinned Lean's, terms and binder kinds")


if __name__ == "__main__":
    tactic_check.main("intros", FILES, WRONG, UNSUPPORTED, implicit)
