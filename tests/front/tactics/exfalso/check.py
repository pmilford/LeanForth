#!/usr/bin/env python3
"""by-exfalso end to end against pinned Lean (plan row TB1; src/front/tactics/exfalso.fs,
src/front/meta-tactic/goal.fs's lf-goal-exfalso): the harness and its usage are
tests/front/tactics/tactic_check.py's."""
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "tests/front/tactics"))
import tactic_check  # noqa: E402

D = "tests/front/tactics/exfalso/"
FILES = [(D + "ex-exact.lf", ["ex_exact"]), (D + "ex-assumption.lf", ["ex_assumption"]),
         (D + "ex-tag.lf", ["ex_tag"])]
WRONG = [(D + "w-ex-exact.lf", 96, "Type mismatch",
          "  h\nhas type\n  a ≤ b\nbut is expected to have type\n  False")]
UNSUPPORTED = []

if __name__ == "__main__":
    tactic_check.main("exfalso", FILES, WRONG, UNSUPPORTED)
