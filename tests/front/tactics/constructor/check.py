#!/usr/bin/env python3
"""by-constructor end to end against pinned Lean (slice a2-iii;
src/front/tactics/constructor.fs, src/front/meta-tactic/constructor.fs):
the harness and its usage are tests/front/tactics/tactic_check.py's."""
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "tests/front/tactics"))
import tactic_check  # noqa: E402

D = "tests/front/tactics/constructor/"
FILES = [(D + "co-and.lf", ["co_and"]), (D + "co-true.lf", ["co_true"]),
         (D + "co-or.lf", ["co_or"]), (D + "co-le.lf", ["co_le"])]
WRONG = [(D + "w-co-false.lf", 383,
          "Tactic `constructor` failed: no applicable constructor found", "\n⊢ False"),
         (D + "w-co-not.lf", 382,
          "Tactic `constructor` failed: target is not an inductive datatype",
          "\na b : Nat\n⊢ ¬a = b")]
UNSUPPORTED = []

if __name__ == "__main__":
    tactic_check.main("constructor", FILES, WRONG, UNSUPPORTED)
