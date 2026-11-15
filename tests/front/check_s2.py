#!/usr/bin/env python3
"""S2's tactics against pinned Lean (plan S2, branch s2-tactics;
src/front/tactic-induction.fs, tactic-rewrite.fs, kabstract.fs,
meta-check.fs; docs/design/S2_INTERFACE.md 4, 5, 9 and appendix G).

1. FE1's rewriting form, the nested induction and the owner's proof set
   (FILES) through `bin/leanforth check --env tests/front/s2-slice.ndjson
   --elab-data tests/front/s2-slice.elab.ndjson`: exit 0, each theorem
   accepted with no axiom; their types and values, dumped by
   tests/front/elab-dump.fs (s2-dump), equal pinned Lean's node for node
   (tests/front/s2-proofs.golden, the output of tests/front/s2-proofs.lean).
2. The wrong proofs (WRONG, twins of tests/front/s2-wrong.lean's): exit 4,
   the error code and Lean's first message (the first lines of the error,
   as LeanForth prints them).
A harness self-test first checks that a changed golden line is told apart.
With --lean: pinned Lean writes the golden again (--write-golden keeps it)
and it must be unchanged, and pinned Lean refuses each wrong twin with the
message the LeanForth file must print.

Usage: GFORTH=... python3 tests/front/check_s2.py
       LEAN=... python3 tests/front/check_s2.py --lean [--write-golden]
"""
import os
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent.parent
GFORTH = os.environ.get("GFORTH", "gforth")
LEAN = os.environ.get("LEAN", ".tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean")
LIMIT = 600
SLICE = "tests/front/s2-slice.ndjson"
DATA = "tests/front/s2-slice.elab.ndjson"
GOLDEN = ROOT / "tests/front/s2-proofs.golden"
# Each file and the theorems it declares, in order.
FILES = [("tests/front/01-zero-add-rw.lf", ["zero_add''"]),
         ("tests/front/04-nested-ih.lf", ["zero_add_nested"]),
         ("tests/front/ps-succ-add.lf", ["ps_succ_add"]),
         ("tests/front/ps-add-comm.lf", ["ps_zero_add", "ps_succ_add", "ps_add_comm"]),
         ("tests/front/ps-mul-add.lf", ["ps_add_assoc", "ps_mul_add"]),
         ("tests/front/ps-length-append.lf", ["ps_zero_add", "ps_succ_add",
                                              "ps_length_append"])]
# The wrong twins: file, code, Lean's message as LeanForth prints it.
GOAL = "case succ\nk : Nat\nih : 0 + k = k\n\u22a2 0 + (k + 1) = k + 1"
WRONG = [("tests/front/s2w-pattern.lf", 215,
          "Tactic `rewrite` failed: Did not find an occurrence of the pattern",
          "  ?n * Nat.succ ?m\nin the target expression\n  0 + (k + 1) = k + 1\n\n" + GOAL),
         ("tests/front/s2w-alt-name.lf", 206, "Invalid alternative name `suc`: Expected `succ`",
          ""),
         ("tests/front/s2w-alt-missing.lf", 207, "Alternative `succ` has not been provided", ""),
         ("tests/front/s2w-alt-twice.lf", 213, "Duplicate alternative name `zero`", ""),
         ("tests/front/s2w-alt-names.lf", 208,
          "Too many variable names provided at alternative `succ`: 3 provided, but 2 expected",
          ""),
         ("tests/front/s2w-not-eq.lf", 218,
          "Invalid rewrite argument: Expected an equality or iff proof or definition name, "
          "but `k` is a value of type", "  Nat"),
         ("tests/front/s2w-rw-unsolved.lf", 89, "unsolved goals", "case succ\nk : Nat")]
# Pinned Lean's messages for the same proofs (tests/front/s2-wrong.lean),
# where its printer and LeanForth's agree (Lean prints (0 + k).succ,
# LeanForth Nat.succ (0 + k): plan 8.6).
LEAN_WRONG = ["Tactic `rewrite` failed: Did not find an occurrence of the pattern\n"
              "  ?n * Nat.succ ?m\nin the target expression\n  0 + (k + 1) = k + 1\n\n" + GOAL,
              "Invalid alternative name `suc`: Expected `succ`",
              "Alternative `succ` has not been provided",
              "Duplicate alternative name `zero`",
              "Too many variable names provided at alternative `succ`: 3 provided, but 2 expected",
              "Invalid rewrite argument: Expected an equality or iff proof or definition name, "
              "but `k` is a value of type\n  Nat",
              "unsolved goals\ncase succ\nk : Nat"]


class Failure(Exception):
    pass


def run(args):
    return subprocess.run(args, cwd=ROOT, stdin=subprocess.DEVNULL, capture_output=True,
                          text=True, timeout=LIMIT, env=dict(os.environ, GFORTH=GFORTH))


def check(path):
    done = run(["bin/leanforth", "check", "--env", SLICE, "--elab-data", DATA, path])
    return done.returncode, done.stdout + done.stderr


def dump(path):
    done = run([GFORTH, "tests/front/elab-dump.fs", "-e", f's" {path}" s2-dump bye'])
    if done.returncode != 0:
        raise Failure(f"elab-dump.fs {path}: exit {done.returncode}\n{done.stdout}{done.stderr}")
    return [line for line in done.stdout.splitlines() if " type " in line or " value " in line]


def golden():
    return {line.split(" ", 2)[0] + " " + line.split(" ", 2)[1]: line
            for line in GOLDEN.read_text(encoding="utf-8").splitlines()}


def self_test(want):
    if len(want) != 16:
        raise Failure(f"harness self-test: {len(want)} golden lines, expected 16")
    wrong = dict(want)
    key = next(iter(wrong))
    wrong[key] = wrong[key].replace("#0", "#1", 1)
    if wrong == want:
        raise Failure("harness self-test: a changed line is not told apart")


def check_files(want):
    for path, names in FILES:
        code, out = check(path)
        if code != 0:
            raise Failure(f"{path}: exit {code}\n{out}")
        for name in names:
            if f"\n{name}: accepted; axioms: none" not in "\n" + out:
                raise Failure(f"{path}: {name} not accepted with no axiom\n{out}")
        for line in dump(path):
            key = " ".join(line.split(" ", 2)[:2])
            if want.get(key) != line:
                raise Failure(f"{path}: {key} differs from pinned Lean's:\n  LeanForth: {line}\n"
                              f"  Lean:      {want.get(key)}")


def check_wrong():
    for path, number, message, detail in WRONG:
        code, out = check(path)
        line = f"error {number} at "
        if code != 4 or line not in out or message not in out or detail not in out:
            raise Failure(f"{path}: exit {code}, expected 4 with {line}{message!r} "
                          f"and {detail!r}\n{out}")


def check_lean(write):
    done = run([LEAN, "-DwarningAsError=true", "tests/front/s2-proofs.lean"])
    if done.returncode != 0:
        raise Failure(f"s2-proofs.lean: exit {done.returncode}\n{done.stdout}{done.stderr}")
    if write:
        GOLDEN.write_text(done.stdout, encoding="utf-8")
    elif done.stdout.splitlines() != GOLDEN.read_text(encoding="utf-8").splitlines():
        raise Failure("s2-proofs.lean: pinned Lean's output is not s2-proofs.golden")
    done = run([LEAN, "-DwarningAsError=true", "tests/front/s2-wrong.lean"])
    out = done.stdout + done.stderr
    missing = [text for text in LEAN_WRONG if text not in out]
    if done.returncode == 0 or missing:
        raise Failure(f"s2-wrong.lean: exit {done.returncode}, missing {missing}\n{out}")


def main():
    want = golden()
    self_test(want)
    if "--lean" in sys.argv:
        check_lean("--write-golden" in sys.argv)
        print(f"check_s2 --lean: s2-proofs.lean gives {GOLDEN.name}; s2-wrong.lean gives "
              f"the {len(LEAN_WRONG)} messages; harness self-test passed")
        return
    check_files(want)
    check_wrong()
    print(f"check_s2: {len(FILES)} files accepted, their {len(want)} type and value lines "
          f"equal pinned Lean's node for node; {len(WRONG)} wrong proofs refused with Lean's "
          f"messages; harness self-test passed")


if __name__ == "__main__":
    try:
        main()
    except (Failure, subprocess.TimeoutExpired) as exc:
        print(f"check_s2: {exc}", file=sys.stderr)
        sys.exit(1)
