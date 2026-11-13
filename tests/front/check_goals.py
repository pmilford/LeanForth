#!/usr/bin/env python3
"""Goals as text against pinned Lean (plan FE1g-1; src/front/goal-print.fs,
docs/design/FE1G_TACTICS.md section 5.7).

tests/front/goals-print.lean puts `trace "=== NAME"` and `trace_state` at
goal states of the FE1 proofs and at the printing rules (groups, lets, a
have, tombstones with numbers, shadowing, no goals, tags); its output from
pinned Lean 4.35.0 is recorded in tests/front/goals-print.expected. The
twin tests/front/goals-print.fs builds the same states by hand and prints
them with LeanForth's goal printer. Each block must equal Lean's, except
for the gaps of the term printer listed in GAPS (plan 8.6), where the one
line that differs must be exactly the listed pair: Lean's line and
LeanForth's. A harness self-test first checks that a changed block is
told apart.

With --lean: pinned Lean on tests/front/goals-print.lean prints exactly
the recorded tests/front/goals-print.expected (--write records it).

Usage: GFORTH=... python3 tests/front/check_goals.py
       LEAN=... python3 tests/front/check_goals.py --lean [--write]
"""
import os
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent.parent
GFORTH = os.environ.get("GFORTH", "gforth")
LEAN = os.environ.get("LEAN", ".tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean")
LEAN_FILE = "tests/front/goals-print.lean"
EXPECTED = ROOT / "tests/front/goals-print.expected"
TWIN = "tests/front/goals-print.fs"
LIMIT = 300
MARK = "=== "

# Block name: (Lean's line, LeanForth's line, the plan item that closes it).
GAPS = {
    "t1.rewritten": ("⊢ (0 + k).succ = k + 1", "⊢ Nat.succ (0 + k) = k + 1",
                     "plan 8.6: Lean's dot notation for Nat.succ x (pp.fieldNotation)"),
    "g1": ("⊢ ∀ (m : Nat), m = m", "⊢ (m : Nat) → m = m",
           "plan 8.6: ∀ where Lean's isProp infers a Π's type (the printer's quick test)"),
    "g3": ("h : ∀ (k : Nat), k = n", "h : (k : Nat) → k = n",
           "plan 8.6: ∀ where Lean's isProp infers a Π's type (the printer's quick test)"),
}


class Failure(Exception):
    pass


def blocks(text):
    """The blocks of a trace output: name -> its lines, in order."""
    found = {}
    name = None
    for line in text.splitlines():
        if line.startswith(MARK):
            name = line[len(MARK):]
            if name in found:
                raise Failure(f"block {name} twice")
            found[name] = []
        elif name is not None:
            found[name].append(line)
    return found


def lean_text():
    run = subprocess.run([LEAN, LEAN_FILE], cwd=ROOT, stdin=subprocess.DEVNULL,
                         capture_output=True, text=True, timeout=LIMIT)
    if run.returncode != 0 or run.stderr:
        raise Failure(f"lean {LEAN_FILE}: exit {run.returncode}\n{run.stdout}{run.stderr}")
    return run.stdout


def twin_text():
    run = subprocess.run([GFORTH, TWIN], cwd=ROOT, stdin=subprocess.DEVNULL,
                         capture_output=True, text=True, timeout=LIMIT)
    if run.returncode != 0 or run.stderr:
        raise Failure(f"{TWIN}: exit {run.returncode}\n{run.stdout}{run.stderr}")
    return run.stdout


def compare(name, want, got):
    """None when the block agrees (or differs exactly by its listed gap)."""
    if want == got:
        return None if name not in GAPS else f"{name}: listed as a gap but equal"
    if name not in GAPS or len(want) != len(got):
        return f"{name}:\n  Lean:      {want}\n  LeanForth: {got}"
    lean, mine, _ = GAPS[name]
    diffs = [(a, b) for a, b in zip(want, got) if a != b]
    if diffs != [(lean, mine)]:
        return f"{name}: differs beyond its gap: {diffs}"
    return None


def check(want, got):
    if list(want) != list(got):
        raise Failure(f"blocks differ: Lean {list(want)}, LeanForth {list(got)}")
    problems = [p for p in (compare(n, want[n], got[n]) for n in want) if p]
    if problems:
        raise Failure("\n".join(problems))


def self_test(want):
    """A block with one character changed, and one gap line changed, are told apart."""
    name = next(iter(want))
    changed = dict(want, **{name: [line.replace("Nat", "Nut") for line in want[name]]})
    gap = next(iter(GAPS))
    wrong = dict(want, **{gap: [line + " " for line in want[gap]]})
    for bad in (changed, wrong):
        try:
            check(want, bad)
        except Failure:
            continue
        raise Failure("harness self-test: a changed block is not told apart")


def main(argv):
    if "--lean" in argv:
        text = lean_text()
        if "--write" in argv:
            EXPECTED.write_text(text, encoding="utf-8")
        if text != EXPECTED.read_text(encoding="utf-8"):
            raise Failure(f"pinned Lean no longer prints {EXPECTED.name}")
        print(f"check_goals.py --lean: {len(blocks(text))} blocks as recorded")
        return
    want = blocks(EXPECTED.read_text(encoding="utf-8"))
    self_test(want)
    got = blocks(twin_text())
    check(want, got)
    print(f"check_goals.py: {len(want)} blocks, {len(want) - len(GAPS)} equal to Lean's, "
          f"{len(GAPS)} differ by their listed gap")


if __name__ == "__main__":
    try:
        main(sys.argv[1:])
    except Failure as failure:
        print(f"check_goals.py: {failure}", file=sys.stderr)
        sys.exit(1)
