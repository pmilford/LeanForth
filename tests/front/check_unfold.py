#!/usr/bin/env python3
"""The front end's environment view against pinned Lean (plan FE1c; ADR 0021 D6, D10).

For each declaration below, pinned Lean 4.35.0 (tests/front/unfold-cases.lean,
which this script writes with --write and checks is up to date) and LeanForth
(tests/front/unfold-cases.fs, src/front/meta-env.fs over the Init slice
tests/front/whnf-slice.ndjson and its elaboration data) each print one line:
the name, its kind, its reducibility status, getUnfoldableConst? and
canUnfold under the six transparency modes, and four facts Lean's whnf asks
of definitions -- matcher, projection function, auxiliary recursor, smart
unfolding (a `_sunfold` definition). The lines must be equal, except that
LeanForth answers "?" (unsupported) for a fact the export and the
elaboration data do not carry yet: allowed only in the four facts of a
definition, counted and listed as gaps with Lean's answer (plan row FE1d2
closes them). A harness self-test first checks that a wrong line is told
apart.

Usage: LEAN=... GFORTH=... python3 tests/front/check_unfold.py [--write]
"""
import os
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent.parent
LEAN = os.environ.get("LEAN", ".tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean")
GFORTH = os.environ.get("GFORTH", "gforth")
LIMIT = 300
LEAN_FILE = ROOT / "tests/front/unfold-cases.lean"
FACTS = ["matcher", "projection", "aux-recursor", "smart-unfolding"]

# Declarations of the slice: every kind, every reducibility status, a
# matcher, an auxiliary recursor of each source, projections, instances.
NAMES = [
    "Nat.add", "HAdd.hAdd", "instHAdd", "instAddNat", "id", "Function.comp", "Nat.pred",
    "OfNat.ofNat", "instOfNatNat", "Prod.fst", "Prod.mk", "Prod", "Nat.casesOn", "Nat.rec",
    "Nat.div", "Nat.zero_add", "Classical.choice", "Quot.lift", "Quot", "Quot.mk", "Eq.ndrec",
    "Nat.below", "Nat.brecOn", "Nat.add.match_1", "Nat.add._f", "outParam", "Unit.unit", "Unit",
    "Nat", "Nat.succ", "Add.add", "HAdd.mk", "Eq.refl", "Nat.mul", "Nat.pow", "Nat.lt",
    "instLTNat", "LT.lt", "propext",
]

LEAN_HEAD = """import Lean
open Lean Meta

def modes : List TransparencyMode :=
  [.all, .default, .reducible, .instances, .none, .implicit]

def statusText : ReducibilityStatus → String
  | .reducible => "reducible" | .semireducible => "semireducible"
  | .irreducible => "irreducible" | .implicitReducible => "implicit_reducible"
  | .instanceReducible => "instance_reducible"

def kindText : ConstantInfo → String
  | .defnInfo _ => "definition" | .thmInfo _ => "theorem" | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quotient" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"

def bit (b : Bool) : String := if b then "1" else "0"

def unfoldCase (n : Name) : MetaM Unit := do
  let info ← getConstInfo n
  let mut s := s!"{n} {kindText info} {statusText (← getReducibilityStatus n)} "
  for m in modes do
    s := s ++ bit (← withTransparency m (getUnfoldableConst? n)).isSome
  s := s ++ " "
  for m in modes do
    s := s ++ bit (← withTransparency m (canUnfold info))
  let env ← getEnv
  s := s ++ " " ++ bit (← getMatcherInfo? n).isSome
  s := s ++ " " ++ bit (← getProjectionFnInfo? n).isSome
  s := s ++ " " ++ bit (isAuxRecursor env n)
  s := s ++ " " ++ bit (env.contains (mkSmartUnfoldingNameFor n))
  IO.println s
"""


class Failure(Exception):
    pass


def lean_source():
    calls = "\n".join(f"  unfoldCase `{name}" for name in NAMES)
    return LEAN_HEAD + "\nrun_meta do\n" + calls + "\n"


def run(command):
    result = subprocess.run(command, cwd=ROOT, stdin=subprocess.DEVNULL, capture_output=True,
                            text=True, timeout=LIMIT)
    lines = [line.strip() for line in result.stdout.splitlines() if line.strip()]
    if result.returncode != 0 or len(lines) != len(NAMES):
        raise Failure(f"{command[0]}: exit {result.returncode}\n{result.stdout}{result.stderr}")
    return lines


def lean_lines():
    if LEAN_FILE.read_text(encoding="utf-8") != lean_source():
        raise Failure(f"{LEAN_FILE.relative_to(ROOT)} differs from the cases: "
                      "python3 tests/front/check_unfold.py --write")
    return run([LEAN, "-DwarningAsError=true", str(LEAN_FILE.relative_to(ROOT))])


def forth_lines():
    calls = " ".join(f's" {name}" ucase' for name in NAMES)
    return run([GFORTH, "tests/front/unfold-cases.fs", "-e", calls + " bye"])


def compare(lean, forth):
    """None when equal, a list of (fact, Lean's answer) gaps when LeanForth
    answers ? only for a definition's facts, else raise."""
    want, got = lean.split(), forth.split()
    if len(want) != 9 or len(got) != 9 or want[:5] != got[:5]:
        raise Failure(f"differs:\n  Lean:      {lean}\n  LeanForth: {forth}")
    gaps = []
    for fact, w, g in zip(FACTS, want[5:], got[5:]):
        if g == w:
            continue
        if g != "?" or want[1] != "definition":
            raise Failure(f"{want[0]} {fact}: Lean {w}, LeanForth {g}")
        gaps.append(f"{want[0]} {fact} (Lean: {w})")
    return gaps


def self_test():
    good = "f definition reducible 111101 111101 0 0 0 0"
    for wrong in ("f definition reducible 111100 111101 0 0 0 0",
                  "f theorem reducible 111101 111101 0 0 0 0",
                  "f definition semireducible 111101 111101 0 0 0 0",
                  "f definition reducible 111101 111101 1 0 0 0"):
        try:
            compare(good, wrong)
        except Failure:
            continue
        raise Failure(f"harness self-test: {wrong} not told apart")
    try:
        compare(good.replace("definition", "inductive"), "f inductive reducible 111101 111101 ? 0 0 0")
    except Failure:
        return
    raise Failure("harness self-test: ? allowed for a non-definition")


def main():
    if sys.argv[1:] == ["--write"]:
        LEAN_FILE.write_text(lean_source(), encoding="utf-8")
        return 0
    try:
        self_test()
        gaps = []
        for lean, forth in zip(lean_lines(), forth_lines()):
            gaps += compare(lean, forth)
    except Failure as error:
        print(f"check_unfold: {error}")
        return 1
    print(f"Environment view: {len(NAMES)} declarations, kind, reducibility status and "
          f"{len(NAMES) * 12} unfolding answers (getUnfoldableConst? and canUnfold, six "
          f"transparency modes) equal to pinned Lean's; {len(NAMES) * 4 - len(gaps)} of "
          f"{len(NAMES) * 4} facts equal; {len(gaps)} answer unsupported (plan FE1d2), "
          f"by fact: {gap_summary(gaps)}; harness self-test passed")
    return 0


def gap_summary(gaps):
    """Per fact: how many definitions answer unsupported, and those for
    which Lean's answer is 1."""
    parts = []
    for fact in FACTS:
        mine = [g for g in gaps if g.split()[1] == fact]
        ones = [g.split()[0] for g in mine if g.endswith("(Lean: 1)")]
        parts.append(f"{fact} {len(mine)} (Lean 1 for: {', '.join(ones) or 'none'})")
    return "; ".join(parts)


if __name__ == "__main__":
    sys.exit(main())
