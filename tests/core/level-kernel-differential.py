"""Random universe levels: LeanForth against pinned Lean 4.35.0's kernel.

Usage: python3 tests/core/level-kernel-differential.py   (from the repository
root; LEAN and GFORTH name the toolchains). Run by
tests/core/level-compare-differential.sh (make check).

For pairs (a, b) of random levels over the parameters u, v and w, it asks
Lean's kernel three things and LeanForth the same three (ADR 0011,
Amendment 1):

* is_equivalent(a, b): Lean's Kernel.isDefEq on Sort a and Sort b, which
  quick_is_def_eq decides by is_equivalent (type_checker.cpp 810-811);
  LeanForth's lf-level-equivalent (level-normalize.fs);
* mk_max(a, b): the type Kernel.check gives LFM.{a, b} for an axiom
  LFM.{p, q} : Sort (max p q + 1), which instantiate rebuilds with mk_max
  (level.cpp 308-315; the arguments are new objects, so nothing is kept);
  LeanForth's lf-level-mk-max (level-make.fs);
* mk_imax(a, b): the sort Kernel.check gives (x : A) → B under
  A : Sort a, B : Sort b (infer_pi, type_checker.cpp 163); LeanForth's
  lf-level-mk-imax.

The levels are printed in prefix text (z, s l, m l l, i l l, p name), as
tests/reference/first-checker-terms.lean prints them, and must agree byte
for byte. The pairs are seeded, so every run checks the same ones; half
of the second levels are variations of the first (arguments swapped, a
zero added, imax for max), so both answers of is_equivalent occur often.
Test-only; it accepts no theorem.
"""
import os
from pathlib import Path
import random
import subprocess
import sys
import tempfile
import pathlib
import functools
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[2] / "scripts"))
import lean_pin  # noqa: E402  $LEAN or the pinned Lean, refused unrun when an elan proxy


@functools.lru_cache(maxsize=None)
def lean():
    """The Lean to run: scripts/lean_pin.py's pinned_lean ($LEAN, else this
    checkout's pinned toolchain), refused before it runs when it is an elan
    proxy or not Lean 4.35.0 (Forth review of reuse-b, finding 4)."""
    return lean_pin.pinned_lean()


GFORTH = os.environ.get("GFORTH", "gforth")
SEEDS = (11, 23, 47)
PAIRS = 600          # per seed
PARAMS = ("u", "v", "w")


def leaf(rng):
    return rng.choice([("z",), ("s", ("z",)), ("p", "u"), ("p", "v"), ("p", "w")])


def level(rng, size):
    if size <= 1:
        return leaf(rng)
    kind = rng.choice("ssmmii")
    if kind == "s":
        return ("s", level(rng, size - 1))
    left = rng.randint(1, size - 2) if size > 2 else 1
    return (kind, level(rng, left), level(rng, max(1, size - 1 - left)))


def vary(rng, lv):
    """A level near lv: the same, max arguments swapped, max with 0, imax
    and max exchanged, or a successor moved, at some node."""
    tag = lv[0]
    roll = rng.random()
    if tag in "mi" and roll < 0.25:
        return (tag, lv[2], lv[1])
    if roll < 0.35:
        return ("m", ("z",), lv) if rng.random() < 0.5 else ("m", lv, ("z",))
    if tag in "mi" and roll < 0.5:
        return ("i" if tag == "m" else "m", lv[1], lv[2])
    if tag == "s":
        return ("s", vary(rng, lv[1]))
    if tag in "mi":
        side = rng.randint(1, 2)
        parts = list(lv)
        parts[side] = vary(rng, parts[side])
        return tuple(parts)
    return lv


def text(lv):
    tag = lv[0]
    if tag == "z":
        return "z"
    if tag == "p":
        return "p " + lv[1]
    return " ".join([tag] + [text(child) for child in lv[1:]])


def pairs():
    cases = []
    for seed in SEEDS:
        rng = random.Random(seed)
        for _ in range(PAIRS):
            a = level(rng, rng.randint(1, 9))
            b = vary(rng, a) if rng.random() < 0.5 else level(rng, rng.randint(1, 9))
            cases.append((text(a), text(b)))
    return cases


LEAN_SOURCE = r'''import Lean
open Lean Elab Command

partial def parse : List String → Option (Level × List String)
  | "z" :: r => some (.zero, r)
  | "s" :: r => do let (l, r) ← parse r; pure (.succ l, r)
  | "m" :: r => do let (a, r) ← parse r; let (b, r) ← parse r; pure (.max a b, r)
  | "i" :: r => do let (a, r) ← parse r; let (b, r) ← parse r; pure (.imax a b, r)
  | "p" :: n :: r => some (.param (.mkSimple n), r)
  | _ => none

def levelText : Level → String
  | .zero => "z"
  | .succ l => "s " ++ levelText l
  | .max a b => "m " ++ levelText a ++ " " ++ levelText b
  | .imax a b => "i " ++ levelText a ++ " " ++ levelText b
  | .param n => "p " ++ n.toString
  | .mvar _ => "?"

def level (s : String) : Level :=
  match parse (s.splitOn " ") with
  | some (l, []) => l
  | _ => panic! s!"bad level {s}"

def lfmType : Expr := .sort (.succ (.max (.param `p) (.param `q)))
def lfm : Declaration :=
  .axiomDecl { name := `LFM, levelParams := [`p, `q], type := lfmType, isUnsafe := false }

def cases : List (String × String) := CASES

def mkMax (env : Environment) (a b : Level) : String :=
  match Kernel.check env {} (.const `LFM [a, b]) with
  | .ok (.sort (.succ l)) => levelText l
  | _ => "error"

def mkImax (env : Environment) (a b : Level) : String :=
  let e : Expr := .lam `A (.sort a) (.lam `B (.sort b)
    (.forallE `x (.bvar 1) (.bvar 1) .default) .default) .default
  match Kernel.check env {} e with
  | .ok (.forallE _ _ (.forallE _ _ (.sort l) _) _) => levelText l
  | _ => "error"

def equivalent (env : Environment) (a b : Level) : String :=
  match Kernel.isDefEq env {} (.sort a) (.sort b) with
  | .ok true => "1"
  | .ok false => "0"
  | .error _ => "error"

run_cmd do
  liftCoreM <| addDecl lfm
  let env ← getEnv
  for (c, i) in cases.zipIdx do
    let a := level c.1
    let b := level c.2
    IO.println s!"{i}|{equivalent env a b}|{mkMax env a b}|{mkImax env a b}"
'''

FORTH_DRIVER = r'''
\ For each case: the two levels read in prefix text, Lean's is_equivalent,
\ mk_max and mk_imax as LeanForth computes them, printed as Lean prints
\ them; every node of the case is given back afterwards.
: lk-.level ( level -- )
  lf-level-read must rot case
    lf-level-tag-zero of 2drop ." z" endof
    lf-level-tag-succ of drop ." s " recurse endof
    lf-level-tag-max of ." m " swap recurse space recurse endof
    lf-level-tag-imax of ." i " swap recurse space recurse endof
    lf-level-tag-param of drop ." p " lf-name-text type endof
    true abort" level-kernel: tag" endcase ;
: lk-equivalent ( a b -- ) 1000000 lf-level-equivalent ok? must 1 and 0 .r ;
: lk-made ( level true | false -- ) must lk-.level ;
: lk-case ( "i a b" -- )
  lf-level-count @ >r fc-number fc-read-level fc-read-level
  rot 0 .r ." |" 2dup lk-equivalent ." |" 2dup lf-level-mk-max lk-made ." |"
  lf-level-mk-imax lk-made cr r> lf-level-count ! ;
fc-world
'''


def lean_rows(cases, directory):
    source = LEAN_SOURCE.replace(
        "CASES", "[" + ",\n  ".join(f'("{a}", "{b}")' for a, b in cases) + "]")
    path = Path(directory) / "LevelKernel.lean"
    path.write_text(source)
    result = subprocess.run([lean(), "-DwarningAsError=true", str(path)], capture_output=True,
                            text=True, check=True)
    return result.stdout.splitlines()


def forth_rows(cases, directory):
    driver = Path("tests/support/first-checker-driver.fs").resolve()
    lines = [f"require {driver}", FORTH_DRIVER]
    lines += [f"lk-case {i} {a} {b}" for i, (a, b) in enumerate(cases)]
    lines.append("bye")
    path = Path(directory) / "level-kernel.fs"
    path.write_text("\n".join(lines) + "\n")
    result = subprocess.run([GFORTH, str(path)], capture_output=True, text=True,
                            stdin=subprocess.DEVNULL, check=True)
    return [line.strip() for line in result.stdout.splitlines() if "|" in line]


def main():
    cases = pairs()
    with tempfile.TemporaryDirectory() as directory:
        lean = lean_rows(cases, directory)
        forth = forth_rows(cases, directory)
    if len(lean) != len(cases) or len(forth) != len(cases):
        print(f"level kernel: {len(lean)} Lean and {len(forth)} Forth rows for "
              f"{len(cases)} cases", file=sys.stderr)
        return 1
    differ = [(c, l, f) for c, l, f in zip(cases, lean, forth) if l != f]
    for case, lrow, frow in differ[:10]:
        print(f"level kernel: {case}\n  Lean:  {lrow}\n  Forth: {frow}", file=sys.stderr)
    if differ or any("error" in row for row in lean):
        print(f"level kernel: {len(differ)} of {len(cases)} cases differ", file=sys.stderr)
        return 1
    equal = sum(row.split("|")[1] == "1" for row in lean)
    simplified = sum(row.split("|")[2] in (a, b) for (a, b), row in zip(cases, lean))
    print(f"{len(cases)} random level pairs agree with Lean's kernel: is_equivalent "
          f"({equal} equal, {len(cases) - equal} not), mk_max ({simplified} gave an "
          "argument) and mk_imax.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
