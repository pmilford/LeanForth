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

Then unfoldDefinition? and whnf themselves (plan S2 merge A): for each term
case below, over the same slice and the variables of tests/front/check_whnf.py,
pinned Lean (tests/front/unfold-terms.lean, written with --write) prints
withTransparency m (unfoldDefinition? e) ("1" and the result, or "0") or
withTransparency m (whnf e), and LeanForth (tests/front/whnf-cases.fs:
lf-meta-unfold, lf-meta-whnf) its own; the lines must be equal (Lean's
error is LeanForth's invalid), except for the gaps listed, where LeanForth
answers unsupported and Lean's answer is shown (plan S2 merge B: smart
unfolding and reduceNat?'s guard).

Usage: LEAN=... GFORTH=... python3 tests/front/check_unfold.py [--write]
"""
import os
import pathlib
import subprocess
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import check_whnf as cw  # noqa: E402  (the term notation and the Lean setup)

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
    "instLTNat", "LT.lt", "propext", "Eq.ndrec_symm", "Eq.ndrecOn", "HEq.ndrec", "Fin.succ",
    "Lean.Syntax.rec",
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
  | .defnInfo _ => "definition" | .thmInfo _ => "theorem" | .axiomInfo _ => "ax" ++ "iom"
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


# ---- unfoldDefinition? and whnf on terms (plan S2 merge A).
c, apps, NAT = cw.c, cw.apps, cw.NAT
OUTP = c("outParam", 1)
INST = apps(c("instHAdd", 0), NAT, c("instAddNat"))
HADD3 = apps(c("HAdd.hAdd", 0, 0, 0), NAT, NAT, NAT, INST)
ADD_ADD = apps(c("Add.add", 0), NAT, c("instAddNat"))
SMART = "S2 merge B smart unfolding (Nat.add._sunfold)"
NAT_GUARD = "S2 merge B reduceNat?'s guard (Nat.add k x)"
CAN_UNFOLD = "S2 merge B canUnfoldAtMatcher and unfoldNestedDIte (whnfMatcher)"
MATCH1 = apps(c("Nat.add.match_1", 1), "m")
MODES = {"all": "all", "default": "default", "reducible": "reducible",
         "instances": "instances", "none": "none", "implicit": "implicit"}

# (kind, mode, term, gap): kind "unfold" (unfoldDefinition?) or "mwhnf"
# (whnf); gap None or the plan item that closes it.
TERMS = [
    ("unfold", "default", apps(OUTP, NAT), None),
    ("unfold", "reducible", apps(OUTP, NAT), None),
    ("unfold", "none", apps(OUTP, NAT), None),
    ("unfold", "default", OUTP, None),
    ("unfold", "all", apps(HADD3, "k", "x"), None),
    ("unfold", "default", apps(HADD3, "k", "x"), None),
    ("unfold", "reducible", apps(HADD3, "k", "x"), None),
    ("unfold", "instances", apps(HADD3, "k", "x"), None),
    ("unfold", "implicit", apps(HADD3, "k", "x"), None),
    ("unfold", "instances", HADD3, None),
    # unfoldProjInst?'s result with no projection at its head (the
    # instance argument missing: a lambda), and with universe arguments
    # other than the declaration's parameters: none (review s2-unfold-a).
    ("unfold", "instances", apps(c("HAdd.hAdd", 0, 0, 0), NAT, NAT, NAT), None),
    ("unfold", "instances", apps(c("HAdd.hAdd", 0, 0), NAT, NAT, NAT, INST, "k", "x"), None),
    ("unfold", "instances", apps(c("HAdd.hAdd", 0, 0, 0), NAT, NAT, NAT, "k", "k", "x"), None),
    ("unfold", "default", apps(c("HAdd.hAdd", 0, 0, 0), NAT, NAT, NAT, "k", "k", "x"), None),
    ("unfold", "reducible", apps(c("Prod.fst", 0, 0), NAT, NAT, cw.pair("a", "b")), None),
    ("unfold", "default", apps(c("outParam", 1, 1), NAT), None),
    ("unfold", "default", INST, None),
    ("unfold", "reducible", INST, None),
    ("unfold", "instances", INST, None),
    ("unfold", "default", apps(ADD_ADD, "k", "x"), None),
    ("unfold", "reducible", apps(ADD_ADD, "k", "x"), None),
    ("unfold", "instances", apps(ADD_ADD, "k", "x"), None),
    ("unfold", "default", c("instAddNat"), None),
    ("unfold", "default", apps(cw.ADD, "k", "x"), SMART),
    ("unfold", "default", cw.ADD, None),
    ("unfold", "default", apps(c("Nat.add.match_1", 1), "k"), None),
    ("unfold", "all", c("Nat.zero_add"), None),
    ("unfold", "default", c("Nat.div"), None),
    ("unfold", "default", apps(c("id", 1), NAT, "k"), None),
    ("unfold", "reducible", apps(c("id", 1), NAT, "k"), None),
    ("unfold", "default", "k", None),
    ("unfold", "default", (cw.LAM, NAT, "#0"), None),
    ("unfold", "default", c("motive"), None),
    ("unfold", "default", apps(c("motive"), "k"), None),
    ("mwhnf", "default", apps(OUTP, NAT), None),
    ("mwhnf", "default", INST, None),
    ("mwhnf", "reducible", INST, None),
    ("mwhnf", "instances", INST, None),
    ("mwhnf", "default", (cw.PROJ, 0, INST), None),
    ("mwhnf", "default", apps(c("id", 1), NAT, "k"), None),
    ("mwhnf", "default", apps(HADD3, "k", "x"), NAT_GUARD),
    ("mwhnf", "instances", apps(HADD3, "k", "x"), NAT_GUARD),
    ("mwhnf", "all", c("Nat.zero_add"), None),
    # reduceMatcher? and an auxiliary recursor's deltaBetaDefinition in
    # whnfCore (S2 merge B): Nat.add.match_1 and Nat.casesOn.
    ("mwhnf", "default", apps(MATCH1, "k", cw.ZERO, "z", "s"), None),
    ("mwhnf", "default", apps(MATCH1, "k", apps(cw.SUCC, "x"), "z", "s"), None),
    ("mwhnf", "default", apps(MATCH1, "k", "x", "z", "s"), None),
    ("mwhnf", "default", apps(MATCH1, "k", cw.ZERO, "z", "s", "a"), None),
    ("mwhnf", "all", apps(MATCH1, "k", ("lit", 2), "z", "s"), None),
    ("mwhnf", "default", apps(MATCH1, "k", cw.ZERO, "z"), None),
    ("mwhnf", "default", apps(c("Nat.casesOn", 1), "m", cw.ZERO, "z", "s"), None),
    ("mwhnf", "default", apps(c("Nat.casesOn", 1), "m", apps(cw.SUCC, "k"), "z", "s"), None),
    ("mwhnf", "reducible", apps(MATCH1, "k", cw.ZERO, "z", "s"), CAN_UNFOLD),
    ("mwhnf", "instances", apps(MATCH1, "k", cw.ZERO, "z", "s"), CAN_UNFOLD),
]

TERMS_FILE = ROOT / "tests/front/unfold-terms.lean"
TERMS_HEAD = """
def unfoldCase (m : TransparencyMode) (e : Expr) : MetaM Unit := do
  try
    match ← withTransparency m (unfoldDefinition? e) with
    | some e' => IO.println s!"1 {← sx e'}"
    | none => IO.println "0"
  catch _ => IO.println "error"

def mwhnfCase (m : TransparencyMode) (e : Expr) : MetaM Unit := do
  try IO.println (← sx (← withTransparency m (whnf e)))
  catch _ => IO.println "error"
"""


def terms_source():
    calls = "\n".join(f"    {kind}Case .{MODES[mode]} {cw.lean(t)}" for kind, mode, t, _ in TERMS)
    used = "    let _ := (m, z, s, k, x, a, b, p, g, n, h, f, q)\n"
    return cw.LEAN_HEAD + TERMS_HEAD + "\n" + cw.LEAN_SETUP + used + calls + "\n"


def terms_lines(command, source=None):
    if source is not None and TERMS_FILE.read_text(encoding="utf-8") != source:
        raise Failure(f"{TERMS_FILE.relative_to(ROOT)} differs from the cases: "
                      "python3 tests/front/check_unfold.py --write")
    result = subprocess.run(command, cwd=ROOT, stdin=subprocess.DEVNULL, capture_output=True,
                            text=True, timeout=LIMIT)
    lines = [line.strip() for line in result.stdout.splitlines() if line.strip()]
    if result.returncode != 0 or len(lines) != len(TERMS):
        raise Failure(f"{command[0]}: exit {result.returncode}\n{result.stdout}{result.stderr}")
    return lines


def terms_compare():
    """The term cases: a list of the gaps' texts; raise on a difference."""
    want = terms_lines([LEAN, "-DwarningAsError=true", str(TERMS_FILE.relative_to(ROOT))],
                       terms_source())
    calls = " ".join(f"{cw.forth(t)} lf-tr-{MODES[mode]} {kind}-run"
                     for kind, mode, t, _ in TERMS)
    got = terms_lines([GFORTH, "tests/front/whnf-cases.fs", "-e", calls + " bye"])
    gaps = []
    for (kind, mode, t, gap), w, g in zip(TERMS, want, got):
        w = w.replace("<md>", "")
        name = f"{kind} {mode} {cw.forth(t)}"
        if gap:
            if g != "unsupported":
                raise Failure(f"{name}: a listed gap answers {g!r} (Lean: {w!r})")
            gaps.append(f"{name[:50]} (Lean: {w[:60]}; {gap})")
        elif w != g and not (w == "error" and g == "invalid"):
            raise Failure(f"{name}:\n  Lean:      {w}\n  LeanForth: {g}")
    return gaps


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
        TERMS_FILE.write_text(terms_source(), encoding="utf-8")
        return 0
    try:
        self_test()
        gaps = []
        for lean, forth in zip(lean_lines(), forth_lines()):
            gaps += compare(lean, forth)
        term_gaps = terms_compare()
    except Failure as error:
        print(f"check_unfold: {error}")
        return 1
    print(f"Environment view: {len(NAMES)} declarations, kind, reducibility status and "
          f"{len(NAMES) * 12} unfolding answers (getUnfoldableConst? and canUnfold, six "
          f"transparency modes) equal to pinned Lean's; {len(NAMES) * 4 - len(gaps)} of "
          f"{len(NAMES) * 4} facts equal; {len(gaps)} answer unsupported (plan FE1d2), "
          f"by fact: {gap_summary(gaps)}; unfoldDefinition? and whnf: "
          f"{len(TERMS) - len(term_gaps)} of {len(TERMS)} term cases equal to pinned Lean's, "
          f"{len(term_gaps)} gaps answer unsupported: {'; '.join(term_gaps)}; "
          f"harness self-test passed")
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
