#!/usr/bin/env python3
"""The front end's whnfCore, getStuckMVar? and inferType against pinned Lean (plan FE1c).

Each case is a term over Init's Nat, Prod, Eq and Quot (the slice
tests/front/whnf-slice.ndjson), free variables m z s k x a b, p : Prod Nat
Nat, a let variable g := fun y => s y, metavariables ?n ?h (unassigned)
and ?f := fun y => s y. Pinned Lean 4.35.0 (tests/front/whnf-cases.lean,
which this script writes with --write and checks is up to date) prints
Meta.whnfCore's result, getStuckMVar?'s answer or inferType's type;
LeanForth (tests/front/whnf-cases.fs: lf-whnf-core, lf-whnf-stuck,
lf-infer) prints its own.
The lines must be equal, except for the cases listed as gaps, where
LeanForth must answer unsupported (a fact or step not ported; the plan
item is named) and Lean's answer is shown. A harness self-test first checks
that a wrong line is told apart.

Lean's terms may hold metadata (mdata, such as the `borrowed` mark of
Nat.add's arguments) that lean4export leaves out, so LeanForth's library
never has it; Lean's lines mark it <md>, and a line equal once the marks
are dropped is counted and listed apart, as equal up to the export's
missing mdata (plan row FE1d2).

Usage: LEAN=... GFORTH=... python3 tests/front/check_whnf.py [--write]
"""
import os
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent.parent
LEAN = os.environ.get("LEAN", ".tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean")
GFORTH = os.environ.get("GFORTH", "gforth")
LIMIT = 300
LEAN_FILE = ROOT / "tests/front/whnf-cases.lean"

FVARS = "mzskxabpg"
MVARS = {"?n": "n", "?h": "h", "?f": "f", "?q": "q"}


def c(name, *levels):
    return ("c", name, levels)


def apps(f, *args):
    for a in args:
        f = ("app", f, a)
    return f


NAT, ZERO, SUCC, REC = c("Nat"), c("Nat.zero"), c("Nat.succ"), c("Nat.rec", 1)
PROD_REC, PROD_MK = c("Prod.rec", 1, 0, 0), c("Prod.mk", 0, 0)
LAM, LET, PROJ, SORT, PI = "lam", "let", "proj", "sort", "pi"
ADD = c("Nat.add")


def rec(*args):
    return apps(REC, "m", "z", "s", *args)


def pair(a, b):
    return apps(PROD_MK, NAT, NAT, a, b)


SFUN = (LAM, NAT, apps("s", "#0"))


# (kind, term, gap): kind "whnf" (whnfCore), "stuck" (getStuckMVar?),
# "infer" (inferType) or "ibeta" (Expr.instantiateBetaRevRange of a body
# and its arguments, given as (body, [a0, ...]));
# gap: None, or the plan item that closes it (LeanForth answers unsupported).
CASES = [
    ("whnf", rec(apps(SUCC, "k")), None),
    ("whnf", rec(ZERO), None),
    ("whnf", rec("k"), None),
    ("whnf", apps(REC, "m", "z", "s"), None),
    ("whnf", rec(ZERO, "x"), None),
    ("whnf", rec(SUCC), None),
    ("whnf", rec("?n"), None),
    ("whnf", rec(apps(SUCC, "?n")), None),
    # reduceRec's clean-up (S2 merge B): cleanupNatOffsetMajor and
    # toCtorIfLit.
    ("whnf", rec(apps(SUCC, apps(SUCC, "k"))), None),
    ("whnf", rec(apps(SUCC, apps(SUCC, apps(SUCC, "k")))), None),
    ("whnf", rec(("lit", 0)), None),
    ("whnf", rec(("lit", 3)), None),
    ("whnf", rec(apps(SUCC, ("lit", 3))), "S3 reduceNat? folding literals (Nat.succ 3)"),
    ("whnf", apps(PROD_REC, NAT, NAT, "m", "s", apps(PROD_MK, NAT, NAT, "a", "b")), None),
    ("whnf", apps(PROD_REC, NAT, NAT, "m", "s", "p"), "FE1c inferType (toCtorWhenStructure)"),
    ("whnf", apps((LAM, NAT, "#0"), "k"), None),
    ("whnf", apps((LAM, NAT, (LAM, NAT, "#1")), "a", "b"), None),
    ("whnf", (LET, NAT, "k", apps("s", "#0")), None),
    ("whnf", apps((LET, NAT, "s", "#0"), "k"), None),
    ("whnf", apps("?f", "k"), None),
    ("whnf", apps("?h", "k"), None),
    ("whnf", apps("g", "k"), None),
    ("whnf", "g", None),
    ("whnf", "?f", None),
    ("whnf", apps(ADD, "k", "k"), None),
    ("whnf", apps(SUCC, "k"), None),
    ("whnf", apps(c("Classical.choice", 1), NAT, "x"), None),
    ("whnf", apps(c("Eq.rec", 1, 1), NAT, "a", "m", "x", "a", apps(c("Eq.refl", 1), NAT, "a")),
     "FE1c inferType and isDefEq (toCtorWhenK)"),
    ("whnf", apps(c("Quot.lift", 1, 1), NAT, "x", NAT, "s", "b", apps(c("Quot.mk", 1), NAT, "x", "a")),
     "FE1c quotient reduction (reduceQuotRec)"),
    ("whnf", (PROJ, 0, pair("a", "b")), None),
    ("whnf", (PROJ, 1, pair("a", "b")), None),
    ("whnf", (PROJ, 0, "p"), None),
    ("whnf", (PROJ, 2, pair("a", "b")), None),
    ("whnf", apps((PROJ, 0, pair(SFUN, "b")), "k"), None),
    ("whnf", (PROJ, 0, apps(SUCC, "k")), None),
    ("whnf", (PROJ, 0, apps(ADD, "k", "k")), "FE1d2 smart unfolding and matcher facts"),
    # A projection's structure by whnf (proj := yesWithDelta, S2 merge A):
    # the instance unfolds to its constructor, the field is taken.
    ("whnf", (PROJ, 0, apps(c("instHAdd", 0), NAT, c("instAddNat"))), None),
    ("whnf", apps((PROJ, 0, apps(c("instHAdd", 0), NAT, c("instAddNat"))), "k", "x"), None),
    ("whnf", rec(apps(c("id", 1), NAT, ZERO)), None),
    ("whnf", rec((LET, NAT, "k", apps(SUCC, "#0"))), None),
    ("whnf", rec(apps((LAM, NAT, "#0"), "k")), None),
    ("whnf", rec(apps(REC, "m", apps(SUCC, "z"), "s", ZERO)), None),
    ("whnf", rec(apps(ADD, "k", "k")), "FE1d2 smart unfolding and matcher facts"),
    ("infer", ADD, None),
    ("infer", apps(ADD, "k"), None),
    ("infer", apps(ADD, "k", "k"), None),
    ("infer", rec("k"), None),
    ("infer", "k", None),
    ("infer", "?n", None),
    ("infer", "g", None),
    ("infer", NAT, None),
    ("infer", (SORT, 0), None),
    ("infer", apps(SUCC, "k"), None),
    ("infer", apps(c("Eq.refl", 1), NAT, "a"), None),
    ("infer", c("HAdd.hAdd", 0, 0, 0), None),
    ("infer", apps(c("HAdd.hAdd", 0, 0, 0), NAT, NAT, NAT,
                   apps(c("instHAdd", 0), NAT, c("instAddNat")), "k", "k"), None),
    ("infer", pair("a", "b"), None),
    ("infer", c("Quot.lift", 1, 1), None),
    ("infer", c("Quot.lift", 1, 2), None),
    ("infer", (LAM, NAT, "#0"), None),
    ("infer", (LAM, NAT, (LAM, NAT, "#1")), None),
    ("infer", (LAM, NAT, apps(c("Eq.refl", 1), NAT, "#0")), None),
    ("infer", (LAM, NAT, "?n"), None),
    ("infer", (LAM, NAT, (LAM, apps(c("Eq", 1), NAT, "#0", "#0"), "#0")), None),
    ("infer", (PI, NAT, NAT), None),
    ("infer", (PI, NAT, apps(c("Eq", 1), NAT, "#0", "#0")), None),
    ("infer", (PI, (SORT, 0), (SORT, 0)), None),
    ("infer", (PI, (SORT, 1), NAT), None),
    ("infer", (PI, (PI, NAT, NAT), NAT), "FE1c a nested telescope for a pi domain"),
    ("infer", (PROJ, 0, pair("a", "b")), "FE1c inferProjType"),
    ("infer", (LET, NAT, "k", "#0"), "FE1c inferLambdaType for let"),
    ("infer", apps(REC, (LAM, NAT, NAT), "z", "s", "k"), None),
    ("infer", apps(REC, (LAM, NAT, apps(c("Eq", 1), NAT, "#0", "#0")), "z", "s", "k"), None),
    # Under a binder of the type, the loose argument is put in where the
    # motive's body has no binder around it (plan FE1g-4); the case that
    # needs Lean's liftLooseBVars is tests/front/infer.fs's (unsupported).
    ("infer", apps(REC, (LAM, NAT, NAT), "z", "s"), None),
    ("ibeta", ("#2", ["k"]), None),
    ("ibeta", ("#3", ["k"]), None),
    ("ibeta", ("#5", ["k", "a"]), None),
    ("ibeta", ((LAM, NAT, "#3"), ["k"]), None),
    ("ibeta", (apps("#0", "a"), [SFUN]), None),
    ("ibeta", (apps("#1", "#0", "#2"), ["a", SFUN]), None),
    ("ibeta", ((LAM, NAT, apps("#1", "#0")), [SFUN]), None),
    ("stuck", "?n", None),
    ("stuck", rec("?n"), None),
    ("stuck", rec("k"), None),
    ("stuck", apps("?h", "k"), None),
    ("stuck", apps("s", "k"), None),
    ("stuck", apps(ADD, "?n", "k"), None),  # projection records (s2-tactics)
    ("stuck", apps(ADD, "k", "k"), None),
    ("stuck", rec(apps(SUCC, "?n")), None),
    ("stuck", (PROJ, 0, "?q"), None),
    ("stuck", apps((PROJ, 0, "?q"), "k"), None),
    ("stuck", rec((LAM, NAT, "#0")), None),
    ("stuck", apps("?f", "k"), "FE1c instantiateMVars with beta (FE1b's beta step)"),
]


LEAN_LEVELS = {0: "Level.zero", 1: "(mkLevelSucc .zero)", 2: "(mkLevelSucc (mkLevelSucc .zero))"}
FORTH_LEVELS = {0: "l0", 1: "lv1", 2: "lv2"}


class Failure(Exception):
    pass


def lean(t):
    if isinstance(t, tuple) and t[0] == "c":
        levels = ", ".join(LEAN_LEVELS[l] for l in t[2])
        return f"(mkConst `{t[1]} [{levels}])"
    if isinstance(t, tuple) and t[0] == "app":
        return f"(mkApp {lean(t[1])} {lean(t[2])})"
    if isinstance(t, tuple) and t[0] == LAM:
        return f"(mkLambda `y .default {lean(t[1])} {lean(t[2])})"
    if isinstance(t, tuple) and t[0] == PROJ:
        return f"(mkProj `Prod {t[1]} {lean(t[2])})"
    if isinstance(t, tuple) and t[0] == SORT:
        return "(mkSort Level.zero)" if t[1] == 0 else "(mkSort (mkLevelSucc .zero))"
    if isinstance(t, tuple) and t[0] == "lit":
        return f"(mkRawNatLit {t[1]})"
    if isinstance(t, tuple) and t[0] == PI:
        return f"(mkForall `y .default {lean(t[1])} {lean(t[2])})"
    if isinstance(t, tuple):
        return f"(mkLet `y {lean(t[1])} {lean(t[2])} {lean(t[3])})"
    if t.startswith("#"):
        return f"(mkBVar {t[1:]})"
    return MVARS.get(t, t)


def forth(t):
    if isinstance(t, tuple) and t[0] == "c":
        levels = " ".join(FORTH_LEVELS[l] for l in t[2])
        return f'{levels} {len(t[2])} s" {t[1]}" cn'.strip()
    if isinstance(t, tuple) and t[0] == "app":
        return f"{forth(t[1])} {forth(t[2])} app"
    if isinstance(t, tuple) and t[0] == LAM:
        return f"{forth(t[1])} {forth(t[2])} lam"
    if isinstance(t, tuple) and t[0] == PROJ:
        return f"{forth(t[2])} {t[1]} proj"
    if isinstance(t, tuple) and t[0] == SORT:
        return "l0 sort" if t[1] == 0 else "lv1 sort"
    if isinstance(t, tuple) and t[0] == "lit":
        return f"{t[1]} nat-lit"
    if isinstance(t, tuple) and t[0] == PI:
        return f"{forth(t[1])} {forth(t[2])} tpi"
    if isinstance(t, tuple):
        return f"{forth(t[1])} {forth(t[2])} {forth(t[3])} let"
    if t.startswith("#"):
        return f"{t[1:]} bv"
    return t if t in MVARS else "f" + t


def lean_case(kind, t):
    if kind != "ibeta":
        return lean(t)
    body, args = t
    return f"{lean(body)} #[{', '.join(lean(a) for a in args)}]"


def forth_case(kind, t):
    """An ibeta case's arguments, the last first: bound variable 0's first."""
    if kind != "ibeta":
        return forth(t)
    body, args = t
    return f"{forth(body)} {' '.join(forth(a) for a in reversed(args))} {len(args)} rxs"


LEAN_HEAD = """import Lean
open Lean Meta

def pl (l : Level) : String := match l.toNat with
  | some n => toString n
  | none => "?l"

partial def sx : Expr → MetaM String
  | .bvar i => return s!"#{i}"
  | .const n us => return n.toString ++ ".{" ++ String.intercalate "," (us.map pl) ++ "}"
  | .fvar id => return (← id.getUserName).toString
  | .mvar id => return "?" ++ (← id.getDecl).userName.toString
  | .app f a => return s!"(app {← sx f} {← sx a})"
  | .lam _ t b _ => return s!"(lam {← sx t} {← sx b})"
  | .forallE _ t b _ => return s!"(pi {← sx t} {← sx b})"
  | .letE _ t v b _ => return s!"(let {← sx t} {← sx v} {← sx b})"
  | .proj _ i e => return s!"(proj {i} {← sx e})"
  | .sort l => return "Sort " ++ pl l
  | .mdata _ e => return s!"<md>{← sx e}"
  | e => return s!"?? {e}"

def whnfCase (e : Expr) : MetaM Unit := do IO.println (← sx (← whnfCore e))

def inferCase (e : Expr) : MetaM Unit := do IO.println (← sx (← inferType e))

def ibetaCase (e : Expr) (args : Array Expr) : MetaM Unit :=
  do IO.println (← sx (e.instantiateBetaRevRange 0 args.size args))

def stuckCase (e : Expr) : MetaM Unit := do
  match ← getStuckMVar? e with
  | some id => IO.println (← sx (mkMVar id))
  | none => IO.println "none"

def nat : Expr := mkConst ``Nat
"""

LEAN_SETUP = """run_meta do
  withLocalDeclD `m nat fun m => do
  withLocalDeclD `z nat fun z => do
  withLocalDeclD `s nat fun s => do
  withLocalDeclD `k nat fun k => do
  withLocalDeclD `x nat fun x => do
  withLocalDeclD `a nat fun a => do
  withLocalDeclD `b nat fun b => do
  withLocalDeclD `p (mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) nat nat) fun p => do
  let sfun := mkLambda `y .default nat (mkApp s (mkBVar 0))
  withLetDecl `g nat sfun fun g => do
    let n ← mkFreshExprMVar nat (userName := `n)
    let h ← mkFreshExprMVar nat (userName := `h)
    let f ← mkFreshExprMVar nat (userName := `f)
    let q ← mkFreshExprMVar nat (userName := `q)
    f.mvarId!.assign sfun
"""


def lean_source():
    calls = "\n".join(f"    {kind}Case {lean_case(kind, t)}" for kind, t, _ in CASES)
    return LEAN_HEAD + "\n" + LEAN_SETUP + calls + "\n"


def run(command):
    result = subprocess.run(command, cwd=ROOT, stdin=subprocess.DEVNULL, capture_output=True,
                            text=True, timeout=LIMIT)
    lines = [line.strip() for line in result.stdout.splitlines() if line.strip()]
    if result.returncode != 0 or len(lines) != len(CASES):
        raise Failure(f"{command[0]}: exit {result.returncode}\n{result.stdout}{result.stderr}")
    return lines


def lean_lines():
    if LEAN_FILE.read_text(encoding="utf-8") != lean_source():
        raise Failure(f"{LEAN_FILE.relative_to(ROOT)} differs from the cases: "
                      "python3 tests/front/check_whnf.py --write")
    return run([LEAN, "-DwarningAsError=true", str(LEAN_FILE.relative_to(ROOT))])


def forth_lines():
    calls = " ".join(f"{forth_case(kind, t)} {kind}-run" for kind, t, _ in CASES)
    return run([GFORTH, "tests/front/whnf-cases.fs", "-e", calls + " bye"])


def self_test():
    if lean(apps("s", "?n")) != "(mkApp s n)" or forth(apps("s", "?n")) != "fs ?n app":
        raise Failure("harness self-test: terms not written as expected")
    for want, got, gap in (("(app s k)", "(app k s)", None), ("none", "unsupported", None),
                           ("(app s k)", "(app s k)", "a gap"), ("x", "(app s k)", "a gap"),
                           ("(pi <md>Nat Nat)", "(pi Nat Nat Nat)", None)):
        try:
            judge("whnf", gap, want, got)
        except Failure:
            continue
        raise Failure(f"harness self-test: {want} / {got} (gap {gap}) not told apart")


def judge(name, gap, want, got):
    """None when the lines agree, the gap's text when LeanForth answers
    unsupported for a listed gap; else raise."""
    if gap:
        if got != "unsupported":
            raise Failure(f"{name}: a listed gap answers {got!r} (Lean: {want!r})")
        short = want if len(want) <= 40 else want[:37] + "..."
        return f"{short} ({gap})"
    if want.replace("<md>", "") != got:
        raise Failure(f"{name}:\n  Lean:      {want}\n  LeanForth: {got}")
    return None


def mdata_note(kind, gap, want):
    """The case's text when Lean's answer held metadata the export drops."""
    return None if gap or "<md>" not in want else f"{kind} {want.replace('<md>', '')}"


def main():
    if sys.argv[1:] == ["--write"]:
        LEAN_FILE.write_text(lean_source(), encoding="utf-8")
        return 0
    try:
        self_test()
        gaps, mdata = [], []
        for (kind, term, gap), want, got in zip(CASES, lean_lines(), forth_lines()):
            text = judge(f"{kind} {forth_case(kind, term)}", gap, want, got)
            if text:
                gaps.append(f"{kind} {text}")
            note = mdata_note(kind, gap, want)
            if note:
                mdata.append(note)
    except Failure as error:
        print(f"check_whnf: {error}")
        return 1
    print(f"whnfCore, getStuckMVar?, inferType and instantiateBetaRevRange: "
          f"{len(CASES) - len(gaps)} of {len(CASES)} "
          "cases equal to "
          f"pinned Lean's; {len(gaps)} gaps answer unsupported, Lean's answer shown: "
          f"{'; '.join(gaps)}; {len(mdata)} of the equal cases equal only once Lean's "
          f"mdata, which the export leaves out, is dropped: {'; '.join(mdata) or 'none'}; "
          "harness self-test passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
