#!/usr/bin/env python3
"""The front end's whnfCore, getStuckMVar?, inferType and term builders against pinned Lean.

Each case is a term over Init's Nat, Prod, Eq and Quot (the slice
tests/front/whnf-slice.ndjson), free variables m z s k x a b, p : Prod Nat
Nat, a let variable g := fun y => s y, metavariables ?n ?h (unassigned)
and ?f := fun y => s y. Pinned Lean 4.35.0 (tests/front/whnf-cases.lean,
which this script writes with --write and checks is up to date) prints
Meta.whnfCore's result, getStuckMVar?'s answer or inferType's type;
LeanForth (tests/front/whnf-cases.fs: lf-whnf-core, lf-whnf-stuck,
lf-infer) prints its own. Build cases (plan slice a2-i, the tactic
library): Meta/AppBuilder.lean's builders (mkEq, mkEqRefl, mkEqSymm,
mkEqTrans, mkExpectedPropHint, mkCongrArg, mkCongrFun, mkEqNDRec, mkAppM,
mkEqMP, mkEqMPR) against src/front/app-builder.fs's, over the free
variables e : a = b, u v : Nat -> Nat and w : u = v besides; an
AppBuilder exception prints "rejected", as LeanForth's rejected outcome.
The lines must be equal, except for the cases listed as gaps, where
LeanForth must answer unsupported (a fact or step not ported; the plan
item is named) and Lean's answer is shown. A harness self-test first checks
that a wrong line is told apart.

Lean's terms may hold metadata (mdata, such as the `borrowed` mark of
Nat.add's arguments) that lean4export leaves out, so LeanForth's library
never has it; Lean's lines mark it <md>, and a line equal once the marks
are dropped is counted and listed apart, as equal up to the export's
missing mdata (plan row FE1d2).

Usage: LEAN=... GFORTH=... python3 tests/front/check_whnf.py [--write | --write-golden]
       GFORTH=... python3 tests/front/check_whnf.py --golden   (Lean's recorded lines,
         tests/front/whnf-cases.golden; make test)
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
# Pinned Lean's lines, recorded for make test's run without Lean (--golden).
GOLDEN = ROOT / "tests/front/whnf-cases.golden"

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
    ("whnf", (PROJ, 0, apps(ADD, "k", "k")), None),
    # A projection's structure by whnf (proj := yesWithDelta, S2 merge A):
    # the instance unfolds to its constructor, the field is taken.
    ("whnf", (PROJ, 0, apps(c("instHAdd", 0), NAT, c("instAddNat"))), None),
    ("whnf", apps((PROJ, 0, apps(c("instHAdd", 0), NAT, c("instAddNat"))), "k", "x"), None),
    ("whnf", rec(apps(c("id", 1), NAT, ZERO)), None),
    ("whnf", rec((LET, NAT, "k", apps(SUCC, "#0"))), None),
    ("whnf", rec(apps((LAM, NAT, "#0"), "k")), None),
    ("whnf", rec(apps(REC, "m", apps(SUCC, "z"), "s", ZERO)), None),
    ("whnf", rec(apps(ADD, "k", "k")), None),
    # isAuxDef is isAuxRecursor alone: whnfCore leaves a noConfusion
    # (review s2-finish M1).
    ("whnf", apps(c("Nat.noConfusion", 0), c("True"), ZERO, ZERO, apps(c("Eq.refl", 1), NAT, ZERO)),
     None),
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
    # inferProjType (S2 merge B: n + 0 unfolds to instAddNat.1 n 0): a
    # field, a field applied, a field whose type names an earlier field
    # (Fin.mk's isLt over val, put in as a projection; ill-typed
    # arguments, as inferType does not check).
    ("infer", (PROJ, 0, pair("a", "b")), None),
    ("infer", (PROJ, 1, pair("a", "b")), None),
    ("infer", (PROJ, 0, "p"), None),
    ("infer", apps((PROJ, 0, apps(c("instHAdd", 0), NAT, c("instAddNat")), "HAdd"), "k", "x"),
     None),
    ("infer", apps((PROJ, 0, c("instAddNat"), "Add"), "k", "x"), None),
    ("infer", (PROJ, 1, apps(c("Fin.mk"), "k", "a", "b"), "Fin"), None),
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


def proj_name(t):
    """A projection's structure: Prod unless the case names another."""
    return t[3] if len(t) > 3 else "Prod"


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
        return f"(mkProj `{proj_name(t)} {t[1]} {lean(t[2])})"
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
        return f'{forth(t[2])} {t[1]} s" {proj_name(t)}" projn'
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
    if kind == "build":
        return f"({t[0]})"
    if kind != "ibeta":
        return lean(t)
    body, args = t
    return f"{lean(body)} #[{', '.join(lean(a) for a in args)}]"


def forth_case(kind, t):
    """An ibeta case's arguments, the last first: bound variable 0's first; a
    build case's code in a word of its own (bcN), whose token build-run runs."""
    if kind == "build":
        n = [b[1] for b in BUILDS].index(t)
        return f": bc{n} {t[1]} ; ' bc{n}"
    if kind != "ibeta":
        return forth(t)
    body, args = t
    return f"{forth(body)} {' '.join(forth(a) for a in reversed(args))} {len(args)} rxs"


# Build cases: (Lean's MetaM Expr, LeanForth's code giving the term).
MOTIVE = (LAM, NAT, apps(c("Eq", 1), NAT, "#0", "b"))
KONST = (LAM, NAT, (LAM, NAT, "#1"))   # fun y z => y


def build(lean_code, forth_code, gap=None):
    return ("build", (lean_code, forth_code), gap)


BUILDS = [
    build("mkEq a b", "fa fb lf-mk-eq"),
    build("mkEqRefl a", "fa lf-mk-eq-refl"),
    build("mkEqSymm e", "fe lf-mk-eq-symm"),
    build("do mkEqSymm (← mkEqRefl a)", "fa lf-mk-eq-refl lf-mk-eq-symm"),
    build("mkEqSymm k", "fk lf-mk-eq-symm"),
    build("do mkEqTrans e (← mkEqSymm e)", "fe fe lf-mk-eq-symm lf-mk-eq-trans"),
    build("do mkEqTrans (← mkEqRefl a) e", "fa lf-mk-eq-refl fe lf-mk-eq-trans"),
    build("do mkEqTrans e (← mkEqRefl b)", "fe fb lf-mk-eq-refl lf-mk-eq-trans"),
    build("mkEqTrans e k", "fe fk lf-mk-eq-trans"),
    build("do return mkExpectedPropHint e (← mkEq a b)",
          "fe fa fb lf-mk-eq lf-mk-expected-prop-hint"),
    build("mkCongrArg u e", "fu fe lf-mk-congr-arg"),
    build("do mkCongrArg u (← mkEqRefl a)", "fu fa lf-mk-eq-refl lf-mk-congr-arg"),
    build("do mkCongrArg u (← mkCongrArg v e)", "fu fv fe lf-mk-congr-arg lf-mk-congr-arg"),
    build("mkCongrArg s e", "fs fe lf-mk-congr-arg"),
    build("mkCongrFun w a", "fw fa lf-mk-congr-fun",
          "FE1c inferType of an application headed by a lambda (getLevel (β' a))"),
    build("do mkCongrFun (← mkEqRefl u) a", "fu lf-mk-eq-refl fa lf-mk-congr-fun"),
    build(f"do mkCongrFun (← mkCongrArg {lean(KONST)} e) b",
          f"{forth(KONST)} fe lf-mk-congr-arg fb lf-mk-congr-fun",
          "FE1c instantiate1 of a value with loose bound variables under a binder "
          "(liftLooseBVars, for Expr.beta f #[#0, b])"),
    build("mkCongrFun e a", "fe fa lf-mk-congr-fun"),
    build(f"mkEqNDRec {lean(MOTIVE)} e e", f"{forth(MOTIVE)} fe fe lf-mk-eq-ndrec"),
    build(f"do mkEqNDRec {lean(MOTIVE)} e (← mkEqRefl a)",
          f"{forth(MOTIVE)} fe fa lf-mk-eq-refl lf-mk-eq-ndrec"),
    build("mkEqNDRec a e e", "fa fe fe lf-mk-eq-ndrec"),
    build("mkAppM ``Nat.succ #[k]", 's" Nat.succ" fk 1 lf-mk-app-m'),
    build("mkAppM ``Eq.refl #[k]", 's" Eq.refl" fk 1 lf-mk-app-m'),
    build("mkAppM ``Nat.succ #[k, k]", 's" Nat.succ" fk fk 2 lf-mk-app-m'),
    build("mkAppM ``Nat.succ #[e]", 's" Nat.succ" fe 1 lf-mk-app-m'),
    # (mkEqMP and mkEqMPR are mkAppM of Eq.mp and Eq.mpr, which this slice
    # lacks: tests/front/tactic-lib.fs checks their terms over the S2 slice.)
]
CASES += BUILDS


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

def buildCase (x : MetaM Expr) : MetaM Unit := do
  try IO.println (← sx (← x)) catch _ => IO.println "rejected"

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
  withLocalDeclD `e (mkApp3 (mkConst ``Eq [mkLevelSucc .zero]) nat a b) fun e => do
  withLocalDeclD `u (mkForall `y .default nat nat) fun u => do
  withLocalDeclD `v (mkForall `y .default nat nat) fun v => do
  withLocalDeclD `w (mkApp3 (mkConst ``Eq [mkLevelSucc .zero]) (mkForall `y .default nat nat) u v) fun w => do
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


def golden(path, lines):
    """Pinned Lean's lines as recorded (--golden: make test, without Lean);
    with Lean, its lines must equal the record (--write-golden writes it)."""
    if "--golden" in sys.argv:
        return path.read_text(encoding="utf-8").splitlines()
    lines = lines()
    if "--write-golden" in sys.argv:
        path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    if path.read_text(encoding="utf-8").splitlines() != lines:
        raise Failure(f"{path.relative_to(ROOT)} differs from pinned Lean's lines: "
                      f"{sys.argv[0]} --write-golden")
    return lines


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
        wanted = golden(GOLDEN, lean_lines)
        if len(wanted) != len(CASES):
            raise Failure(f"{GOLDEN.relative_to(ROOT)}: {len(wanted)} lines for {len(CASES)} cases")
        for (kind, term, gap), want, got in zip(CASES, wanted, forth_lines()):
            text = judge(f"{kind} {forth_case(kind, term)}", gap, want, got)
            if text:
                gaps.append(f"{kind} {text}")
            note = mdata_note(kind, gap, want)
            if note:
                mdata.append(note)
    except Failure as error:
        print(f"check_whnf: {error}")
        return 1
    print(f"whnfCore, getStuckMVar?, inferType, instantiateBetaRevRange and the term builders: "
          f"{len(CASES) - len(gaps)} of {len(CASES)} "
          "cases equal to "
          f"pinned Lean's; {len(gaps)} gaps answer unsupported, Lean's answer shown: "
          f"{'; '.join(gaps)}; {len(mdata)} of the equal cases equal only once Lean's "
          f"mdata, which the export leaves out, is dropped: {'; '.join(mdata) or 'none'}; "
          "harness self-test passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
