#!/usr/bin/env python3
"""The front end's isDefEq against pinned Lean (plan FE1c).

Each case asks isDefEq t s over the slice tests/front/whnf-slice.ndjson,
with the variables of tests/front/check_whnf.py and, made after them,
the metavariables ?r : Nat, ?t : Nat -> Nat, ?y : Nat -> Nat -> Nat, the
free variables j : Nat (out of their scope), e c : a = b, u : Nat ->
Nat, v w : PUnit.{1}, i : a = b -> Nat and the synthetic opaque ?o :
Nat. Pinned Lean
4.35.0 (tests/front/defeq-cases.lean, which this script writes with
--write and checks is up to date) prints "true" and both sides with
their metavariables instantiated, or "false"; LeanForth
(tests/front/defeq-cases.fs: lf-meta-defeq) prints its own. Every case
starts from the same metavariable context (Lean restores its saved
state, LeanForth rolls back a mark). Kinds: eq under the elaborator's
configuration (run_meta: foApprox, ctxApprox), meta under Meta's default,
deep one depth deeper (withNewMCtxDepth), red, inst and impl at reducible,
instances and implicit transparency; stuck and dstuck the elaborator's with
isDefEqStuckEx (the stuck signal, S1 §2; Lean's line "stuck" is its
isDefEqStuck exception), at this depth and one deeper, guard
isDefEqGuarded with isDefEqStuckEx. Made last: the free variable
d : Nat -> PUnit.{1} and the level metavariable ?lu (level "u").
The lines must be equal, except for the cases listed as gaps, where
LeanForth must answer unsupported (a step not ported; the plan item is
named) and Lean's answer is shown. A harness self-test first checks that
a wrong line is told apart.

Pinned Lean's lines are kept in tests/front/defeq.golden (--write-golden
writes it from a Lean run; every Lean run checks it is unchanged), so
that make test compares LeanForth's lines with them without Lean
(--golden).

Usage: LEAN=... GFORTH=... python3 tests/front/check_defeq.py
       [--write | --write-golden | --golden]
"""
import os
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent.parent
LEAN = os.environ.get("LEAN", ".tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean")
GFORTH = os.environ.get("GFORTH", "gforth")
LIMIT = 300
LEAN_FILE = ROOT / "tests/front/defeq-cases.lean"
GOLDEN = ROOT / "tests/front/defeq.golden"

FVARS = set("mzskxabpgjecuvwid")
MVARS = {"?n": "n", "?h": "h", "?f": "f", "?q": "q", "?r": "r", "?t": "t", "?y": "y", "?o": "o"}
LAM, LET, PROJ, SORT, PI, LIT = "lam", "let", "proj", "sort", "pi", "lit"


def c(name, *levels):
    return ("c", name, levels)


def apps(f, *args):
    for a in args:
        f = ("app", f, a)
    return f


NAT, ZERO, SUCC, REC = c("Nat"), c("Nat.zero"), c("Nat.succ"), c("Nat.rec", 1)
ADD, PUNIT, UNIT = c("Nat.add"), c("PUnit", 1), c("PUnit.unit", 1)
PROD_MK = c("Prod.mk", 0, 0)
NAT2 = (PI, NAT, NAT)


def succ(t):
    return apps(SUCC, t)


def pair(a, b):
    return apps(PROD_MK, NAT, NAT, a, b)


def ofnat(n):
    return apps(c("OfNat.ofNat", 0), NAT, (LIT, n), apps(c("instOfNatNat"), (LIT, n)))


def hadd(a, b):
    inst = apps(c("instHAdd", 0), NAT, c("instAddNat"))
    return apps(c("HAdd.hAdd", 0, 0, 0), NAT, NAT, NAT, inst, a, b)


def lam(body, dom=NAT):
    return (LAM, dom, body)


ADD_ADD = apps(c("Add.add", 0), NAT, c("instAddNat"))
HADD_MK = apps(c("HAdd.mk", 0, 0, 0), NAT, NAT, NAT,
               (LAM, NAT, (LAM, NAT, apps(ADD_ADD, "#1", "#0"))))
SMART = "S2 merge B smart unfolding (Nat.add._sunfold)"
SMART_MUL = "S2 merge B smart unfolding (Nat.mul._sunfold, the greater height unfolded first)"
ID1, FST, MUL, PRED = c("id", 1), c("Prod.fst", 0, 0), c("Nat.mul"), c("Nat.pred")
UNIT_TYPE, DEC_LT = c("Unit"), c("Nat.decLt")
PROJ_TYPE = "FE1c inferType of a projection (proof irrelevance)"
PROD_F = apps(c("Prod", 0, 0), NAT2, NAT)
STUCK_PROJ = "FE1c getStuckMVar? of a projection whose structure needs whnf (isDefEqOnFailure)"


def mk_f(f, n):
    return apps(PROD_MK, NAT2, NAT, f, n)


# (id P (Prod.mk (fun x => x) 0)).1 k: whnf of the structure unfolds id.
ID_FST_K = apps((PROJ, 0, apps(ID1, PROD_F, mk_f(lam("#0"), (LIT, 0)))), "k")
HMUL_U = apps(c("HMul.hMul", 0, 0, 0), NAT, NAT, NAT,
              apps(c("HMul.mk", 0, 0, 0), NAT, NAT, NAT, lam(lam(apps("u", "#1")))), "k", "x")

EQAB = apps(c("Eq", 1), NAT, "a", "b")
REFL_A = apps(c("Eq.refl", 1), NAT, "a")
MOTIVE, STEP = lam(NAT), lam(lam("#0"))

# (kind, t, s, gap): gap None, or the plan item that closes it (LeanForth
# answers unsupported).
CASES = [
    # isDefEqQuick: equal nodes, literals, sorts, constants, binders.
    ("eq", "k", "k", None),
    ("eq", "k", "x", None),
    ("eq", NAT, NAT, None),
    ("eq", ZERO, SUCC, None),
    ("eq", (SORT, 0), (SORT, 0), None),
    ("eq", (SORT, 0), (SORT, 1), None),
    ("eq", (LIT, 2), (LIT, 2), None),
    ("eq", (LIT, 2), (LIT, 3), None),
    ("eq", PUNIT, c("PUnit", 2), None),
    ("eq", lam("#0"), lam("#0"), None),
    ("eq", lam("#0"), lam("#0", (SORT, 0)), None),
    ("eq", NAT2, NAT2, None),
    ("eq", NAT2, (PI, NAT, (SORT, 0)), None),
    ("eq", lam(succ("#0")), lam(succ("?n")), None),
    ("eq", lam("?n"), lam("k"), None),
    ("eq", lam("?n"), lam("#0"), None),
    ("eq", (LET, NAT, "k", "x"), "x", None),
    ("eq", (LET, NAT, "k", "#0"), "k", "FE1c inferType of a let (proof irrelevance)"),
    ("eq", "g", lam(apps("s", "#0")), None),
    # Eta.
    ("eq", lam(apps("u", "#0")), "u", None),
    ("eq", "u", lam(apps("u", "#0")), None),
    ("eq", lam(succ("#0")), SUCC, None),
    ("eq", lam(apps("?t", "#0")), "u", None),
    ("eq", lam(apps("?t", "#0")), SUCC, None),
    ("eq", lam(apps("?t", "#0")), lam(apps("u", "#0")), None),
    # Proof irrelevance.
    ("eq", "e", "c", None),
    ("eq", "e", REFL_A, None),
    # Assignment: scope, occurs check, types.
    ("eq", "?n", "k", None),
    ("eq", "k", "?n", None),
    ("eq", "?n", succ("k"), None),
    ("eq", "?n", "j", None),
    ("eq", "?r", "k", None),
    ("eq", "?r", "j", None),
    ("eq", "?n", succ("?n"), None),
    ("eq", "?n", NAT, None),
    ("eq", "?t", SUCC, None),
    ("eq", "?t", "u", None),
    ("eq", "?n", "?h", None),
    ("eq", "?o", "k", None),
    ("eq", "?n", "?o", None),
    # Patterns and first-order approximation.
    ("eq", apps("?t", "j"), succ("j"), None),
    ("eq", apps("?t", "j"), succ("k"), None),
    ("eq", apps("?t", "j"), apps("u", "j"), None),
    ("eq", apps("?t", "k"), succ("k"), None),
    ("meta", apps("?t", "k"), succ("k"), None),
    ("eq", apps("?y", "k", "k"), apps(ADD, "k", "k"), None),
    ("eq", apps("?y", "j", "j"), apps(ADD, "j", "j"), None),
    ("eq", apps("?y", "j", "k"), apps(ADD, "k", "j"),
     "S2 unfoldDefinition? in first-order approximation (Nat.add's smart unfolding, merge B)"),
    ("eq", apps("?t", "k"), apps("?t", "k"), None),
    ("eq", apps("?t", "k"), apps("?t", "x"), None),
    ("eq", apps("?t", (LIT, 2)), succ("k"), None),
    ("eq", apps("?t", "k"), "?n", None),
    ("eq", "?n", "?r", None),
    ("eq", "?r", "?n", None),
    ("eq", "?n", (LIT, 2), None),
    # Applications: arguments, heads.
    ("eq", apps("u", "k"), apps("u", "x"), None),
    ("eq", apps("u", "k"), apps("u", "?n"), None),
    ("eq", apps("u", "?n"), succ("k"), None),
    ("eq", pair("a", "b"), pair("a", "?n"), None),
    ("eq", pair("a", "b"), pair("b", "a"), None),
    ("eq", "p", pair((PROJ, 0, "p"), (PROJ, 1, "p")), "FE1c structure eta with fields"),
    ("eq", pair("a", "b"), "p", "FE1c structure eta with fields"),
    ("eq", (PROJ, 0, "p"), "a", "FE1c projections (isDefEqProj)"),
    # whnfCore of both sides.
    ("eq", apps(REC, MOTIVE, "z", STEP, ZERO), "z", None),
    ("eq", apps(lam(succ("#0")), "k"), succ("k"), None),
    ("eq", apps(REC, MOTIVE, "z", STEP, "?n"), "k", "FE1e synthPending (class facts, FE1e1)"),
    ("eq", apps(REC, "m", "z", "s", ZERO), "z", None),
    ("eq", "?n", apps(REC, MOTIVE, "?n", STEP, ZERO), None),
    ("eq", lam("k"), "k", None),
    # Unit-like structures and structure eta without fields.
    ("eq", "v", "w", None),
    ("eq", "v", UNIT, None),
    ("eq", UNIT, "w", None),
    # Nat offsets and values.
    ("eq", succ("?h"), succ(succ("k")), None),
    ("eq", succ("?h"), succ(succ("?r")), None),
    ("eq", succ(succ("?h")), succ("k"), SMART),
    ("eq", succ("k"), succ("x"), None),
    ("eq", succ("?h"), (LIT, 3), None),
    ("eq", succ("k"), (LIT, 0), None),
    ("eq", (LIT, 0), ZERO, None),
    ("eq", (LIT, 1), ZERO, None),
    ("eq", (LIT, 3), succ(succ(succ(ZERO))), "FE1c reduceNat? (isDefEqNat)"),
    ("eq", succ("?h"), hadd(ofnat(0), hadd("k", ofnat(1))),
     SMART + " after lazy delta (FE1's acceptance case)"),
    ("eq", hadd("k", ofnat(1)), succ("k"), None),
    # Depth: a metavariable of the outer depth is read-only.
    ("deep", "?n", "k", None),
    ("deep", apps("u", "?n"), apps("u", "k"), None),
    # Transparency: what may be unfolded.
    ("red", ADD, c("Nat.mul"), None),
    ("eq", ADD, c("Nat.mul"), None),
    ("red", apps(ADD, "k", "x"), apps(ADD, "k", "x"), None),
    ("red", apps(ADD, "k", "x"), apps(ADD, "x", "k"), "FE1c unification hints (the hint table)"),
    ("eq", apps(ADD, "k", "x"), apps(ADD, "x", "k"), SMART),
    # Instances and implicit transparency, with arguments; at reducible,
    # an assignment's types compared at implicit (id Nat unfolds there).
    ("inst", apps("u", "k"), apps("u", "x"), None),
    ("inst", apps(ADD, "k", "x"), apps(ADD, "k", "?n"), None),
    ("impl", apps("u", "?n"), apps("u", "k"), None),
    ("red", "?t", lam("#0", apps(c("id", 2), (SORT, 1), NAT)), None),
    ("red", apps(c("Eq.refl", 1), ADD, "a"), apps(c("Eq.refl", 1), c("Nat.mul"), "a"), None),
    ("red", ADD, "k", "FE1c unification hints (the hint table)"),
    ("eq", "?n", apps(ADD, "?n", "k"), "S2 merge B reduceNat?'s guard (whnf of Nat.add ?n k)"),
    # Lazy delta (S2 merge A, ExprDefEq.lean:1544-1849): one side unfolds
    # (outParam, Lean's p4b and p4f; at implicit with a level
    # metavariable); a reducible side first; class projections unpacked
    # to the other side's head (packedInstanceOf?), on either side, with an
    # assignment; one name at two levels (both unfolded).
    ("eq", apps(c("outParam", 2), (SORT, 1)), (SORT, 1), None),
    ("impl", apps(c("outParam", 2), (SORT, "u1")), (SORT, 1), None),
    ("eq", apps(c("outParam", 1), NAT), NAT, None),
    ("red", NAT, apps(c("outParam", 1), NAT), None),
    ("eq", apps(c("outParam", 1), NAT), apps(c("id", 2), (SORT, 1), NAT), None),
    ("eq", apps(c("id", 1), NAT, "k"), "k", None),
    ("eq", hadd("k", "x"), apps(ADD_ADD, "k", "x"), None),
    ("eq", apps(ADD_ADD, "k", "x"), hadd("k", "x"), None),
    ("eq", hadd("k", "x"), apps(ADD, "k", "x"), None),
    ("eq", hadd("?n", "x"), apps(ADD_ADD, "k", "x"), None),
    ("eq", hadd("k", "x"), hadd("x", "k"), SMART),
    ("eq", c("id", 1), c("id", 2), None),
    ("eq", apps(c("outParam", 1), "?n"), apps(ADD, "k", "x"), None),
    ("eq", apps(c("outParam", 1), "?n"), NAT, None),
    ("eq", apps(c("id", 1), NAT, apps(ADD, "?n", "x")), apps(ADD, "k", "x"), None),
    ("eq", apps(ADD, "?n", "x"), apps(ADD, "k", "x"), None),
    # An instance argument at reducible is compared at implicit, where
    # instHAdd unfolds to its constructor.
    ("red", hadd("k", "x"), apps(c("HAdd.hAdd", 0, 0, 0), NAT, NAT, NAT, HADD_MK, "k", "x"),
     None),
    ("inst", hadd("k", "x"), apps(ADD_ADD, "k", "x"),
     "S2 merge B isDefEqProjInst (ExprDefEq.lean:2356)"),
    ("impl", pair("a", "b"), pair("a", "?n"), None),
    ("inst", ADD, "k", "FE1c isDefEqProjInst (projection facts, FE1d2)"),
    # Lazy delta's choices (review s2-unfold-a H1): a projection function
    # on one side only unfolds the other side (?n := Prod.fst ..., not a);
    # without metavariables the side of the greater height unfolds first
    # (Nat.mul, 2, before id, 1; its smart unfolding a gap); after both
    # sides unfold, the side whose head the other's unfolding reached is
    # compared as it is (id against Function.comp's unfolding); tryHeuristic
    # compares a non-trivial definition's arguments first (Nat.pred: height
    # 2, a value that is not simple).
    ("meta", apps(ID1, NAT, "?n"), apps(FST, NAT, NAT, pair("a", "b")), None),
    ("meta", apps(FST, NAT, NAT, pair("a", "b")), apps(ID1, NAT, "?n"), None),
    ("eq", apps(ID1, NAT, apps(MUL, "k", "x")), apps(MUL, "k", "x"), SMART_MUL),
    ("eq", apps(MUL, "k", "x"), apps(ID1, NAT, apps(MUL, "k", "x")),
     "S3 evalNat's Nat.mul (isDefEqOffsetNat, nat-offset.fs; folding literals)"),
    ("eq", apps(ID1, NAT, apps(ADD, "k", "x")),
     apps(c("Function.comp", 1, 1, 1), NAT, NAT, NAT, apps(ID1, NAT), apps(ADD, "k"), "x"), None),
    ("eq", apps(PRED, "x"), apps(PRED, apps(ID1, NAT, "x")), None),
    # The other branches of these steps (review s2-unfold-a's coverage):
    # the left side unfolded to a head the right side lacks, which does not
    # unfold (Nat.add alone has a smart-unfolding body); an abbreviation
    # ranked above a regular definition, at reducible and at default
    # transparency (Unit, outParam); a reducible right side alone first;
    # packedInstanceOf? reaching a head that is no constant (u k: a gap
    # before lazy delta today); id's
    # value simple, so id is trivial; a non-trivial definition by height
    # (Nat.decLt, 3); a class projection's abbreviation at default; one
    # name with universe arguments that do not fit it; a constant against
    # an application of it.
    ("eq", apps(ID1, (PI, NAT, NAT2), MUL), ADD, None),
    ("red", UNIT_TYPE, apps(c("outParam", 1), UNIT_TYPE), None),
    ("eq", UNIT_TYPE, apps(c("outParam", 1), UNIT_TYPE), None),
    ("eq", apps(c("id", 2), (SORT, 1), NAT), apps(c("outParam", 1), NAT), None),
    ("eq", apps(c("HAdd.hAdd", 0, 0, 0), NAT, NAT, NAT,
                apps(c("HAdd.mk", 0, 0, 0), NAT, NAT, NAT, lam(lam(apps("u", "#1")))), "k", "x"),
     apps(ID1, NAT, apps("u", "k")),
     "FE1c isDefEqOffsetNat's instance test (HAdd.hAdd of an instance other than Nat's: Lean"
     " asks isDefEq at instances)"),
    ("eq", apps(ID1, NAT, "x"), apps(ID1, NAT, apps(ID1, NAT, "x")), None),
    ("eq", apps(DEC_LT, "k", "x"), apps(DEC_LT, "k", apps(ID1, NAT, "x")), None),
    ("eq", hadd("k", "x"), hadd("k", apps(ID1, NAT, "x")), PROJ_TYPE),
    ("eq", c("id", 1, 1), c("id", 2), None),
    ("eq", ID1, apps(ID1, NAT), None),
    # (review s2-unfold-a re-check M3-new) packedInstanceOf? reaching a
    # head that is no constant (u k), id on the left; two constants of one
    # name whose levels unify; an abbreviation that is no projection
    # function at tryHeuristic (Nat.isValidChar, whose unfolding then asks
    # a projection's type).
    ("eq", apps(ID1, NAT, apps("u", "k")), HMUL_U, None),
    ("eq", c("id", "u"), ID1, None),
    ("eq", apps(c("Nat.isValidChar"), "k"), apps(c("Nat.isValidChar"), apps(ID1, NAT, "k")),
     PROJ_TYPE),
    # isExprDefEqExpensive's whnfCore reduces a projection's structure by
    # whnf (proj := yesWithDelta: id unfolds at default), where
    # isExprDefEqAux's whnfCoreAtDefEq does not (review s2-unfold-a M1).
    ("meta", "k", ID_FST_K, None),
    ("meta", ID_FST_K, "k", PROJ_TYPE),
    # At reducible and instances id stays: whnfCore leaves the projection
    # stuck (Lean: false), where a whnfCore at default would unfold it
    # (review s2-unfold-a re-check M1-new).
    ("red", "k", ID_FST_K, STUCK_PROJ),
    ("inst", "k", ID_FST_K, STUCK_PROJ),
    # isExprDefEqAux's whnfCoreAtDefEq leaves the projection (id stays at
    # instances); Lean then reduces it in isExprDefEqExpensive, after
    # isDefEqProj.
    ("meta", "a", (PROJ, 0, apps(ID1, apps(c("Prod", 0, 0), NAT, NAT), pair("a", "b"))),
     "FE1c projections (isDefEqProj)"),
    # Offsets and values are unsigned cells (review B1).
    ("eq", succ("?h"), (LIT, 2**63), None),
    ("eq", succ(hadd("?h", ofnat(2**63))), (LIT, 5), None),
    ("eq", succ("?h"), (LIT, 2**64 - 1), None),
    ("eq", hadd(hadd(ofnat(2**62), ofnat(2**62)), ofnat(2**62)), (LIT, 3 * 2**62),
     None),
    ("eq", succ(hadd(hadd(hadd("?h", ofnat(2**62)), ofnat(2**62)), ofnat(2**62))),
     (LIT, 3 * 2**62 + 1), None),
    ("eq", succ(hadd("k", hadd(hadd(ofnat(2**62), ofnat(2**62)), ofnat(2**62)))),
     succ("?h"), None),
    # A constructor short of its arguments; a proof argument skipped.
    ("eq", "p", apps(PROD_MK, NAT, NAT, "a"), None),
    ("eq", apps("i", "e"), apps("i", (PROJ, 0, "p")), None),
    # The stuck signal (S1 §2): two heads neither side assigns
    # (ExprDefEq.lean:2118); a stuck metavariable of an outer depth in
    # isDefEqOnFailure (2182), raised only one depth deeper; caught by
    # isDefEqAppFallback when a late case (unit-like) answers true; a level
    # metavariable of an outer depth (LevelDefEq.lean:169); isDefEqGuarded.
    ("stuck", "?o", "k", None),
    ("eq", "?o", "k", None),
    ("dstuck", "?n", "k", None),
    ("guard", "?o", "k", None),
    ("stuck", apps(REC, MOTIVE, "z", STEP, "?o"), "k", None),
    ("dstuck", apps(REC, MOTIVE, "z", STEP, "?o"), "k", None),
    ("dstuck", apps("d", "k"), apps(REC, lam(PUNIT), UNIT, lam(lam("#0", PUNIT)), "?o"), None),
    ("eq", apps("d", "k"), apps(REC, lam(PUNIT), UNIT, lam(lam("#0", PUNIT)), "?o"), None),
    ("dstuck", apps("u", "k"), apps(REC, MOTIVE, "z", STEP, "?o"), None),
    ("deep", (SORT, "u"), (SORT, 1), None),
    ("dstuck", (SORT, "u"), (SORT, 1), None),
    ("dstuck", (SORT, "u"), (SORT, "u"), None),
    ("stuck", (SORT, "u"), (SORT, 1), None),
]


LEAN_LEVELS = {0: "Level.zero", 1: "Level.one", 2: "(mkLevelSucc Level.one)", "u": "lu",
               "u1": "(mkLevelSucc lu)"}
FORTH_LEVELS = {0: "l0", 1: "lv1", 2: "lv2", "u": "lvu", "u1": "lvu1"}


class Failure(Exception):
    pass


def lean(t):
    if isinstance(t, tuple):
        tag = t[0]
        if tag == "c":
            return f"(mkConst `{t[1]} [{', '.join(LEAN_LEVELS[l] for l in t[2])}])"
        if tag == "app":
            return f"(mkApp {lean(t[1])} {lean(t[2])})"
        if tag == LAM:
            return f"(mkLambda `y .default {lean(t[1])} {lean(t[2])})"
        if tag == PI:
            return f"(mkForall `y .default {lean(t[1])} {lean(t[2])})"
        if tag == PROJ:
            return f"(mkProj `Prod {t[1]} {lean(t[2])})"
        if tag == SORT:
            return f"(mkSort {LEAN_LEVELS[t[1]]})"
        if tag == LIT:
            return f"(mkRawNatLit {t[1]})"
        return f"(mkLet `y {lean(t[1])} {lean(t[2])} {lean(t[3])})"
    if t.startswith("#"):
        return f"(mkBVar {t[1:]})"
    return MVARS.get(t, t)


def forth(t):
    if isinstance(t, tuple):
        tag = t[0]
        if tag == "c":
            levels = " ".join(FORTH_LEVELS[l] for l in t[2])
            return f'{levels} {len(t[2])} s" {t[1]}" cn'.strip()
        if tag == "app":
            return f"{forth(t[1])} {forth(t[2])} app"
        if tag == LAM:
            return f"{forth(t[1])} {forth(t[2])} lam"
        if tag == PI:
            return f"{forth(t[1])} {forth(t[2])} tpi"
        if tag == PROJ:
            return f"{forth(t[2])} {t[1]} proj"
        if tag == SORT:
            return f"{FORTH_LEVELS[t[1]]} sort"
        if tag == LIT:
            assert 0 <= t[1] < 2**64, t   # one unsigned cell in nlit
            return f"{t[1]} nlit"
        return f"{forth(t[1])} {forth(t[2])} {forth(t[3])} let"
    if t.startswith("#"):
        return f"{t[1:]} bv"
    if t in MVARS:
        return t
    assert t in FVARS, t
    return "f" + t


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
  | .lit (.natVal n) => return toString n
  | .mdata _ e => return s!"<md>{← sx e}"
  | e => return s!"?? {e}"

def answer (t s : Expr) (go : MetaM Bool) : MetaM Unit := do
  let saved ← saveState
  try
    if ← go then
      IO.println s!"true {← sx (← instantiateMVars t)} {← sx (← instantiateMVars s)}"
    else
      IO.println "false"
  catch ex =>
    match ex with
    | .internal id _ => IO.println (if id == isDefEqStuckExceptionId then "stuck" else "error")
    | _ => IO.println "error"
  saved.restore

def eqCase (t s : Expr) : MetaM Unit := answer t s (isDefEq t s)

def stuckCase (t s : Expr) : MetaM Unit :=
  answer t s (withConfig (fun c => { c with isDefEqStuckEx := true }) (isDefEq t s))

def dstuckCase (t s : Expr) : MetaM Unit :=
  answer t s (withNewMCtxDepth (withConfig (fun c => { c with isDefEqStuckEx := true })
    (isDefEq t s)))

def guardCase (t s : Expr) : MetaM Unit :=
  answer t s (withConfig (fun c => { c with isDefEqStuckEx := true }) (isDefEqGuarded t s))

def metaCase (t s : Expr) : MetaM Unit :=
  answer t s (withConfig (fun c => { c with foApprox := false, ctxApprox := false }) (isDefEq t s))

def deepCase (t s : Expr) : MetaM Unit := answer t s (withNewMCtxDepth (isDefEq t s))

def redCase (t s : Expr) : MetaM Unit := answer t s (withReducible (isDefEq t s))

def instCase (t s : Expr) : MetaM Unit :=
  answer t s (withTransparency .instances (isDefEq t s))

def implCase (t s : Expr) : MetaM Unit :=
  answer t s (withTransparency .implicit (isDefEq t s))

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
  let nat2 := mkForall `y .default nat nat
  let r ← mkFreshExprMVar nat (userName := `r)
  let t ← mkFreshExprMVar nat2 (userName := `t)
  let y ← mkFreshExprMVar (mkForall `y .default nat nat2) (userName := `y)
  let eqab := mkApp3 (mkConst ``Eq [Level.one]) nat a b
  withLocalDeclD `j nat fun j => do
  withLocalDeclD `e eqab fun e => do
  withLocalDeclD `c eqab fun c => do
  withLocalDeclD `u nat2 fun u => do
  withLocalDeclD `v (mkConst ``PUnit [Level.one]) fun v => do
  withLocalDeclD `w (mkConst ``PUnit [Level.one]) fun w => do
  withLocalDeclD `i (mkForall `y .default eqab nat) fun i => do
  let o ← mkFreshExprMVar nat (kind := .syntheticOpaque) (userName := `o)
  withLocalDeclD `d (mkForall `y .default nat (mkConst ``PUnit [Level.one])) fun d => do
  let lu ← mkFreshLevelMVar
  let _ := (m, z, k, x, p, g, n, h, q, r, t, y, j, e, c, u, v, w, i, o, d, lu)
"""


def lean_source():
    calls = "\n".join(f"  {kind}Case {lean(t)} {lean(s)}" for kind, t, s, _ in CASES)
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
                      "python3 tests/front/check_defeq.py --write")
    return run([LEAN, "-DwarningAsError=true", str(LEAN_FILE.relative_to(ROOT))])


def forth_lines():
    calls = " ".join(f"{forth(t)} {forth(s)} {kind}-dq" for kind, t, s, _ in CASES)
    return run([GFORTH, "tests/front/defeq-cases.fs", "-e", calls + " bye"])


def judge(name, gap, want, got):
    """None when the lines agree (Lean's error is LeanForth's invalid),
    the gap's text when LeanForth answers unsupported for a listed gap;
    else raise."""
    if gap:
        if got != "unsupported":
            raise Failure(f"{name}: a listed gap answers {got!r} (Lean: {want!r})")
        short = want if len(want) <= 40 else want[:37] + "..."
        return f"{short} ({gap})"
    if want != got and not (want == "error" and got == "invalid"):
        raise Failure(f"{name}:\n  Lean:      {want}\n  LeanForth: {got}")
    return None


def self_test():
    if lean(apps("u", "?n")) != "(mkApp u n)" or forth(apps("u", "?n")) != "fu ?n app":
        raise Failure("harness self-test: terms not written as expected")
    for want, got, gap in (("true k k", "false", None), ("false", "unsupported", None),
                           ("true k k", "true k k", "a gap"), ("error", "false", None)):
        try:
            judge("eq", gap, want, got)
        except Failure:
            continue
        raise Failure(f"harness self-test: {want} / {got} (gap {gap}) not told apart")


def golden_lines():
    """Lean's lines as recorded in the golden file, which must match the cases."""
    lines = GOLDEN.read_text(encoding="utf-8").splitlines()
    if len(lines) != len(CASES):
        raise Failure(f"{GOLDEN.relative_to(ROOT)} has {len(lines)} lines for {len(CASES)} cases: "
                      "python3 tests/front/check_defeq.py --write-golden")
    return lines


def wanted(args):
    """Pinned Lean's lines, checked against the golden file; or (--golden,
    without Lean, as make test runs it) the golden file's."""
    if args == ["--golden"]:
        return golden_lines()
    lines = lean_lines()
    if args == ["--write-golden"]:
        GOLDEN.write_text("\n".join(lines) + "\n", encoding="utf-8")
    if golden_lines() != lines:
        raise Failure(f"{GOLDEN.relative_to(ROOT)} differs from pinned Lean's lines")
    return lines


def main():
    args = sys.argv[1:]
    if args == ["--write"]:
        LEAN_FILE.write_text(lean_source(), encoding="utf-8")
        return 0
    try:
        self_test()
        gaps, kinds = [], {}
        for (kind, t, s, gap), want, got in zip(CASES, wanted(args), forth_lines()):
            text = judge(f"{kind} {forth(t)} =?= {forth(s)}", gap, want, got)
            if text:
                gaps.append(f"{text}")
            answer = want.split()[0]
            kinds[answer] = kinds.get(answer, 0) + 1
    except Failure as error:
        print(f"check_defeq: {error}")
        return 1
    mix = ", ".join(f"{n} {a}" for a, n in sorted(kinds.items()))
    source = "the golden file's" if args == ["--golden"] else "pinned Lean's"
    print(f"isDefEq: {len(CASES) - len(gaps)} of {len(CASES)} cases equal to {source} "
          f"(Lean's answers: {mix}); {len(gaps)} gaps answer unsupported, Lean's answer shown: "
          f"{'; '.join(gaps)}; harness self-test passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
