#!/usr/bin/env python3
"""The front end's Meta layer against pinned Lean (plan FE1c; ADR 0021 D5, D6).

Each case below is run twice: by pinned Lean 4.35.0
(tests/front/meta-cases.lean, which this script writes with --write and
checks is up to date, calling Meta.isLevelDefEqAux, Expr.instantiate1,
Expr.abstract and Expr.headBeta) and by LeanForth (tests/front/meta-cases.fs, calling
lf-meta-level-defeq, lf-meta-instantiate1, lf-meta-abstract and
lf-meta-head-beta on the same
terms). Both print one line per case: the answer and every named level
metavariable's value afterwards, or the resulting term as an S-expression.
The lines must be equal, except that LeanForth's "unsupported" stands for
Lean's postponed level pair, and for the cases listed as gaps (levels with
max, which Lean normalizes and LeanForth does not port yet), where
LeanForth must answer unsupported and Lean's answer is shown. A harness
self-test first checks that a wrong line is told apart.

Usage: LEAN=... GFORTH=... python3 tests/front/check_meta.py [--write]
"""
import os
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent.parent
LEAN = os.environ.get("LEAN", ".tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean")
GFORTH = os.environ.get("GFORTH", "gforth")
LIMIT = 300
LEAN_FILE = ROOT / "tests/front/meta-cases.lean"
LAM, PI, APP = "lam", "pi", "app"

# Level cases: (lhs, rhs, read-only metavariables, gap?). Levels: numerals,
# u and v (parameters), ?a .. ?d (metavariables made inside a new depth),
# ?r and ?s (made outside it: read-only), x+k, (max x y).
LEVELS = [
    ("u", "u", "", False), ("0", "1", "", False), ("u+1", "u", "", False),
    ("u", "v", "", False), ("u+3", "u+3", "", False), ("?a", "1", "", False),
    ("?a+1", "2", "", False), ("?a+1", "?b", "", False), ("?a", "u+2", "", False),
    ("?a", "?a+1", "", False), ("u+1", "?a+2", "", False), ("0", "?a", "", False),
    ("?a+1", "v", "", False), ("0", "?a+1", "", False), ("?a", "?b", "", False),
    ("?r", "1", "r", False), ("?r", "?a", "r", False), ("?a+1", "?r", "r", False),
    ("?r+1", "?s", "rs", False), ("(max u v)", "(max u v)", "", False),
    ("(max u v)", "(max v u)", "", True), ("?a", "(max u v)", "", True),
]

# Universe-parameter cases: (level, names, levels, gap?) for
# Level.instantiateParams, and (term, names, levels, gap?) for
# Expr.instantiateLevelParams, terms with ("sort", level) and
# ("const", level, level) for C.{l1, l2}. A level with max over a parameter
# is a gap (Lean simplifies with mkLevelMax').
LPARAMS = [
    ("u+1", ["u"], ["2"], False), ("v", ["u"], ["1"], False), ("u", ["u", "u"], ["1", "2"], False),
    ("(max 1 0)", ["u"], ["1"], False), ("u+2", ["u", "v"], ["v+1", "0"], False),
    ("(max u v)", ["u"], ["1"], False), ("(max u v)", ["u", "v"], ["1", "2"], False),
    ("(imax u v)", ["v"], ["1"], False), ("(imax u v)", ["u", "v"], ["v", "0"], False),
    ("(max (max u v) u)", ["v"], ["u"], False),
]

# mkLevelMax' and mkLevelIMax' on two levels: ("max" | "imax", u, v).
LOPS = [
    ("max", "u", "u"), ("max", "0", "u"), ("max", "u", "0"), ("max", "1", "2"),
    ("max", "u+2", "1"), ("max", "(max u v)", "u"), ("max", "v", "(max u v)"),
    ("max", "u+1", "u"), ("max", "u", "u+1"), ("max", "u", "v"), ("max", "u+1", "v+2"),
    ("imax", "u", "1"), ("imax", "u", "0"), ("imax", "0", "u"), ("imax", "u", "u"),
    ("imax", "u", "v"), ("imax", "u", "(max v 1)"), ("imax", "u", "(imax v 1)"),
    ("imax", "1", "(imax u v)"), ("max", "u+1", "1"), ("max", "1", "u+1"),
]
SORT, CONST = "sort", "const"
TPARAMS = [
    ((SORT, "u"), ["u"], ["1"], False), ((CONST, "u", "v"), ["u", "v"], ["1", "0"], False),
    ((LAM, (SORT, "u"), (SORT, "u+1")), ["u"], ["v"], False),
    ((PI, (SORT, "v"), (APP, (CONST, "u", "v"), "#0")), ["v"], ["u+1"], False),
    ((APP, "x", "y"), ["u"], ["1"], False), ((CONST, "0", "1"), ["u"], ["v"], False),
    ((SORT, "(max u v)"), ["u"], ["1"], False),
    ((SORT, "(imax u v)"), ["v"], ["0"], False),
    ((SORT, "(max u u)"), [], [], False),
]

# Term cases: ("inst1", body, value), ("abst", term, [x0, ...]) or
# ("beta", term). Terms: P (Prop),
# x and y (free variables of type Prop), ?m (a metavariable of type
# Prop), #i (a bound variable), ("app", f, a), ("lam", T, b), ("pi", T, b).
ID = (LAM, "P", "#0")
FLIP = (LAM, "P", (LAM, "P", (APP, "#0", "#1")))
TERMS = [
    ("inst1", "#0", "x"), ("inst1", "#1", "x"), ("inst1", (LAM, "P", "#1"), "x"),
    ("inst1", ID, "x"), ("inst1", (APP, "#0", "#0"), "x"),
    ("inst1", (PI, "P", (APP, "#1", "#0")), "y"),
    ("inst1", (LAM, "P", (LAM, "P", (APP, "#2", "#1"))), "x"),
    ("inst1", (APP, "#0", "?m"), "x"), ("inst1", (LAM, "P", "#2"), "x"),
    ("inst1", "#0", (APP, "x", "?m")),
    ("beta", (APP, ID, "x")), ("beta", (APP, (APP, FLIP, "x"), "y")),
    ("beta", (APP, (APP, ID, "x"), "y")), ("beta", (APP, "x", "y")),
    ("beta", (APP, FLIP, "x")), ("beta", (APP, (APP, ID, ID), "x")), ("beta", "P"),
    ("abst", (APP, "x", "y"), ["x"]), ("abst", (APP, "x", "y"), ["x", "y"]),
    ("abst", (APP, "x", "y"), ["y", "x"]), ("abst", (LAM, "P", (APP, "x", "#0")), ["x"]),
    ("abst", (PI, "P", (APP, "y", (LAM, "P", "x"))), ["x", "y"]),
    ("abst", (APP, "?m", "x"), ["?m"]), ("abst", (APP, "x", "y"), ["x", "x"]),
    ("abst", (APP, "x", "y"), []), ("abst", (LAM, "P", "#3"), ["x"]),
]


CASES = len(LEVELS) + len(TERMS) + len(LOPS) + len(LPARAMS) + len(TPARAMS)


class Failure(Exception):
    pass


def level_parse(text):
    """A level of the cases as a tuple: ("num", k), ("param", n),
    ("mvar", c), ("max", a, b), ("succ", l, k)."""
    text = text.strip()
    m = re.fullmatch(r"(.*)\+(\d+)", text)
    if m and m.group(1).count("(") == m.group(1).count(")"):
        return ("succ", level_parse(m.group(1)), int(m.group(2)))
    if text.isdigit():
        return ("num", int(text))
    for op in ("max", "imax"):
        if text.startswith(f"({op} "):
            inner = text[len(op) + 2:-1]
            depth = 0
            for i, ch in enumerate(inner):
                depth += {"(": 1, ")": -1}.get(ch, 0)
                if ch == " " and depth == 0:
                    return (op, level_parse(inner[:i]), level_parse(inner[i + 1:]))
    if text.startswith("?"):
        return ("mvar", text[1])
    return ("param", text)


def level_lean(t):
    kind = t[0]
    if kind == "num":
        return f"(Nat.repeat mkLevelSucc {t[1]} Level.zero)"
    if kind == "param":
        return f"(mkLevelParam `{t[1]})"
    if kind == "mvar":
        return f"m{t[1]}"
    if kind == "max":
        return f"(mkLevelMax {level_lean(t[1])} {level_lean(t[2])})"
    if kind == "imax":
        return f"(mkLevelIMax {level_lean(t[1])} {level_lean(t[2])})"
    return f"(Nat.repeat mkLevelSucc {t[2]} {level_lean(t[1])})"


def level_forth(t, index):
    kind = t[0]
    if kind == "num":
        return "zero" + " lsucc" * t[1]
    if kind == "param":
        return t[1]
    if kind == "mvar":
        return f"{index[t[1]]} mv"
    if kind == "max":
        return f"{level_forth(t[1], index)} {level_forth(t[2], index)} lmax"
    if kind == "imax":
        return f"{level_forth(t[1], index)} {level_forth(t[2], index)} limax"
    return level_forth(t[1], index) + " lsucc" * t[2]


def mvars_of(*texts):
    seen = []
    for text in texts:
        for c in re.findall(r"\?([a-z])", text):
            if c not in seen:
                seen.append(c)
    return seen


LEAN_HEAD = """import Lean
open Lean Meta

partial def pl (ms : List (LMVarId × String)) (l : Level) : String :=
  let k := l.getOffset
  let base : Option String := match l.getLevelOffset with
    | .zero => none
    | .param n => some n.toString
    | .mvar id => some ((ms.lookup id).getD "?_")
    | .max x y => some s!"(max {pl ms x} {pl ms y})"
    | .imax x y => some s!"(imax {pl ms x} {pl ms y})"
    | _ => some "??"
  match base with
  | none => toString k
  | some s => if k == 0 then s else s!"{s}+{k}"

def levelCase (ms : List (LMVarId × String)) (l r : Level) : MetaM Unit := do
  let res ← isLevelDefEqAux l r
  let ans := if (← getPostponed).size > 0 then "postponed" else toString res
  let vs ← ms.mapM fun (id, n) => do
    return s!" {n}={pl ms (← instantiateLevelMVars (mkLevelMVar id))}"
  IO.println (ans ++ String.join vs)

partial def sx : Expr → MetaM String
  | .bvar i => return s!"#{i}"
  | .sort .zero => return "Prop"
  | .sort l => return s!"Sort {pl [] l}"
  | .const _ us => return "C.{" ++ String.intercalate "," (us.map (pl [])) ++ "}"
  | .fvar id => return (← id.getUserName).toString
  | .mvar _ => return "?m"
  | .app f a => return s!"(app {← sx f} {← sx a})"
  | .lam _ t b _ => return s!"(lam {← sx t} {← sx b})"
  | .forallE _ t b _ => return s!"(pi {← sx t} {← sx b})"
  | e => return s!"?? {e}"
"""


def lean_level_case(lhs, rhs, readonly):
    names = mvars_of(lhs, rhs)
    outer = [c for c in names if c in readonly]
    inner = [c for c in names if c not in readonly]
    lines = ["run_meta do"]
    lines += [f"  let m{c} ← mkFreshLevelMVar" for c in outer]
    lines.append("  withNewMCtxDepth do")
    lines += [f"    let m{c} ← mkFreshLevelMVar" for c in inner]
    pairs = ", ".join(f'(m{c}.mvarId!, "{c}")' for c in outer + inner)
    lines.append(f"    levelCase [{pairs}] {level_lean(level_parse(lhs))} "
                 f"{level_lean(level_parse(rhs))}")
    return "\n".join(lines)


def term_lean(t):
    if isinstance(t, tuple) and t[0] == SORT:
        return f"(mkSort {level_lean(level_parse(t[1]))})"
    if isinstance(t, tuple) and t[0] == CONST:
        return f"(mkConst `C [{level_lean(level_parse(t[1]))}, {level_lean(level_parse(t[2]))}])"
    if isinstance(t, tuple):
        kind, a, b = t
        if kind == APP:
            return f"(mkApp {term_lean(a)} {term_lean(b)})"
        maker = "mkLambda" if kind == LAM else "mkForall"
        return f"({maker} `a .default {term_lean(a)} {term_lean(b)})"
    if t.startswith("#"):
        return f"(mkBVar {t[1:]})"
    return {"P": "(mkSort Level.zero)", "x": "x", "y": "y", "?m": "m"}[t]


def term_forth(t):
    if isinstance(t, tuple) and t[0] == SORT:
        return f"{level_forth(level_parse(t[1]), {})} sort-of"
    if isinstance(t, tuple) and t[0] == CONST:
        return f"{level_forth(level_parse(t[1]), {})} {level_forth(level_parse(t[2]), {})} const2"
    if isinstance(t, tuple):
        kind, a, b = t
        word = {APP: "app", LAM: "lam", PI: "tpi"}[kind]
        return f"{term_forth(a)} {term_forth(b)} {word}"
    if t.startswith("#"):
        return f"{t[1:]} bv"
    return {"P": "prop", "x": "fx", "y": "fy", "?m": "hole"}[t]


def lean_term_cases():
    lines = ["run_meta do",
             "  withLocalDeclD `x (mkSort Level.zero) fun x => do",
             "  withLocalDeclD `y (mkSort Level.zero) fun y => do",
             "    let m ← mkFreshExprMVar (mkSort Level.zero)"]
    for case in TERMS:
        if case[0] == "inst1":
            expr = f"(Expr.instantiate1 {term_lean(case[1])} {term_lean(case[2])})"
        elif case[0] == "abst":
            xs = ", ".join(term_lean(x) for x in case[2])
            expr = f"(Expr.abstract {term_lean(case[1])} #[{xs}])"
        else:
            expr = f"(Expr.headBeta {term_lean(case[1])})"
        lines.append(f"    IO.println (← sx {expr})")
    return "\n".join(lines)


def lean_names(names):
    return "[" + ", ".join(f"`{n}" for n in names) + "]"


def lean_levels(levels):
    return "[" + ", ".join(level_lean(level_parse(l)) for l in levels) + "]"


def lean_param_cases():
    lines = ["run_meta do",
             "  withLocalDeclD `x (mkSort Level.zero) fun x => do",
             "  withLocalDeclD `y (mkSort Level.zero) fun y => do"]
    for op, u, v in LOPS:
        maker = "mkLevelMax'" if op == "max" else "mkLevelIMax'"
        lines.append(f"    IO.println (pl [] ({maker} {level_lean(level_parse(u))} "
                     f"{level_lean(level_parse(v))}))")
    for level, names, levels, _ in LPARAMS:
        lines.append(f"    IO.println (pl [] (Level.instantiateParams "
                     f"{level_lean(level_parse(level))} {lean_names(names)} {lean_levels(levels)}))")
    for term, names, levels, _ in TPARAMS:
        lines.append(f"    IO.println (← sx (Expr.instantiateLevelParams {term_lean(term)} "
                     f"{lean_names(names)} {lean_levels(levels)}))")
    return "\n".join(lines)


def lean_source():
    text = LEAN_HEAD + "\n" + "\n\n".join(lean_level_case(l, r, ro) for l, r, ro, _ in LEVELS)
    return text + "\n\n" + lean_term_cases() + "\n\n" + lean_param_cases() + "\n"


def lean_lines():
    if LEAN_FILE.read_text(encoding="utf-8") != lean_source():
        raise Failure(f"{LEAN_FILE.relative_to(ROOT)} differs from the cases: "
                      "python3 tests/front/check_meta.py --write")
    run = subprocess.run([LEAN, "-DwarningAsError=true", str(LEAN_FILE.relative_to(ROOT))],
                         cwd=ROOT, stdin=subprocess.DEVNULL, capture_output=True, text=True,
                         timeout=LIMIT)
    lines = [line for line in run.stdout.splitlines() if line.strip()]
    if run.returncode != 0 or len(lines) != CASES:
        raise Failure(f"pinned Lean: exit {run.returncode}\n{run.stdout}{run.stderr}")
    return lines


def forth_level_case(lhs, rhs, readonly):
    names = mvars_of(lhs, rhs)
    outer = [c for c in names if c in readonly]
    inner = [c for c in names if c not in readonly]
    index = {c: i for i, c in enumerate(outer + inner)}
    make = " ".join(f"char {c} add-mv" for c in outer)
    make += " lf-mctx-deeper " + " ".join(f"char {c} add-mv" for c in inner)
    return (f"level-case {make} {level_forth(level_parse(lhs), index)} "
            f"{level_forth(level_parse(rhs), index)} level-run")


def forth_lines():
    calls = [forth_level_case(l, r, ro) for l, r, ro, _ in LEVELS]
    for case in TERMS:
        if case[0] == "inst1":
            calls.append(f"{term_forth(case[1])} {term_forth(case[2])} inst1-run")
        elif case[0] == "abst":
            xs = " ".join(term_forth(x) for x in case[2])
            calls.append(f"{term_forth(case[1])} {xs} {len(case[2])} xs abst-run")
        else:
            calls.append(f"{term_forth(case[1])} beta-run")
    ids = {"u": "101", "v": "102"}
    for op, u, v in LOPS:
        calls.append(f"{level_forth(level_parse(u), {})} {level_forth(level_parse(v), {})} "
                     f"{op}-run")
    for level, names, levels, _ in LPARAMS:
        calls.append(f"{' '.join(ids[n] for n in names)} {len(names)} params "
                     f"{' '.join(level_forth(level_parse(l), {}) for l in levels)} {len(levels)} args "
                     f"{level_forth(level_parse(level), {})} {len(names)} lps-run")
    for term, names, levels, _ in TPARAMS:
        calls.append(f"{' '.join(ids[n] for n in names)} {len(names)} params "
                     f"{' '.join(level_forth(level_parse(l), {}) for l in levels)} {len(levels)} args "
                     f"{term_forth(term)} {len(names)} ilp-run")
    run = subprocess.run([GFORTH, "tests/front/meta-cases.fs", "-e", " ".join(calls) + " bye"],
                         cwd=ROOT, stdin=subprocess.DEVNULL, capture_output=True, text=True,
                         timeout=LIMIT)
    lines = [line.strip() for line in run.stdout.splitlines() if line.strip()]
    if run.returncode != 0 or len(lines) != CASES:
        raise Failure(f"meta-cases.fs: exit {run.returncode}\n{run.stdout}{run.stderr}")
    return lines


def agree(lean, forth):
    """Equal lines; LeanForth's unsupported is Lean's postponed pair."""
    if lean == forth:
        return True
    return lean.startswith("postponed") and forth == "unsupported" + lean[len("postponed"):]


def self_test():
    for lean, forth in (("true a=1", "true a=2"), ("false", "true"), ("true a=1", "unsupported a=1"),
                        ("(app x y)", "(app y x)")):
        if agree(lean, forth):
            raise Failure(f"harness self-test: {lean} / {forth} not told apart")


def main():
    if sys.argv[1:] == ["--write"]:
        LEAN_FILE.write_text(lean_source(), encoding="utf-8")
        return 0
    try:
        self_test()
        lean, forth = lean_lines(), forth_lines()
        gaps = []
        names = ([f"{l} =?= {r}" for l, r, _, _ in LEVELS] + [str(c) for c in TERMS]
                 + [f"{op} {u} {v}" for op, u, v in LOPS]
                 + [f"{c[0]} {c[1]} := {c[2]}" for c in LPARAMS + TPARAMS])
        gap_flags = ([g for _, _, _, g in LEVELS] + [False] * (len(TERMS) + len(LOPS))
                     + [c[3] for c in LPARAMS + TPARAMS])
        for name, gap, want, got in zip(names, gap_flags, lean, forth):
            if gap:
                if not got.startswith("unsupported"):
                    raise Failure(f"{name}: a listed gap now answers {got!r} (Lean: {want!r}); "
                                  "compare it and take it off the gap list")
                gaps.append(f"{name} (Lean: {want})")
            elif not agree(want, got):
                raise Failure(f"{name}:\n  Lean:      {want}\n  LeanForth: {got}")
    except Failure as error:
        print(f"check_meta: {error}")
        return 1
    print(f"Meta layer: {CASES - len(gaps)} cases equal to pinned Lean's "
          f"({len(LEVELS)} level unifications, {len(TERMS)} instantiations, abstractions and "
          f"head-beta steps, {len(LOPS)} mkLevelMax'/mkLevelIMax', "
          f"{len(LPARAMS) + len(TPARAMS)} universe-parameter instantiations); "
          f"{len(gaps)} gaps answer unsupported: {'; '.join(gaps)}; harness self-test passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
