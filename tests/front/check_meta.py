#!/usr/bin/env python3
"""The front end's Meta layer against pinned Lean (plan FE1c; ADR 0021 D5, D6).

Each case below is run twice: by pinned Lean 4.35.0 (a Lean file this
script writes, calling Meta.isLevelDefEqAux, Expr.instantiate1 and
Expr.headBeta) and by LeanForth (tests/front/meta-cases.fs, calling
lf-level-defeq, lf-meta-instantiate1 and lf-meta-head-beta on the same
terms). Both print one line per case: the answer and every named level
metavariable's value afterwards, or the resulting term as an S-expression.
The lines must be equal, except that LeanForth's "unsupported" stands for
Lean's postponed level pair, and for the cases listed as gaps (levels with
max, which Lean normalizes and LeanForth does not port yet), where
LeanForth must answer unsupported and Lean's answer is shown. A harness
self-test first checks that a wrong line is told apart.

Usage: LEAN=... GFORTH=... python3 tests/front/check_meta.py
"""
import os
import pathlib
import re
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent.parent
LEAN = os.environ.get("LEAN", ".tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean")
GFORTH = os.environ.get("GFORTH", "gforth")
LIMIT = 300

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

# Term cases: ("inst1", body, value) or ("beta", term). Terms: P (Prop),
# x and y (free variables of type Prop), ?m (a metavariable of type
# Prop), #i (a bound variable), ("app", f, a), ("lam", T, b), ("pi", T, b).
LAM, PI, APP = "lam", "pi", "app"
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
]


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
    if text.startswith("(max "):
        inner = text[5:-1]
        depth = 0
        for i, ch in enumerate(inner):
            depth += {"(": 1, ")": -1}.get(ch, 0)
            if ch == " " and depth == 0:
                return ("max", level_parse(inner[:i]), level_parse(inner[i + 1:]))
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
        else:
            expr = f"(Expr.headBeta {term_lean(case[1])})"
        lines.append(f"    IO.println (← sx {expr})")
    return "\n".join(lines)


def lean_lines():
    text = LEAN_HEAD + "\n" + "\n\n".join(lean_level_case(l, r, ro) for l, r, ro, _ in LEVELS)
    text += "\n\n" + lean_term_cases() + "\n"
    with tempfile.TemporaryDirectory() as tmp:
        path = pathlib.Path(tmp) / "Meta.lean"
        path.write_text(text, encoding="utf-8")
        run = subprocess.run([LEAN, "-DwarningAsError=true", str(path)], cwd=ROOT,
                             stdin=subprocess.DEVNULL, capture_output=True, text=True,
                             timeout=LIMIT)
    lines = [line for line in run.stdout.splitlines() if line.strip()]
    if run.returncode != 0 or len(lines) != len(LEVELS) + len(TERMS):
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
        else:
            calls.append(f"{term_forth(case[1])} beta-run")
    run = subprocess.run([GFORTH, "tests/front/meta-cases.fs", "-e", " ".join(calls) + " bye"],
                         cwd=ROOT, stdin=subprocess.DEVNULL, capture_output=True, text=True,
                         timeout=LIMIT)
    lines = [line.strip() for line in run.stdout.splitlines() if line.strip()]
    if run.returncode != 0 or len(lines) != len(LEVELS) + len(TERMS):
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
    try:
        self_test()
        lean, forth = lean_lines(), forth_lines()
        gaps = []
        names = [f"{l} =?= {r}" for l, r, _, _ in LEVELS] + [str(c) for c in TERMS]
        gap_flags = [g for _, _, _, g in LEVELS] + [False] * len(TERMS)
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
    print(f"Meta layer: {len(LEVELS) - len(gaps)} level unifications and {len(TERMS)} "
          "instantiations and head-beta steps equal to pinned Lean's; "
          f"{len(gaps)} gaps answer unsupported: {'; '.join(gaps)}; harness self-test passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
