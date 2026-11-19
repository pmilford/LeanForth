#!/usr/bin/env python3
"""The natural reader against pinned Lean (plan FE1a; ADR 0021 D4, D8).

Each statement below is written in Lean and in natural LeanForth. Pinned
Lean 4.35.0 expands the Lean spelling's macros (tests/front/operators.lean,
every nested macro too: `0 + n = n` is `binrel% Eq (binop% HAdd.hAdd 0 n)
n`); the natural reader builds a syntax tree from the LeanForth spelling
(tests/front/trees.fs prints it). Both are parsed into the same nested
form and must be equal, statement for statement: the operator words build
Lean's macros of Lean's constants, and a name takes its explicit arguments
in Lean's order. A harness self-test first checks that a wrong tree is
told apart. Syntax only: nothing is elaborated or checked.

It also checks that pinned Lean, through scripts/export.sh, reproduces the
export tests/front/front.fs reads for argument counts that depend on
unfolding (tests/front/unfold-slice.ndjson, from
tests/reference/front-unfold.lean) and its manifest, byte for byte.

Usage: LEAN=... GFORTH=... python3 tests/front/check_front.py
"""
import os
import pathlib
import re
import subprocess
import sys
import tempfile
import functools
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[2] / "scripts"))
import lean_pin  # noqa: E402  $LEAN or the pinned Lean, refused unrun when an elan proxy


@functools.lru_cache(maxsize=None)
def lean_binary():
    """The Lean to run: scripts/lean_pin.py's pinned_lean ($LEAN, else this
    checkout's pinned toolchain), refused before it runs when it is an elan
    proxy or not Lean 4.35.0 (Forth review of reuse-b, finding 4)."""
    return lean_pin.pinned_lean()


ROOT = pathlib.Path(__file__).resolve().parent.parent.parent
GFORTH = os.environ.get("GFORTH", "gforth")
LIMIT = 300

# (the Lean spelling as in operators.lean, the natural LeanForth spelling)
CASES = [
    ("0 + n = n", "0 n + n ="),
    ("2 * 3 ≤ 7", "2 3 * 7 ≤"),
    ("0 + n + m = m * n", "0 n + m + m n * ="),
    ("Nat.succ n = n + 1", "n Nat.succ n 1 + ="),
    ("n = 0 + (n + 0)", "n 0 n 0 + + ="),
    ("congrArg Nat.succ n = n", "' Nat.succ n congrArg n ="),
]


class Failure(Exception):
    pass


def tokens(text):
    """Tokens of a printed tree; Lean's hygiene marks (✝, ✝¹) dropped."""
    text = re.sub("✝[⁰¹²³⁴⁵⁶⁷⁸⁹]*", "", text)
    return re.findall(r"[()]|[^\s()]+", text)


def parse(toks):
    """binop%/binrel% NAME A B, ( HEAD ARGS... ), ( binop% ... ) or an atom,
    as nested tuples; the whole line must be one expression."""
    def expr(i):
        tok = toks[i]
        if tok in ("binop%", "binrel%"):
            a, j = expr(i + 2)
            b, k = expr(j)
            return (tok, toks[i + 1], a, b), k
        if tok == "(":
            if toks[i + 1] in ("binop%", "binrel%"):
                inner, j = expr(i + 1)
            else:
                items, j = [], i + 1
                while toks[j] != ")":
                    item, j = expr(j)
                    items.append(item)
                inner = ("app", *items) if len(items) > 1 else items[0]
            if toks[j] != ")":
                raise Failure(f"unbalanced: {' '.join(toks)}")
            return inner, j + 1
        if tok == ")":
            raise Failure(f"unexpected ): {' '.join(toks)}")
        return tok, i + 1
    tree, end = expr(0)
    if end != len(toks):
        raise Failure(f"trailing tokens: {' '.join(toks)}")
    return tree


def lean_trees():
    run = subprocess.run([lean_binary(), "-DwarningAsError=true", "tests/front/operators.lean"], cwd=ROOT,
                         stdin=subprocess.DEVNULL, capture_output=True, text=True, timeout=LIMIT)
    lines = [line for line in run.stdout.splitlines() if line.strip()]
    if run.returncode != 0 or len(lines) != len(CASES):
        raise Failure(f"pinned Lean on operators.lean: exit {run.returncode}\n{run.stdout}{run.stderr}")
    source = (ROOT / "tests/front/operators.lean").read_text(encoding="utf-8")
    for case, _ in CASES:
        if f"#expand {case}\n" not in source:
            raise Failure(f"operators.lean lacks #expand {case}")
    return [parse(tokens(line)) for line in lines]


def forth_trees():
    calls = " ".join(f's" {lf}" tree' for _, lf in CASES)
    run = subprocess.run([GFORTH, "src/main.fs", "tests/front/trees.fs", "-e", calls + " bye"],
                         cwd=ROOT, stdin=subprocess.DEVNULL, capture_output=True, text=True,
                         timeout=LIMIT)
    lines = [line for line in run.stdout.splitlines() if line.strip()]
    if run.returncode != 0 or len(lines) != len(CASES):
        raise Failure(f"trees.fs: exit {run.returncode}\n{run.stdout}{run.stderr}")
    return [parse(tokens(line)) for line in lines]


def self_test():
    """The comparison tells a swapped operand and a missing macro apart."""
    good = parse(tokens("binrel% Eq✝ (binop% HAdd.hAdd✝ 0 n) n"))
    for wrong in ("binrel% Eq (binop% HAdd.hAdd n 0) n", "binrel% Eq (HAdd.hAdd 0 n) n",
                  "binop% Eq (binop% HAdd.hAdd 0 n) n"):
        if parse(tokens(wrong)) == good:
            raise Failure(f"harness self-test: {wrong} not told apart")


def check_unfold_slice():
    """The fixture export and its manifest, made again by pinned Lean."""
    with tempfile.TemporaryDirectory() as work:
        work = pathlib.Path(work)
        env = dict(os.environ, LEAN=lean_binary(), LEAN_PATH=str(work))
        run = subprocess.run([lean_binary(), "-DwarningAsError=true", "-o", str(work / "FrontUnfold.olean"),
                              "tests/reference/front-unfold.lean"], cwd=ROOT, env=env,
                             stdin=subprocess.DEVNULL, capture_output=True, timeout=LIMIT)
        if run.returncode != 0:
            raise Failure("pinned Lean refuses tests/reference/front-unfold.lean")
        made = work / "unfold-slice.ndjson"
        run = subprocess.run(["bash", "scripts/export.sh", str(made), "FrontUnfold", "--", "c", "d"],
                             cwd=ROOT, env=env, stdin=subprocess.DEVNULL, capture_output=True,
                             timeout=LIMIT)
        if run.returncode != 0:
            raise Failure(f"scripts/export.sh: exit {run.returncode}\n{run.stderr.decode()[-400:]}")
        for suffix in ("", ".manifest.json"):
            mine = (ROOT / f"tests/front/unfold-slice.ndjson{suffix}").read_bytes()
            if pathlib.Path(str(made) + suffix).read_bytes() != mine:
                raise Failure(f"scripts/export.sh does not reproduce unfold-slice.ndjson{suffix}")


def main():
    try:
        self_test()
        check_unfold_slice()
        lean, forth = lean_trees(), forth_trees()
        for (spelling, lf), want, got in zip(CASES, lean, forth):
            if want != got:
                raise Failure(f"{spelling} / {lf}:\n  Lean:   {want}\n  reader: {got}")
    except Failure as error:
        print(f"check_front: {error}")
        return 1
    print(f"natural reader: {len(CASES)} statements read as pinned Lean expands them "
          "(binop%, binrel%, applications); harness self-test passed; "
          "tests/front/unfold-slice.ndjson reproduced byte for byte")
    return 0


if __name__ == "__main__":
    sys.exit(main())
