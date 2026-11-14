#!/usr/bin/env python3
"""The elaborator against pinned Lean (plan S1; src/front/elab-pending.fs,
elab-app.fs, elab-term.fs, elab-decl.fs; docs/design/S1_INTERFACE.md 11).

1. tests/front/s1-now.lf (what runs with no instance search) through
   `bin/leanforth check --env tests/front/s1-slice.ndjson --elab-data ...`:
   exit 0, every theorem accepted, its #check lines printed as pinned Lean
   prints them (tests/front/s1-now.golden, the output of
   tests/front/s1-now.lean) except the printer gaps listed below; and the
   theorems' types and values, dumped by tests/front/elab-dump.fs, equal
   pinned Lean's node for node (the golden's S-expression lines).
2. The S1 files that wait for instance search (plan FE1e5, synth.fs) and
   lazy delta (S2 merge A, outParam unfolded): each stops with error 139
   (exit 2), nothing checked, nothing accepted (PENDING; SWITCH: then each
   gives pinned Lean's answer, shown with --lean).
3. --elab-fuel 3: exhausted, error 138, exit 3; its misuses refused (exit
   4); a text of only #check lines exits 0 with "nothing checked by the
   kernel".
A harness self-test first checks that a changed golden line is told apart.
With --lean: pinned Lean writes the golden again (--write-golden keeps
it) and it must be unchanged; the S1 twins give the answers the pending
files will have: s1-check.lean prints 0 + 0 = 0 : Prop, s1-rfl.lean is
accepted, s1-rfl-wrong.lean fails with "Tactic `rfl` failed".

Usage: GFORTH=... python3 tests/front/check_elab.py
       LEAN=... GFORTH=... python3 tests/front/check_elab.py --lean [--write-golden]
"""
import os
import pathlib
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent.parent
GFORTH = os.environ.get("GFORTH", "gforth")
LEAN = os.environ.get("LEAN", ".tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean")
LIMIT = 600
SLICE = "tests/front/s1-slice.ndjson"
DATA = "tests/front/s1-slice.elab.ndjson"
NOW = "tests/front/s1-now.lf"
NOW_LEAN = "tests/front/s1-now.lean"
GOLDEN = ROOT / "tests/front/s1-now.golden"
THEOREMS = ["zero_eq", "zero_eq_term", "self_eq", "succ_eq", "succ_eq_exact"]
# LeanForth's printer shows an implicit argument with @ where its binder's
# kind is not known (present/term-printer.fs; plan 8.6): the term is the
# same, the elaborated declarations are compared node for node.
PRINTER_GAPS = {"@Eq.refl Nat Nat.zero : Nat.zero = Nat.zero":
                "Eq.refl Nat.zero : Nat.zero = Nat.zero"}
# The S1 files and what pinned Lean gives (SWITCH when synth.fs and S2's
# merge A land: then LeanForth's answer is Lean's).
PENDING = [("tests/front/s1-check.lf", "tests/front/s1-check.lean", "0 + 0 = 0 : Prop"),
           ("tests/front/s1-rfl.lf", "tests/front/s1-rfl.lean", ""),
           ("tests/front/s1-rfl-wrong.lf", "tests/front/s1-rfl-wrong.lean",
            "Tactic `rfl` failed")]


class Failure(Exception):
    pass


def run(args, **kw):
    return subprocess.run(args, cwd=ROOT, stdin=subprocess.DEVNULL, capture_output=True,
                          text=True, timeout=LIMIT, env=dict(os.environ, GFORTH=GFORTH), **kw)


def check(path, *extra):
    done = run(["bin/leanforth", "check", "--env", SLICE, "--elab-data", DATA, *extra, path])
    return done.returncode, done.stdout + done.stderr


def dump(path):
    done = run([GFORTH, "tests/front/elab-dump.fs", "-e", f's" {path}" elab-dump bye'])
    if done.returncode != 0:
        raise Failure(f"elab-dump.fs {path}: exit {done.returncode}\n{done.stdout}{done.stderr}")
    return [line for line in done.stdout.splitlines() if " type " in line or " value " in line]


def golden():
    return GOLDEN.read_text(encoding="utf-8").splitlines()


def checks_of(lines):
    return [line for line in lines if " : " in line and " type " not in line
            and " value " not in line]


def terms_of(lines):
    return [line for line in lines if " type (" in line or " value (" in line]


def differ(got, want):
    if got == want:
        return None
    for i, (g, w) in enumerate(zip(got, want)):
        if g != w:
            return f"line {i + 1}:\n  LeanForth: {g}\n  Lean:      {w}"
    return f"{len(got)} lines, Lean has {len(want)}"


def self_test(want):
    wrong = list(want)
    wrong[0] = wrong[0].replace("Nat.zero", "Nat.succ", 1)
    if differ(wrong, want) is None:
        raise Failure("harness self-test: a changed line is not told apart")


def check_now(want):
    code, out = check(NOW)
    if code != 0:
        raise Failure(f"{NOW}: exit {code}\n{out}")
    for name in THEOREMS:
        if f"{name}: accepted" not in out:
            raise Failure(f"{NOW}: {name} not accepted\n{out}")
    printed = [PRINTER_GAPS.get(line, line) for line in checks_of(out.splitlines())]
    bad = differ(printed, checks_of(want))
    if bad:
        raise Failure(f"{NOW}: #check lines differ from pinned Lean's, {bad}")
    bad = differ(dump(NOW), terms_of(want))
    if bad:
        raise Failure(f"{NOW}: elaborated terms differ from pinned Lean's, {bad}")


def check_pending():
    for path, _, _ in PENDING:
        code, out = check(path)
        if code != 2 or "error 139 at" not in out or "accepted" in out:
            raise Failure(f"{path}: exit {code}, expected 2 with error 139 (pending)\n{out}")


def check_limits():
    code, out = check(NOW, "--elab-fuel", "3")
    if code != 3 or "error 138 at" not in out:
        raise Failure(f"--elab-fuel 3: exit {code}, expected 3 with error 138\n{out}")
    with tempfile.TemporaryDirectory() as work:
        only = pathlib.Path(work) / "only.lf"
        only.write_text("Nat.zero Nat.zero = #check\n", encoding="utf-8")
        code, out = check(str(only))
        if code != 0 or "nothing checked by the kernel" not in out:
            raise Failure(f"#check only: exit {code}\n{out}")
    for args, said in MISUSES:
        done = run(["bin/leanforth", "check", *args])
        if done.returncode != 4 or said not in done.stdout + done.stderr:
            raise Failure(f"leanforth check {' '.join(args)}: exit {done.returncode}, "
                          f"expected 4 with {said!r}\n{done.stdout}{done.stderr}")


# --elab-fuel's misuses: each refused before anything runs (exit 4).
MISUSES = (
    (["--elab-fuel", "5", SLICE], "--elab-fuel goes only with a LeanForth text (FILE.lf)"),
    (["--env", SLICE, "--elab-fuel", "x5", NOW], "not an elaboration fuel amount: x5"),
    (["--env", SLICE, "--elab-fuel", "9007199254740992", NOW],
     "an elaboration fuel above 9007199254740991: 9007199254740992"),
    (["--env", SLICE, NOW, "--elab-fuel"], "an option without its value: --elab-fuel"),
)


def lean(path):
    done = run([LEAN, "-j", "2", "-DwarningAsError=true", path])
    return done.returncode, done.stdout + done.stderr


def check_lean(write):
    code, out = lean(NOW_LEAN)
    if code != 0:
        raise Failure(f"{NOW_LEAN}: exit {code}\n{out}")
    if write:
        GOLDEN.write_text(out, encoding="utf-8")
    elif out.splitlines() != golden():
        raise Failure(f"{NOW_LEAN}: pinned Lean's output is not {GOLDEN.name}")
    for _, twin, said in PENDING:
        code, out = lean(twin)
        if said not in out or (code == 0) != ("failed" not in said):
            raise Failure(f"{twin}: exit {code}, expected {said!r}\n{out}")


def main():
    want = golden()
    self_test(want)
    if "--lean" in sys.argv:
        check_lean("--write-golden" in sys.argv)
        print(f"check_elab --lean: {NOW_LEAN} gives {GOLDEN.name}; the S1 twins give "
              f"the pending files' answers; harness self-test passed")
        return
    check_now(want)
    check_pending()
    check_limits()
    print(f"check_elab: {NOW}: {len(THEOREMS)} theorems accepted, their terms equal pinned "
          f"Lean's node for node, #check lines as Lean's ({len(PRINTER_GAPS)} printer gap); "
          f"{len(PENDING)} S1 files pending (error 139); --elab-fuel and #check-only exits; "
          f"harness self-test passed")


if __name__ == "__main__":
    try:
        main()
    except (Failure, subprocess.TimeoutExpired) as exc:
        print(f"check_elab: {exc}", file=sys.stderr)
        sys.exit(1)
