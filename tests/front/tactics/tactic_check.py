#!/usr/bin/env python3
"""A tactic's end-to-end check against pinned Lean (tactic plug-in design,
slice a2-iii; tests/front/tactics/NAME/check.py calls main with its lists).

1. Each accepted file (FILES) through `bin/leanforth check --env
   tests/front/s2-slice.ndjson --elab-data tests/front/s2-slice.elab.ndjson
   --steps -`: exit 0, each theorem named accepted with no axiom, the step
   log valid by schemas/tactic-steps-1.schema.json (tests/front/check_s2.py's
   check_log), and every theorem's type and value, dumped by
   tests/front/elab-dump.fs, equal to pinned Lean's node for node
   (tests/front/tactics/goal-layer.golden, the output of goal-layer.lean);
   the step logs, together, equal NAME/steps.golden (LeanForth's own,
   reviewed: each step's goals with their tags, in order).
2. Each wrong twin (WRONG): exit 4, the error code, Lean's first line and the
   detail given (as LeanForth prints them); each file not supported yet
   (UNSUPPORTED): exit 2 and the code, never accepted.
3. A tactic's own further check (main's EXTRA), such as intros/check.py's terms of goals no
   LeanForth text can state, whose lines (with a "NAME binders K ..." line of binder kinds)
   are in the same golden.
With --lean: pinned Lean writes the golden again (--write-golden keeps it)
and it must be unchanged, and pinned Lean refuses each wrong twin of
goal-layer-wrong.lean with the first line and detail the LeanForth file
must print (LEAN_SAME: the wrong twins whose text both print alike).

Usage: GFORTH=... python3 tests/front/tactics/NAME/check.py
       LEAN=... python3 tests/front/tactics/NAME/check.py --lean [--write-golden]
"""
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent.parent.parent
sys.path.insert(0, str(ROOT / "tests/front"))
import check_s2 as s2  # noqa: E402

TACTICS = ROOT / "tests/front/tactics"
GOLDEN = TACTICS / "goal-layer.golden"
DUMPED = re.compile(r"^\S+ (type|value|binders) ")


class Failure(Exception):
    pass


def golden():
    return {" ".join(line.split(" ", 2)[:2]): line
            for line in GOLDEN.read_text(encoding="utf-8").splitlines()}


def check_steps(name, logs):
    """The step logs against NAME/steps.golden (LeanForth's own, reviewed:
    the goals after each step, their tags and order; --write-steps writes it)."""
    path = TACTICS / name / "steps.golden"
    if "--write-steps" in sys.argv:
        path.write_text("\n".join(logs) + "\n", encoding="utf-8")
    if logs != path.read_text(encoding="utf-8").splitlines():
        raise Failure(f"the step logs differ from {path.relative_to(ROOT)} "
                      f"(--write-steps after a review)")


def check_files(files, want):
    """Each file's check and dump run side by side (LEANFORTH_TEST_JOBS), read in order."""
    logs = []
    finished = s2.run_many([argv for path, _ in files for argv in
                            (s2.check_argv(path, "--steps", "-"), s2.dump_argv(path))])
    for path, names in files:
        code, out = s2.outcome(next(finished))
        if code != 0:
            raise Failure(f"{path}: exit {code}\n{out}")
        logs += s2.step_lines(out)
        try:
            s2.check_log(path, s2.step_lines(out))
        except s2.Failure as exc:
            raise Failure(str(exc)) from exc
        for name in names:
            if f"\n{name}: accepted; axioms: none" not in "\n" + out:
                raise Failure(f"{path}: {name} not accepted with no axiom\n{out}")
        lines = s2.dump_lines(path, next(finished))
        if len(lines) != 2 * len(names):
            raise Failure(f"{path}: {len(lines)} dumped lines for {names}")
        for line in lines:
            key = " ".join(line.split(" ", 2)[:2])
            if want.get(key) != line:
                raise Failure(f"{path}: {key} differs from pinned Lean's:\n  LeanForth: {line}\n"
                              f"  Lean:      {want.get(key)}")
    return logs


def check_refused(wrong, unsupported):
    finished = s2.run_many([s2.check_argv(path) for path, *_ in list(wrong) + list(unsupported)])
    for path, number, first, detail in wrong:
        code, out = s2.outcome(next(finished))
        if code != 4 or f"error {number} at " not in out or f"{first}\n{detail}" not in out:
            raise Failure(f"{path}: exit {code}, expected 4, error {number} and "
                          f"{first!r}\n{detail!r}\n{out}")
    for path, number, text in unsupported:
        code, out = s2.outcome(next(finished))
        if code != 2 or f"error {number} at " not in out or text not in out:
            raise Failure(f"{path}: exit {code}, expected 2 with error {number}, {text!r}\n{out}")


def check_lean(wrong, write):
    done, wrong_done = s2.run_many([[s2.lean_binary(), source] for source in
                                    ("tests/front/tactics/goal-layer.lean",
                                     "tests/front/tactics/goal-layer-wrong.lean")])
    if done.returncode != 0:
        raise Failure(f"goal-layer.lean: exit {done.returncode}\n{done.stdout}{done.stderr}")
    lines = [line for line in done.stdout.splitlines() if DUMPED.match(line)]
    if write:
        GOLDEN.write_text("\n".join(lines) + "\n", encoding="utf-8")
    elif lines != GOLDEN.read_text(encoding="utf-8").splitlines():
        raise Failure("goal-layer.lean: pinned Lean's output is not goal-layer.golden")
    out = wrong_done.stdout + wrong_done.stderr
    missing = [first for _, _, first, detail in wrong if f"{first}\n{detail}" not in out]
    if wrong_done.returncode == 0 or missing:
        raise Failure(f"goal-layer-wrong.lean: exit {wrong_done.returncode}, missing {missing}\n{out}")


def main(name, files, wrong, unsupported, extra=None):
    """EXTRA, when given, is a further plain-mode check: a function taking golden()'s map that
    raises Failure or gives a phrase for the summary."""
    try:
        if "--lean" in sys.argv:
            check_lean(wrong, "--write-golden" in sys.argv)
            print(f"{name} --lean: goal-layer.lean gives {GOLDEN.name}; pinned Lean prints "
                  f"the {len(wrong)} wrong twins' messages")
            return
        check_steps(name, check_files(files, golden()))
        check_refused(wrong, unsupported)
        more = f"; {extra(golden())}" if extra else ""
        print(f"{name}: {len(files)} files accepted, their terms equal pinned Lean's node for "
              f"node and their step logs valid and as golden; {len(wrong)} wrong twins refused "
              f"with Lean's "
              f"messages; {len(unsupported)} not supported yet (exit 2){more}")
    except (Failure, subprocess.TimeoutExpired) as exc:
        print(f"{name}: {exc}", file=sys.stderr)
        sys.exit(1)
