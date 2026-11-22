#!/usr/bin/env python3
"""A tactic's end-to-end check against pinned Lean (tactic plug-in design,
slice a2-iii; tests/front/tactics/NAME/check.py calls main with its lists).

1. Each accepted file (FILES) through `bin/leanforth check --env
   tests/front/s2-slice.ndjson --elab-data tests/front/s2-slice.elab.ndjson
   --steps -`: exit 0, each theorem named accepted with no axiom (a name
   written NAME=AXIOMS: with the checker's report AXIOMS instead), the step
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
A batch of tactics (plan row TB2: tests/front/tactics/batch-*/) keeps its own
Lean twins and golden: main's lean=, lean_wrong= and golden= name them (the
defaults are goal-layer.lean, goal-layer-wrong.lean and goal-layer.golden), so
batches edit no shared file.

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
LEAN_TWINS = "tests/front/tactics/goal-layer.lean"
LEAN_WRONG = "tests/front/tactics/goal-layer-wrong.lean"
DUMPED = re.compile(r"^\S+ (type|value|binders) ")
SEE = re.compile(r"; see line:col \d+:\d+")


class Failure(Exception):
    pass


def golden(path=GOLDEN):
    """The golden's lines by their first two words (NAME type, NAME value, NAME binders)."""
    return {" ".join(line.split(" ", 2)[:2]): line
            for line in pathlib.Path(path).read_text(encoding="utf-8").splitlines()}


read_golden = golden   # main's own name for it, whose golden= argument is a path


def check_steps(name, logs):
    """The step logs against NAME/steps.golden (LeanForth's own, reviewed:
    the goals after each step, their tags and order; --write-steps writes it)."""
    path = TACTICS / name / "steps.golden"
    if "--write-steps" in sys.argv:
        path.write_text("\n".join(logs) + "\n", encoding="utf-8")
    if logs != path.read_text(encoding="utf-8").splitlines():
        raise Failure(f"the step logs differ from {path.relative_to(ROOT)} "
                      f"(--write-steps after a review)")


class Env:
    """The library a tactic's files are checked against: the S2 slice by default (None), or
    another export, its elaboration data and tests/front/elab-dump.fs's word that dumps
    against them (decide's: plan S3a)."""

    def __init__(self, export, data, dump_word):
        self.export, self.data, self.dump_word = export, data, dump_word


def check_argv(env, path, *more):
    if env is None:
        return s2.check_argv(path, *more)
    return ["bin/leanforth", "check", "--env", env.export, "--elab-data", env.data, *more, path]


def dump_argv(env, path):
    if env is None:
        return s2.dump_argv(path)
    return [s2.GFORTH, "tests/front/elab-dump.fs", "-e", f's" {path}" {env.dump_word} bye']


def theorem_axioms(entry):
    """A FILES name, NAME or NAME=AXIOMS: the theorem and the axiom report its line must give
    (none, or the checker's list, as a by_cases over Classical.propDecidable needs)."""
    name, _, axioms = entry.partition("=")
    return name, axioms or "none"


def check_files(files, want, env=None):
    """Each file's check and dump run side by side (LEANFORTH_TEST_JOBS), read in order."""
    logs = []
    finished = s2.run_many([argv for path, _ in files for argv in
                            (check_argv(env, path, "--steps", "-"), dump_argv(env, path))])
    for path, names in files:
        code, out = s2.outcome(next(finished))
        if code != 0:
            raise Failure(f"{path}: exit {code}\n{out}")
        logs += s2.step_lines(out)
        try:
            s2.check_log(path, s2.step_lines(out))
        except s2.Failure as exc:
            raise Failure(str(exc)) from exc
        for entry in names:
            name, axioms = theorem_axioms(entry)
            if f"\n{name}: accepted; axioms: {axioms}" not in "\n" + out:
                raise Failure(f"{path}: {name} not accepted with axioms {axioms}\n{out}")
        lines = s2.dump_lines(path, next(finished))
        if len(lines) != 2 * len(names):
            raise Failure(f"{path}: {len(lines)} dumped lines for {names}")
        for line in lines:
            key = " ".join(line.split(" ", 2)[:2])
            if want.get(key) != line:
                raise Failure(f"{path}: {key} differs from pinned Lean's:\n  LeanForth: {line}\n"
                              f"  Lean:      {want.get(key)}")
    return logs


def check_refused(wrong, unsupported, env=None):
    """A wrong twin's message is compared without LeanForth's second place (an elaborator's
    error inside a tactic: "; see line:col L:C" at the first line's end, which Lean's
    message has not; tactic batch 3c's ⟨ ⟩ errors)."""
    finished = s2.run_many([check_argv(env, path) for path, *_ in list(wrong) + list(unsupported)])
    for path, number, first, detail in wrong:
        code, out = s2.outcome(next(finished))
        out = SEE.sub("", out)
        if code != 4 or f"error {number} at " not in out or f"{first}\n{detail}" not in out:
            raise Failure(f"{path}: exit {code}, expected 4, error {number} and "
                          f"{first!r}\n{detail!r}\n{out}")
    for path, number, text in unsupported:
        code, out = s2.outcome(next(finished))
        if code != 2 or f"error {number} at " not in out or text not in out:
            raise Failure(f"{path}: exit {code}, expected 2 with error {number}, {text!r}\n{out}")


def check_lean(wrong, write, lean=LEAN_TWINS, lean_wrong=LEAN_WRONG, golden_path=GOLDEN):
    """Pinned Lean runs LEAN (its dump must be GOLDEN_PATH, or becomes it with WRITE) and
    LEAN_WRONG (it must fail, printing each wrong twin's first line and detail)."""
    golden_path = pathlib.Path(golden_path)
    done, wrong_done = s2.run_many([[s2.lean_binary(), source] for source in (lean, lean_wrong)])
    if done.returncode != 0:
        raise Failure(f"{lean}: exit {done.returncode}\n{done.stdout}{done.stderr}")
    lines = [line for line in done.stdout.splitlines() if DUMPED.match(line)]
    if write:
        golden_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    elif lines != golden_path.read_text(encoding="utf-8").splitlines():
        raise Failure(f"{lean}: pinned Lean's output is not {golden_path.name}")
    out = wrong_done.stdout + wrong_done.stderr
    missing = [first for _, _, first, detail in wrong if f"{first}\n{detail}" not in out]
    if wrong_done.returncode == 0 or missing:
        raise Failure(f"{lean_wrong}: exit {wrong_done.returncode}, missing {missing}\n{out}")


def main(name, files, wrong, unsupported, extra=None, env=None, lean=LEAN_TWINS,
         lean_wrong=LEAN_WRONG, golden=GOLDEN):
    """EXTRA, when given, is a further plain-mode check: a function taking golden()'s map that
    raises Failure or gives a phrase for the summary. ENV, when given, is the library (Env)
    the files are checked and dumped against, else the S2 slice. LEAN, LEAN_WRONG and GOLDEN
    name the Lean twins, the wrong twins and the golden (a batch's own; goal-layer's by
    default)."""
    try:
        if "--lean" in sys.argv:
            check_lean(wrong, "--write-golden" in sys.argv, lean, lean_wrong, golden)
            print(f"{name} --lean: {pathlib.Path(lean).name} gives {pathlib.Path(golden).name}; "
                  f"pinned Lean prints the {len(wrong)} wrong twins' messages")
            return
        want = read_golden(golden)
        check_steps(name, check_files(files, want, env))
        check_refused(wrong, unsupported, env)
        more = f"; {extra(want)}" if extra else ""
        print(f"{name}: {len(files)} files accepted, their terms equal pinned Lean's node for "
              f"node and their step logs valid and as golden; {len(wrong)} wrong twins refused "
              f"with Lean's "
              f"messages; {len(unsupported)} not supported yet (exit 2){more}")
    except (Failure, subprocess.TimeoutExpired) as exc:
        print(f"{name}: {exc}", file=sys.stderr)
        sys.exit(1)
