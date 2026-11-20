#!/usr/bin/env python3
"""Tactic proofs read and run, end to end (plans FE1g-2 and FE1g-3;
src/front/tactic-syntax.fs, tactic-run.fs; docs/design/FE1G_TACTICS.md
sections 3 and 4).

1. The record of each FE1 file (FILES below), printed by
   tests/front/tactic-dump.fs in its format 1, with the error the run ends
   with, equals tests/front/tactics.golden line for line. A harness
   self-test first checks that a changed record is told apart.
2. The messages of src/author/errors.fs's catalogue for the codes of
   CODES (89, 90, 94, 96, 97), as LeanForth prints them, equal the
   messages below, which the Lean run checks against pinned Lean's.
3. `bin/leanforth check --env tests/front/tactic-slice.ndjson FILE` on
   each file, and with tests/front/run-slice.ndjson on the runner's files
   (RUN_FILES), exits 2 with error 139 at its end NAME (not supported yet:
   the elaborator, src/front/elab-decl.fs, needs the library's
   elaboration data, which these runs do not give; the runner's own outcomes are
   tests/front/tactic-run.fs's, with stand-in elaborators), and on
   malformed twins written here exits 4 with the twin's error code;
   nothing is checked, nothing accepted.
With --lean instead: pinned Lean, through scripts/export.sh, reproduces
the exports these tests run against (tests/front/tactic-slice.ndjson:
Nat.add_succ, Nat.zero_add and congrArg from Init, with what they use;
tests/front/run-slice.ndjson: Nat.zero_add, sorryAx and Bool.false) and
their manifests, byte for byte; pinned Lean parses or refuses the shapes
of tests/front/tactic-shapes.lean as the reader does (an empty proof, a
by-induction-with with no alternative, rw [] and dotted and nested names
read; an alternative with no tactic refused); and on
tests/front/tactic-run.lean pinned Lean gives the outcomes the runner's
tests pin: unsolved goals at by with exactly the goal lines
tests/front/tactic-run.fs compares (LEAN_GOALS), sorry accepted with the
warning "declaration uses `sorry`" (an error under -DwarningAsError=true,
which every Lean run of the tests passes; the theorem is added all the
same) and sorryAx its one axiom, "No goals to be solved" at a second
sorry, each error's first line the message errors.fs's catalogue has
for its code, the terms of the proofs tests/front/tactic-basic.fs pins
node for node, and the goal after intro on beta redexes.

Usage: GFORTH=... python3 tests/front/check_tactics.py
       LEAN=... python3 tests/front/check_tactics.py --lean
"""
import os
import pathlib
import re
import subprocess
import sys
import tempfile
import functools
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[2] / "scripts"))
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[2] / "tests/support"))
from parallel_runs import run_all  # noqa: E402  independent runs side by side, results in order
import lean_pin  # noqa: E402  $LEAN or the pinned Lean, refused unrun when an elan proxy


@functools.lru_cache(maxsize=None)
def lean_binary():
    """The Lean to run: scripts/lean_pin.py's pinned_lean ($LEAN, else this
    checkout's pinned toolchain), refused before it runs when it is an elan
    proxy or not Lean 4.35.0 (Forth review of reuse-b, finding 4)."""
    return lean_pin.pinned_lean()


ROOT = pathlib.Path(__file__).resolve().parent.parent.parent
GFORTH = os.environ.get("GFORTH", "gforth")
SLICE_NAMES = ["Nat.add_succ", "Nat.zero_add", "congrArg"]
GOLDEN = ROOT / "tests/front/tactics.golden"
SLICE = "tests/front/tactic-slice.ndjson"
RUN_SLICE_NAMES = ["Nat.zero_add", "sorryAx", "Bool.false"]
RUN_SLICE = "tests/front/run-slice.ndjson"
RUN_FILES = ["tests/front/05-unsolved.lf", "tests/front/06-sorry.lf",
             "tests/front/07-intro-exact.lf", "tests/front/08-rfl.lf"]
BASIC_TWIN = ROOT / "tests/front/tactic-basic.fs"
# FE1g-4's errors: each theorem's first message and the lines under it, as
# pinned Lean prints them and as tests/front/tactic-basic.fs pins them
# (message, lines; the Forth test holds the lines as one s\" literal, the
# blank line of Lean's tactic errors its first \n).
BASIC_ERRORS = {
    "intro_twice": ("Tactic `introN` failed: There are no additional binders or `let` "
                    "bindings in the goal to introduce", ["", "p : Prop", "a✝ : p", "⊢ p"]),
    "exact_sort": ("Type mismatch", ["  p", "has type", "  Prop",
                                     "of sort `Type` but is expected to have type", "  p",
                                     "of sort `Prop`"]),
    "exact_wrong": ("Type mismatch", ["  h", "has type", "  q",
                                      "but is expected to have type", "  p"]),
    "refl_wrong": ("Tactic `rfl` failed: The left-hand side",
                   ["  p", "is not definitionally equal to the right-hand side", "  q", "",
                    "p q : Prop", "⊢ p = q"]),
}
# The terms pinned Lean prints for the proofs tests/front/tactic-basic.fs
# compares node by node (the first two, refl_x and imp_pq also through the
# kernel).
BASIC_TERMS = ["fun (p : Prop) (h : p) => h", "fun (p : Prop) => @Eq.refl.{1} Prop p",
               "fun (a : Type) (x : a) => @Eq.refl.{1} a x", "fun (p q : Prop) (h : p) => h",
               "fun (p : Prop) (h1 h2 : p) => @Eq.refl.{0} p h1"]
# The goal trace_state prints after intro h in intro_beta and intro_whnf
# (tactic-basic.fs's h-goal): the domain and the body head-beta reduced.
INTRO_GOAL = ["p : Prop", "h : p", "⊢ p"]
# The catalogue code (src/author/errors.fs) of each theorem's first error,
# whose message must be pinned Lean's word for word (review fe1g3 L7).
CODES = {"zero_add_open": 89, "sorry_twice": 90, "intro_twice": 94, "exact_sort": 96,
         "exact_wrong": 96, "refl_wrong": 97}
LEAN_MESSAGES = {"zero_add_open": "unsolved goals", "sorry_twice": "No goals to be solved",
                 **{name: message for name, (message, _) in BASIC_ERRORS.items()}}
RUN_LEAN = ROOT / "tests/front/tactic-run.lean"
RUN_TWIN = ROOT / "tests/front/tactic-run.fs"
# The goal lines under Lean's "unsolved goals" for zero_add_open, which
# tests/front/tactic-run.fs pins as the detail of error 89 (lean-goals).
LEAN_GOALS = ["n : Nat", "⊢ 0 + n = n"]
LIMIT = 300
FILES = ["tests/front/01-zero-add-rw.lf", "tests/front/01-zero-add.lf",
         "tests/front/02-add-zero-rfl.lf", "tests/front/03-zero-add-exact.lf",
         "tests/front/04-nested-ih.lf"]

# Malformed twins of 01-zero-add-rw.lf: (what changes, old text, new text,
# the error the command line must print).
MAIN = (ROOT / FILES[0]).read_text(encoding="utf-8")
TWINS = [
    ("by-end missing", "  by-end\n", "", "error 82 at line:col 16:1"),
    ("| outside by-induction-with", "n by-induction-with", "n by-induction",
     "error 83 at line:col 14:3"),
    ("=> missing", "| zero =>  ", "| zero ", "error 84 at line:col 14:15"),
    ("] missing", "ih ]", "ih", "error 82 at line:col 16:3"),
    ("an empty alternative", "by-rfl\n", "\n", "error 85 at line:col 15:3"),
]


class Failure(Exception):
    pass


def run_command(command):
    """A finished run of (argument list, environment or None)."""
    argv, env = command
    return subprocess.run(argv, cwd=ROOT, stdin=subprocess.DEVNULL, capture_output=True, text=True,
                          timeout=LIMIT, env=env)


def run_many(commands):
    """run of each (argument list, environment or None), side by side
    (tests/support/parallel_runs.py; LEANFORTH_TEST_JOBS, 1 for one at a time): the finished
    runs in the order of commands."""
    return run_all(commands, run=run_command)


def dump_argv():
    calls = " ".join(f's" {path}" tactic-dump-file' for path in FILES)
    return [GFORTH, "src/main.fs", "tests/front/tactic-dump.fs", "-e", calls + " bye"]


def dump_records(done):
    if done.returncode != 0 or done.stderr:
        raise Failure(f"tactic-dump.fs: exit {done.returncode}\n{done.stdout}{done.stderr}")
    return done.stdout.splitlines()


def differ(got, want):
    """The first line where the records differ, or None."""
    for i, (a, b) in enumerate(zip(got, want)):
        if a != b:
            return f"line {i + 1}:\n  golden: {b}\n  record: {a}"
    if len(got) != len(want):
        return f"{len(got)} lines, the golden file has {len(want)}"
    return None


def self_test(want):
    """A record with one argument moved is told apart."""
    changed = [line.replace("@15:41", "@15:42") for line in want]
    if changed == want or differ(changed, want) is None:
        raise Failure("harness self-test: a changed record is not told apart")


def catalogue_argv():
    codes = sorted(set(CODES.values()))
    calls = " ".join(f"{code} lf-author-message type cr" for code in codes)
    return [GFORTH, "src/main.fs", "-e", calls + " bye"]


def catalogue_texts(done):
    """errors.fs's message for each code of CODES, as LeanForth prints it, from a finished run."""
    codes = sorted(set(CODES.values()))
    lines = done.stdout.splitlines()
    if done.returncode != 0 or done.stderr or len(lines) != len(codes):
        raise Failure(f"the catalogue: exit {done.returncode}\n{done.stdout}{done.stderr}")
    return dict(zip(codes, lines))


def catalogue():
    return catalogue_texts(run_command((catalogue_argv(), None)))


def check_catalogue(texts):
    for name, code in CODES.items():
        if texts[code] != LEAN_MESSAGES[name]:
            raise Failure(f"error {code}: errors.fs says {texts[code]!r}, pinned Lean on "
                          f"{name} {LEAN_MESSAGES[name]!r}")


def check_argv(path, slice_=SLICE):
    return ["bin/leanforth", "check", "--env", slice_, str(path)]


def check_command(path, slice_=SLICE):
    """The run of bin/leanforth check on path, as (argument list, environment)."""
    return check_argv(path, slice_), dict(os.environ, GFORTH=GFORTH)


def outcomes(finished):
    """(exit status, output) of each finished bin/leanforth run."""
    for done in finished:
        yield done.returncode, done.stdout + done.stderr


CHECKED = [(f, SLICE) for f in FILES] + [(f, RUN_SLICE) for f in RUN_FILES]


def read_files(finished):
    """The runs of CHECKED, in order: exit 2 with error 139, nothing accepted."""
    for path, _ in CHECKED:
        code, out = next(finished)
        if code != 2 or "error 139 at" not in out or "accepted" in out:
            raise Failure(f"{path}: exit {code}, expected 2 with error 139\n{out}")


def write_twins(work):
    """Each twin's file (None for a twin whose text to change is not in MAIN once)."""
    paths = []
    for number, (what, old, new, error) in enumerate(TWINS):
        folder = pathlib.Path(work) / str(number)
        folder.mkdir()
        path = folder / "twin.lf"
        once = MAIN.count(old) == 1
        if once:
            path.write_text(MAIN.replace(old, new), encoding="utf-8")
        paths.append(path if once else None)
    return paths


def read_twins(paths, finished):
    for (what, old, new, error), path in zip(TWINS, paths):
        if path is None:
            raise Failure(f"twin {what}: {old!r} is not in {FILES[0]} once")
        code, out = next(finished)
        if code != 4 or error not in out or "accepted" in out:
            raise Failure(f"twin {what}: exit {code}, expected 4 with {error}\n{out}")


def check_slice(slice_=SLICE, names=SLICE_NAMES):
    """The export and its manifest, made again by pinned Lean."""
    with tempfile.TemporaryDirectory() as work:
        made = pathlib.Path(work) / pathlib.Path(slice_).name
        run = subprocess.run(["bash", "scripts/export.sh", str(made), "Init", "--", *names],
                             cwd=ROOT, env=dict(os.environ, LEAN=lean_binary()), stdin=subprocess.DEVNULL,
                             capture_output=True, timeout=LIMIT)
        if run.returncode != 0:
            raise Failure(f"scripts/export.sh: exit {run.returncode}\n{run.stderr.decode()[-400:]}")
        for suffix in ("", ".manifest.json"):
            mine = (ROOT / f"{slice_}{suffix}").read_bytes()
            if pathlib.Path(str(made) + suffix).read_bytes() != mine:
                raise Failure(f"scripts/export.sh does not reproduce {slice_}{suffix}")


# The shapes of tests/front/tactic-shapes.lean: each theorem's first error
# as pinned Lean reports it, or None; FE1g-2 reads s1, s2, s3, s5 and s6
# and refuses s4 (error 85), as the unit tests check.
SHAPES = ROOT / "tests/front/tactic-shapes.lean"
SHAPE_ERRORS = {"s1": "unsolved goals", "s2": "Alternative `zero` has not been provided",
                "s3": None, "s4": "unexpected token '|'; expected", "s5": None, "s6": None}
ERROR = re.compile(r"^[^:]*:(\d+):\d+: error: (.*)$")


def theorem_at(lines, number):
    """The theorem whose text holds line number (from 1)."""
    name = None
    for i, line in enumerate(lines[:number], 1):
        if line.startswith("theorem "):
            name = line.split()[1]
    return name


def check_shapes():
    run = subprocess.run([lean_binary(), "-DwarningAsError=true", str(SHAPES)], cwd=ROOT,
                         stdin=subprocess.DEVNULL, capture_output=True, text=True, timeout=LIMIT)
    lines = SHAPES.read_text(encoding="utf-8").splitlines()
    first = {}
    for line in (run.stdout + run.stderr).splitlines():
        match = ERROR.match(line)
        if match:
            first.setdefault(theorem_at(lines, int(match.group(1))), match.group(2))
    for name, want in SHAPE_ERRORS.items():
        got = first.get(name)
        if (want is None) != (got is None) or (want is not None and not got.startswith(want)):
            raise Failure(f"tactic-shapes.lean: {name}: pinned Lean says {got!r}, expected {want!r}")


def lean_messages(path):
    """Pinned Lean's messages on path: (line, kind, text, following lines)."""
    run = subprocess.run([lean_binary(), "-DwarningAsError=true", str(path)], cwd=ROOT,
                         stdin=subprocess.DEVNULL, capture_output=True, text=True,
                         timeout=LIMIT)
    head = re.compile(r"^[^:]*:(\d+):\d+: (error|warning): (.*)$")
    messages = []
    for line in (run.stdout + run.stderr).splitlines():
        match = head.match(line)
        if match:
            messages.append((int(match.group(1)), match.group(2), match.group(3), []))
        elif messages:
            messages[-1][3].append(line)
    return messages, run.stdout + run.stderr


def check_run_lean():
    """The runner's outcomes as pinned Lean has them (tactic-run.lean)."""
    messages, out = lean_messages(RUN_LEAN)
    lines = RUN_LEAN.read_text(encoding="utf-8").splitlines()
    by_name = {}
    for number, kind, text, rest in messages:
        by_name.setdefault(theorem_at(lines, number), []).append((kind, text, rest))
    unsolved = by_name.get("zero_add_open", [])
    if not unsolved or unsolved[0][:2] != ("error", "unsolved goals") \
            or unsolved[0][2][:len(LEAN_GOALS)] != LEAN_GOALS:
        raise Failure(f"tactic-run.lean: zero_add_open: {unsolved!r}")
    for name in ("zero_add_sorry", "sorry_p"):
        said = [(kind, text) for kind, text, _ in by_name.get(name, [])]
        # Lean's warning, an error under -DwarningAsError=true (as every
        # Lean run of the tests); the theorem is added all the same.
        if said != [("error", "declaration uses `sorry`")]:
            raise Failure(f"tactic-run.lean: {name}: {said!r}")
        if f"'{name}' depends on axioms: [sorryAx]" not in out:
            raise Failure(f"tactic-run.lean: {name} does not depend on sorryAx alone")
    twice = by_name.get("sorry_twice", [])
    if not twice or twice[0][:2] != ("error", "No goals to be solved"):
        raise Failure(f"tactic-run.lean: sorry_twice: {twice!r}")
    pinned = 's\\" ' + "\\n".join(LEAN_GOALS) + '"'
    if pinned not in RUN_TWIN.read_text(encoding="utf-8"):
        raise Failure(f"tests/front/tactic-run.fs does not pin the goal lines {pinned}")
    basic = BASIC_TWIN.read_text(encoding="utf-8")
    for name, (message, lines) in BASIC_ERRORS.items():
        said = by_name.get(name, [])
        if not said or said[0][:2] != ("error", message) or said[0][2][:len(lines)] != lines:
            raise Failure(f"tactic-run.lean: {name}: {said[:1]!r}")
        pinned = 's\\" ' + "\\n".join(lines) + '"'
        if pinned not in basic:
            raise Failure(f"tests/front/tactic-basic.fs does not pin {name}'s lines {pinned}")
    for term in BASIC_TERMS:
        if term not in out:
            raise Failure(f"tactic-run.lean: pinned Lean does not print {term}")
    if out.count("\n".join(INTRO_GOAL)) != 2:
        raise Failure(f"tactic-run.lean: intro_beta, intro_whnf: not the goal {INTRO_GOAL}")
    pinned = 's\\" ' + "\\n".join(INTRO_GOAL) + '"'
    if pinned not in basic:
        raise Failure(f"tests/front/tactic-basic.fs does not pin the goal {pinned}")
    texts = catalogue()
    for name, code in CODES.items():
        said = by_name.get(name, [])
        if not said or said[0][1] != texts[code]:
            raise Failure(f"error {code}: errors.fs says {texts[code]!r}, pinned Lean on "
                          f"{name} {said[:1]!r}")


def main_lean():
    try:
        check_slice()
        check_slice(RUN_SLICE, RUN_SLICE_NAMES)
        check_shapes()
        check_run_lean()
    except Failure as error:
        print(f"check_tactics: {error}")
        return 1
    print(f"{SLICE}, {RUN_SLICE} and their manifests reproduced byte for byte by pinned "
          f"Lean; pinned Lean parses and refuses the {len(SHAPE_ERRORS)} shapes of "
          "tests/front/tactic-shapes.lean as the reader does, and gives the runner's "
          "outcomes, terms and goals of tests/front/tactic-run.lean, its messages "
          "errors.fs's")
    return 0


def main():
    if "--lean" in sys.argv[1:]:
        return main_lean()
    try:
        want = GOLDEN.read_text(encoding="utf-8").splitlines()
        self_test(want)
        with tempfile.TemporaryDirectory() as work:
            twins = write_twins(work)
            finished = run_many([(dump_argv(), None), (catalogue_argv(), None)]
                                + [check_command(path, slice_) for path, slice_ in CHECKED]
                                + [check_command(path) for path in twins if path is not None])
            records, texts = next(finished), next(finished)
            checked = outcomes(finished)
            problem = differ(dump_records(records), want)
            if problem:
                raise Failure(f"the records differ from {GOLDEN.relative_to(ROOT)}, {problem}")
            check_catalogue(catalogue_texts(texts))
            read_files(checked)
            read_twins(twins, checked)
    except Failure as error:
        print(f"check_tactics: {error}")
        return 1
    print(f"tactic records: {len(FILES)} files read as tests/front/tactics.golden says; "
          f"errors.fs's messages for codes {sorted(set(CODES.values()))} as pinned; "
          f"leanforth check stops each and {len(RUN_FILES)} more with error 139 (exit 2) "
          f"and {len(TWINS)} malformed twins with their errors (exit 4); harness "
          "self-test passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
