#!/usr/bin/env python3
"""Block coverage of the Forth source (plan task 1.4.1): make coverage.

Usage (from the repository root):
  python3 scripts/coverage.py [--gforth GFORTH] [--files] [--uncovered OUTPUT]
                              [--keep DIR] [--save-full PATH] [--check [--only FILE]... |
                              --update-baseline [--reason TEXT]] [-- COMMAND ...]
  python3 scripts/coverage.py --file FILE [--tests "TEST..."] [--all-tests] [--jobs N]
  python3 scripts/coverage.py --changed [BASE] [--jobs N]
  python3 scripts/coverage.py --set-baseline FILE --blocks N [--total M] [--reason TEXT]
  python3 scripts/coverage.py --drop-baseline FILE
  python3 scripts/coverage.py --debt

Runs COMMAND (default: make test) with GFORTH set to
scripts/coverage-gforth.sh, so that every Gforth run of the command, the
Python tests' too, loads Gforth 1.0's coverage.fs first and leaves its
block counts (scripts/coverage-prelude.fs). Then it joins the counts of
all runs and prints, for each folder of src/, the basic blocks compiled
in any run and how many of them ran at least once. make test's smoke
check loads every module of src/ on its own, so every block counts, also
those of modules no test runs.

A block is Gforth's: the code from one counter to the next, a counter
being placed at each colon definition's start, at each control-flow word
and at the start of each source line inside a definition. A block that ran
is not a tested block: the measure finds code no test reaches, and says
nothing about whether the tests check what that code does (make mutants
asks that). Runs that end with an uncaught THROW (such as the harness's
deliberate failures) leave no counts.

Every Gforth run goes through the counting wrapper: the Makefile keeps a GFORTH
that names scripts/coverage-gforth.sh, bin/leanforth's --fast finds
scripts/gforth-fast beside it, which hands over to the wrapper, and Python
tests that start $GFORTH use it. The measurement fails (exit 1) when no run left
counts, when more than 10% of the runs left none, or when fewer runs left counts
than 90% of tests/coverage-baseline.json's "runs": the tool must never again stop
counting silently, as it did unnoticed until 2026-11-12.

--check compares each file's never-run blocks with tests/coverage-baseline.json
(the ratchet, make coverage-check) and fails when a file's grow or a file the
baseline lacks has any never-run block. --update-baseline rewrites the baseline
from this measurement; a new file with never-run blocks needs --reason TEXT, kept
in the baseline, and the other files keep their reasons.

--only FILE (repeatable; make coverage-focus) limits --check to those files: run
by hand with COMMAND every target of make test that loads or runs FILE (unit and
end-to-end), FILE's counts are those of the whole make test. A FILE no run loaded
is noted, not failed (make daily's full run measures it), and the checks of the run
counts against the baseline's, which assume all of make test, are left out. No
change tier runs it since 2026-11-19 (owner): they run --changed instead.

--per-target FILE writes, for each file, each make target's compiled and run
blocks (JSON): a focused run of any set of targets can then be computed from
one full run (focused_never_run). Each run is attributed to its target through
the Makefile's RUN (scripts/timed.sh sets LF_MAKE_TARGET; this tool sets
LF_TIMING_LOG when it is unset so that RUN goes through it).

--files also prints every file; --uncovered OUTPUT writes each block that never
ran, as file:line:column, to the new file OUTPUT (an output file: never a path
under src/, tests/, scripts/ or docs/, nor a file git tracks, which it would
overwrite); --keep keeps the raw counts in DIR. --save-full PATH (make coverage
and make coverage-check, into the main checkout's untracked
.claude/work/coverage/last-full-run.json) keeps each file's never-run blocks of a
run of all of make test, for --file to compare with. The command must pass: a
failure is reported and the exit status is 1. Needs Gforth 1.0 (Gforth 0.7.3
has no coverage.fs) and the files under scripts/.

Which unit tests (make cover and --changed; TESTING_STRATEGY.md "Paying coverage debt"):
the Forth unit test files that load FILE are the Forth files under tests/ that the recipes
of make test's unit targets name (make -n; tests/test-classes.txt) whose require closure
holds FILE, directly or through src/main.fs or any other chain. When there are more than
NARROW_ABOVE (8) of them, the narrowed set runs first: those that name a word FILE defines
and those of FILE's module folders (tests/TOP directly for src/TOP/..., and all of
tests/DIR/STEM/ for src/DIR/STEM.fs, a plug-in's own tests); when a block it asks about is
left never run, every other one that loads FILE runs too before the report (so a test that
reaches FILE only through text, a .lf file or a name built at run time, still counts).
--tests names the tests instead (no widening), --all-tests runs them all at once. Each
test file runs on its own under the counting wrapper, --jobs at a time (default JOBS or 4).

Paying coverage debt (make cover, make cover-debt): --file FILE (make cover FILE=...) runs
FILE's unit tests so, in seconds, and prints FILE's blocks, its never-run blocks now, the
baseline's count and reason, and each never-run block: its lines, the word it is in, its
source text, whether the baseline's reason names one of its lines, and whether the last
saved full run (--save-full) left it never run too. A unit-test-only run can show more
never-run blocks than the ratchet, whose count is over all of make test (end-to-end targets
run code too). Exit 0 when the count is not above the baseline's, 1 when it is or a test
failed, 2 when no test loads FILE.

The branch coverage check (make cover-changed [BASE=...]; owner, 2026-11-19,
OWNER_DECISIONS.md "Coverage in the branch in seconds, the whole-suite ratchet at night";
make tier and scripts/push.sh run it, make daily the whole-suite ratchet): --changed [BASE]
finds the merge base of BASE (default main) and HEAD, and the Forth files of src/ added or
modified since (committed, uncommitted, new; deleted ones skipped), and for each the lines
the branch added or changed: those of each hunk of git diff -U0 whose code differs, comment
and blank lines left out (a hunk that edits only comments or white space changes no code). A
file that defines no word, or whose changes are all comments, needs no run. The others' unit
tests run as above (each test file once for all of them, widening for a file with a
never-run block on a changed line), and every never-run block on a changed line is printed
as file:line: word: source text. Exit 1 when there is one, when a touched file has no unit
test that loads it, or when a test fails; 0 otherwise. The one exception: a block whose line
the file's baseline entry names in a reason that starts with "unreachable:" (code no input
can reach) is printed as accepted. The output is in a fixed order; the time goes to stderr.

--set-baseline FILE --blocks N changes FILE's entry of the baseline alone,
without a run: lowering needs nothing; raising needs --reason; a new entry
needs --total M (the file's blocks), and with never-run blocks for a file that
had none --reason must name each of them by its line number. --drop-baseline
FILE removes the entry. Both print the old and the new entry. --debt (make
cover-debt) lists every entry with never-run blocks, largest first, with its
reason: the to-do list of the debt.
"""
import argparse
import collections
import hashlib
import importlib.util
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
WRAPPER = ROOT / "scripts/coverage-gforth.sh"
PRELUDE = ROOT / "scripts/coverage-prelude.fs"
COUNT_HEAD = re.compile(r"^(.+):(\d+):(\d+)$")
BASELINE = ROOT / "tests/coverage-baseline.json"
SHORTFALL = 0.9   # fewer runs with counts than this share of the baseline's fails
MAKE_VARIABLES = ("MAKEFLAGS", "MAKELEVEL", "MFLAGS", "MAKEOVERRIDES")


def resolve(gforth):
    if "/" in gforth:
        return str((Path.cwd() / gforth).resolve())
    found = shutil.which(gforth)
    return found or gforth


def has_coverage(gforth):
    """Whether this Gforth loads the prelude (it needs coverage.fs)."""
    env = {k: v for k, v in os.environ.items() if k != "LF_COVERAGE_OUT"}
    try:
        result = subprocess.run([gforth, str(PRELUDE), "-e", "bye"], env=env,
                                stdin=subprocess.DEVNULL, capture_output=True, timeout=60)
    except (OSError, subprocess.TimeoutExpired):
        return False
    return result.returncode == 0 and not result.stdout and not result.stderr


def run_command(command, gforth, directory):
    env = {k: v for k, v in os.environ.items() if k not in MAKE_VARIABLES}
    env.update(GFORTH=str(WRAPPER), LF_COVERAGE_GFORTH=gforth,
               LF_COVERAGE_DIR=str(directory))
    # The Makefile's RUN then goes through scripts/timed.sh, which names each command's
    # target (LF_MAKE_TARGET) for the counts of its runs (--per-target).
    env.setdefault("LF_TIMING_LOG", str(directory / "timing.txt"))
    return subprocess.run(command, cwd=ROOT, env=env, stdin=subprocess.DEVNULL).returncode


def source_key(name, cwd, root=ROOT):
    """The path of a counted file relative to the root, or None outside src/."""
    path = Path(name)
    if not path.is_absolute():
        path = Path(cwd) / path
    try:
        relative = Path(os.path.normpath(path)).relative_to(root)
    except ValueError:
        return None
    return str(relative) if relative.parts[0] == "src" else None


def read_runs(directory, targets=None, root=ROOT):
    """({(file, line, column): count} over src/, runs with counts, runs without); with a dict
    TARGETS, also fills it with {make target: {block: count}} (a run without a target under "").

    A run's file has one line per block compiled, src/ or not (about 40,000), and
    a make test has over a thousand runs: the lines are first summed per working
    directory (and target) by their text, and only the distinct ones are parsed."""
    sums, counted, empty = {}, 0, 0
    for out in sorted(directory.glob("run.*")):
        if out.name.endswith(".cwd"):
            continue
        about = Path(str(out) + ".cwd").read_text(encoding="utf-8", errors="replace").splitlines()
        cwd, target = about[0], (about[1] if len(about) > 1 and targets is not None else "")
        table, seen = sums.setdefault((cwd, target), {}), False
        with open(out, encoding="utf-8", errors="replace") as handle:
            for line in handle:
                seen = True
                head, sep, count = line.rpartition(": ")
                if sep:
                    table[head] = table.get(head, 0) + int(count)
        counted, empty = counted + seen, empty + (not seen)
    blocks = {}
    for (cwd, target), table in sums.items():
        mine = targets.setdefault(target, {}) if targets is not None else None
        for head, count in table.items():
            match = COUNT_HEAD.match(head)
            key = match and source_key(match[1], cwd, root)
            if key:
                block = (key, int(match[2]), int(match[3]))
                blocks[block] = blocks.get(block, 0) + count
                if mine is not None:
                    mine[block] = mine.get(block, 0) + count
    return blocks, counted, empty


def per_target(blocks, targets):
    """{file: {"blocks", "never_run", "targets": {target: {"compiled", "ran": [index]}}}}: each
    target's runs of each file, the blocks as indices into the file's sorted blocks."""
    order = {}
    for block in sorted(blocks):
        table = order.setdefault(block[0], {})
        table[block] = len(table)
    files = {name: {"blocks": len(table), "never_run": sum(1 for b in table if blocks[b] == 0),
                    "targets": {}} for name, table in order.items()}
    for target, table in targets.items():
        for block, count in table.items():
            entry = files[block[0]]["targets"].setdefault(target, {"compiled": 0, "ran": []})
            entry["compiled"] += 1
            if count:
                entry["ran"].append(order[block[0]][block])
    for entry in files.values():
        for row in entry["targets"].values():
            row["ran"].sort()
    return files


def focused_never_run(table, chosen):
    """(blocks, never run) of one file of per_target() over the targets CHOSEN only: what a
    focused run of those targets measures. None when none of them loads the file."""
    rows = [table["targets"][t] for t in chosen if t in table["targets"]]
    if not rows:
        return None
    if len(rows) == len(table["targets"]):
        return table["blocks"], table["never_run"]   # every run of the file: the full run's count
    # Fewer targets: the compiled blocks are taken as the largest set one target compiled (a file
    # compiles the same blocks wherever it loads, but for conditional compilation).
    ran = set().union(*(set(r["ran"]) for r in rows))
    compiled = max(r["compiled"] for r in rows)
    return compiled, compiled - len(ran)


def totals(blocks, group):
    """{group name: [blocks, executed]} with group ( file -- name )."""
    table = {}
    for (name, _, _), count in blocks.items():
        entry = table.setdefault(group(name), [0, 0])
        entry[0] += 1
        entry[1] += count > 0
    return table


def print_table(title, table):
    print(f"{title:<40} {'blocks':>7} {'ran':>7} {'coverage':>9}")
    total = [0, 0]
    for name in sorted(table):
        size, ran = table[name]
        total[0] += size
        total[1] += ran
        print(f"{name:<40} {size:>7} {ran:>7} {100 * ran / size:>8.1f}%")
    print(f"{'total':<40} {total[0]:>7} {total[1]:>7} {100 * total[1] / total[0]:>8.1f}%")


def per_file(blocks):
    """{file: [blocks, never run]}."""
    return {name: [size, size - ran] for name, (size, ran) in totals(blocks, str).items()}


def run_problems(counted, empty, baseline, focused=False):
    """Reasons why the measurement itself cannot be trusted (empty when it can); a focused
    run (--only) is a few targets, so only "no counts at all" applies to it."""
    problems = []
    if counted == 0:
        problems.append("no Gforth run left counts")
    if focused:
        return problems
    if empty > 0.1 * (counted + empty):
        problems.append(f"{empty} of {counted + empty} Gforth runs left no counts")
    expected = baseline.get("runs", 0) if baseline else 0
    if expected and counted < SHORTFALL * expected:
        problems.append(f"only {counted} Gforth runs left counts; the baseline "
                        f"({BASELINE.name}) has {expected}")
    return problems


def load_baseline():
    return json.loads(BASELINE.read_text(encoding="utf-8")) if BASELINE.exists() else None


def ratchet(files, baseline):
    """Messages for each file whose never-run blocks grew, or that is new with some."""
    known = baseline["files"] if baseline else {}
    messages = []
    for name, (size, never) in sorted(files.items()):
        entry = known.get(name)
        if entry is None and never:
            messages.append(f"{name}: new file with {never} of {size} blocks never run "
                            f"and no reason listed in the baseline")
        elif entry is not None and never > entry["never_run"]:
            messages.append(f"{name}: {never} blocks never run, the baseline allows "
                            f"{entry['never_run']}")
    return messages


DEFINITION = re.compile(r"(?m)^[ \t]*:(noname)?[ \t\n]|[ \t]:noname[ \t\n]")


def compiles_blocks(name, root=ROOT):
    """Whether source NAME defines a word, so that a run that loads it counts blocks: a load
    list such as src/main.fs (requires only) has none and is never in the counts."""
    try:
        return bool(DEFINITION.search((Path(root) / name).read_text(encoding="utf-8", errors="replace")))
    except OSError:
        return True


def focus(files, only):
    """FILES limited to ONLY, and a note for each file of ONLY that no run loaded: the full run
    (make coverage-check, in make daily) measures it, as it measures every file. A file that
    defines no word (src/main.fs, a load list) compiles no block, so it gets no note."""
    kept = {name: files[name] for name in only if name in files}
    return kept, [f"{name}: no run of these targets loaded it; make daily's full coverage run measures it"
                  for name in only if name not in files and compiles_blocks(name)]


def new_baseline(files, counted, old, reason):
    """The baseline for this measurement; a new file with never-run blocks needs REASON."""
    known = old["files"] if old else {}
    out = {}
    for name, (size, never) in sorted(files.items()):
        entry = {"blocks": size, "never_run": never}
        why = known.get(name, {}).get("reason") or (reason if never else None)
        if never and not why:
            raise SystemExit(f"{name} is new with {never} never-run blocks: "
                             f"--update-baseline needs --reason TEXT")
        if why:
            entry["reason"] = why
        out[name] = entry
    return {"runs": counted, "files": out}


# --- paying coverage debt: one file's blocks and its baseline entry (2026-11-19) ---------------

SAVE_NAME = ".claude/work/coverage/last-full-run.json"
PROTECTED = ("src", "tests", "scripts", "docs")
# A line number in a baseline reason: digits not part of a date, a version, a hash or a word.
LINE_NUMBER = re.compile(r"(?<![\w.-])(\d{1,5})(?![\w.-])")
DEFINITION_HEAD = re.compile(r"(?<!\S):(?:noname(?!\S)|\s+(\S+))")
SEMICOLON = re.compile(r"(?<!\S);(?!\S)")
TEXT_WIDTH = 110


class Refused(Exception):
    """A baseline change or an output path the tool refuses, with the reason."""


def main_checkout(root=ROOT):
    """The main checkout of ROOT's repository: a worktree shares its untracked .claude/work."""
    try:
        common = subprocess.run(["git", "rev-parse", "--git-common-dir"], cwd=root, capture_output=True,
                                text=True, check=True).stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        return Path(root)
    path = Path(common) if os.path.isabs(common) else Path(root) / common
    return path.resolve().parent


def default_save(root=ROOT):
    """Where a full run keeps its never-run blocks (LEANFORTH_COVERAGE_SAVE overrides)."""
    return Path(os.environ.get("LEANFORTH_COVERAGE_SAVE") or main_checkout(root) / SAVE_NAME)


def output_problem(path, root=ROOT):
    """Why --uncovered must not write PATH, or None: it names an output file, never one of the
    tree's sources (src/, tests/, scripts/, docs/) nor any file git tracks (it once overwrote a
    source file)."""
    target = Path(path).resolve()
    for base in {Path(root).resolve(), main_checkout(root)}:
        try:
            parts = target.relative_to(base).parts
        except ValueError:
            continue
        if parts and parts[0] in PROTECTED:
            return f"{path} is under {parts[0]}/; --uncovered names an output file, give a new path elsewhere"
    if target.exists():
        found = subprocess.run(["git", "ls-files", "--error-unmatch", target.name], cwd=target.parent,
                               capture_output=True)
        if found.returncode == 0:
            return f"{path} is a file git tracks; --uncovered names an output file, give a new path"
    return None


def blank_comments(text):
    """TEXT with its comments (a backslash to the line's end, `( ... )`) turned into spaces,
    newlines kept, so that offsets and line numbers stay those of the file."""
    out, i, n = list(text), 0, len(text)
    while i < n:
        if text[i].isspace():
            i += 1
            continue
        j = i
        while j < n and not text[j].isspace():
            j += 1
        word = text[i:j]
        if word == "\\":
            while i < n and text[i] != "\n":
                out[i] = " "
                i += 1
        elif word == "(":
            while i < n and text[i] != ")":
                out[i] = out[i] if text[i] == "\n" else " "
                i += 1
            if i < n:
                out[i] = " "
            i += 1
        else:
            i = j
    return "".join(out)


def describe_blocks(text, starts):
    """{(line, column): (last line, word, text)} for the blocks STARTS ((line, column), Gforth's
    1-based places) of a source file's TEXT: the lines the block spans, the colon definition it
    is in, and its source text without comments up to the next block, the definition's `;` or
    the next definition, whitespace collapsed and cut at TEXT_WIDTH."""
    clean = blank_comments(text)
    offsets = [0]
    for line in text.split("\n"):
        offsets.append(offsets[-1] + len(line) + 1)

    def offset(line, column):
        return min(offsets[max(1, min(line, len(offsets) - 1)) - 1] + column - 1, len(text))
    heads = [(m.start(), m.group(1) or ":noname") for m in DEFINITION_HEAD.finditer(clean)]
    places = sorted(set(starts))
    out = {}
    for k, (line, column) in enumerate(places):
        begin = offset(line, column)
        end = offset(*places[k + 1]) if k + 1 < len(places) else len(text)
        segment = clean[begin:max(begin, end)]
        stop = SEMICOLON.search(segment)
        if stop:
            segment = segment[:stop.end()]
        head = DEFINITION_HEAD.search(segment)
        if head and head.start() > 0:
            segment = segment[:head.start()]
        segment = segment.rstrip()
        last = line + segment.count("\n")
        word = next((name for at, name in reversed(heads) if at < begin), "")
        words = " ".join(segment.split())
        out[(line, column)] = (last, word, words if len(words) <= TEXT_WIDTH else words[:TEXT_WIDTH - 3] + "...")
    return out


def file_digest(text):
    return hashlib.sha256(text.encode("utf-8", errors="replace")).hexdigest()


def full_run_record(blocks, command, root=ROOT):
    """The record --save-full keeps: each file's blocks and never-run blocks (line, column,
    word, text), with the file's digest, so that a later --file run can match its blocks."""
    by_file = {}
    for (name, line, column), count in blocks.items():
        by_file.setdefault(name, {})[(line, column)] = count
    files = {}
    for name, table in sorted(by_file.items()):
        try:
            text = (Path(root) / name).read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        never = sorted(place for place, count in table.items() if count == 0)
        about = describe_blocks(text, table) if never else {}
        files[name] = {"sha256": file_digest(text), "blocks": len(table),
                       "never_run": [[line, column, about[(line, column)][1], about[(line, column)][2]]
                                     for line, column in never]}
    head = subprocess.run(["git", "rev-parse", "--short", "HEAD"], cwd=root, capture_output=True, text=True)
    return {"head": head.stdout.strip(), "date": time.strftime("%Y-%m-%d %H:%M"), "command": command,
            "files": files}


def save_full(path, record):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(record) + "\n", encoding="utf-8")


def load_full(path):
    try:
        return json.loads(Path(path).read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return None


_scripts = {}


def load_script(name, root=ROOT):
    """A script of scripts/ as a module (their names have hyphens), loaded once."""
    key = (str(root), name)
    if key not in _scripts:
        if str(root / "scripts") not in sys.path:
            sys.path.insert(0, str(root / "scripts"))
        spec = importlib.util.spec_from_file_location(name.replace("-", "_")[:-3], root / "scripts" / name)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        _scripts[key] = module
    return _scripts[key]


def forth_words(text):
    """The names a Forth source defines, as scripts/check-duplicates.py reads definitions."""
    return load_script("check-duplicates.py").definitions_of_text(text)[1]


class UnitTests:
    """The Forth unit test files of make test and what each loads (make cover, --changed): the
    Forth files under tests/ that the recipes of make test's unit targets name (make -n;
    tests/test-classes.txt classes the targets), each with its require closure through
    src/main.fs or any other chain (scripts/test-tier.py's forth_closure), in the working tree.
    Built from the repository's root, in about a second."""

    def __init__(self, tier):
        e2e = tier.end_to_end()
        targets = [u for u in tier.units(tier.make_database("check")[0])[1] if u not in e2e]
        with ThreadPoolExecutor(max_workers=8) as pool:
            texts = list(pool.map(tier.changed_tests.recipe, targets))
        self.files = sorted({name for text in texts for name in tier.changed_tests.named_files(text)
                             if name.startswith("tests/") and name.endswith(".fs")})
        loads = {}
        self.closure = {name: tier.forth_closure([name], tier.read_worktree, loads) for name in self.files}

    def loading(self, path):
        """The unit test files whose require closure holds PATH, sorted."""
        return [name for name in self.files if path in self.closure[name]]


def naming_tests(path, tests, root=ROOT):
    """Those of TESTS whose text names a word PATH defines (case folded)."""
    names = forth_words((Path(root) / path).read_text(encoding="utf-8", errors="replace"))
    chosen = []
    for test in tests:
        try:
            words = set((Path(root) / test).read_text(encoding="utf-8", errors="replace").lower().split())
        except OSError:
            continue
        if words & names:
            chosen.append(test)
    return chosen


# The selection rule (make cover, --changed): a file that more unit test files load than this
# first runs the narrowed set (narrowed_tests), and the rest only when blocks are left never run.
NARROW_ABOVE = 8


def module_folders(path):
    """(the module's test folder or None, the file's own test folder) of a source file of src/:
    tests/TOP for src/TOP/... (its test files directly in it: tests/front for src/front/x.fs and
    src/front/tactics/case.fs), and tests/DIR/STEM/ for src/DIR/STEM.fs (all of it: a plug-in's
    own tests, tests/front/tactics/case/ for src/front/tactics/case.fs)."""
    parts = Path(path).with_suffix("").parts[1:]
    return (f"tests/{parts[0]}" if len(parts) > 1 else None), "tests/" + "/".join(parts) + "/"


def narrowed_tests(path, every, root=ROOT):
    """The tests to run first of EVERY (the unit test files that load PATH): all of them when they
    are NARROW_ABOVE or fewer; else those that name a word PATH defines and those of its module
    folders (module_folders), or all when none is either. The caller runs the rest of EVERY when
    a block it asks about is left never run, so a test that reaches PATH only through text (a .lf
    file, a name built at run time) is still found."""
    if len(every) <= NARROW_ABOVE:
        return list(every)
    top, own = module_folders(path)
    chosen = set(naming_tests(path, every, root))
    chosen |= {t for t in every if os.path.dirname(t) == top or t.startswith(own)}
    return sorted(chosen) or list(every)


Run = collections.namedtuple("Run", "status counted empty blocks")


def run_each(tests, gforth, wanted, root=ROOT, jobs=4, timeout=1800):
    """{test: Run(exit status, Gforth runs with counts, runs without, {(file, line, column): count}
    of the files WANTED)} of each Forth test file run on its own under the counting wrapper in
    ROOT, JOBS at a time (each run is a wrapper, the strict wrapper and Gforth: three processes)."""
    env = {k: v for k, v in os.environ.items() if k not in MAKE_VARIABLES + ("LF_MAKE_TARGET",)}
    env.update(LF_COVERAGE_GFORTH=gforth)
    directory = Path(tempfile.mkdtemp(prefix="leanforth-cover-"))

    def one(numbered):
        number, test = numbered
        own = directory / str(number)
        own.mkdir()
        try:
            status = subprocess.run([str(WRAPPER), test], cwd=root, env=dict(env, LF_COVERAGE_DIR=str(own)),
                                    stdin=subprocess.DEVNULL, capture_output=True, timeout=timeout).returncode
        except subprocess.TimeoutExpired:
            status = "timeout"
        blocks, counted, empty = read_runs(own, root=root)
        shutil.rmtree(own, ignore_errors=True)
        return Run(status, counted, empty, {b: c for b, c in blocks.items() if b[0] in wanted})
    try:
        with ThreadPoolExecutor(max_workers=max(1, jobs)) as pool:
            return dict(zip(tests, pool.map(one, enumerate(tests))))
    finally:
        shutil.rmtree(directory, ignore_errors=True)


def joined(runs, path):
    """{(line, column): count} of PATH's blocks summed over RUNS (run_each's)."""
    total = {}
    for run in runs.values():
        for (name, line, column), count in run.blocks.items():
            if name == path:
                total[(line, column)] = total.get((line, column), 0) + count
    return total


def reason_lines(reason):
    return {int(n) for n in LINE_NUMBER.findall(reason or "")}


def full_run_marks(name, text, never, about, saved):
    """{place: note} for each never-run block of NAME now, against the saved full run: by place
    when the file is unchanged since, else by its word and text."""
    entry = (saved or {}).get("files", {}).get(name)
    if entry is None:
        return {}
    if entry.get("sha256") == file_digest(text):
        before = {(line, column) for line, column, _, _ in entry["never_run"]}
        return {p: "also never run in the last full run" if p in before else "ran in the last full run"
                for p in never}
    before = collections.Counter((word, words) for _, _, word, words in entry["never_run"])
    marks = {}
    for p in never:
        key = about[p][1:]
        if before[key]:
            before[key] -= 1
            marks[p] = "also never run in the last full run (matched by word and text: the file changed since)"
        else:
            marks[p] = "ran in the last full run, or changed since it"
    return marks


def cover(path, tests, gforth, root=ROOT, jobs=4, baseline=None, saved=None, chosen_how="", wider=()):
    """Run TESTS under coverage and report PATH's never-run blocks: (exit status, report lines).
    When blocks are left never run (or none was loaded) and WIDER names more tests (the rest of the
    unit test files that load PATH), those run too before the report."""
    started = time.time()
    runs = run_each(list(tests), gforth, {path}, root, jobs)
    mine = joined(runs, path)
    rest = [t for t in wider if t not in runs]
    if rest and (not mine or 0 in mine.values()):
        runs.update(run_each(rest, gforth, {path}, root, jobs))
        mine = joined(runs, path)
    else:
        rest = []
    seconds = time.time() - started
    counted, empty = sum(r.counted for r in runs.values()), sum(r.empty for r in runs.values())
    lines = [f"cover {path}: {len(runs)} unit test file(s) in {seconds:.1f} s "
             f"({counted} Gforth runs with counts, {empty} without){chosen_how}"]
    if rest:
        lines.append(f"  widened: blocks were left never run, so the other {len(rest)} unit test files "
                     "that load it ran too")
    statuses = {t: r.status for t, r in runs.items()}
    lines += [f"  test: {t}" + ("" if statuses[t] == 0 else f"  FAILED (exit {statuses[t]})") for t in runs]
    entry = ((baseline or {}).get("files") or {}).get(path)
    allowed = entry["never_run"] if entry else 0
    if not mine:
        lines.append(f"FAILED: no test run loaded {path} (name its tests with --tests, make cover TESTS=...)")
        return 2, lines
    text = (Path(root) / path).read_text(encoding="utf-8", errors="replace")
    never = sorted(p for p, count in mine.items() if count == 0)
    about = describe_blocks(text, mine)
    lines.append(f"blocks {len(mine)}, never run now {len(never)}; baseline "
                 + (f"{entry['blocks']} blocks, {allowed} never run" if entry else "has no entry (0 allowed)"))
    if entry and entry.get("reason"):
        lines.append(f"  baseline reason: {entry['reason']}")
    lines.append("  note: only unit tests ran; the ratchet counts over all of make test, whose end-to-end "
                 "targets run code too, so this list can be longer than the ratchet's")
    named = reason_lines(entry.get("reason") if entry else "")
    marks = full_run_marks(path, text, never, about, saved)
    if saved is None:
        lines.append("  no saved full run to compare with (make coverage-check keeps one: --save-full)")
    elif path not in saved.get("files", {}):
        lines.append(f"  the saved full run ({saved.get('head')}) did not load {path}")
    else:
        lines.append(f"  compared with the full run of {saved.get('head')} ({saved.get('date')})")
    for place in never:
        last, word, words = about[place]
        span = f"{place[0]}" if last == place[0] else f"{place[0]}-{last}"
        hit = sorted(n for n in named if place[0] <= n <= last)
        notes = [f"baseline reason names line {hit[0]}" if hit else "baseline reason names none of its lines"]
        if place in marks:
            notes.append(marks[place])
        lines.append(f"  {path}:{span}:{place[1]} in {word or '(no definition)'}: {words}")
        lines.append(f"      [{'; '.join(notes)}]")
    failed = [t for t in runs if statuses[t] != 0]
    if failed:
        lines.append(f"FAILED: {len(failed)} test file(s) failed: {' '.join(failed)}")
        return 1, lines
    if len(never) > allowed:
        lines.append(f"ABOVE the baseline: {len(never)} never-run blocks, the baseline allows {allowed} "
                     "(the full ratchet may still pass: see the note above)")
        return 1, lines
    lines.append(f"not above the baseline: {len(never)} never-run blocks, the baseline allows {allowed}")
    return 0, lines


# --- the branch coverage check (owner, 2026-11-19): make cover-changed --------------------------

UNREACHABLE = "unreachable:"


def git_text(root, *args):
    """git's output in ROOT; a failed git command raises Refused with its message."""
    run = subprocess.run(["git", *args], cwd=root, capture_output=True, text=True)
    if run.returncode != 0:
        raise Refused(f"git {' '.join(args)}: {run.stderr.strip()}")
    return run.stdout


def touched_sources(base, root=ROOT):
    """([path], {untracked path}): the Forth files of src/ added or modified since commit BASE, in
    the working tree (committed, uncommitted and new untracked files); a deleted file has no line
    to run, and a rename counts as its new file, all of it added."""
    found = {}
    for line in git_text(root, "diff", "--name-status", "--no-renames", base, "--", "src").splitlines():
        status, path = line.split("\t", 1)
        found[path] = status[0]
    untracked = set(git_text(root, "ls-files", "--others", "--exclude-standard", "--", "src").splitlines())
    for path in untracked:
        found.setdefault(path, "A")
    return sorted(p for p, s in found.items() if s != "D" and p.endswith(".fs")), untracked


def diff_hunks(diff):
    """[(first, last, removed text, added text)] of the hunks of a `git diff -U0` text of one file:
    the lines of the new file each hunk adds or changes (none for a pure deletion: last < first)
    and the text it removes and adds (the hunk header as scripts/test-tier.py's HUNK reads it)."""
    head, hunks = load_script("test-tier.py").HUNK, []
    for line in diff.splitlines():
        found = head.match(line)
        if found:
            first = int(found[1])
            hunks.append((first, first + int(found[2] or "1") - 1, [], []))
        elif hunks and line[:1] in ("-", "+"):
            hunks[-1][2 if line[0] == "-" else 3].append(line[1:])
    return [(first, last, "\n".join(old), "\n".join(new)) for first, last, old, new in hunks]


def code_of(text):
    """Forth TEXT's code: comments left out (blank_comments), white space collapsed."""
    return " ".join(blank_comments(text).split())


def changed_code_lines(path, text, base, untracked, root=ROOT):
    """The lines of PATH (TEXT, its working-tree text) that the branch added or changed since BASE
    and that hold code: the lines of each hunk of `git diff -U0` whose code differs (a hunk that
    only edits comments or white space, an indentation or a stack comment, is no change), every
    line of an untracked file; a line that is all comment or blank space never counts."""
    if path in untracked:
        lines = range(1, text.count("\n") + 2)
    else:
        diff = git_text(root, "diff", "-U0", "--no-renames", base, "--", path)
        lines = sorted({n for first, last, old, new in diff_hunks(diff) if code_of(old) != code_of(new)
                        for n in range(first, last + 1)})
    clean = blank_comments(text).split("\n")
    return [n for n in lines if n <= len(clean) and clean[n - 1].strip()]


def changed_blocks(text, blocks, code):
    """[((line, column), last line, word, text, count)] of the blocks (BLOCKS, {(line, column):
    count}) of a source TEXT that hold a line of CODE (changed code lines), in order."""
    about = describe_blocks(text, blocks)
    code = set(code)
    return [(place, *about[place], blocks[place]) for place in sorted(blocks)
            if any(n in code for n in range(place[0], about[place][0] + 1))]


def unreachable_lines(entry):
    """The lines a baseline entry's reason excuses: those it names when it starts with
    "unreachable:" (the convention for code no input can reach), else none."""
    reason = ((entry or {}).get("reason") or "").strip()
    return reason_lines(reason) if reason.lower().startswith(UNREACHABLE) else set()


def changed_plan(files, base, untracked, root=ROOT):
    """({path: (text, changed code lines)} of the FILES to measure, {path: note} of the others): a
    file that defines no word compiles no block, and one whose changes are all comments or white
    space has no changed block."""
    measure, notes = {}, {}
    for path in files:
        text = (Path(root) / path).read_text(encoding="utf-8", errors="replace")
        code = changed_code_lines(path, text, base, untracked, root)
        if not compiles_blocks(path, root):
            notes[path] = "defines no word: it compiles no block"
        elif not code:
            notes[path] = "only comments or white space changed: no block to run"
        else:
            measure[path] = (text, code)
    return measure, notes


def gaps_of(path, measured, runs):
    """Whether PATH (MEASURED: its text and changed code lines) has a never-run block on a changed
    line over RUNS, or no block at all (no run loaded it)."""
    text, code = measured
    blocks = joined(runs, path)
    return not blocks or any(b[4] == 0 for b in changed_blocks(text, blocks, code))


def measure_changed(measure, gforth, root=ROOT, jobs=4, units=None):
    """({path: the unit test files that load it}, {test: Run}) of the files MEASURE names
    (changed_plan's): each file's narrowed tests run first, each test file once for all of them;
    then, for each file with a never-run block on a changed line, every other test that loads it."""
    units = units or UnitTests(load_script("test-tier.py", root))
    every = {p: units.loading(p) for p in measure}
    first = sorted({t for p in measure for t in narrowed_tests(p, every[p], root)})
    runs = run_each(first, gforth, set(measure), root, jobs)
    widen = [p for p in measure if gaps_of(p, measure[p], runs)]
    rest = sorted({t for p in widen for t in every[p]} - set(runs))
    if rest:
        runs.update(run_each(rest, gforth, set(measure), root, jobs))
    return every, runs


def block_line(path, block):
    """file:line: word: text of a block of changed_blocks."""
    (line, _), _, word, words, _ = block
    return f"{path}:{line}: {word or '(no definition)'}: {words}"


def file_verdict(path, measured, loading, runs, entry):
    """(report lines, a file:line: word: text line for each never-run block on a changed line,
    failed) of one measured file (MEASURED: its text and changed code lines; LOADING: the unit test
    files that load it; ENTRY: its baseline entry, whose "unreachable:" reason may excuse a block)."""
    text, code = measured
    if not loading:
        return [f"  {path}: FAILED: no unit test file loads it (no Forth file under tests/ that a unit target "
                "of make test names requires it): add a unit test"], [], True
    allowed = unreachable_lines(entry)
    found = changed_blocks(text, joined(runs, path), code)
    never = [b for b in found if b[4] == 0]
    gaps = [b for b in never if not allowed & set(range(b[0][0], b[1] + 1))]
    verdict = (f"{len(found)} block(s) on them, {len(gaps)} never run" if gaps else
               f"{len(found)} block(s) on them, every one ran" if found else
               "no block on them (code outside a definition)")
    lines = [f"  {path}: {len(code)} changed code line(s), {verdict} "
             f"({len([t for t in loading if t in runs])} of {len(loading)} unit test files that load it)"]
    lines += [f"    {block_line(path, b)}  [accepted: the baseline's reason for {path} starts with "
              f"\"{UNREACHABLE}\" and names line {b[0][0]}]" for b in never if b not in gaps]
    return lines, [block_line(path, b) for b in gaps], bool(gaps)


def check_changed(base, gforth, root=ROOT, jobs=4, baseline=None, units=None):
    """The branch coverage check (make cover-changed): (exit status, report lines). For each Forth
    file of src/ added or modified since commit BASE, the unit test files that load it run under
    coverage (measure_changed), and each never-run block on a line the branch added or changed is
    reported as file:line: word: text. Such a block passes only when the file's baseline entry
    has a reason that starts with "unreachable:" and names its line. Exit 1 when a block is
    reported, a touched file no unit test loads, or a test fails; else 0. UNITS (a UnitTests)
    saves finding the tests again."""
    files, untracked = touched_sources(base, root)
    if not files:
        return 0, [f"cover-changed: no Forth file of src/ added or modified since {base[:12]}: nothing to check"]
    measure, notes = changed_plan(files, base, untracked, root)
    every, runs = measure_changed(measure, gforth, root, jobs, units) if measure else ({}, {})
    lines = [f"cover-changed: {len(files)} Forth file(s) of src/ added or modified since {base[:12]}"]
    reported, files_failed = [], 0
    for path in files:
        if path in notes:
            lines.append(f"  {path}: {notes[path]}")
            continue
        entry = ((baseline or {}).get("files") or {}).get(path)
        report, gaps, failed = file_verdict(path, measure[path], every[path], runs, entry)
        lines += report
        reported += gaps
        files_failed += failed
    failed = sorted(t for t, r in runs.items() if r.status != 0)
    lines += [f"  test FAILED: {t} (exit {runs[t].status})" for t in failed] + reported
    if reported or files_failed or failed:
        lines.append(f"cover-changed: FAILED: {len(reported)} never-run block(s) on changed lines, "
                     f"{files_failed} file(s) failing, {len(failed)} test file(s) failed; write the tests "
                     "(make cover FILE=... lists a file's blocks)")
        return 1, lines
    lines.append(f"cover-changed: every block on a changed line ran ({len(runs)} unit test file(s) run)")
    return 0, lines


def set_entry(baseline, name, never, total=None, reason=None, root=ROOT):
    """Change NAME's entry of BASELINE in place to NEVER never-run blocks: (old, new) entries.
    Raises Refused when raising without a reason, when a new entry lacks its total, or when a
    file that had no never-run block gets some without a reason naming each by its line."""
    files = baseline.setdefault("files", {})
    old = files.get(name)
    reason = (reason or "").strip()
    if never < 0:
        raise Refused("--blocks must be 0 or more")
    if old is None and not (Path(root) / name).is_file():
        raise Refused(f"{name} is no file of the tree")
    if old is None and total is None:
        raise Refused(f"{name} has no baseline entry: a new entry needs --total (the file's blocks)")
    had = old["never_run"] if old else 0
    if never > had and not reason:
        raise Refused(f"{name}: raising the never-run count from {had} to {never} needs --reason "
                      "(never raise a number to make the check pass: add tests)")
    if had == 0 and never > 0 and len(reason_lines(reason)) < never:
        raise Refused(f"{name} had no never-run block: --reason must name each of the {never} by its "
                      f"line number (it names {len(reason_lines(reason))})")
    new = dict(old or {})
    new["blocks"] = total if total is not None else new["blocks"]
    new["never_run"] = never
    if never > new["blocks"]:
        raise Refused(f"{name}: {never} never-run blocks of {new['blocks']}")
    if reason:
        new["reason"] = reason
    if never == 0:
        new.pop("reason", None)
    files[name] = {k: new[k] for k in ("blocks", "never_run", "reason") if k in new}
    baseline["files"] = dict(sorted(files.items()))
    return old, baseline["files"][name]


def drop_entry(baseline, name):
    files = baseline.get("files", {})
    if name not in files:
        raise Refused(f"{name} has no baseline entry")
    return files.pop(name)


def debt_lines(baseline):
    """The baseline's entries with never-run blocks, largest first, with their reasons."""
    rows = sorted(((e["never_run"], name, e) for name, e in baseline.get("files", {}).items()
                   if e.get("never_run")), key=lambda r: (-r[0], r[1]))
    out = [f"coverage debt: {sum(r[0] for r in rows)} never-run blocks in {len(rows)} files "
           f"({BASELINE.name}), largest first"]
    for never, name, entry in rows:
        out.append(f"{never:>5} of {entry['blocks']:<5} {name}")
        out.append(f"        reason: {entry.get('reason', '(none)')}")
    folders = collections.Counter()
    for never, name, _ in rows:
        folders[str(Path(name).parent)] += never
    out.append("by folder: " + ", ".join(f"{f} {n}" for f, n in sorted(folders.items(), key=lambda kv: -kv[1])))
    return out


def baseline_command(args):
    """--set-baseline, --drop-baseline and --debt: the exit status."""
    baseline = load_baseline() or {"runs": 0, "files": {}}
    if args.debt:
        print("\n".join(debt_lines(baseline)))
        return 0
    name = os.path.normpath(args.set_baseline or args.drop_baseline)
    try:
        if args.drop_baseline:
            old, new = drop_entry(baseline, name), None
        else:
            if args.blocks is None:
                raise Refused("--set-baseline needs --blocks N (the never-run blocks)")
            old, new = set_entry(baseline, name, args.blocks, args.total, args.reason)
    except Refused as why:
        print(f"refused: {why}")
        return 1
    BASELINE.write_text(json.dumps(baseline, indent=1) + "\n", encoding="utf-8")
    print(f"{name} in {BASELINE.name}:\n  old {json.dumps(old)}\n  new {json.dumps(new)}")
    if new is None and (ROOT / name).is_file() and old and old.get("never_run"):
        print(f"note: {name} still exists; the ratchet now allows it no never-run block")
    return 0


def cover_command(args, gforth):
    """--file: choose the tests, run them and print the report; the exit status."""
    path = os.path.normpath(args.file)
    if not path.startswith("src/") or not (ROOT / path).is_file():
        print(f"--file names a Forth file of src/: {args.file}")
        return 2
    wider = []
    if args.tests:
        tests, how = args.tests.split(), "; named by --tests"
    else:
        every = UnitTests(load_script("test-tier.py")).loading(path)
        tests = every if args.all_tests else narrowed_tests(path, every)
        wider = [t for t in every if t not in tests]
        how = (f"; of the {len(every)} Forth unit test files that load it, "
               + (f"the {len(tests)} that name one of its words or sit in its module's test folders "
                  "first (the rest when a block is left never run; --all-tests runs all)" if wider else "all"))
    if not tests:
        print(f"no Forth unit test file loads {path}: name its tests with --tests (make cover TESTS=...)")
        return 2
    status, lines = cover(path, tests, gforth, ROOT, args.jobs, load_baseline(), load_full(default_save()), how,
                          wider)
    print("\n".join(lines))
    return status


def changed_command(args, gforth):
    """--changed: the branch coverage check against the merge base of BASE and HEAD; the exit status."""
    try:
        base = git_text(ROOT, "merge-base", args.changed, "HEAD").strip()
    except Refused as why:
        print(f"cover-changed: {why}")
        return 2
    started = time.time()
    status, lines = check_changed(base, gforth, ROOT, args.jobs, load_baseline())
    print("\n".join(lines), flush=True)
    print(f"cover-changed: {time.time() - started:.1f} s (merge base of {args.changed} and HEAD: {base[:12]})",
          file=sys.stderr)
    return status


def main(argv=None):
    global BASELINE
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--gforth", default=os.environ.get("GFORTH", "gforth"))
    parser.add_argument("--files", action="store_true")
    parser.add_argument("--uncovered", metavar="OUTPUT",
                        help="write each never-run block to the new OUTPUT file (never a source or tracked file)")
    parser.add_argument("--keep")
    parser.add_argument("--baseline", default=str(BASELINE))
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--update-baseline", action="store_true")
    parser.add_argument("--reason", default="")
    parser.add_argument("--only", action="append", default=[], metavar="FILE")
    parser.add_argument("--per-target", metavar="FILE",
                        help="write each make target's runs of each file (JSON; per_target())")
    parser.add_argument("--save-full", nargs="?", const="default", metavar="PATH",
                        help="keep each file's never-run blocks of this run of all of make test")
    parser.add_argument("--file", metavar="FILE", help="one file's never-run blocks over unit tests only")
    parser.add_argument("--tests", help="the Forth test files --file runs (space-separated)")
    parser.add_argument("--all-tests", action="store_true")
    parser.add_argument("--changed", nargs="?", const="main", metavar="BASE",
                        help="the branch coverage check of the source files changed since the merge base "
                             "of BASE (default main) and HEAD")
    parser.add_argument("--jobs", type=int, default=int(os.environ.get("JOBS") or 4))
    parser.add_argument("--set-baseline", metavar="FILE")
    parser.add_argument("--drop-baseline", metavar="FILE")
    parser.add_argument("--blocks", type=int, help="--set-baseline's never-run blocks")
    parser.add_argument("--total", type=int, help="--set-baseline's blocks of the file")
    parser.add_argument("--debt", action="store_true")
    parser.add_argument("command", nargs="*")
    args = parser.parse_args(argv)
    if args.only and (args.update_baseline or not args.check):
        parser.error("--only needs --check and cannot update the baseline")
    BASELINE = Path(args.baseline)
    if args.set_baseline or args.drop_baseline or args.debt:
        return baseline_command(args)
    if args.uncovered and output_problem(args.uncovered):
        print("refused: " + output_problem(args.uncovered))
        return 2
    command = args.command or ["make", "test"]
    gforth = resolve(args.gforth)
    if not has_coverage(gforth):
        print(f"make coverage needs Gforth 1.0's coverage.fs; {gforth} cannot load "
              f"{PRELUDE.relative_to(ROOT)}")
        return 2
    if args.file or args.changed:
        os.chdir(ROOT)   # the test finder (scripts/test-tier.py) works from the root
        return cover_command(args, gforth) if args.file else changed_command(args, gforth)
    directory = Path(args.keep) if args.keep else Path(tempfile.mkdtemp(prefix="leanforth-cov-"))
    directory.mkdir(parents=True, exist_ok=True)
    try:
        status = run_command(command, gforth, directory)
        targets = {} if args.per_target else None
        blocks, counted, empty = read_runs(directory, targets)
        if args.per_target:
            with open(args.per_target, "w", encoding="utf-8") as handle:
                json.dump({"command": command, "files": per_target(blocks, targets)}, handle)
    finally:
        if not args.keep:
            shutil.rmtree(directory, ignore_errors=True)
    print(f"\nBlock coverage of src/ over: {' '.join(command)} "
          f"({counted} Gforth runs with counts, {empty} without)")
    baseline = load_baseline()
    problems = run_problems(counted, empty, None if args.update_baseline else baseline, bool(args.only))
    if not blocks:
        print("FAILED: no counts were collected; " + "; ".join(problems))
        return 1
    print_table("folder", totals(blocks, lambda name: str(Path(name).parent)))
    if args.files:
        print()
        print_table("file", totals(blocks, lambda name: name))
    if args.uncovered:
        with open(args.uncovered, "w", encoding="utf-8") as handle:
            for (name, line, column), count in sorted(blocks.items()):
                if count == 0:
                    handle.write(f"{name}:{line}:{column}\n")
    if status != 0:
        print(f"FAILED: {' '.join(command)} exited with status {status} under coverage")
        return 1
    if problems:
        print("FAILED: " + "; ".join(problems))
        return 1
    files = per_file(blocks)
    if args.save_full and not args.only:
        where = default_save() if args.save_full == "default" else Path(args.save_full)
        save_full(where, full_run_record(blocks, command))
        print(f"kept each file's never-run blocks in {where} (for --file, make cover)")
    if args.update_baseline:
        text = json.dumps(new_baseline(files, counted, baseline, args.reason), indent=1)
        BASELINE.write_text(text + "\n", encoding="utf-8")
        print(f"wrote {BASELINE}")
    elif args.check:
        if args.only:
            files, notes = focus(files, [os.path.normpath(name) for name in args.only])
            for note in notes:
                print("note: " + note)
        messages = ratchet(files, baseline) if baseline else [f"no {BASELINE.name}"]
        for message in messages:
            print("FAILED: " + message)
        if messages:
            return 1
        which = f"of {', '.join(sorted(files))} " if args.only else ""
        print(f"coverage ratchet: no file {which}has more never-run blocks than the baseline")
    return 0


if __name__ == "__main__":
    sys.exit(main())
