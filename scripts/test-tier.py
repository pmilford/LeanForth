#!/usr/bin/env python3
"""The change tier of a range of commits and the suites it needs (plan 9.4.6).

Usage (from the repository root):
  python3 scripts/test-tier.py [--base REF] [--files FILE...] [--full] [--json]

Classifies the files that differ between the merge base of REF (default
main) and HEAD, uncommitted and new untracked files included (or the files
given by --files), into the change tiers of AGENTS.md ("Test by what a
change reaches"; owner, 2026-11-13), and prints the tier, each file's reason
and the suites the tier needs; --json prints the same as one JSON object.
scripts/tested-tree.py runs the suites, reusing recorded passes (make tier,
scripts/push.sh). --full gives the full tier whatever changed.

Each file gets a tier; the range gets the largest:
  docs     a Markdown file, docs/, .claude/, .codex/, prompts/, LICENSE or
           .gitignore: make check-docs, the targets that use the file (a
           page whose examples run, a catalogue a test reads) and, run by
           make tier itself, the progress check.
  tests    any other file under tests/: the targets that use it on Gforth
           1.0, and those of them that are unit tests (tests/test-classes.txt)
           and run Gforth also on gforth-fast and Gforth 0.7.3; its planted
           faults (those whose test command names it, and fault entries new
           or changed in tests/mutants/faults.toml) and the block coverage of
           the source files the changed tests drive (make coverage-check when
           one of them is loaded by src/main.fs). A test file no target uses
           selects the targets that use a file of its folder; with none, the
           range is full.
  library  a Forth file of src/lib/ that src/main.fs does not load: the
           targets that use it (the unit tests on all three engines), its
           faults and its coverage.
  front    a Forth file of src/front/ that src/main.fs does not load: the
           same, and make test-front and reference-front.
  full     everything else: any file src/main.fs loads, at HEAD or at the
           base (so a library that becomes loaded is full), src/main.fs,
           src/kernel, core, import, cli and every other folder of src/,
           the Makefile, scripts/, bin/, schemas/, lean-toolchain, .github/
           any deleted or renamed-away file but documents (what used it is
           known only from the base tree) and any file not named above. Suites: make coverage-check (make
           test once, instrumented, and the coverage ratchet: every unit
           test on Gforth 1.0 and every end-to-end test of make test), make
           test-unit on gforth-fast, make check-rest (the rest of make check,
           every pinned-Lean comparison included), make test-unit on Gforth
           0.7.3 (at the push), and the planted faults
           whose entries are new or changed, or whose old text lies on or
           next to a changed line of its file (plan 9.4.8j); a fault of a
           changed file whose text was left alone is left to the stale
           check and the daily full run of make mutants.

src/main.fs's closure follows Forth's require, include and needs, also in
comments (more is loaded, never less). A target uses what
scripts/changed-tests.py finds (the files its recipe names, followed through
Forth loads, Python imports and named repository paths); every changed
Forth source also selects smoke, check-portable-forth and
check-forth-quality. A target of make test that runs Gforth (its recipe
names it) and is no end-to-end test (tests/test-classes.txt; owner,
2026-11-14) runs on gforth-fast and Gforth 0.7.3 too; plan() fails (exit 2)
when a suite would drop such a unit test from an engine or run an end-to-end
test on one. A smaller tier is a heuristic over
named files: when in doubt the tier is the larger one. What it leaves to
the daily full run: block coverage of files a changed library or test loads
but does not test, and documents a test reads through a path built at run
time. Exit status 0, or 2 for a usage or git error.
"""
import argparse
import hashlib
import importlib.util
import json
import os
import re
import subprocess
import sys
import tomllib
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location("changed_tests", os.path.join(HERE, "changed-tests.py"))
changed_tests = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(changed_tests)
_spec = importlib.util.spec_from_file_location("test_classes", os.path.join(HERE, "test-classes.py"))
test_classes = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(test_classes)
_spec = importlib.util.spec_from_file_location("tactic_plugins", os.path.join(HERE, "check-tactic-plugins.py"))
tactic_plugins = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(tactic_plugins)

PROGRAMS = (".fs", ".py", ".sh")
TOOL_TESTS = ("tests/scripts/", "tests/mutants/", "tests/lean-cache/", "tests/test-classes.txt")
TIERS = ("none", "docs", "tests", "library", "front", "tactic", "full")
# The tactic tier (owner, 2026-11-17, the tactic plug-in design's decision 2): only for a branch
# scripts/check-tactic-plugins.py finds confined. Its S1/S2 pinned-Lean comparisons:
TACTIC_REFERENCE = ("reference-front",)
DOC_FOLDERS = ("docs/", ".claude/", ".codex/", "prompts/")
DOC_FILES = {"LICENSE", ".gitignore"}
MAIN = "src/main.fs"
FAULTS = "tests/mutants/faults.toml"
FAULTS_DIR = "tests/mutants/faults.d"   # read with FAULTS as one list (scripts/mutants.py)
COVERAGE_BASELINE = "tests/coverage-baseline.json"
SOURCE_RULE_TARGETS = ("smoke", "check-portable-forth", "check-forth-quality")
FRONT_TARGETS = ("test-front", "test-front-e2e", "reference-front")
FORTH_LOAD = re.compile(r"\b(?:require|include|needs)\s+(\S+\.fs)\b", re.IGNORECASE)
TARGET_VARIABLE = changed_tests.TARGET_VARIABLE
# The engines unit tests run on besides Gforth 1.0 (owner, 2026-11-14): gforth-fast, the
# users' default, and Gforth 0.7.3, CI's portability host (only at the push and in the daily
# run: tested-tree.py tier --with-073). End-to-end tests run once, on Gforth 1.0.
ENGINES = {"fast": "gforth-fast", "073": "Gforth 0.7.3"}
# The engines of a tier (make tier, scripts/push.sh): gforth-fast only. Gforth 0.7.3 runs in
# make daily and make tag-check alone (owner, 2026-11-17).
TIER_ENGINES = ("fast",)
# The full tier (owner, 2026-11-17): make test on Gforth 1.0 (plain; the coverage of the changed
# files runs first, as a coverage-focus suite, and stands for its own targets), make test-unit
# on gforth-fast and make check-rest; tested-tree.py reuses each target whose inputs are
# unchanged. The whole coverage ratchet (make coverage-check) runs in make daily.
FULL_SUITES = (
    {"label": "test", "goals": ["test"]},
    {"label": "testfast", "goals": ["test-unit"], "engine": "fast"},
    {"label": "check-rest", "goals": ["check-rest"]},
)
# The daily full run (make daily) and what make tag-check requires: every suite, cache off.
DAILY_SUITES = (
    {"label": "coverage-check", "goals": ["coverage-check"]},
    {"label": "testfast", "goals": ["test-unit"], "engine": "fast"},
    {"label": "check-rest", "goals": ["check-rest"]},
    {"label": "test073", "goals": ["test-unit"], "engine": "073"},
)


def git(*args, check=True):
    result = subprocess.run(["git", *args], capture_output=True, text=True)
    if check and result.returncode != 0:
        print(f"test-tier: git {' '.join(args)}: {result.stderr.strip()}", file=sys.stderr)
        raise SystemExit(2)
    return result.stdout


# --- the make database --------------------------------------------------------

def make_database(goal="check"):
    """({target: [prerequisites]}, {target with a recipe}, {variable: value}) of make -pn GOAL."""
    text = subprocess.run(["make", "-pn", "--no-print-directory", goal], capture_output=True,
                          text=True, env=changed_tests.make_env()).stdout
    return parse_database(text)


def parse_database(text):
    """The rules and simple variables of a make -p listing (its "# Files" blocks)."""
    rules, recipes, variables = {}, set(), {}
    for match in re.finditer(r"^(\w+) :?= (.*)$", text, re.MULTILINE):
        variables.setdefault(match[1], match[2])
    for block in re.split(r"\n\s*\n", text):
        lines = block.splitlines()
        if not lines or lines[0].startswith("# Not a target"):
            continue
        # A target's own variables ("target: VAR := value") come before its rule line.
        heads = [re.match(r"^([\w./-]+):(?![:=])(.*)$", line) for line in lines]
        heads = [h for h in heads if h and not TARGET_VARIABLE.match(h[2])]
        if not heads:
            continue
        name = heads[0][1]
        rules.setdefault(name, []).extend(p for p in heads[0][2].split() if p != "|")
        if any(line.startswith("\t") or line.startswith("#  recipe to execute") for line in lines[1:]):
            recipes.add(name)
    return rules, recipes, variables


def reach(goals, rules):
    """Every target make builds for GOALS (the goals and all their prerequisites)."""
    seen, todo = set(), list(goals)
    while todo:
        name = todo.pop()
        if name not in seen:
            seen.add(name)
            todo += rules.get(name, [])
    return seen


def units(rules):
    """The targets make test-changed would pick from (scripts/changed-tests.py's leaves of
    make check), in make check's order: (all of them, those of make test)."""
    every = changed_tests.leaf_targets("check", rules)
    of_test = set(changed_tests.leaf_targets("test", rules))
    return every, [u for u in every if u in of_test]


# --- what a file reaches -------------------------------------------------------

def forth_closure(start, read):
    """The Forth files START loads through require, include and needs (comments too).
    READ ( path -- text or None ) reads one file of the tree in question."""
    seen, todo = set(), list(start)
    while todo:
        path = todo.pop()
        if path in seen:
            continue
        text = read(path)
        if text is None:
            continue
        seen.add(path)
        for name in FORTH_LOAD.findall(text):
            for base in (os.path.dirname(path), "."):
                candidate = os.path.normpath(os.path.join(base, name))
                if read(candidate) is not None:
                    todo.append(candidate)
                    break
    return seen


def read_worktree(path):
    try:
        with open(path, encoding="utf-8", errors="replace") as stream:
            return stream.read()
    except OSError:
        return None


def reader_at(rev):
    """A READ for forth_closure over the tree of commit REV."""
    names = set(git("ls-tree", "-r", "--name-only", rev).splitlines())
    cache = {}

    def read(path):
        if path not in names:
            return None
        if path not in cache:
            cache[path] = git("show", f"{rev}:{path}")
        return cache[path]
    return read


def changed_files(base):
    """[(status, path)] between the merge base of BASE and HEAD, the worktree's uncommitted
    changes and untracked files included; a rename is a deletion and an addition."""
    merge_base = git("merge-base", base, "HEAD").strip()
    found = {}
    for line in git("diff", "--name-status", "--no-renames", merge_base).splitlines():
        status, path = line.split("\t", 1)
        found[path] = status[0]
    for path in git("ls-files", "--others", "--exclude-standard").splitlines():
        if path != ".tools":
            found.setdefault(path, "A")
    return merge_base, sorted((status, path) for path, status in found.items())


def is_doc(path):
    return path.endswith(".md") or path.startswith(DOC_FOLDERS) or path in DOC_FILES


def category(path, loaded):
    """(tier, reason) of one file; LOADED is every Forth file src/main.fs loads."""
    if is_doc(path):
        return "docs", "documentation"
    if path.startswith("tests/"):
        return "tests", "a test or test data"
    if path.startswith("src/") and path.endswith(".fs"):
        if path == MAIN or path in loaded:
            return "full", "src/main.fs loads it (bin/leanforth and most tests load src/main.fs)"
        if path.startswith("src/lib/"):
            return "library", "a library src/main.fs does not load"
        if path.startswith("src/front/"):
            return "front", "a front-end file src/main.fs does not load"
        return "full", "a Forth source outside src/lib and src/front"
    return "full", "not documentation, a test, a library or the front end"


class Reach:
    """The targets of make check and the files each uses (changed-tests.py's closure)."""

    def __init__(self, rules):
        self.every, self.of_test = units(rules)
        with ThreadPoolExecutor(max_workers=8) as pool:
            self.text = dict(zip(self.every, pool.map(changed_tests.recipe, self.every)))
        self.cache = {}
        self.uses = {u: changed_tests.closure(changed_tests.named_files(self.text[u]), self.cache)
                     for u in self.every}
        self.inputs = None

    def loaders(self, path):
        """The targets of make test that may load or run PATH: those whose inputs (Inputs, the
        finder of the per-target reuse) hold it, unit and end-to-end alike, and any whose recipe
        make -n cannot print. A file's block counts over them are those of all of make test."""
        if self.inputs is None:
            self.inputs = Inputs()
            self.inputs.prefetch(self.of_test)
        return [u for u in self.of_test if (self.inputs.read(u) is None or path in self.inputs.read(u))]

    def users(self, path):
        return [u for u in self.every if path in self.uses[u]]

    def data_users(self, path):
        """Targets whose programs may read a data file through a path built at run time: those
        naming its basename or its folder's name, or searching with a glob for its file type.
        More than needed is chosen, never less."""
        ext, parent = os.path.splitext(path)[1], os.path.basename(os.path.dirname(path))
        found = set()
        for program in self.cache:
            if os.path.splitext(program)[1] not in changed_tests.COMMENT:
                continue
            text = read_worktree(program) or ""
            globs = re.search(r"\b(?:r?glob|walk|listdir|iterdir)\b", text) and ext and ext in text
            quoted = parent and program.endswith((".py", ".sh")) and re.search(f"[\"']{re.escape(parent)}[\"']", text)
            if os.path.basename(path) in text or quoted or globs:
                found.add(program)
        return [u for u in self.every if any(p in self.uses[u] for p in found)]

    def folder_users(self, path):
        folder = os.path.dirname(path) + "/"
        return [u for u in self.every if any(f.startswith(folder) for f in self.uses[u])]

    def runs_gforth(self, unit):
        return "gforth" in self.text[unit]

    def driven(self, path):
        """The source files a test file drives: the files of src/ its programs name or load
        without passing through another source file; for a data file, those of every
        program that names it."""
        if os.path.splitext(path)[1] in changed_tests.COMMENT:
            programs = [path]
        else:
            programs = [p for p, used in self.cache.items() if path in used]
        found, seen, todo = set(), set(), list(programs)
        while todo:
            current = todo.pop()
            if current in seen:
                continue
            seen.add(current)
            if current.startswith("src/"):
                found.add(current)
                continue
            if current.startswith("tests/") and os.path.splitext(current)[1] in changed_tests.COMMENT:
                if current not in self.cache:
                    self.cache[current] = changed_tests.used_files(current, read_worktree(current) or "")
                todo += self.cache[current]
        return found


# --- what a target reads: per-target reuse (owner, 2026-11-17) ------------------------

DIGEST_VERSION = 1
# Make lines that change how every recipe runs (the shell, exported variables come from make).
MAKE_SPECIAL = re.compile(r"^\s*(?:SHELL|\.SHELLFLAGS|\.ONESHELL|\.POSIX|\.EXPORT_ALL_VARIABLES|unexport|"
                          r"vpath|-?include|MAKEFLAGS)\b.*$", re.MULTILINE)
# Toolchain placeholders: a record's Gforth, Lean and cache mode are keyed by their versions and
# mode (scripts/tested-tree.py), so a digest names none of their paths.
PLACEHOLDERS = ("GFORTH=@GFORTH@", "GFORTH_FAST=@GFORTH_FAST@", "LEAN=@LEAN@", "LEAN_CACHE=1")
# Exported variables that only locate a toolchain or the shared Lean cache.
TOOL_LOCATIONS = {"LEANFORTH_GFORTH", "LEANFORTH_LEAN", "LEANFORTH_LEAN_CACHE_DIR", "LEANFORTH_LEAN_CACHE"}
COVERAGE_TOOL = ("scripts/coverage.py", "scripts/coverage-gforth.sh", "scripts/coverage-prelude.fs")
FAULT_RUNNER = ("scripts/mutants.py", "scripts/gforth-strict.sh")


def clean_env():
    """The environment a digest's make runs in: the caller's without what an enclosing make (make
    once, make tier) or push.sh passes down, so a digest is the same whoever computes it."""
    dropped = {"LF_TIMING_LOG", "GFORTH", "LEAN", "LEANEXPORT", "LEAN_CACHE", "TEST_TIMEOUT", "JOBS", "CI"}
    return {k: v for k, v in changed_tests.make_env().items()
            if k not in dropped and not k.startswith(("LEANFORTH_", "MAKE"))}


def digest_of(*parts):
    return hashlib.sha256(json.dumps(parts, sort_keys=True).encode()).hexdigest()


class Inputs:
    """What each target of make check reads in HEAD's tree, and a digest of it: its recipe as
    make -n prints it (prerequisites' recipes included, the checkout's path and the toolchain
    left out), the variables make exports to every recipe and the special make lines, and the
    git blob of every file changed-tests.py's input_files() finds from the recipe (programs
    followed through loads, imports and named paths; data by folder, name, extension and
    template). None, never reused, when a reason makes the inputs unknowable: a program or the
    recipe reads git's index or history, files outside the checkout or an export the
    environment names, or lists a folder the finder cannot name."""

    def __init__(self):
        self.top = os.getcwd()
        self.tracked = changed_tests.tracked_files()
        self.index = changed_tests.file_index(self.tracked)
        self.cache, self.recipes, self.digests, self.reasons, self.reads = {}, {}, {}, {}, {}
        exported = self.environment()
        makefile = read_worktree("Makefile") or ""
        self.global_text = exported + "\n".join(MAKE_SPECIAL.findall(makefile))
        self.global_files, self.global_reasons = changed_tests.input_files(
            changed_tests.named_files(exported), self.tracked, self.cache, self.index)

    def normal(self, text):
        return text.replace(self.top + "/", "").replace(self.top, ".")

    def environment(self):
        """The variables make exports to every recipe (beyond the caller's own), normalized."""
        env = clean_env()
        run = subprocess.run(["make", "-s", "--no-print-directory", "--eval", "__lf_inputs_env: ; @env -0",
                              "__lf_inputs_env", *PLACEHOLDERS], capture_output=True, text=True, env=env)
        lines = []
        for item in run.stdout.split("\0"):
            name, _, value = item.partition("=")
            if name and env.get(name) != value and name not in TOOL_LOCATIONS and not name.startswith(("MAKE", "MFLAGS")):
                lines.append(f"{name}={self.normal(value)}")
        return "\n".join(sorted(lines)) + "\n"

    def recipe(self, target):
        if target not in self.recipes:
            self.recipes[target] = self._recipe(target)
        return self.recipes[target]

    def prefetch(self, targets):
        """make -n of every target of TARGETS, eight at a time (each takes a fraction of a second)."""
        todo = [t for t in targets if t not in self.recipes]
        with ThreadPoolExecutor(max_workers=8) as pool:
            for name, text in zip(todo, pool.map(self._recipe, todo)):
                self.recipes[name] = text

    def _recipe(self, target):
        run = subprocess.run(["make", "-n", "--no-print-directory", "-j1", target, *PLACEHOLDERS],
                             capture_output=True, text=True, env=clean_env())
        return self.normal(run.stdout) if run.returncode == 0 else None

    def read(self, name):
        """The files target NAME may read (the files its digest covers), or None when make -n
        fails. The coverage of a file is measured over every target of make test that reads it."""
        if name not in self.reads:
            text = self.recipe(name)
            self.reads[name] = None if text is None else self.files(changed_tests.named_files(text))[0]
        return self.reads[name]

    def files(self, start):
        """(input files, reasons) of programs and files START, the exported ones included."""
        files, reasons = changed_tests.input_files(start, self.tracked, self.cache, self.index)
        return files | self.global_files, reasons + self.global_reasons

    def blobs(self, files):
        return sorted((p, self.tracked[p]) for p in files)

    def target(self, name):
        """The digest of target NAME's inputs, or None (its reasons in self.reasons[NAME])."""
        if name not in self.digests:
            text = self.recipe(name)
            if text is None:
                files, reasons = set(), [f"make -n {name} failed"]
            else:
                named = changed_tests.named_files(text)
                files, reasons = self.files(named)
                reasons = [f"its recipe {why}" for rule, why in changed_tests.UNRESOLVED if rule.search(text)] + reasons
                if not named & set(self.tracked):
                    reasons.append("its recipe names no file of the tree, so what it reads is unknown")
            self.reasons[name] = reasons
            self.digests[name] = None if reasons else digest_of(DIGEST_VERSION, "target", text, self.global_text,
                                                                 self.blobs(files))
        return self.digests[name]

    def fault(self, entry):
        """The digest of a planted fault: its entry, its file and what its test command reads, and
        the runner (whose own git listing only copies the tree the test then reads)."""
        if not entry or entry.get("file") not in self.tracked:
            return None
        files, reasons = self.files(changed_tests.named_files(str(entry.get("test", ""))) | {entry["file"]})
        if reasons:
            return None
        files |= {p for p in FAULT_RUNNER if p in self.tracked}
        return digest_of(DIGEST_VERSION, "fault", entry, self.global_text, self.blobs(files))

    def coverage(self, path, targets, baseline):
        """The digest of the coverage ratchet of PATH over TARGETS: their digests, the baseline's
        entry for PATH and the coverage tool's files; None when a target's is."""
        digests = [self.target(t) for t in sorted(set(targets))]
        if None in digests or path not in self.tracked:
            return None
        entry = (baseline or {}).get("files", {}).get(path)
        return digest_of(DIGEST_VERSION, "coverage", path, self.tracked[path], entry, digests,
                         self.blobs(p for p in COVERAGE_TOOL if p in self.tracked))


# --- planted faults --------------------------------------------------------------

def is_fault_file(path):
    """Whether PATH is a file of the fault list: FAULTS or a *.toml of FAULTS_DIR."""
    return path == FAULTS or (os.path.dirname(path) == FAULTS_DIR and path.endswith(".toml"))


def fault_list(rev=None):
    """{id: entry} of the whole fault list (FAULTS and FAULTS_DIR's files) in the worktree, or at
    commit REV. A worktree file that does not parse, or an id given twice, stops the plan (exit 2;
    make mutants refuses such a list too); at REV it gives None, so every entry counts as new."""
    if rev is None:
        listed = sorted(os.listdir(FAULTS_DIR)) if os.path.isdir(FAULTS_DIR) else []
        names = [FAULTS] + [f"{FAULTS_DIR}/{n}" for n in listed]
        read = read_worktree
    else:
        listed = git("ls-tree", "--name-only", f"{rev}:{FAULTS_DIR}", check=False).split()
        names = [FAULTS] + [f"{FAULTS_DIR}/{n}" for n in sorted(listed)]

        def read(name):
            return git("show", f"{rev}:{name}", check=False)
    found = {}
    for name in (n for n in names if is_fault_file(n)):
        try:
            entries = [f for f in tomllib.loads(read(name) or "").get("fault", []) if "id" in f]
        except (tomllib.TOMLDecodeError, TypeError, AttributeError) as error:
            if rev is not None:
                return None
            print(f"test-tier: {name}: malformed fault file: {error}", file=sys.stderr)
            raise SystemExit(2)
        for entry in entries:
            if entry["id"] in found:
                if rev is not None:
                    return None
                print(f"test-tier: fault {entry['id']} is given twice ({name})", file=sys.stderr)
                raise SystemExit(2)
            found[entry["id"]] = entry
    return found


def selected_faults(changed, base_rev):
    """Fault ids whose file or test command names a changed file, or, when the fault list
    changed, whose entry is new or differs from BASE_REV's; never a fault of a missing file.
    A fault also counts when its test command's programs load a changed file (tests/support
    helpers such as tester.fs), through changed-tests.py's closure."""
    paths = {p for _, p in changed}
    cache = {}
    now = fault_list()
    before = None
    if any(is_fault_file(p) for p in paths):
        before = fault_list(base_rev) or {}
    chosen = []
    for ident, fault in now.items():
        if not os.path.isfile(str(fault.get("file", ""))):
            continue
        named = set(changed_tests.PATH.findall(str(fault.get("test", "")))) | {fault.get("file")}
        named |= changed_tests.closure(changed_tests.named_files(str(fault.get("test", ""))), cache)
        if named & paths or (before is not None and before.get(ident) != fault):
            chosen.append(ident)
    return chosen


HUNK = re.compile(r"^@@ -\d+(?:,\d+)? \+(\d+)(?:,(\d+))? @@", re.MULTILINE)


def changed_lines(path, base_rev):
    """The lines of PATH as it is now that differ from BASE_REV, as (first, last) ranges (a
    deletion as the line it follows)."""
    diff = git("diff", "-U0", "--no-renames", base_rev, "--", path, check=False) or ""
    return [(int(first), int(first) + max(int(count or "1"), 1) - 1)
            for first, count in HUNK.findall(diff)]


def text_lines(text, old):
    """(first, last) lines of OLD's first occurrence in TEXT, or None."""
    at = text.find(old)
    if at < 0:
        return None
    first = text.count("\n", 0, at) + 1
    return first, first + old.count("\n")


def touched_faults(changed, base_rev):
    """The full tier's faults (plan 9.4.8j): those whose entry is new or differs from
    BASE_REV's, and those whose old text lies on or next to a line the change touched in its
    file. A fault of a changed file whose text the change left alone still applies as
    before (mutants.py's stale check confirms its old text); the daily full run of make
    mutants covers it."""
    paths = {p for s, p in changed if s != "D"}
    now = fault_list()
    before = None
    if any(is_fault_file(p) for _, p in changed):
        before = fault_list(base_rev) or {}
    hunks, chosen = {}, []
    for ident, fault in now.items():
        path, old = str(fault.get("file", "")), str(fault.get("old", ""))
        if not os.path.isfile(path):
            continue
        if before is not None and before.get(ident) != fault:
            chosen.append(ident)
        elif path in paths:
            if path not in hunks:
                hunks[path] = (changed_lines(path, base_rev), read_worktree(path) or "")
            ranges, text = hunks[path]
            span = text_lines(text, old)
            if span is None or any(a <= span[1] + 1 and span[0] - 1 <= b for a, b in ranges):
                chosen.append(ident)
    return chosen


def full_result(result, changed, base_rev, reach=None, loaded=()):
    """The full tier's suites, and its faults (none for an empty range): the coverage of the
    changed source files first, then FULL_SUITES, then the faults."""
    if result["tier"] == "full":
        result["faults"] = touched_faults(changed, base_rev)
        result["coverage"] = coverage_need(result["files"], reach or Reach(make_database()[0]), loaded, base_rev)
        result["suites"] = coverage_suites(result["coverage"]) + [dict(s) for s in FULL_SUITES]
        if result["faults"]:
            result["suites"].append({"label": "faults", "goals": ["mutants"],
                                     "vars": {"FAULTS": ",".join(result["faults"])}})
    return result


# --- the plan -----------------------------------------------------------------------

def changed_since(rev):
    """[(status, path)] between commit REV and HEAD (committed changes only)."""
    lines = git("diff", "--name-status", "--no-renames", rev, "HEAD").splitlines()
    return sorted((line.split("\t", 1)[0][0], line.split("\t", 1)[1]) for line in lines)


def plan(changed, merge_base, full=False, reach=None):
    """The tier of CHANGED ([(status, path)]) and its suites, as one dictionary. MERGE_BASE
    is the commit the range starts from (None for a list of files: HEAD stands in). REACH,
    a Reach of this tree's Makefile, saves building it again."""
    base_rev = merge_base or "HEAD"
    loaded = forth_closure([MAIN], read_worktree)
    if any(s == "D" for s, _ in changed):
        loaded |= forth_closure([MAIN], reader_at(base_rev))
    files = []
    tactic = None
    if not full and any(p.startswith(tactic_plugins.TACTICS) for _, p in changed):
        tactic = tactic_plugins.check(changed)
    for status, path in changed:
        tier, why = category(path, loaded)
        if tactic and tactic["confined"] and tier != "docs":
            tier, why = "tactic", "a confined tactic plug-in's own file (scripts/check-tactic-plugins.py)"
        if status == "D" and tier != "docs":
            # What used a deleted file (or a rename's old half) is known only from the base
            # tree, which Reach does not read: the safe answer is the full tier.
            tier, why = "full", "deleted or renamed away: its users and coverage are not known from this tree"
        files.append({"path": path, "status": status, "tier": tier, "why": why})
    tier = max((f["tier"] for f in files), key=TIERS.index, default="none")
    if full:
        tier = "full"
    result = {"base": merge_base, "tier": tier, "files": files, "targets": [], "engine_targets": [],
              "faults": [], "coverage": None, "suites": [], "tactic_check": tactic}
    if tier == "none":
        return result
    reach_ = reach or Reach(make_database()[0])
    if tier == "full":
        return full_result(result, changed, base_rev, reach_, loaded)
    chosen = set()
    for f in files:
        path, users = f["path"], reach_.users(f["path"])
        if f["tier"] == "tests" and os.path.splitext(path)[1] not in changed_tests.COMMENT:
            users = users + reach_.data_users(path)
        if is_fault_file(path):
            users = users + reach_.users(FAULTS)   # a faults.d file is part of the one list
        if path.startswith("src/") and path.endswith(".fs"):
            users += SOURCE_RULE_TARGETS
        if path.endswith(".md"):
            users.append("check-docs")
        if f["tier"] == "front":
            users += FRONT_TARGETS
        if f["tier"] == "tactic":
            users += tactic_targets(reach_)
            if os.path.splitext(path)[1] not in changed_tests.COMMENT:
                users += reach_.data_users(path)
        if f["tier"] == "tests" and not users:
            users = reach_.folder_users(path)
            f["why"] += "; no target names it, so the targets of its folder"
            if not users:
                f["tier"], f["why"] = "full", "a test file no target uses, nor any file of its folder"
        if f["tier"] == "docs" and not users:
            users = ["check-docs"]
        f["targets"] = sorted(set(users))
        chosen |= set(users)
    tier = max((f["tier"] for f in files), key=TIERS.index)
    result["tier"] = tier
    if tier == "full":
        return full_result(result, changed, base_rev, reach_, loaded)
    result["targets"] = [u for u in reach_.every if u in chosen] + sorted(chosen - set(reach_.every))
    engine_unit = engine_units(reach_)
    result["engine_targets"] = [u for u in reach_.of_test if u in chosen and engine_unit(u)]
    if tier != "docs":
        result["faults"] = selected_faults(changed, base_rev)
        result["coverage"] = coverage_need(files, reach_, loaded, base_rev)
    result["suites"] = suites_of(result)
    problems = engine_problems(result, engine_unit, end_to_end())
    if problems:
        print("test-tier: " + "; ".join(problems), file=sys.stderr)
        raise SystemExit(2)
    return result


def tactic_targets(reach_):
    """The tactic tier's targets (the design's decision 2): the front end's unit tests (the unit
    targets of make test that run a program of tests/front/), every end-to-end run of .lf files
    (an end-to-end target that reads a .lf file) and the S1/S2 pinned-Lean comparisons."""
    e2e = end_to_end()
    units = [u for u in reach_.of_test if u not in e2e and any(p.startswith("tests/front/") for p in reach_.uses[u])]
    lf_runs = [u for u in reach_.every if u in e2e and any(p.endswith(".lf") for p in reach_.uses[u])]
    return units + lf_runs + [t for t in TACTIC_REFERENCE if t in reach_.every]


def end_to_end():
    """The end-to-end targets of tests/test-classes.txt. A target the table lacks counts as a
    unit test here, so the engines run more, never less (make check-test-classes refuses it)."""
    return test_classes.OfClass(test_classes.read()[0], "e2e")


def engine_units(reach_):
    """( target -- flag ): whether a target is a unit test of make test whose recipe runs Gforth,
    which every engine runs."""
    e2e, of_test = end_to_end(), set(reach_.of_test)
    return lambda u: u in of_test and u not in e2e and reach_.runs_gforth(u)


def engine_problems(result, engine_unit, e2e):
    """Why RESULT's suites break the owner's split (2026-11-14), or []: in a smaller tier each
    reached target for which ENGINE_UNIT holds runs on every engine of a tier (TIER_ENGINES) and
    no target of E2E (the end-to-end tests) runs on one; the full tier runs make test-unit on
    each; no tier runs Gforth 0.7.3 (make daily does)."""
    on = {s["engine"]: s["goals"] for s in result["suites"] if s.get("engine")}
    problems = [f"a tier runs {ENGINES[e]} (only make daily does)" for e in on if e not in TIER_ENGINES]
    if result["tier"] == "full":
        return problems + [f"the full tier runs no make test-unit on {ENGINES[engine]}" for engine in TIER_ENGINES
                           if on.get(engine) != ["test-unit"]]
    for engine, name in ((e, ENGINES[e]) for e in TIER_ENGINES):
        goals = on.get(engine, [])
        problems += [f"unit test {u} would not run on {name}" for u in result["targets"]
                     if engine_unit(u) and u not in goals]
        problems += [f"end-to-end test {u} would run on {name}" for u in goals if u in e2e]
    return problems


def runs_forth(path):
    """Whether a changed test file can run Forth code: a Forth file, data, or a program that
    names Gforth (a Python test of a script that only names source files as text runs none).
    The tests of the test tooling (TOOL_TESTS: the scripts' tests on throw-away repositories,
    the fault runner's, the Lean cache's, the class table) run no Forth of src/."""
    if path.startswith(TOOL_TESTS):
        return False
    if os.path.splitext(path)[1] not in (".py", ".sh"):
        return True
    return re.search(r"gforth|\.fs\b.*(?:run|include|require)|leanforth", read_worktree(path) or "",
                     re.IGNORECASE) is not None


def baseline_changes(base_rev):
    """The files whose entries of tests/coverage-baseline.json differ from BASE_REV's, or None
    when the run count differs or either side does not parse (then all of make coverage-check)."""
    try:
        now = json.loads(read_worktree(COVERAGE_BASELINE) or "")
        before = json.loads(git("show", f"{base_rev}:{COVERAGE_BASELINE}", check=False) or "")
        if now.get("runs") != before.get("runs"):
            return None
        a, b = now.get("files", {}), before.get("files", {})
        return {p for p in set(a) | set(b) if a.get(p) != b.get(p)}
    except (ValueError, AttributeError):
        return None


def coverage_need(files, reach_, loaded, base_rev="HEAD"):
    """None, {"kind": "all"} (make coverage-check) or {"kind": "focus", files, targets, skipped}:
    the ratchet of the changed source files (owner, 2026-11-17): every Forth file of src/ the
    change touches, the files a changed test drives and the files whose baseline entry changed,
    over every target of make test that loads or runs one of them, unit and end-to-end
    (Reach.loaders, 2026-11-18): tests/coverage-baseline.json counts a file's never-run blocks
    over all of make test, and only these targets run its blocks, so the focused count is the
    full run's. A file no target of make test reads ("skipped") is left to make daily's full
    run. Only a change of the baseline's run count needs all of make coverage-check, which make
    daily runs. LOADED is kept for the callers."""
    focus = set()
    for f in files:
        if f["status"] == "D" and f["path"].startswith("tests/") and f["path"].endswith(PROGRAMS):
            return {"kind": "all", "why": f"{f['path']} was deleted: what it drove is known only from the base"}
        if f["status"] == "D":
            continue
        if f["path"] == COVERAGE_BASELINE:
            changed = baseline_changes(base_rev)
            if changed is None:
                return {"kind": "all", "why": f"{COVERAGE_BASELINE}'s run count changed"}
            focus |= {p for p in changed if os.path.isfile(p)}
        elif f["path"].startswith("src/") and f["path"].endswith(".fs"):
            focus.add(f["path"])
        elif f["tier"] == "tests" and runs_forth(f["path"]):
            focus |= reach_.driven(f["path"])
    focus = {p for p in focus if p.endswith(".fs")}
    if not focus:
        return None
    loaders = {p: reach_.loaders(p) for p in sorted(focus)}
    measured = sorted(p for p in focus if loaders[p])
    targets = [u for u in reach_.of_test if any(u in loaders[p] for p in measured)]
    return {"kind": "focus", "files": measured, "targets": targets,
            "skipped": sorted(p for p in focus if not loaders[p])}


def coverage_suites(cover):
    if cover and cover["kind"] == "all":
        return [{"label": "coverage-check", "goals": ["coverage-check"]}]
    if cover and cover["files"]:
        return [{"label": "coverage-focus", "goals": ["coverage-focus"],
                 "vars": {"COVERAGE_FILES": " ".join(cover["files"]),
                          "COVERAGE_TARGETS": " ".join(cover["targets"])}}]
    return []


def suites_of(result):
    """The suites of a tier smaller than full, the instrumented run first (its record then
    stands in for the plain runs of the same targets)."""
    suites = coverage_suites(result["coverage"])
    if result["targets"]:
        suites.append({"label": "targets", "goals": result["targets"]})
    for engine in TIER_ENGINES if result["engine_targets"] else ():
        suites.append({"label": f"targets{engine}", "goals": result["engine_targets"], "engine": engine})
    if result["faults"]:
        suites.append({"label": "faults", "goals": ["mutants"], "vars": {"FAULTS": ",".join(result["faults"])}})
    return suites


def describe(result):
    """The plan as text, for people."""
    lines = [f"tier: {result['tier']} ({len(result['files'])} changed files since {result['base'] or 'the given list'})"]
    for f in result["files"]:
        lines.append(f"  {f['status']} {f['path']}: {f['tier']}, {f['why']}")
    tactic = result.get("tactic_check")
    if tactic:
        lines.append("tactic plug-in check: " + ("confined" if tactic["confined"] else
                                                 "; ".join(tactic["problems"] + tactic["reasons"])))
    for path in (result.get("coverage") or {}).get("skipped", []):
        lines.append(f"coverage of {path}: no target of make test reads it; make daily's full run measures it")
    for s in result["suites"]:
        extra = " ".join(f"{k}='{v}'" for k, v in s.get("vars", {}).items())
        gforth = f" ({ENGINES[s['engine']]})" if s.get("engine") else ""
        lines.append(f"suite {s['label']}{gforth}: make {' '.join(s['goals'])} {extra}".rstrip())
    return "\n".join(lines)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--base", default="main")
    parser.add_argument("--files", nargs="+", help="these files (as modified) instead of git's changes")
    parser.add_argument("--full", action="store_true", help="the full tier whatever changed")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)
    os.chdir(git("rev-parse", "--show-toplevel").strip())
    if args.files:
        merge_base, changed = None, [("M" if os.path.exists(p) else "D", os.path.normpath(p)) for p in args.files]
    else:
        merge_base, changed = changed_files(args.base)
    result = plan(changed, merge_base, args.full)
    print(json.dumps(result, indent=1) if args.json else describe(result))
    return 0


if __name__ == "__main__":
    sys.exit(main())
