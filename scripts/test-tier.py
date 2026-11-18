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

TIERS = ("none", "docs", "tests", "library", "front", "full")
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
FULL_SUITES = (
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


def full_result(result, changed, base_rev):
    """The full tier's suites, and its faults (none for an empty range)."""
    if result["tier"] == "full":
        result["faults"] = touched_faults(changed, base_rev)
        result["suites"] = [dict(s) for s in FULL_SUITES]
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
    for status, path in changed:
        tier, why = category(path, loaded)
        if status == "D" and tier != "docs":
            # What used a deleted file (or a rename's old half) is known only from the base
            # tree, which Reach does not read: the safe answer is the full tier.
            tier, why = "full", "deleted or renamed away: its users and coverage are not known from this tree"
        files.append({"path": path, "status": status, "tier": tier, "why": why})
    tier = max((f["tier"] for f in files), key=TIERS.index, default="none")
    if full:
        tier = "full"
    result = {"base": merge_base, "tier": tier, "files": files, "targets": [], "engine_targets": [],
              "faults": [], "coverage": None, "suites": []}
    if tier in ("full", "none"):
        return full_result(result, changed, base_rev)
    reach_ = reach or Reach(make_database()[0])
    chosen = set()
    for f in files:
        path, users = f["path"], reach_.users(f["path"])
        if f["tier"] == "tests" and os.path.splitext(path)[1] not in changed_tests.COMMENT:
            users = users + reach_.data_users(path)
        if path.startswith("src/") and path.endswith(".fs"):
            users += SOURCE_RULE_TARGETS
        if path.endswith(".md"):
            users.append("check-docs")
        if f["tier"] == "front":
            users += FRONT_TARGETS
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
        return full_result(result, changed, base_rev)
    result["targets"] = [u for u in reach_.every if u in chosen] + sorted(chosen - set(reach_.every))
    engine_unit = engine_units(reach_)
    result["engine_targets"] = [u for u in reach_.of_test if u in chosen and engine_unit(u)]
    if tier != "docs":
        result["faults"] = selected_faults(changed, base_rev)
        result["coverage"] = coverage_need(files, reach_, loaded)
    result["suites"] = suites_of(result)
    problems = engine_problems(result, engine_unit, end_to_end())
    if problems:
        print("test-tier: " + "; ".join(problems), file=sys.stderr)
        raise SystemExit(2)
    return result


def end_to_end():
    """The end-to-end targets of tests/test-classes.txt. A target the table lacks counts as a
    unit test here, so the engines run more, never less (make check-test-classes refuses it)."""
    return set(test_classes.of_class(test_classes.read()[0], "e2e"))


def engine_units(reach_):
    """( target -- flag ): whether a target is a unit test of make test whose recipe runs Gforth,
    which every engine runs."""
    e2e, of_test = end_to_end(), set(reach_.of_test)
    return lambda u: u in of_test and u not in e2e and reach_.runs_gforth(u)


def engine_problems(result, engine_unit, e2e):
    """Why RESULT's suites break the owner's split (2026-11-14), or []: in a smaller tier each
    reached target for which ENGINE_UNIT holds runs on every engine and no target of E2E (the
    end-to-end tests) runs on one; the full tier runs make test-unit on every engine."""
    on = {s["engine"]: s["goals"] for s in result["suites"] if s.get("engine")}
    if result["tier"] == "full":
        return [f"the full tier runs no make test-unit on {name}" for engine, name in ENGINES.items()
                if on.get(engine) != ["test-unit"]]
    problems = []
    for engine, name in ENGINES.items():
        goals = on.get(engine, [])
        problems += [f"unit test {u} would not run on {name}" for u in result["targets"]
                     if engine_unit(u) and u not in goals]
        problems += [f"end-to-end test {u} would run on {name}" for u in goals if u in e2e]
    return problems


def coverage_need(files, reach_, loaded):
    """None, {"kind": "all"} (make coverage-check) or {"kind": "focus", files, targets}."""
    focus = set()
    for f in files:
        if f["status"] == "D":
            continue
        if f["path"] == COVERAGE_BASELINE:
            return {"kind": "all", "why": f"{COVERAGE_BASELINE} changed"}
        if f["tier"] in ("library", "front"):
            focus.add(f["path"])
        elif f["tier"] == "tests":
            focus |= reach_.driven(f["path"])
    focus = {p for p in focus if p.endswith(".fs")}
    if not focus:
        return None
    if focus & (loaded | {MAIN}):
        return {"kind": "all", "why": "a changed test drives files src/main.fs loads: "
                + " ".join(sorted(focus & (loaded | {MAIN}))[:3])}
    targets = [u for u in reach_.of_test if any(p in reach_.uses[u] for p in focus)]
    targets += [u for u in ("smoke",) if u not in targets]
    return {"kind": "focus", "files": sorted(focus), "targets": targets}


def suites_of(result):
    """The suites of a tier smaller than full, the instrumented run first (its record then
    stands in for the plain runs of the same targets)."""
    suites, cover = [], result["coverage"]
    if cover and cover["kind"] == "all":
        suites.append({"label": "coverage-check", "goals": ["coverage-check"]})
    elif cover:
        suites.append({"label": "coverage-focus", "goals": ["coverage-focus"],
                       "vars": {"COVERAGE_FILES": " ".join(cover["files"]),
                                "COVERAGE_TARGETS": " ".join(cover["targets"])}})
    if result["targets"]:
        suites.append({"label": "targets", "goals": result["targets"]})
    for engine in ENGINES if result["engine_targets"] else ():
        suites.append({"label": f"targets{engine}", "goals": result["engine_targets"], "engine": engine})
    if result["faults"]:
        suites.append({"label": "faults", "goals": ["mutants"], "vars": {"FAULTS": ",".join(result["faults"])}})
    return suites


def describe(result):
    """The plan as text, for people."""
    lines = [f"tier: {result['tier']} ({len(result['files'])} changed files since {result['base'] or 'the given list'})"]
    for f in result["files"]:
        lines.append(f"  {f['status']} {f['path']}: {f['tier']}, {f['why']}")
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
