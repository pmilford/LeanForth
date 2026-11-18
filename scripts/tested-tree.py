#!/usr/bin/env python3
"""Records of the suites that passed on a tree, and the runner of the change tiers
(plan 9.4.6; owner, 2026-11-13: never re-run a suite on a tree that already passed it).

Usage (from the repository root):
  python3 scripts/tested-tree.py once -- make GOAL... [VAR=VALUE...]      (make once)
  python3 scripts/tested-tree.py record -- make GOAL... [VAR=VALUE...]
  python3 scripts/tested-tree.py lookup -- make GOAL... [VAR=VALUE...]
  python3 scripts/tested-tree.py list [--all]
  python3 scripts/tested-tree.py tier [--base REF] [--full] [--with-073]
          [--lean-cache MODE] [--jobs N] [--nice N] [--make MAKE] [--log-prefix PATH]
          [--summary FILE] [--no-progress] [--dry-run]                   (make tier, push.sh)
  python3 scripts/tested-tree.py daily [--jobs N] [--nice N] [--make MAKE] [--dry-run] ...
                                                                          (make daily)
  python3 scripts/tested-tree.py daily-status [--warn-hours H]            (push.sh)
  python3 scripts/tested-tree.py tag-check                                (make tag-check)

A record says that a make command exited 0 on the tree `git rev-parse HEAD^{tree}` names,
with this Gforth (`--version` of GFORTH, else of the Makefile's default), this Lean (of
LEAN) and this LEAN_CACHE mode. It keeps the commit, branch, date, command and seconds,
and what the run stands for ("covers"): every target make built for its goals (make -pn);
for make coverage-check also the coverage ratchet of every file, and make test's targets
except those of the Makefile's COVERAGE_ENGINE_DIFFERS, whose Gforth changes under
coverage; for make coverage-focus the ratchet of COVERAGE_FILES and its targets so; for
make mutants each fault it ran (FAULTS, else all). A goal given any other variable stands
only for that exact command. Make options other than -s and --no-print-directory (-n,
-k, -i ...) are refused.

record runs the command and writes a record only when it exited 0 and the tree was the
same, with nothing uncommitted, before and after the run. A worktree with changes to
tracked files, or with new files under src/, tests/, scripts/, bin/, schemas/ or docs/
(which the suites' globs would pick up), is refused before anything runs: the tree would
not be what was tested. A failed run writes nothing. lookup exits 0 when records with this
Gforth and Lean and a cache mode at least as strong (0 or verify stand for 1, verify for
0; for make test's own targets, which run no Lean, any mode) cover all the command stands
for, and prints them; else 1. Records of HEAD's tree count whole. A record of an earlier
commit of HEAD's history counts for what the change since that commit cannot reach: the
change gets scripts/test-tier.py's tier, and the record loses that tier's targets and
faults (and all coverage, when the tier asks for coverage); a full tier leaves it nothing.
So a documentation commit after a tested merge needs only make check-docs and the targets
that read its pages. once is lookup, then record of what is still missing (only the
targets of make check or the faults that hold it; the whole command when coverage is
missing). list prints the records of HEAD's tree (--all: every record).

tier runs the suites of scripts/test-tier.py's tier of BASE...HEAD (default main) in
order, each as once does. A suite of the unit tests on another engine (test-tier.py's
ENGINES) runs with GFORTH set to that engine: gforth-fast beside the main checkout's
Gforth 1.0 (LF_GFORTH_FAST names another), or Gforth 0.7.3; its records name the engine
(gforth-fast prints Gforth 1.0's version, so its records add "(gforth-fast)"). The 0.7.3
suites run only with --with-073, which push.sh passes: a branch's tier leaves them to the
push and the daily run (owner, 2026-11-14). Then the progress check
(scripts/check-progress.py BASE) runs, unless --no-progress. --dry-run prints what would
run or be reused and runs nothing. It prints, and writes to --summary as one line, each
suite: ran (exit status, seconds, command) or reused (the record's commit and date), and
the full tier's suites the tier did not need.

daily is the daily full run (owner, 2026-11-17: its own command, run once a night and before
a tag, never forced by a push): the full tier of HEAD with LEAN_CACHE=0 and Gforth 0.7.3,
each suite recorded per tree as tier records it. A daily run of a tree is complete when that
tree has records of make coverage-check, make test-unit on gforth-fast, make check-rest (or
make check) with LEAN_CACHE=0 and make test-unit on Gforth 0.7.3, none narrowed by a variable.
daily-status prints the newest complete daily run (its date, commit and age) and, with
--warn-hours H, a warning when there is none or it is older than H hours; it always exits 0
(push.sh reports it, never refuses on it). tag-check exits 0 when HEAD's exact tree has a
complete daily run (a tag requires one), else 1 naming what is missing.

Records live in the main checkout's .claude/work/ci/tested/ (one JSON file each), shared
by every worktree of the clone like the Lean cache and never committed; LF_TESTED_DIR
names another folder (the tests use a temporary one). LF_TESTED_NOW (YYYY-MM-DD
HH:MM:SS) fixes the clock for tests; LF_GFORTH073 names Gforth 0.7.3 (default the main
checkout's .claude/work/A/gforth073.sh), LF_GFORTH_FAST gforth-fast (default the main
checkout's .tools/gforth/bin/gforth-fast). Exit status: the command's (record, once; 0 when
reused), 0 or 1 (lookup, tier, daily, tag-check), 0 (daily-status), 2 usage error, 3 refused or not recordable.
"""
import argparse
import datetime
import hashlib
import importlib.util
import json
import os
import re
import shlex
import subprocess
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location("test_tier", os.path.join(HERE, "test-tier.py"))
test_tier = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(test_tier)

VERSION = 1
LOCAL_GFORTH = ".tools/gforth/bin/gforth"
LOCAL_LEAN = ".tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean"
WATCHED = ("src", "tests", "scripts", "bin", "schemas", "docs")
NEUTRAL = {"JOBS", "TEST_TIMEOUT", "MUTANTS_TIMEOUT", "GFORTH", "LEAN", "LEAN_CACHE", "LEAN_CACHE_DIR",
           "FAULTS", "COVERAGE_FILES", "COVERAGE_TARGETS"}
NARROWING = {"FAULTS", "COVERAGE_FILES", "COVERAGE_TARGETS"}  # a run with them is partial
MAKE_OPTIONS = {"-s", "--silent", "--no-print-directory"}
STRONGER = {"1": {"1", "0", "verify"}, "0": {"0", "verify"}, "verify": {"verify"}}
COVERAGE_ALL = "coverage:all"
VARIABLE = re.compile(r"^([A-Za-z_][A-Za-z0-9_]*)=(.*)$", re.DOTALL)


class Refused(Exception):
    """The command cannot be run or recorded as asked (exit status 3)."""


class Usage(Exception):
    """A malformed command (exit status 2)."""


def git(*args):
    result = subprocess.run(["git", *args], capture_output=True, text=True)
    if result.returncode != 0:
        raise Refused(f"git {' '.join(args)}: {result.stderr.strip()}")
    return result.stdout.strip()


def checkout():
    """The main checkout of this clone (where .claude/work lives), from any worktree."""
    common = git("rev-parse", "--path-format=absolute", "--git-common-dir")
    return os.path.dirname(common) if common.endswith("/.git") else git("rev-parse", "--show-toplevel")


def tested_dir():
    return os.environ.get("LF_TESTED_DIR") or os.path.join(checkout(), ".claude/work/ci/tested")


def gforth073():
    return os.environ.get("LF_GFORTH073") or os.path.join(checkout(), ".claude/work/A/gforth073.sh")


def gforth_fast():
    return os.environ.get("LF_GFORTH_FAST") or os.path.join(checkout(), ".tools/gforth/bin/gforth-fast")


def engine_gforth(engine):
    """The GFORTH of a suite run on ENGINE (test-tier.py's ENGINES)."""
    return {"fast": gforth_fast, "073": gforth073}[engine]()


def now():
    return os.environ.get("LF_TESTED_NOW") or datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")


def tree():
    return git("rev-parse", "HEAD^{tree}")


def dirty():
    """Why this worktree is not exactly HEAD's tree, as far as the suites can see."""
    lines = git("status", "--porcelain", "--untracked-files=no").splitlines()
    others = git("ls-files", "--others", "--exclude-standard").splitlines()
    # Untracked files of the watched folders and every root-level file (lean-toolchain, Makefile).
    lines += ["?? " + p for p in others if "/" not in p or p.split("/")[0] in WATCHED]
    return [line for line in lines if line.strip()]


# --- commands and what they stand for ---------------------------------------------

def parse(argv):
    """(goals, {variable: value}) of a make command line."""
    if not argv or os.path.basename(argv[0]) not in ("make", "gmake"):
        raise Usage("only a make command can be recorded: make GOAL... [VAR=VALUE...]")
    goals, variables = [], {}
    for word in argv[1:]:
        match = VARIABLE.match(word)
        if word.startswith("-"):
            if word not in MAKE_OPTIONS:
                raise Usage(f"make option {word} is refused: it changes what a pass means")
        elif match:
            variables[match[1]] = match[2]
        else:
            goals.append(word)
    if not goals:
        raise Usage("name the goals: make's default goal is not recorded")
    return goals, variables


_versions = {}


def version(program):
    if program not in _versions:
        try:
            run = subprocess.run([program, "--version"], stdin=subprocess.DEVNULL, capture_output=True,
                                 text=True, timeout=120)
            lines = (run.stdout or run.stderr).strip().splitlines()
            _versions[program] = lines[0].strip() if run.returncode == 0 and lines else None
        except (OSError, subprocess.TimeoutExpired):
            _versions[program] = None
    return _versions[program]


def toolchain(variables):
    """{"gforth", "lean", "lean_cache"} of a command, as its make run would use them."""
    gforth = variables.get("GFORTH") or (LOCAL_GFORTH if os.path.exists(LOCAL_GFORTH) else "gforth")
    lean = variables.get("LEAN") or (LOCAL_LEAN if os.path.exists(LOCAL_LEAN) else "lean")
    cache = variables.get("LEAN_CACHE") or os.environ.get("LEAN_CACHE") or ("0" if os.environ.get("CI") else "1")
    found = version(gforth)
    if found is None:
        raise Refused(f"cannot read the version of the Gforth {gforth}")
    # gforth-fast prints the version of Gforth's checking engine: the record names the engine.
    if os.path.basename(os.path.realpath(gforth)).startswith("gforth-fast"):
        found += " (gforth-fast)"
    return {"gforth": found, "lean": version(lean) or "none", "lean_cache": cache}


class Make:
    """make's database of this tree: what a command's goals build."""

    def __init__(self):
        self.rules, self.recipes, variables = test_tier.make_database()
        self.differs = self.built(variables.get("COVERAGE_ENGINE_DIFFERS", "").split())
        self.of_test = self.built(["test"])
        self.units = test_tier.units(self.rules)[0]
        self.reach, self.deltas = None, {}

    def built(self, goals):
        return test_tier.reach(goals, self.rules) & self.recipes

    def since(self, commit):
        """(what the change from COMMIT to HEAD reaches, its tier), or (None, tier) when it
        reaches everything (the full tier) or COMMIT is no ancestor of HEAD. What it reaches:
        the targets of its tier, its faults, and every coverage item ("coverage") when the
        tier asks for coverage."""
        if commit not in self.deltas:
            ancestor = subprocess.run(["git", "merge-base", "--is-ancestor", commit, "HEAD"],
                                      capture_output=True).returncode == 0
            if not ancestor:
                self.deltas[commit] = (None, "not an ancestor")
            else:
                self.reach = self.reach or test_tier.Reach(self.rules)
                result = test_tier.plan(test_tier.changed_since(commit), commit, reach=self.reach)
                reached = None
                if result["tier"] != "full":
                    reached = self.built(result["targets"]) | {"fault:" + f for f in result["faults"]}
                    reached |= {"coverage"} if result["coverage"] else set()
                self.deltas[commit] = (reached, result["tier"])
        return self.deltas[commit]

    def covers(self, goals, variables):
        """Everything a pass of make GOALS VARIABLES stands for."""
        extra = {k: v for k, v in variables.items() if k not in NEUTRAL}
        if extra:
            return {f"{g} {json.dumps(extra, sort_keys=True)}" for g in goals}
        out = set()
        for goal in goals:
            if goal == "coverage-check":
                out |= {goal, COVERAGE_ALL} | (self.of_test - self.differs)
            elif goal == "coverage-focus":
                out |= {"coverage:" + f for f in variables.get("COVERAGE_FILES", "").split()}
                out |= self.built(variables.get("COVERAGE_TARGETS", "").split()) - self.differs
            elif goal == "mutants":
                faults = [f for f in variables.get("FAULTS", "").split(",") if f] or all_faults()
                out |= {"fault:" + f for f in faults}
            else:
                out |= self.built([goal]) or {goal}
        return out

    def lean_free(self, needs):
        """Whether NEEDS are only make test's targets and coverage, which run no Lean."""
        return all(n in self.of_test or n.startswith("coverage") for n in needs)


def all_faults():
    return list(test_tier.fault_entries(test_tier.read_worktree(test_tier.FAULTS) or ""))


# --- records --------------------------------------------------------------------------

def load_records():
    folder, records = tested_dir(), []
    if not os.path.isdir(folder):
        return records
    for name in sorted(os.listdir(folder)):
        if name.endswith(".json"):
            try:
                with open(os.path.join(folder, name), encoding="utf-8") as stream:
                    record = json.load(stream)
            except (OSError, ValueError):
                print(f"tested-tree: unreadable record {name}, ignored", file=sys.stderr)
                continue
            if isinstance(record, dict) and record.get("version") == VERSION and record.get("exit") == 0:
                records.append(record)
    return records


def write_record(record):
    folder = tested_dir()
    os.makedirs(folder, exist_ok=True)
    key = json.dumps([record[k] for k in ("suite", "gforth", "lean", "lean_cache", "command")])
    path = os.path.join(folder, f"{record['tree']}-{hashlib.sha256(key.encode()).hexdigest()[:16]}.json")
    handle, temporary = tempfile.mkstemp(dir=folder, prefix=".record-")
    with os.fdopen(handle, "w", encoding="utf-8") as stream:
        json.dump(record, stream, indent=1, sort_keys=True)
        stream.write("\n")
    os.replace(temporary, path)
    return path


MAX_EARLIER_COMMITS = 40   # earlier commits whose records lookup weighs, newest first


def matching(records, chain, lean_free):
    return [r for r in records if r.get("gforth") == chain["gforth"] and r.get("lean") == chain["lean"]
            and (lean_free or r.get("lean_cache") in STRONGER.get(chain["lean_cache"], {chain["lean_cache"]}))]


def usable(record, reached):
    """What RECORD still stands for after a change that REACHED these items."""
    covers = set(record.get("covers", ()))
    if "coverage" in reached:
        covers = {c for c in covers if not c.startswith("coverage")}
    return covers - reached


def gained(have, needs):
    """HAVE with each coverage item of NEEDS when it holds the ratchet of every file."""
    return have | {n for n in needs if n.startswith("coverage:")} if COVERAGE_ALL in have else have


def lookup(argv, make=None, records=None):
    """(missing, [(record, note)] used, toolchain) for a command at HEAD: records of HEAD's
    tree, then records of earlier commits of HEAD's history for all the change since that
    commit cannot reach (scripts/test-tier.py's tier of it; none when that tier is full)."""
    goals, variables = parse(argv)
    make = make or Make()
    chain = toolchain(variables)
    needs = make.covers(goals, variables)
    pool = matching(load_records() if records is None else records, chain, make.lean_free(needs))
    here, have, used = tree(), set(), []

    def take(record, covers, note):
        """Use RECORD (standing for COVERS) when it supplies something still missing."""
        nonlocal have
        before, after = needs - gained(have, needs), needs - gained(have | covers, needs)
        if before - after:
            have |= covers
            used.append((record, note))

    for record in (r for r in pool if r.get("tree") == here):
        take(record, set(record.get("covers", ())), "this tree")
    earlier = sorted((r for r in pool if r.get("tree") != here), key=lambda r: r.get("date", ""), reverse=True)
    for commit in list(dict.fromkeys(r["commit"] for r in earlier))[:MAX_EARLIER_COMMITS]:
        if not needs - gained(have, needs):
            break
        reached, tier = make.since(commit)
        if reached is not None:
            for record in (r for r in earlier if r["commit"] == commit):
                take(record, usable(record, reached), f"changes since are tier {tier}")
    return needs - gained(have, needs), used, chain


def shown(argv):
    return " ".join(shlex.quote(a) for a in argv)


def reused_text(used):
    """The records a lookup used: commit, date, command, and whether they are of this tree."""
    return ", ".join(f"{r['commit'][:10]} {r['date']} ({r['command']}"
                     + ("" if note == "this tree" else f"; {note}") + ")" for r, note in used)


def narrowed(argv, missing, make):
    """The command that runs only what MISSING lacks: its faults, or the targets of make check
    that hold it (variables kept), or ARGV itself when coverage is missing or no such
    targets hold all of it."""
    goals, variables = parse(argv)
    keep = [a for a in argv[1:] if VARIABLE.match(a) and not a.startswith(("FAULTS=", "COVERAGE_"))]
    if any(m.startswith("coverage") for m in missing):
        return argv
    faults = sorted(m[len("fault:"):] for m in missing if m.startswith("fault:"))
    if goals == ["mutants"] and len(faults) == len(missing):
        return [argv[0], "mutants", "FAULTS=" + ",".join(faults), *keep]
    picked = [u for u in make.units if make.built([u]) & missing]
    if faults or not picked or missing - set().union(*(make.built([u]) for u in picked)):
        return argv
    return [argv[0], *picked, *keep]


# What an enclosing make (make once, make tier) passes down; the command's own make sets
# them again from its command line, so the run is the one its record describes.
INHERITED = ("MAKEFLAGS", "MAKELEVEL", "MFLAGS", "MAKEOVERRIDES", "GFORTH", "LEANEXPORT", "LEANFORTH_LEAN",
             "LEANFORTH_LEAN_CACHE", "LEANFORTH_LEAN_CACHE_DIR")


def make_env():
    return {k: v for k, v in os.environ.items() if k not in INHERITED}


def record(argv, log=None, nice=None, make=None):
    """Run ARGV; on exit 0 with the tree unchanged, write its record. Returns the status."""
    goals, variables = parse(argv)
    problems = dirty()
    if problems:
        raise Refused("the worktree differs from HEAD's tree (commit first, or run make itself): "
                      + "; ".join(problems[:5]))
    chain = toolchain(variables)
    covers = sorted((make or Make()).covers(goals, variables))
    before, commit = tree(), git("rev-parse", "HEAD")
    branch = git("rev-parse", "--abbrev-ref", "HEAD")
    started, date = time.monotonic(), now()
    command = ["nice", "-n", str(nice), *argv] if nice is not None else argv
    print(f"tested-tree: running {shown(argv)}", flush=True)
    if log:
        with open(log, "w", encoding="utf-8") as stream:
            status = subprocess.run(command, env=make_env(), stdin=subprocess.DEVNULL, stdout=stream,
                                    stderr=subprocess.STDOUT).returncode
    else:
        status = subprocess.run(command, env=make_env(), stdin=subprocess.DEVNULL).returncode
    seconds = round(time.monotonic() - started, 1)
    if status != 0:
        print(f"tested-tree: {shown(argv)} exited {status} after {seconds:.0f} s; nothing recorded")
        return status
    if tree() != before or dirty():
        raise Refused("the tree changed during the run; nothing recorded")
    entry = {"version": VERSION, "tree": before, "suite": " ".join(goals), "variables": variables,
             "gforth": chain["gforth"], "lean": chain["lean"], "lean_cache": chain["lean_cache"],
             "commit": commit, "branch": branch, "exit": 0, "date": date, "seconds": seconds,
             "command": shown(argv), "covers": covers}
    write_record(entry)
    print(f"tested-tree: passed in {seconds:.0f} s; recorded for tree {before[:12]} (commit {commit[:10]})")
    return 0


def once(argv, log=None, nice=None):
    make = Make()
    missing, used, _ = lookup(argv, make)
    if not missing and not dirty():
        print(f"tested-tree: {shown(argv)} already passed: {reused_text(used)}")
        return 0
    if used:
        print(f"tested-tree: reused {reused_text(used)}; running the rest")
        argv = narrowed(argv, missing, make)
    return record(argv, log, nice, make)


# --- the tier runner -------------------------------------------------------------------

def daily_needs():
    """{suite name: ( record -- flag )}: the suites of a complete daily run, with this toolchain."""
    chain = toolchain({})
    engines = {}
    for engine in test_tier.ENGINES:
        try:
            engines[engine] = toolchain({"GFORTH": engine_gforth(engine)})["gforth"]
        except Refused:
            engines[engine] = None
    return {
        "make coverage-check": lambda r: r["suite"] == "coverage-check" and r["gforth"] == chain["gforth"],
        "make test-unit on gforth-fast": lambda r: r["suite"] == "test-unit" and r["gforth"] == engines["fast"],
        "make check-rest with LEAN_CACHE=0": lambda r: r["suite"] in ("check-rest", "check")
        and r["gforth"] == chain["gforth"] and r["lean_cache"] in ("0", "verify"),
        "make test-unit on Gforth 0.7.3": lambda r: r["suite"] in ("test-unit", "test")
        and r["gforth"] == engines["073"],
    }, chain["lean"]


def daily_runs(records):
    """{tree: (date, commit) of its complete daily run, or the needs it lacks as a list}. A run
    with a variable that changes what it tests (FAULTS=, COVERAGE_FILES=, ...) never counts."""
    needs, lean = daily_needs()
    trees = {}
    for r in records:
        if r.get("lean") == lean and all(k in NEUTRAL - NARROWING for k in (r.get("variables") or {})):
            trees.setdefault(r["tree"], []).append(r)
    out = {}
    for name, rows in trees.items():
        found = {need: max((r for r in rows if ok(r)), key=lambda r: r["date"], default=None)
                 for need, ok in needs.items()}
        missing = [need for need, r in found.items() if r is None]
        last = max((r for r in found.values() if r), key=lambda r: r["date"], default=None)
        out[name] = missing if missing else (last["date"], last["commit"])
    return out


def daily_missing_here(records):
    """The suites of a daily run HEAD's tree lacks ([] when it has a complete one)."""
    found = daily_runs(records).get(tree())
    return list(daily_needs()[0]) if found is None else (found if isinstance(found, list) else [])


def daily_status(warn_hours):
    """Print the newest complete daily run and its age; warn (never fail) when it is missing or
    older than WARN_HOURS. Returns 0."""
    runs = [v for v in daily_runs(load_records()).values() if isinstance(v, tuple)]
    if not runs:
        print("daily run: none recorded; run make daily (without the Lean cache, Gforth 0.7.3 included)"
              + ("\nwarning: no daily run recorded" if warn_hours is not None else ""))
        return 0
    date, commit = max(runs)
    fmt = "%Y-%m-%d %H:%M:%S"
    hours = (datetime.datetime.strptime(now(), fmt) - datetime.datetime.strptime(date, fmt)).total_seconds() / 3600
    print(f"daily run: last complete {date} (commit {commit[:10]}), {hours:.0f} hours ago")
    if warn_hours is not None and hours > warn_hours:
        print(f"warning: the last daily run is older than {warn_hours:g} hours; run make daily")
    return 0


def tag_check():
    missing = daily_missing_here(load_records())
    if missing:
        print(f"tested-tree: no complete daily run for this tree ({tree()[:12]}): missing {', '.join(missing)}; "
              "run make daily before tagging")
        return 1
    print(f"tested-tree: this tree ({tree()[:12]}) has a complete daily run: it may be tagged")
    return 0


def run_daily(args):
    """The daily full run: the full tier's four suites on HEAD with LEAN_CACHE=0 and Gforth
    0.7.3, each run and recorded for this exact tree (records of other trees are not reused)."""
    os.chdir(git("rev-parse", "--show-toplevel"))
    if dirty() and not args.dry_run:
        raise Refused("the worktree differs from HEAD's tree: " + "; ".join(dirty()[:5]))
    missing = daily_missing_here(load_records())
    if not missing:
        print(f"tested-tree: daily run of this tree ({tree()[:12]}) already recorded")
        return 0
    status, lines = 0, []
    need_of = {"coverage-check": "make coverage-check", "testfast": "make test-unit on gforth-fast",
               "check-rest": "make check-rest with LEAN_CACHE=0", "test073": "make test-unit on Gforth 0.7.3"}
    for suite in test_tier.FULL_SUITES:
        need = need_of[suite["label"]]
        argv = suite_argv(suite, args.make, args.jobs, "0")
        if need not in missing:
            lines.append(f"{suite['label']} recorded for this tree")
        elif args.dry_run:
            lines.append(f"{suite['label']} would run: {shown(argv)}")
        else:
            log = f"{args.log_prefix}{suite['label']}.log" if args.log_prefix else None
            code = record(argv, log, args.nice)
            lines.append(f"{suite['label']} ran: exit {code}: {shown(argv)}")
            status = status or (1 if code else 0)
    print(f"daily run of tree {tree()[:12]} (LEAN_CACHE=0, Gforth 0.7.3 included)")
    for line in lines:
        print("  " + line)
    return status


def suite_argv(suite, make_program, jobs, cache):
    argv = [make_program, *suite["goals"], *(f"{k}={v}" for k, v in suite.get("vars", {}).items()),
            f"JOBS={jobs}", f"LEAN_CACHE={cache}"]
    return argv + ([f"GFORTH={engine_gforth(suite['engine'])}"] if suite.get("engine") else [])


def run_tier(args):
    os.chdir(git("rev-parse", "--show-toplevel"))
    problems = dirty()
    if problems and not args.dry_run:
        raise Refused("the worktree differs from HEAD's tree: " + "; ".join(problems[:5]))
    merge_base, changed = test_tier.changed_files(args.base)
    result = test_tier.plan(changed, merge_base, args.full)
    cache, notes = args.lean_cache, []
    dropped = [] if args.with_073 else [s["label"] for s in result["suites"] if s.get("engine") == "073"]
    result["suites"] = [s for s in result["suites"] if s["label"] not in dropped]
    print(test_tier.describe(result))
    for note in notes:
        print(note)
    make, lines, status, tree_hash = Make(), [], 0, tree()
    for suite in result["suites"]:
        argv = suite_argv(suite, args.make, args.jobs, cache)
        label = suite["label"]
        try:
            missing, used, _ = lookup(argv, make)
            if not missing:
                lines.append(f"{label} reused: {reused_text(used)}")
                continue
            argv = narrowed(argv, missing, make) if used else argv
            rest = f"; the rest reused: {reused_text(used)}" if used else ""
            if args.dry_run:
                lines.append(f"{label} would run: {shown(argv)}{rest}")
                continue
            started = time.monotonic()
            log = f"{args.log_prefix}{label}.log" if args.log_prefix else None
            code = record(argv, log, args.nice, make)
            lines.append(f"{label} ran: exit {code}, {time.monotonic() - started:.0f} s: {shown(argv)}{rest}")
        except Refused as error:
            code = 3
            lines.append(f"{label} refused: {error}")
        status = status or (1 if code else 0)
    labels = {s["label"] for s in result["suites"]}
    skipped = [s["label"] for s in test_tier.FULL_SUITES if s["label"] not in labels]
    skipped = [label for label in skipped if label not in dropped]
    if skipped and result["tier"] != "full":
        lines.append(f"not run (tier {result['tier']} does not reach them): {', '.join(skipped)}")
    if dropped:
        lines.append(f"not run on a branch (Gforth 0.7.3 runs at the push and in the daily run): "
                     f"{', '.join(dropped)}")
    if not args.no_progress:
        code = subprocess.run([sys.executable, os.path.join(HERE, "check-progress.py"), args.base]).returncode
        lines.append(f"progress check exit {code}")
        status = status or (1 if code else 0)
    head = f"tier {result['tier']} of {args.base}...HEAD (tree {tree_hash[:12]})" + "".join(f"; {n}" for n in notes)
    print(head)
    for line in lines:
        print("  " + line)
    if args.summary:
        with open(args.summary, "w", encoding="utf-8") as stream:
            stream.write("; ".join([head] + lines) + "\n")
    return status


def list_records(show_all):
    here = None if show_all else tree()
    for r in load_records():
        if here is None or r.get("tree") == here:
            print(f"{r['date']} {r['tree'][:12]} {r['commit'][:10]} {r['suite']} | {r['gforth']} | "
                  f"LEAN_CACHE={r['lean_cache']} | {r['seconds']:.0f} s | {r['command']}")
    return 0


def main(argv=None):
    argv = sys.argv[1:] if argv is None else argv
    command = argv[argv.index("--") + 1:] if "--" in argv else []
    options = argv[:argv.index("--")] if "--" in argv else argv
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("action", choices=("once", "record", "lookup", "list", "tier", "daily", "daily-status",
                                           "tag-check"))
    parser.add_argument("--all", action="store_true")
    parser.add_argument("--base", default="main")
    parser.add_argument("--full", action="store_true")
    parser.add_argument("--with-073", action="store_true")
    parser.add_argument("--warn-hours", type=float)
    parser.add_argument("--lean-cache", default="1", choices=sorted(STRONGER))
    parser.add_argument("--jobs", default="8")
    parser.add_argument("--nice", type=int)
    parser.add_argument("--make", default="make")
    parser.add_argument("--log-prefix")
    parser.add_argument("--summary")
    parser.add_argument("--no-progress", action="store_true")
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args(options)
    try:
        if args.action == "list":
            return list_records(args.all)
        if args.action == "tier":
            return run_tier(args)
        if args.action == "daily":
            return run_daily(args)
        os.chdir(git("rev-parse", "--show-toplevel"))
        if args.action == "daily-status":
            return daily_status(args.warn_hours)
        if args.action == "tag-check":
            return tag_check()
        if args.action == "lookup":
            missing, used, _ = lookup(command)
            print(f"tested-tree: covered by {reused_text(used)}" if not missing
                  else f"tested-tree: not covered on this tree: {' '.join(sorted(missing)[:8])}")
            return 0 if not missing else 1
        return (once if args.action == "once" else record)(command)
    except Usage as error:
        print(f"tested-tree: {error}", file=sys.stderr)
        return 2
    except Refused as error:
        print(f"tested-tree: refused: {error}", file=sys.stderr)
        return 3


if __name__ == "__main__":
    sys.exit(main())
