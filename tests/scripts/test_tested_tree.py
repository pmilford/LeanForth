#!/usr/bin/env python3
"""Tests of scripts/tested-tree.py and scripts/push.sh's choices (plan 9.4.6), on throw-away
repositories with stub toolchains (tests/scripts/tier_fixture.py) and a temporary records
folder (LF_TESTED_DIR): a pass recorded and reused; a failed run, a dirty worktree and a
tree changed during the run record nothing; another Gforth, Lean or weaker cache mode
misses; what make check and make coverage-check stand for; the tier runner reusing,
reducing and running; the daily full run; push.sh's dry run, its refusals, a push to a
fake remote and its record of what ran and what was reused."""
import json
import pathlib
import shutil
import subprocess
import sys
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import tier_fixture  # noqa: E402

ROOT = tier_fixture.ROOT
TODAY = tier_fixture.TODAY


class Base(unittest.TestCase):
    def setUp(self):
        self.repo = tier_fixture.Repo()

    def tearDown(self):
        self.repo.close()

    def records_tool(self, *args, **extra):
        return self.repo.script("tested-tree.py", *args, **extra)

    def records(self):
        folder = self.repo.records
        return [json.loads(p.read_text()) for p in sorted(folder.glob("*.json"))] if folder.exists() else []

    def assertRan(self, run, code=0):
        self.assertEqual(run.returncode, code, run.stdout + run.stderr)
        return run.stdout


class Records(Base):
    def test_record_then_lookup_and_once_reuse(self):
        self.assertRan(self.records_tool("record", "--", "make", "test-lib", "JOBS=2"))
        [record] = self.records()
        self.assertEqual(record["tree"], self.repo.git("rev-parse", "HEAD^{tree}"))
        self.assertEqual(record["commit"], self.repo.git("rev-parse", "HEAD"))
        self.assertEqual((record["suite"], record["exit"], record["gforth"], record["lean_cache"]),
                         ("test-lib", 0, "gforth 1.0.0 stub", "1"))
        self.assertEqual(record["lean"], "Lean (version 4.35.0, stub)")
        self.assertEqual(record["date"], f"{TODAY} 12:00:00")
        self.assertEqual(record["command"], "make test-lib JOBS=2")
        self.assertEqual(record["covers"], ["test-lib"])
        self.assertEqual(self.repo.logged(), ["gforth10 tests/lib/a.fs"])
        self.assertIn("covered by", self.assertRan(self.records_tool("lookup", "--", "make", "test-lib")))
        out = self.assertRan(self.records_tool("once", "--", "make", "test-lib", "JOBS=8"))
        self.assertIn("already passed: ", out)
        self.assertNotIn("changes since", out)
        self.assertEqual(len(self.repo.logged()), 1, "once ran the suite again")
        self.assertIn("test-lib", self.assertRan(self.records_tool("list")))

    def test_once_runs_when_missing(self):
        self.assertRan(self.records_tool("once", "--", "make", "test-lib"))
        self.assertEqual(len(self.records()), 1)
        self.assertEqual(len(self.repo.logged()), 1)

    def test_failed_run_writes_nothing(self):
        run = self.records_tool("record", "--", "make", "test-lib", STUB_FAIL_ON="tests/lib")
        self.assertNotEqual(run.returncode, 0)
        self.assertIn("nothing recorded", run.stdout)
        self.assertEqual(self.records(), [])
        self.assertEqual(self.assertRan(self.records_tool("lookup", "--", "make", "test-lib"), 1).count("not covered"), 1)

    def test_dirty_worktree_refused_before_running(self):
        self.repo.write("./docs/A.md", "# dirty\n")
        run = self.records_tool("record", "--", "make", "test-lib")
        self.assertEqual(run.returncode, 3, run.stderr)
        self.assertIn("differs from HEAD's tree", run.stderr)
        self.assertEqual((self.records(), self.repo.logged()), ([], []))

    def test_new_file_where_the_suites_look_refused(self):
        self.repo.write("tests/lib/new.fs", "\\ new\n")
        self.assertEqual(self.records_tool("once", "--", "make", "test-lib").returncode, 3)
        self.repo.remove("tests/lib/new.fs")
        self.repo.write("scratch/notes.txt", "elsewhere\n")
        self.assertRan(self.records_tool("once", "--", "make", "test-lib"))

    def test_tree_changed_during_the_run(self):
        run = self.records_tool("record", "--", "make", "sneaky")
        self.assertEqual(run.returncode, 3, run.stdout + run.stderr)
        self.assertIn("the tree changed during the run", run.stderr)
        self.assertEqual(self.records(), [])

    def test_same_tree_hits_full_change_misses(self):
        self.assertRan(self.records_tool("record", "--", "make", "test-lib"))
        self.repo.commit("an empty commit keeps the tree")
        self.assertIn("(make test-lib)", self.assertRan(self.records_tool("lookup", "--", "make", "test-lib")))
        self.repo.write("src/lib/used.fs", ": used 2 ;\n")
        self.repo.commit("a change src/main.fs loads: the full tier")
        self.assertRan(self.records_tool("lookup", "--", "make", "test-lib"), 1)

    def test_earlier_commit_stands_for_what_the_change_cannot_reach(self):
        self.assertRan(self.records_tool("record", "--", "make", "check"))
        self.repo.write("./docs/A.md", "# a documentation commit\n")
        self.repo.commit("docs")
        out = self.assertRan(self.records_tool("lookup", "--", "make", "test-lib", "reference-core"))
        self.assertIn("changes since are tier docs", out)
        self.assertIn("not covered on this tree: check-docs",
                      self.assertRan(self.records_tool("lookup", "--", "make", "check"), 1))
        # once runs only what the change reaches, then the whole of make check is covered.
        out = self.assertRan(self.records_tool("once", "--", "make", "check"))
        self.assertIn("running make check-docs", out)
        self.assertEqual(self.repo.logged()[-1], "check-docs")
        self.assertRan(self.records_tool("lookup", "--", "make", "check"))

    def test_earlier_commit_and_a_library_change(self):
        self.assertRan(self.records_tool("record", "--", "make", "coverage-check"))
        self.assertRan(self.records_tool("record", "--", "make", "mutants"))
        self.repo.write("src/lib/free.fs", ": free-word 9 ;\n")
        self.repo.commit("library")
        missing = self.assertRan(self.records_tool("lookup", "--", "make", "coverage-check"), 1)
        self.assertIn("coverage", missing, "a library change reaches the coverage ratchet")
        self.assertRan(self.records_tool("lookup", "--", "make", "test-core"))
        self.assertRan(self.records_tool("lookup", "--", "make", "test-lib"), 1)
        self.assertRan(self.records_tool("lookup", "--", "make", "mutants", "FAULTS=core-one"))
        self.assertRan(self.records_tool("lookup", "--", "make", "mutants", "FAULTS=free-one"), 1)

    def test_record_of_another_branch_is_not_used(self):
        self.repo.git("checkout", "-q", "-b", "other")
        self.repo.write("./docs/A.md", "# other branch\n")
        self.repo.commit("other")
        self.assertRan(self.records_tool("record", "--", "make", "test-lib"))
        self.repo.git("checkout", "-q", "main")
        self.repo.write("README.md", "# main moves on\n")
        self.repo.commit("main")
        self.assertRan(self.records_tool("lookup", "--", "make", "test-lib"), 1)

    def test_toolchain_change_misses(self):
        self.assertRan(self.records_tool("record", "--", "make", "reference-core"))
        self.assertRan(self.records_tool("lookup", "--", "make", "reference-core"))
        self.assertRan(self.records_tool("lookup", "--", "make", "reference-core", STUB_GFORTH_VERSION="gforth 1.0.1"), 1)
        self.assertRan(self.records_tool("lookup", "--", "make", "reference-core",
                                   STUB_LEAN_VERSION="Lean (version 4.36.0)"), 1)
        gforth073 = str(self.repo.path / ".tools/gforth073")
        self.assertRan(self.records_tool("lookup", "--", "make", "reference-core", f"GFORTH={gforth073}"), 1)

    def test_cache_modes(self):
        self.assertRan(self.records_tool("record", "--", "make", "reference-core", "LEAN_CACHE=1"))
        self.assertRan(self.records_tool("lookup", "--", "make", "reference-core", "LEAN_CACHE=0"), 1)
        self.assertRan(self.records_tool("record", "--", "make", "reference-core", "LEAN_CACHE=0"))
        self.assertRan(self.records_tool("lookup", "--", "make", "reference-core", "LEAN_CACHE=0"))
        self.assertRan(self.records_tool("lookup", "--", "make", "reference-core", "LEAN_CACHE=1"))
        self.assertRan(self.records_tool("lookup", "--", "make", "reference-core", "LEAN_CACHE=verify"), 1)

    def test_make_test_targets_run_no_lean(self):
        self.assertRan(self.records_tool("record", "--", "make", "test-lib", "LEAN_CACHE=1"))
        self.assertRan(self.records_tool("lookup", "--", "make", "test-lib", "LEAN_CACHE=0"))

    def test_check_stands_for_its_parts(self):
        self.assertRan(self.records_tool("record", "--", "make", "check"))
        for goals in (["test-lib"], ["check-rest"], ["test"], ["test-front", "reference-front"]):
            self.assertRan(self.records_tool("lookup", "--", "make", *goals))
        self.assertRan(self.records_tool("lookup", "--", "make", "coverage-check"), 1)

    def test_coverage_check_stands_for_make_test_but_the_engine_targets(self):
        self.assertRan(self.records_tool("record", "--", "make", "coverage-check"))
        self.assertRan(self.records_tool("lookup", "--", "make", "test-lib", "test-core"))
        self.assertRan(self.records_tool("lookup", "--", "make", "test-cli"), 1)
        self.assertRan(self.records_tool("lookup", "--", "make", "test"), 1)
        self.assertRan(self.records_tool("lookup", "--", "make", "coverage-focus", "COVERAGE_FILES=src/lib/free.fs",
                                   "COVERAGE_TARGETS=test-lib"))
        self.assertRan(self.records_tool("lookup", "--", "make", "check-rest"), 1)

    def test_faults(self):
        self.assertRan(self.records_tool("record", "--", "make", "mutants", "FAULTS=free-one,core-one"))
        self.assertRan(self.records_tool("lookup", "--", "make", "mutants", "FAULTS=core-one"))
        self.assertRan(self.records_tool("lookup", "--", "make", "mutants", "FAULTS=alone-one"), 1)
        self.assertRan(self.records_tool("lookup", "--", "make", "mutants"), 1)

    def test_other_variables_stand_only_for_themselves(self):
        self.assertRan(self.records_tool("record", "--", "make", "test-lib", "EXPORT=x.ndjson"))
        self.assertRan(self.records_tool("lookup", "--", "make", "test-lib"), 1)
        self.assertRan(self.records_tool("lookup", "--", "make", "test-lib", "EXPORT=x.ndjson"))

    def test_usage_errors(self):
        for argv in (["make", "-k", "test-lib"], ["make", "-n", "test-lib"], ["make", "-i", "check"],
                     ["bash", "-c", "true"], ["make", "JOBS=2"], []):
            with self.subTest(argv=argv):
                self.assertEqual(self.records_tool("record", "--", *argv).returncode, 2)
        self.assertEqual(self.records(), [])

    def test_missing_gforth_refused(self):
        run = self.records_tool("record", "--", "make", "test-lib", "GFORTH=/no/such/gforth")
        self.assertEqual(run.returncode, 3)
        self.assertIn("cannot read the version", run.stderr)


class Tier(Base):
    def tier(self, *extra, **env):
        return self.records_tool("tier", "--base", "base", "--no-progress", "--jobs", "2", *extra, **env)

    def test_runs_then_reuses(self):
        self.repo.write("./docs/A.md", "# docs\n")
        self.repo.commit("docs")
        out = self.assertRan(self.tier("--dry-run"))
        self.assertIn("targets would run: make check-docs JOBS=2 LEAN_CACHE=1", out)
        self.assertEqual((self.records(), self.repo.logged()), ([], []))
        out = self.assertRan(self.tier())
        self.assertIn("targets ran: exit 0", out)
        self.assertIn("not run (tier docs does not reach them): coverage-check, testfast, check-rest, test073", out)
        self.assertEqual(self.repo.logged(), ["check-docs"])
        out = self.assertRan(self.tier())
        self.assertIn("targets reused: ", out)
        self.assertEqual(self.repo.logged(), ["check-docs"])

    def test_library_tier_runs_each_suite(self):
        self.repo.write("src/lib/free.fs", ": free-word 1 ;\n")
        self.repo.commit("library")
        summary = self.repo.path.parent / "summary.txt"
        self.assertRan(self.tier("--with-073", "--summary", str(summary)))
        log = self.repo.logged()
        self.assertIn("gforth10 coverage-focus src/lib/free.fs over smoke test-lib test-front", log)
        self.assertIn("gforth073 tests/lib/a.fs", log)
        self.assertIn("gforthfast tests/lib/a.fs", log)
        self.assertIn("gforth10 mutants free-one,alone-one", log)
        self.assertNotIn("gforth10 tests/lib/a.fs", log, "the instrumented run stands for the plain one")
        self.assertIn("check-portable-forth", log)
        line = summary.read_text()
        self.assertIn("tier library of base...HEAD", line)
        self.assertIn("coverage-focus ran: exit 0", line)
        self.assertEqual(len(line.splitlines()), 1)

    def test_branch_tier_leaves_073_to_the_push(self):
        # Owner, 2026-11-14: Gforth 0.7.3 runs at the push and in the daily run, not on a branch.
        self.repo.write("src/lib/free.fs", ": free-word 1 ;\n")
        self.repo.commit("library")
        out = self.assertRan(self.tier())
        self.assertNotIn("gforth073", " ".join(self.repo.logged()))
        self.assertIn("gforthfast tests/lib/a.fs", self.repo.logged(), "gforth-fast runs on a branch")
        self.assertIn("not run on a branch (Gforth 0.7.3 runs at the push and in the daily run): targets073", out)
        self.assertNotIn("targets073 ran", out)
        out = self.assertRan(self.tier("--with-073"))
        self.assertIn("targets073 ran: exit 0", out)
        self.assertIn("gforth073 tests/lib/a.fs", self.repo.logged())

    def test_partly_covered_suite_runs_the_rest(self):
        self.repo.write("tests/lib/a.fs", "require ../../src/lib/free.fs\n\\ more\n")
        self.repo.commit("a test")
        self.assertRan(self.records_tool("record", "--", "make", "mutants", "FAULTS=free-one"))
        out = self.assertRan(self.tier())
        self.assertIn("faults reused", out)

    def test_failure_fails_the_tier_and_records_nothing_for_it(self):
        self.repo.write("tests/lib/a.fs", "require ../../src/lib/free.fs\n\\ more\n")
        self.repo.commit("a test")
        out = self.assertRan(self.tier(STUB_FAIL_ON="mutants"), 1)
        self.assertIn("faults ran: exit 2", out)
        self.assertFalse(any(r["suite"] == "mutants" for r in self.records()))

    def test_dirty_tree_refused(self):
        self.repo.write("./docs/A.md", "# dirty\n")
        self.assertEqual(self.tier().returncode, 3)

    def daily(self, *suites):
        for argv in suites:
            self.assertRan(self.records_tool("record", "--", "make", *argv))

    def fast(self):
        return str(self.repo.path / ".tools/gforth/bin/gforth-fast")

    def test_daily_command_runs_the_full_tier_without_the_cache(self):
        """Owner, 2026-11-17: the daily full run is its own command, never forced by a tier."""
        self.repo.write("./docs/A.md", "# docs\n")
        self.repo.commit("docs")
        out = self.assertRan(self.tier("--with-073", "--dry-run"))
        self.assertIn("tier docs", out)
        self.assertNotIn("LEAN_CACHE=0", out)
        out = self.assertRan(self.records_tool("daily", "--jobs", "2", "--dry-run"))
        for text in ("coverage-check would run: make coverage-check JOBS=2 LEAN_CACHE=0",
                     "testfast would run: make test-unit JOBS=2 LEAN_CACHE=0 GFORTH=",
                     "check-rest would run: make check-rest JOBS=2 LEAN_CACHE=0",
                     "test073 would run: make test-unit JOBS=2 LEAN_CACHE=0 GFORTH="):
            self.assertIn(text, out)
        self.assertEqual(self.records(), [])
        self.assertRan(self.records_tool("daily", "--jobs", "2"))
        self.assertEqual(sorted((r["suite"], r["lean_cache"]) for r in self.records()),
                         [("check-rest", "0"), ("coverage-check", "0"), ("test-unit", "0"), ("test-unit", "0")])
        self.assertIn("already recorded", self.assertRan(self.records_tool("daily", "--jobs", "2")))

    def test_daily_run_needs_every_suite_without_narrowing(self):
        gforth073 = str(self.repo.path / ".tools/gforth073")
        self.daily(["coverage-check"], ["test-unit", f"GFORTH={gforth073}"], ["test-unit", f"GFORTH={self.fast()}"],
                   ["check-rest", "LEAN_CACHE=1"], ["check-rest", "LEAN_CACHE=0", "FAULTS=free-one"])
        out = self.assertRan(self.records_tool("tag-check"), 1)
        self.assertIn("missing make check-rest with LEAN_CACHE=0", out)
        self.daily(["check", "LEAN_CACHE=0"])
        self.assertIn("may be tagged", self.assertRan(self.records_tool("tag-check")))

    def test_tag_needs_a_daily_run_of_its_exact_tree(self):
        self.assertIn("no complete daily run", self.assertRan(self.records_tool("tag-check"), 1))
        self.assertRan(self.records_tool("daily", "--jobs", "2"))
        self.assertRan(self.records_tool("tag-check"))
        self.repo.write("./docs/A.md", "# a documentation commit after the daily run\n")
        self.repo.commit("docs")
        self.assertIn("no complete daily run", self.assertRan(self.records_tool("tag-check"), 1),
                      "a daily run of an earlier tree does not let this one be tagged")

    def test_daily_status_and_its_warning(self):
        out = self.assertRan(self.records_tool("daily-status", "--warn-hours", "36"))
        self.assertIn("daily run: none recorded", out)
        self.assertIn("warning: no daily run recorded", out)
        self.assertRan(self.records_tool("daily", "--jobs", "2", LF_TESTED_NOW="2026-11-11 08:00:00"))
        out = self.assertRan(self.records_tool("daily-status", "--warn-hours", "36"))
        self.assertIn("daily run: last complete 2026-11-11 08:00:00", out)
        self.assertIn("52 hours ago", out)
        self.assertIn("warning: the last daily run is older than 36 hours", out)
        out = self.assertRan(self.records_tool("daily-status", "--warn-hours", "36",
                                               LF_TESTED_NOW="2026-11-12 08:00:00"))
        self.assertIn("24 hours ago", out)
        self.assertNotIn("warning", out)

    def test_untracked_root_file_makes_the_tree_dirty(self):
        self.repo.write("lean-toolchain", "leanprover/lean4:v4.35.0\n")
        self.assertEqual(self.tier().returncode, 3)

    def test_full_tier_after_a_documentation_commit(self):
        self.repo.write("Makefile", self.repo.path.joinpath("Makefile").read_text() + "\n")
        self.repo.commit("Makefile")
        gforth073 = str(self.repo.path / ".tools/gforth073")
        for argv in (["coverage-check"], ["check-rest"], ["test-unit", f"GFORTH={gforth073}"],
                     ["test-unit", f"GFORTH={self.fast()}"]):
            self.assertRan(self.records_tool("record", "--", "make", *argv))
        self.repo.write("./docs/A.md", "# the review log, after the merge\n")
        self.repo.commit("docs")
        before = len(self.repo.logged())
        out = self.assertRan(self.tier("--with-073"))
        self.assertIn("tier full", out)
        self.assertIn("coverage-check ran: exit 0", out)
        self.assertIn("make check-docs JOBS=2 LEAN_CACHE=1; the rest reused: ", out)
        self.assertIn("changes since are tier docs", out)
        self.assertIn("check-rest reused", out)
        # check-docs on Gforth 1.0 (instrumented), gforth-fast and 0.7.3: a unit test on each engine.
        self.assertEqual(self.repo.logged()[before:], ["check-docs", "check-docs", "check-docs"])
        self.assertIn("reused", self.assertRan(self.tier("--with-073")))

    def test_full_tier_reuses_a_make_check(self):
        self.repo.write("Makefile", self.repo.path.joinpath("Makefile").read_text() + "\n")
        self.repo.commit("Makefile")
        self.assertRan(self.records_tool("record", "--", "make", "check"))
        out = self.assertRan(self.tier("--with-073", "--dry-run"))
        self.assertIn("check-rest reused", out)
        self.assertIn("coverage-check would run", out)
        self.assertIn("testfast would run", out)
        self.assertIn("test073 would run", out)

    def test_fast_engine_records_are_its_own(self):
        """gforth-fast prints Gforth 1.0's version; its records name the engine."""
        self.assertRan(self.records_tool("record", "--", "make", "test-lib", f"GFORTH={self.fast()}"))
        [record] = self.records()
        self.assertEqual(record["gforth"], "gforth 1.0.0 stub (gforth-fast)")
        self.assertEqual(self.repo.logged(), ["gforthfast tests/lib/a.fs"])
        self.assertRan(self.records_tool("lookup", "--", "make", "test-lib"), 1)
        self.assertRan(self.records_tool("lookup", "--", "make", "test-lib", f"GFORTH={self.fast()}"))


class Push(Base):
    """scripts/push.sh in a copy of the fixture, with a bare repository as origin."""

    def setUp(self):
        super().setUp()
        self.remote = self.repo.path.parent / "remote.git"
        subprocess.run(["git", "init", "-q", "--bare", "-b", "main", str(self.remote)], check=True,
                       capture_output=True)
        for name in ("push.sh", "tested-tree.py", "test-tier.py", "changed-tests.py", "test-classes.py"):
            shutil.copy(ROOT / "scripts" / name, self.repo.path / "scripts" / name)
        self.repo.stub("scripts/check-progress.py", "import os, sys\nprint('progress stub')\n"
                       "sys.exit(int(os.environ.get('STUB_PROGRESS', '0')))\n")
        self.repo.stub("scripts/check-forth-quality.py", "print('quality stub')\n")
        self.repo.write(".claude/work/CPU_MODE", "day\n")
        self.repo.commit("scripts")
        self.repo.git("remote", "add", "origin", str(self.remote))
        self.repo.git("push", "-q", "origin", "main")
        self.repo.git("fetch", "-q", "origin")

    def push(self, *args, **env):
        return self.repo.run("bash", "scripts/push.sh", *args, **env)

    def remote_head(self):
        return subprocess.run(["git", "--git-dir", str(self.remote), "rev-parse", "main"], capture_output=True,
                              text=True, check=True).stdout.strip()

    def test_refusals(self):
        self.assertIn("nothing to push", self.assertRan(self.push()))
        self.repo.git("checkout", "-q", "-b", "work")
        self.repo.write("./docs/A.md", "# on a branch\n")
        self.repo.commit("branch")
        self.assertIn("not on main", self.assertRan(self.push(), 1))
        self.assertIn("tier docs", self.assertRan(self.push("--dry-run")), "a dry run works on a branch")
        self.repo.git("checkout", "-q", "main")
        self.repo.write("./docs/A.md", "# dirty\n")
        self.assertIn("uncommitted changes", self.assertRan(self.push(), 1))
        self.assertEqual(self.push("--bogus").returncode, 2)

    def code_change(self):
        self.repo.write("Makefile", self.repo.path.joinpath("Makefile").read_text() + "\n")
        self.repo.commit("Makefile")

    def test_docs_push_plans_only_the_docs_tier(self):
        """Owner, 2026-11-17: the first push of a day runs its own tier, no daily full run."""
        before = self.remote_head()
        self.repo.write("./docs/A.md", "# docs\n")
        self.repo.commit("docs")
        out = self.assertRan(self.push("--dry-run"))
        self.assertIn("tier docs", out)
        self.assertIn("targets would run: make check-docs JOBS=2 LEAN_CACHE=1", out)
        for text in ("coverage-check would run", "check-rest would run", "test073 would run", "LEAN_CACHE=0",
                     "tier full"):
            self.assertNotIn(text, out)
        self.assertIn("warning: no daily run recorded", out)
        self.assertEqual((self.remote_head(), self.records(), self.repo.logged()), (before, [], []))

    def test_code_push_keeps_the_cache(self):
        self.code_change()
        out = self.assertRan(self.push("--dry-run"))
        self.assertIn("tier full", out)
        for text in ("coverage-check would run: make coverage-check JOBS=2 LEAN_CACHE=1",
                     "testfast would run: make test-unit JOBS=2 LEAN_CACHE=1",
                     "check-rest would run: make check-rest JOBS=2 LEAN_CACHE=1",
                     "test073 would run: make test-unit JOBS=2 LEAN_CACHE=1"):
            self.assertIn(text, out)
        self.assertNotIn("LEAN_CACHE=0", out)

    def test_push_warns_of_a_stale_daily_run(self):
        self.assertRan(self.records_tool("daily", "--jobs", "2", LF_TESTED_NOW="2026-11-11 20:00:00"))
        self.repo.write("./docs/A.md", "# docs\n")
        self.repo.commit("docs")
        out = self.assertRan(self.push("--dry-run"))
        self.assertIn("daily run: last complete 2026-11-11 20:00:00", out)
        self.assertIn("warning: the last daily run is older than 36 hours", out)
        out = self.assertRan(self.push("--dry-run", LF_TESTED_NOW="2026-11-12 20:00:00"))
        self.assertIn("24 hours ago", out)
        self.assertNotIn("warning", out)

    def test_push_runs_records_and_reuses(self):
        self.repo.write("./docs/A.md", "# docs\n")
        self.repo.commit("docs")
        tested_head = self.repo.git("rev-parse", "HEAD")
        out = self.assertRan(self.push())
        self.assertEqual(self.remote_head(), self.repo.git("rev-parse", "HEAD"))
        self.assertEqual(self.repo.git("log", "-1", "--format=%s"), f"Record the local CI of {tested_head[:7]}")
        line = (self.repo.path / "docs/development/ci-results.log").read_text().splitlines()[-1]
        for text in ("progress 0; forth-quality 0; suites exit 0", "tier docs", "targets ran: exit 0",
                     "not run (tier docs does not reach them): coverage-check, testfast, check-rest, test073",
                     "daily run: none recorded", "gforth 1.0.0 stub"):
            self.assertIn(text, line)
        self.assertEqual([r["suite"] for r in self.records()], ["check-docs"])
        # A code change: its full tier, once, with the cache; the daily run stays its own command.
        self.code_change()
        tested_head = self.repo.git("rev-parse", "HEAD")
        self.assertRan(self.push())
        line = (self.repo.path / "docs/development/ci-results.log").read_text().splitlines()[-1]
        for text in ("tier full", "coverage-check ran: exit 0", "testfast ran: exit 0", "check-rest ran: exit 0",
                     "test073 ran: exit 0"):
            self.assertIn(text, line)
        self.assertNotIn("LEAN_CACHE=0", line)
        self.assertTrue((self.repo.path / f".claude/work/ci/{tested_head[:7]}-check-rest.log").exists())

    def test_failure_is_not_pushed(self):
        before = self.remote_head()
        self.code_change()
        out = self.assertRan(self.push(STUB_FAIL_ON="coverage-check"), 1)
        self.assertIn("coverage-check ran: exit 2", out)
        self.assertIn("not pushed", out)
        self.assertEqual(self.remote_head(), before)
        self.assertIn("not pushed", self.assertRan(self.push(STUB_PROGRESS="1"), 1))
        self.assertEqual(self.remote_head(), before)


if __name__ == "__main__":
    unittest.main()
