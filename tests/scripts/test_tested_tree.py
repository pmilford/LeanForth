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
        self.assertIn("not run (tier docs does not reach them): coverage-check, check-rest, test073", out)
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

    def test_daily_full_run(self):
        self.repo.write("./docs/A.md", "# docs\n")
        self.repo.commit("docs")
        out = self.assertRan(self.tier("--daily", "--with-073", "--dry-run"))
        self.assertIn("daily full run: none recorded today (2026-11-13)", out)
        self.assertIn("coverage-check would run: make coverage-check JOBS=2 LEAN_CACHE=0", out)
        self.assertIn("check-rest would run: make check-rest JOBS=2 LEAN_CACHE=0", out)
        self.assertIn("test073 would run: make test JOBS=2 LEAN_CACHE=0 GFORTH=", out)
        gforth073 = str(self.repo.path / ".tools/gforth073")
        self.daily(["coverage-check"], ["check-rest", "LEAN_CACHE=1"], ["test", f"GFORTH={gforth073}"])
        out = self.assertRan(self.tier("--daily", "--with-073", "--dry-run"))
        self.assertIn("of make check-rest with LEAN_CACHE=0", out, "a cached check-rest is no daily run")
        self.daily(["check", "LEAN_CACHE=0"])
        out = self.assertRan(self.tier("--daily", "--with-073", "--dry-run"))
        self.assertNotIn("daily full run", out)
        self.assertIn("tier docs", out)

    def test_daily_run_with_changing_variables_does_not_count(self):
        gforth073 = str(self.repo.path / ".tools/gforth073")
        self.daily(["coverage-check"], ["test", f"GFORTH={gforth073}"],
                   ["check-rest", "LEAN_CACHE=0", "FAULTS=free-one"])
        self.repo.write("./docs/A.md", "# docs\n")
        self.repo.commit("docs")
        out = self.assertRan(self.tier("--daily", "--dry-run"))
        self.assertIn("of make check-rest with LEAN_CACHE=0", out)

    def test_untracked_root_file_makes_the_tree_dirty(self):
        self.repo.write("lean-toolchain", "leanprover/lean4:v4.35.0\n")
        self.assertEqual(self.tier().returncode, 3)

    def test_daily_run_of_yesterday_does_not_count(self):
        gforth073 = str(self.repo.path / ".tools/gforth073")
        for argv in (["coverage-check"], ["check-rest", "LEAN_CACHE=0"], ["test", f"GFORTH={gforth073}"]):
            self.assertRan(self.records_tool("record", "--", "make", *argv, LF_TESTED_NOW="2026-11-12 23:59:00"))
        self.repo.write("./docs/A.md", "# docs\n")
        self.repo.commit("docs")
        self.assertIn("daily full run", self.assertRan(self.tier("--daily", "--dry-run")))

    def test_full_tier_after_a_documentation_commit(self):
        self.repo.write("Makefile", self.repo.path.joinpath("Makefile").read_text() + "\n")
        self.repo.commit("Makefile")
        gforth073 = str(self.repo.path / ".tools/gforth073")
        for argv in (["coverage-check"], ["check-rest"], ["test", f"GFORTH={gforth073}"]):
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
        self.assertEqual(self.repo.logged()[before:], ["check-docs", "check-docs"])
        self.assertIn("reused", self.assertRan(self.tier("--with-073")))

    def test_full_tier_reuses_a_make_check(self):
        self.repo.write("Makefile", self.repo.path.joinpath("Makefile").read_text() + "\n")
        self.repo.commit("Makefile")
        self.assertRan(self.records_tool("record", "--", "make", "check"))
        out = self.assertRan(self.tier("--with-073", "--dry-run"))
        self.assertIn("check-rest reused", out)
        self.assertIn("coverage-check would run", out)
        self.assertIn("test073 would run", out)


class Push(Base):
    """scripts/push.sh in a copy of the fixture, with a bare repository as origin."""

    def setUp(self):
        super().setUp()
        self.remote = self.repo.path.parent / "remote.git"
        subprocess.run(["git", "init", "-q", "--bare", "-b", "main", str(self.remote)], check=True,
                       capture_output=True)
        for name in ("push.sh", "tested-tree.py", "test-tier.py", "changed-tests.py"):
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
        self.assertIn("not on main", self.assertRan(self.push(), 1))
        self.repo.git("checkout", "-q", "main")
        self.repo.write("./docs/A.md", "# dirty\n")
        self.assertIn("uncommitted changes", self.assertRan(self.push(), 1))
        self.assertEqual(self.push("--bogus").returncode, 2)

    def test_dry_run_pushes_nothing(self):
        before = self.remote_head()
        self.repo.write("./docs/A.md", "# docs\n")
        self.repo.commit("docs")
        out = self.assertRan(self.push("--dry-run"))
        self.assertIn("daily full run", out)
        self.assertIn("would run", out)
        self.assertEqual((self.remote_head(), self.records(), self.repo.logged()), (before, [], []))

    def test_push_runs_records_and_reuses(self):
        self.repo.write("./docs/A.md", "# docs\n")
        self.repo.commit("docs")
        tested_head = self.repo.git("rev-parse", "HEAD")
        out = self.assertRan(self.push())
        self.assertIn("daily full run", out)
        self.assertEqual(self.remote_head(), self.repo.git("rev-parse", "HEAD"))
        self.assertEqual(self.repo.git("log", "-1", "--format=%s"), f"Record the local CI of {tested_head[:7]}")
        line = (self.repo.path / "docs/development/ci-results.log").read_text().splitlines()[-1]
        for text in ("progress 0; forth-quality 0; suites exit 0", "tier full", "coverage-check ran: exit 0",
                     "check-rest ran: exit 0", "LEAN_CACHE=0", "test073 ran: exit 0", "gforth 1.0.0 stub"):
            self.assertIn(text, line)
        self.assertEqual(sorted(r["suite"] for r in self.records()), ["check-rest", "coverage-check", "test"])
        self.assertTrue((self.repo.path / f".claude/work/ci/{tested_head[:7]}-check-rest.log").exists())
        # Today's full run is recorded: a documentation commit now runs its own tier only.
        self.repo.write("./docs/A.md", "# docs again\n")
        self.repo.commit("docs again")
        out = self.assertRan(self.push())
        self.assertNotIn("daily full run", out)
        line = (self.repo.path / "docs/development/ci-results.log").read_text().splitlines()[-1]
        self.assertIn("tier docs", line)
        self.assertIn("targets ran: exit 0", line)
        self.assertIn("not run (tier docs does not reach them): coverage-check, check-rest, test073", line)

    def test_failure_is_not_pushed(self):
        before = self.remote_head()
        self.repo.write("./docs/A.md", "# docs\n")
        self.repo.commit("docs")
        out = self.assertRan(self.push(STUB_FAIL_ON="coverage-check"), 1)
        self.assertIn("coverage-check ran: exit 2", out)
        self.assertIn("not pushed", out)
        self.assertEqual(self.remote_head(), before)
        self.assertIn("not pushed", self.assertRan(self.push(STUB_PROGRESS="1"), 1))
        self.assertEqual(self.remote_head(), before)


if __name__ == "__main__":
    unittest.main()
