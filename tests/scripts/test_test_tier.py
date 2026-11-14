#!/usr/bin/env python3
"""Tests of scripts/test-tier.py (plan 9.4.6): every tier, mixed ranges, a library that
becomes loaded by src/main.fs, deleted and renamed files, the Makefile and scripts, on
throw-away repositories (tests/scripts/tier_fixture.py); then the real Makefile's split of
make check and the real tree's classes."""
import importlib.util
import json
import os
import pathlib
import subprocess
import sys
import time
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import tier_fixture  # noqa: E402

ROOT = tier_fixture.ROOT
spec = importlib.util.spec_from_file_location("test_tier", ROOT / "scripts/test-tier.py")
tt = importlib.util.module_from_spec(spec)
spec.loader.exec_module(tt)


class Fixture(unittest.TestCase):
    """Each test changes a fresh copy of the fixture and asks for the tier of base...HEAD."""

    def setUp(self):
        self.repo = tier_fixture.Repo()

    def tearDown(self):
        self.repo.close()

    def tier(self, *extra):
        run = self.repo.script("test-tier.py", "--base", "base", "--json", *extra)
        self.assertEqual(run.returncode, 0, run.stderr)
        return json.loads(run.stdout)

    def change(self, files, message="change"):
        for name, text in files.items():
            self.repo.write(name, text)
        self.repo.commit(message)
        return self.tier()

    def labels(self, result):
        return [s["label"] for s in result["suites"]]

    def assertFull(self, result):
        self.assertEqual(result["tier"], "full")
        faults = ["faults"] if result["faults"] else []
        self.assertEqual(self.labels(result), ["coverage-check", "check-rest", "test073"] + faults)
        self.assertEqual([s["goals"] for s in result["suites"]][:3],
                         [["coverage-check"], ["check-rest"], ["test"]])


class Tiers(Fixture):
    def test_nothing_changed(self):
        result = self.tier()
        self.assertEqual((result["tier"], result["suites"]), ("none", []))

    def test_docs_only(self):
        result = self.change({"./docs/A.md": "# A, changed\n", "README.md": "# changed\n"})
        self.assertEqual(result["tier"], "docs")
        self.assertEqual(result["targets"], ["check-docs"])
        self.assertEqual((result["targets073"], result["faults"], result["coverage"]), ([], [], None))
        self.assertEqual(self.labels(result), ["targets"])

    def test_docs_a_test_reads(self):
        self.repo.write("tests/front/check_front.py", 'DATA = "./docs/A.md"\n')
        self.repo.commit("a test reads a page")
        self.repo.git("tag", "-f", "base")
        result = self.change({"./docs/A.md": "# A, changed\n"})
        self.assertEqual(result["tier"], "docs")
        self.assertEqual(result["targets"], ["check-docs", "reference-front"])

    def test_tests_only(self):
        result = self.change({"tests/lib/a.fs": "require ../../src/lib/free.fs\n\\ more\n"})
        self.assertEqual(result["tier"], "tests")
        self.assertEqual(result["targets"], ["test-lib"])
        self.assertEqual(result["targets073"], ["test-lib"])
        self.assertEqual(result["faults"], ["free-one"])
        # Every target of make test that loads the file, test-front through src/front/alone.fs.
        self.assertEqual(result["coverage"], {"kind": "focus", "files": ["src/lib/free.fs"],
                                              "targets": ["smoke", "test-lib", "test-front"]})
        self.assertEqual(self.labels(result), ["coverage-focus", "targets", "targets073", "faults"])

    def test_tests_that_drive_main_need_all_coverage(self):
        result = self.change({"tests/core/c.fs": "require ../../src/main.fs\n\\ more\n"})
        self.assertEqual(result["tier"], "tests")
        self.assertEqual(result["coverage"]["kind"], "all")
        self.assertEqual(self.labels(result)[0], "coverage-check")
        self.assertEqual(result["faults"], ["core-one"])

    def test_test_data(self):
        result = self.change({"tests/front/data.txt": "other data\n"})
        self.assertEqual(result["tier"], "tests")
        self.assertEqual(result["targets"], ["reference-front"])
        self.assertEqual(result["targets073"], [])

    def test_unused_test_file_takes_its_folder(self):
        result = self.change({"tests/lib/notes.txt": "notes\n"})
        self.assertEqual(result["tier"], "tests")
        self.assertEqual(result["targets"], ["test-lib"])

    def test_unused_test_folder_is_full(self):
        self.assertFull(self.change({"tests/new/x.fs": "\\ new\n"}))

    def test_coverage_baseline(self):
        result = self.change({"tests/coverage-baseline.json": '{"runs": 1}\n'})
        self.assertEqual(result["coverage"]["kind"], "all")

    def test_changed_fault_entry(self):
        text = tier_fixture.FAULTS.replace('reason = "stub"\n\n[[fault]]\nid = "core-one"',
                                           'reason = "changed"\n\n[[fault]]\nid = "core-one"')
        result = self.change({"tests/mutants/faults.toml": text})
        self.assertEqual(result["tier"], "tests")
        self.assertEqual(result["faults"], ["free-one"])

    def test_library_nothing_loads(self):
        result = self.change({"src/lib/free.fs": ": free-word 1 ;\n"})
        self.assertEqual(result["tier"], "library")
        self.assertEqual(result["targets"], ["check-portable-forth", "check-forth-quality", "smoke",
                                             "test-lib", "test-front"])
        self.assertEqual(result["targets073"], ["smoke", "test-lib", "test-front"])
        self.assertEqual(result["faults"], ["free-one", "alone-one"])
        self.assertEqual(result["coverage"], {"kind": "focus", "files": ["src/lib/free.fs"],
                                              "targets": ["smoke", "test-lib", "test-front"]})

    def test_library_main_loads(self):
        self.assertFull(self.change({"src/lib/used.fs": ": used 1 ;\n"}))

    def test_library_that_becomes_loaded(self):
        self.assertFull(self.change({"src/lib/free.fs": ": free-word 2 ;\n",
                                     "src/core/c.fs": "require ../lib/used.fs\nrequire ../lib/free.fs\n"}))

    def test_library_loaded_through_a_new_file(self):
        self.assertFull(self.change({"src/lib/new.fs": "require ./free.fs\n",
                                     "src/lib/used.fs": "require ./new.fs\n: used ;\n"}))

    def test_library_loaded_since_an_earlier_commit(self):
        self.repo.write("src/core/c.fs", "require ../lib/used.fs\nrequire ../lib/free.fs\n")
        self.repo.commit("main.fs now loads free.fs")
        self.repo.git("tag", "-f", "base")
        self.assertFull(self.change({"src/lib/free.fs": ": free-word 3 ;\n"}))

    def test_front_nothing_loads(self):
        result = self.change({"src/front/alone.fs": "require ../lib/free.fs\n: alone 1 ;\n"})
        self.assertEqual(result["tier"], "front")
        self.assertTrue({"test-front", "reference-front", "smoke"} <= set(result["targets"]))
        self.assertEqual(result["faults"], ["alone-one"])
        self.assertEqual(result["coverage"]["files"], ["src/front/alone.fs"])

    def test_front_main_loads(self):
        self.assertFull(self.change({"src/front/loaded.fs": ": loaded 1 ;\n"}))

    def test_full_files(self):
        for name in ("Makefile", "scripts/check.py", "bin/tool", "src/core/c.fs", "src/main.fs",
                     "src/program/p.fs", "schemas/x.json", ".github/ci.yml", "lean-toolchain"):
            with self.subTest(name=name):
                base = self.repo.git("rev-parse", "HEAD")
                path = self.repo.path / name
                old = path.read_text() if path.exists() else ""
                self.assertFull(self.change({name: old + "\n# changed\n"}))
                self.repo.git("reset", "-q", "--hard", base)

    def test_full_tier_runs_the_faults_whose_text_changed(self):
        """Plan 9.4.8j: the full tier runs the faults whose old text a change touched."""
        result = self.change({"src/core/c.fs": "require  ../lib/used.fs\n"})
        self.assertFull(result)
        self.assertEqual(result["faults"], ["core-one"])
        self.assertEqual(result["suites"][-1]["vars"], {"FAULTS": "core-one"})

    def test_full_tier_leaves_the_faults_of_untouched_text(self):
        self.change({"src/core/c.fs": "require ../lib/used.fs\n\\ 1\n\\ 2\n\\ 3\n\\ 4\n"})
        self.repo.git("tag", "-f", "base")
        result = self.change({"src/core/c.fs": "require ../lib/used.fs\n\\ 1\n\\ 2\n\\ 3\n\\ four\n"})
        self.assertFull(result)
        self.assertEqual(result["faults"], [])

    def test_full_tier_runs_the_changed_fault_entries(self):
        text = tier_fixture.FAULTS.replace('new = "eerf"', 'new = "eref"')
        result = self.change({"tests/mutants/faults.toml": text, "src/program/p.fs": ": p 1 ;\n"})
        self.assertFull(result)
        self.assertEqual(result["faults"], ["free-one"])

    def test_mixed_range_takes_the_largest(self):
        result = self.change({"./docs/A.md": "# B\n", "tests/lib/a.fs": "require ../../src/lib/free.fs\n\\ x\n",
                              "src/lib/free.fs": ": free-word 4 ;\n"})
        self.assertEqual(result["tier"], "library")
        self.assertIn("check-docs", result["targets"])
        self.assertIn("test-lib", result["targets"])
        self.assertFull(self.change({"src/core/c.fs": "require ../lib/used.fs\n\\ x\n"}))

    def test_deleted_library_main_loaded(self):
        self.repo.remove("src/lib/used.fs")
        self.assertFull(self.change({"src/core/c.fs": "\\ no library\n"}))

    def test_deleted_file_classified_by_the_base(self):
        self.repo.remove("src/lib/used.fs")
        self.repo.commit("delete")
        changed = [("D", "src/lib/used.fs")]
        cwd = os.getcwd()
        os.chdir(self.repo.path)
        try:
            result = tt.plan(changed, self.repo.git("rev-parse", "base"))
        finally:
            os.chdir(cwd)
        self.assertEqual(result["tier"], "full")

    def test_deleted_test_data(self):
        # Its users are known only from the base tree: the full tier (review B1).
        self.repo.remove("tests/front/data.txt")
        self.assertFull(self.change({}))

    def test_deleted_library_nothing_loads(self):
        # B1: a deleted library must not select only the source rules (the bigint case).
        self.repo.remove("src/lib/free.fs")
        self.assertFull(self.change({}))

    def test_deleted_test_needs_its_coverage(self):
        # B4: a deleted test that drove a loaded file is the full tier, coverage included.
        self.repo.remove("tests/core/c.fs")
        result = self.change({})
        self.assertFull(result)
        self.assertEqual(result["suites"][0]["goals"], ["coverage-check"])

    def test_renamed_test_the_makefile_no_longer_finds(self):
        self.repo.git("mv", "tests/lib/a.fs", "tests/lib/b.fs")
        self.assertFull(self.change({}))

    def test_renamed_document(self):
        self.repo.git("mv", "./docs/A.md", "./docs/B.md")
        result = self.change({})
        self.assertEqual(result["tier"], "docs")
        self.assertEqual(sorted(f["status"] for f in result["files"]), ["A", "D"])

    def test_uncommitted_and_untracked_count(self):
        self.repo.write("src/lib/used.fs", ": used 9 ;\n")
        self.assertFull(self.tier())
        self.repo.git("checkout", "src/lib/used.fs")
        self.repo.write("src/lib/fresh.fs", ": fresh ;\n")
        self.assertEqual(self.tier()["tier"], "library")

    def test_full_flag(self):
        self.repo.write("./docs/A.md", "# x\n")
        self.repo.commit("docs")
        self.assertFull(self.tier("--full"))

    def test_text_output(self):
        self.change({"src/lib/free.fs": ": free-word 5 ;\n"})
        run = self.repo.script("test-tier.py", "--base", "base")
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertIn("tier: library", run.stdout)
        self.assertIn("suite targets073 (Gforth 0.7.3): make smoke test-lib test-front", run.stdout)

    def test_bad_base(self):
        run = self.repo.script("test-tier.py", "--base", "no-such-ref")
        self.assertEqual(run.returncode, 2)
        self.assertIn("test-tier: git", run.stderr)


class Reaches(Fixture):
    """Run-time paths, sys.path imports and test helpers (review B2, B3)."""

    def setUp(self):
        files = dict(tier_fixture.FILES)
        files["Makefile"] = files["Makefile"].replace(
            "\t$(GFORTH) tests/core/c.fs\n", "\t$(GFORTH) tests/core/c.fs\n\tpython3 tests/core/lvl.py\n"
        ).replace("\t$(GFORTH) tests/cli/cli.fs\n", "\t$(GFORTH) tests/cli/cli.fs\n\tpython3 tests/cli/shared.py\n")
        files["tests/core/lvl.py"] = 'import sys\nsys.path.insert(0, "tests/support")\nimport preview\n'
        files["tests/support/preview.py"] = "X = 1\n"
        files["tests/support/tester.fs"] = ": t ;\n"
        files["tests/lib/a.fs"] = "require ../../src/lib/free.fs\nrequire ../support/tester.fs\n"
        files["tests/core/cases/x.ndjson"] = "{}\n"
        files["tests/cli/shared.py"] = 'P = ROOT / "tests" / "core" / "cases"\n'
        self.repo = tier_fixture.Repo(files)

    def test_python_import_through_sys_path(self):
        result = self.change({"tests/support/preview.py": "X = 2\n"})
        self.assertEqual(result["tier"], "tests")
        self.assertIn("test-core", result["targets"])

    def test_data_read_through_a_joined_path(self):
        result = self.change({"tests/core/cases/x.ndjson": "{}\n{}\n"})
        self.assertEqual(result["tier"], "tests")
        self.assertIn("test-cli", result["targets"])

    def test_data_found_by_a_glob_of_its_type(self):
        self.repo.write("tests/cli/shared.py", 'import pathlib\nL = pathlib.Path("tests").rglob("*.ndjson")\n')
        self.repo.commit("glob")
        result = self.change({"tests/core/cases/x.ndjson": "{}\n{}\n"})
        self.assertIn("test-cli", result["targets"])

    def test_test_helper_selects_the_faults_that_load_it(self):
        result = self.change({"tests/support/tester.fs": ": t 1 ;\n"})
        self.assertEqual(result["tier"], "tests")
        self.assertEqual(result["faults"], ["free-one"])


class Units(unittest.TestCase):
    def test_category(self):
        loaded = {"src/lib/used.fs"}
        cases = {"./docs/x.md": "docs", "src/README.md": "docs", ".claude/agents/a.md": "docs",
                 ".codex/agents/a.toml": "docs", "LICENSE": "docs", "tests/lib/x.fs": "tests",
                 "tests/x.json": "tests", "src/lib/used.fs": "full", "src/lib/free.fs": "library",
                 "src/front/x.fs": "front", "src/main.fs": "full", "src/kernel/x.fs": "full",
                 "src/core/x.fs": "full", "src/import/x.fs": "full", "src/cli/x.fs": "full",
                 "src/author/x.fs": "full", "src/lib/data.json": "full", "Makefile": "full",
                 "scripts/push.sh": "full", "bin/leanforth": "full", "something-new": "full"}
        for path, tier in cases.items():
            self.assertEqual(tt.category(os.path.normpath(path), loaded)[0], tier, path)

    def test_parse_database(self):
        text = ("# Files\n\n# Not a target:\nsrc/x.fs:\n\nall: a b | c\n#  recipe to execute (from 'M'):\n"
                "\techo\n\nslow: RUN := timeout 9\nslow:\n\ttrue\n\nagg: a\n\nV := 1 2\n")
        rules, recipes, variables = tt.parse_database(text)
        self.assertEqual(rules["all"], ["a", "b", "c"])
        self.assertNotIn("src/x.fs", rules)
        self.assertEqual(rules["slow"], [])
        self.assertEqual(recipes, {"all", "slow"})
        self.assertEqual(variables["V"], "1 2")
        self.assertEqual(tt.reach(["all"], rules), {"all", "a", "b", "c"})

    def test_forth_closure_follows_loads_only(self):
        files = {"m.fs": "require ./a.fs\n\\ include ./b.fs\n", "a.fs": "needs c.fs\n", "b.fs": "", "c.fs": "",
                 "d.fs": ""}
        found = tt.forth_closure(["m.fs"], files.get)
        self.assertEqual(found, {"m.fs", "a.fs", "b.fs", "c.fs"})


class RealTree(unittest.TestCase):
    """The project's own Makefile and tree (read only)."""

    @classmethod
    def setUpClass(cls):
        cwd = os.getcwd()
        os.chdir(ROOT)
        try:
            cls.rules, cls.recipes, cls.variables = tt.make_database()
            cls.loaded = tt.forth_closure([tt.MAIN], tt.read_worktree)
        finally:
            os.chdir(cwd)

    def built(self, goals):
        return tt.reach(goals, self.rules) & self.recipes

    def test_check_is_test_and_check_rest(self):
        self.assertEqual(self.built(["check"]), self.built(["test"]) | self.built(["check-rest"]))

    def test_check_rest_repeats_only_the_engine_targets(self):
        differs = self.variables["COVERAGE_ENGINE_DIFFERS"].split()
        self.assertEqual(differs, ["test-cli"])
        self.assertEqual(self.built(["test"]) & self.built(["check-rest"]), self.built(differs))

    def test_main_loads_the_checker(self):
        self.assertIn("src/kernel/check-declaration.fs", self.loaded)
        self.assertIn("src/cli/leanforth.fs", self.loaded)

    def plan_files(self, files):
        run = subprocess.run([sys.executable, str(ROOT / "scripts/test-tier.py"), "--json", "--files", *files],
                             cwd=ROOT, capture_output=True, text=True, env=tier_fixture.make_env())
        self.assertEqual(run.returncode, 0, run.stderr)
        return json.loads(run.stdout)

    def test_real_libraries(self):
        libraries = sorted(str(p.relative_to(ROOT)) for p in (ROOT / "src/lib").glob("*.fs"))
        free = [p for p in libraries if p not in self.loaded]
        loaded = [p for p in libraries if p in self.loaded]
        self.assertEqual(self.plan_files(loaded[:1])["tier"], "full")
        if free:
            started = time.monotonic()
            result = self.plan_files(free[:1])
            self.assertLess(time.monotonic() - started, 60, "the classifier became slow")
            self.assertEqual(result["tier"], "library")
            self.assertIn("smoke", result["targets"])

    def test_real_kernel_and_docs(self):
        self.assertEqual(self.plan_files(["src/kernel/check-declaration.fs"])["tier"], "full")
        self.assertEqual(self.plan_files(["docs/development/TEST_WORKFLOW_REVIEW.md"])["tier"], "docs")


if __name__ == "__main__":
    unittest.main()
