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
        """The full tier (owner, 2026-11-17): the changed files' coverage (if any), make test, make
        test-unit on gforth-fast, make check-rest, the faults; never Gforth 0.7.3 (make daily)."""
        self.assertEqual(result["tier"], "full")
        faults = ["faults"] if result["faults"] else []
        labels = [label for label in self.labels(result) if not label.startswith("coverage-")]
        self.assertEqual(labels, ["test", "testfast", "check-rest"] + faults)
        self.assertEqual([(s["goals"], s.get("engine")) for s in result["suites"] if s["label"] in labels[:3]],
                         [(["test"], None), (["test-unit"], "fast"), (["check-rest"], None)])
        self.assertFalse([s for s in result["suites"] if s.get("engine") == "073"], "0.7.3 runs only in make daily")


class Tiers(Fixture):
    def test_nothing_changed(self):
        result = self.tier()
        self.assertEqual((result["tier"], result["suites"]), ("none", []))

    def test_docs_only(self):
        result = self.change({"./docs/A.md": "# A, changed\n", "README.md": "# changed\n"})
        self.assertEqual(result["tier"], "docs")
        self.assertEqual(result["targets"], ["check-docs"])
        self.assertEqual((result["engine_targets"], result["faults"], result["coverage"]), ([], [], None))
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
        self.assertEqual(result["engine_targets"], ["test-lib"])
        self.assertEqual(result["faults"], ["free-one"])
        # Every target of make test that loads the file, test-front through src/front/alone.fs.
        self.assertEqual(result["coverage"], {"kind": "focus", "files": ["src/lib/free.fs"],
                                              "targets": ["smoke", "test-lib", "test-front"]})
        self.assertEqual(self.labels(result), ["coverage-focus", "targets", "targetsfast", "faults"])
        engines = {s["engine"]: s["goals"] for s in result["suites"] if s.get("engine")}
        self.assertEqual(engines, {"fast": ["test-lib"]})

    def test_tests_that_drive_main_measure_only_the_files_they_drive(self):
        # Owner, 2026-11-17: the ratchet of the files a change reaches, over their unit tests.
        result = self.change({"tests/core/c.fs": "require ../../src/main.fs\n\\ more\n"})
        self.assertEqual(result["tier"], "tests")
        self.assertEqual(result["coverage"], {"kind": "focus", "files": ["src/main.fs"],
                                              "targets": ["test-core", "smoke"]})
        self.assertEqual(self.labels(result)[0], "coverage-focus")
        self.assertEqual(result["faults"], ["core-one"])

    def test_full_tier_measures_only_the_changed_files(self):
        """The coverage of an untouched file is not measured again: only make daily does."""
        result = self.change({"src/core/c.fs": "require ../lib/used.fs\n\\ changed\n"})
        self.assertFull(result)
        self.assertEqual(result["coverage"], {"kind": "focus", "files": ["src/core/c.fs"],
                                              "targets": ["smoke", "test-core"]})
        self.assertEqual(result["suites"][0]["vars"], {"COVERAGE_FILES": "src/core/c.fs",
                                                       "COVERAGE_TARGETS": "smoke test-core"})
        self.repo.git("reset", "-q", "--hard", "base")
        result = self.change({"Makefile": tier_fixture.MAKEFILE + "\n"})
        self.assertFull(result)
        self.assertIsNone(result["coverage"], "a Makefile change measures no coverage")

    def test_end_to_end_tests_measure_a_file_no_unit_test_loads(self):
        self.repo.write("tests/cli/cli.fs", "require ../../src/program/p.fs\n")
        self.repo.commit("only an end-to-end test loads p.fs")
        self.repo.git("tag", "-f", "base")
        result = self.change({"src/program/p.fs": ": p 3 ;\n"})
        self.assertEqual(result["coverage"]["targets"], ["smoke", "test-cli"])

    def test_changed_baseline_entries_are_measured(self):
        self.repo.write("tests/coverage-baseline.json", '{"runs": 5, "files": {}}\n')
        self.repo.commit("a baseline")
        self.repo.git("tag", "-f", "base")
        result = self.change({"tests/coverage-baseline.json":
                              '{"runs": 5, "files": {"src/lib/free.fs": {"blocks": 2, "never_run": 1}}}\n'})
        self.assertEqual(result["coverage"]["files"], ["src/lib/free.fs"])
        result = self.change({"tests/coverage-baseline.json": '{"runs": 6, "files": {}}\n'})
        self.assertEqual(result["coverage"]["kind"], "all")

    def test_test_data(self):
        result = self.change({"tests/front/data.txt": "other data\n"})
        self.assertEqual(result["tier"], "tests")
        self.assertEqual(result["targets"], ["reference-front"])
        self.assertEqual(result["engine_targets"], [])

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

    def test_faults_d_file_is_part_of_the_list(self):
        """Slice (a1): tests/mutants/faults.d/*.toml is read with faults.toml as one list."""
        moved = tier_fixture.FAULTS.split("[[fault]]\nid = \"core-one\"")[0]
        rest = "[[fault]]\nid = \"core-one\"" + tier_fixture.FAULTS.split("[[fault]]\nid = \"core-one\"")[1]
        self.repo.write("tests/mutants/faults.toml", rest)
        self.repo.write("tests/mutants/faults.d/free.toml", moved)
        self.repo.commit("move a fault")
        self.repo.git("tag", "-f", "base")
        result = self.change({"tests/mutants/faults.d/free.toml": moved.replace('new = "eerf"', 'new = "eref"')})
        self.assertEqual(result["tier"], "tests")
        self.assertEqual(result["faults"], ["free-one"])
        self.assertEqual(self.change({"tests/lib/a.fs": "require ../../src/lib/free.fs\n\\ x\n"})["faults"],
                         ["free-one"], "a fault of faults.d whose test names a changed file")

    def test_malformed_or_repeated_faults_d_stops_the_plan(self):
        for text in ("[[fault]\nid = broken\n", tier_fixture.FAULTS):
            with self.subTest(text=text[:20]):
                self.repo.write("tests/mutants/faults.d/bad.toml", text)
                self.repo.commit("a fault file")
                run = self.repo.script("test-tier.py", "--base", "base", "--json")
                self.assertEqual(run.returncode, 2, run.stdout)
                self.assertIn("test-tier: ", run.stderr)

    def test_library_nothing_loads(self):
        result = self.change({"src/lib/free.fs": ": free-word 1 ;\n"})
        self.assertEqual(result["tier"], "library")
        self.assertEqual(result["targets"], ["check-portable-forth", "check-forth-quality", "smoke",
                                             "test-lib", "test-front"])
        self.assertEqual(result["engine_targets"], ["smoke", "test-lib", "test-front"])
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
        # B4: a deleted test that drove a loaded file is the full tier, coverage included: what it
        # drove is known only from the base tree, so all of make coverage-check runs.
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
        self.assertNotIn("0.7.3", run.stdout)
        self.assertIn("suite targetsfast (gforth-fast): make smoke test-lib test-front", run.stdout)

    def test_bad_base(self):
        run = self.repo.script("test-tier.py", "--base", "no-such-ref")
        self.assertEqual(run.returncode, 2)
        self.assertIn("test-tier: git", run.stderr)


class Engines(Fixture):
    """Owner, 2026-11-14: unit tests on gforth-fast and Gforth 0.7.3 too, end-to-end tests once."""

    def engines(self, result):
        return {s["engine"]: s["goals"] for s in result["suites"] if s.get("engine")}

    def test_end_to_end_test_runs_once(self):
        result = self.change({"tests/cli/cli.fs": "\\ the command line, changed\n"})
        self.assertEqual(result["tier"], "tests")
        self.assertEqual(result["targets"], ["test-cli"])
        self.assertEqual((result["engine_targets"], self.engines(result)), ([], {}))
        self.assertEqual(self.labels(result), ["targets"])

    def test_unclassified_target_runs_on_every_engine(self):
        # A target the table lacks counts as a unit test: the engines run more, never less.
        self.repo.write("tests/test-classes.txt", tier_fixture.CLASSES.replace("test-cli e2e\n", ""))
        self.repo.commit("test-cli unclassified")
        self.repo.git("tag", "-f", "base")
        result = self.change({"tests/cli/cli.fs": "\\ the command line, changed\n"})
        self.assertEqual(self.engines(result), {"fast": ["test-cli"]})

    def test_plan_without_a_reached_unit_test_on_an_engine_fails(self):
        result = {"tier": "tests", "targets": ["test-lib", "test-core", "check-docs", "test-cli"],
                  "suites": [{"label": "targetsfast", "goals": ["test-core"], "engine": "fast"}]}
        unit = {"test-lib", "test-core"}.__contains__
        self.assertEqual(tt.engine_problems(result, unit, {"test-cli"}),
                         ["unit test test-lib would not run on gforth-fast"])
        result["suites"][0]["goals"].append("test-lib")
        self.assertEqual(tt.engine_problems(result, unit, {"test-cli"}), [])

    def test_plan_with_an_end_to_end_test_on_an_engine_fails(self):
        result = {"tier": "library", "targets": ["test-lib", "test-cli"],
                  "suites": [{"label": "targetsfast", "goals": ["test-lib", "test-cli"], "engine": "fast"}]}
        self.assertEqual(tt.engine_problems(result, {"test-lib"}.__contains__, {"test-cli"}),
                         ["end-to-end test test-cli would run on gforth-fast"])

    def test_no_tier_runs_073(self):
        """Owner, 2026-11-17: Gforth 0.7.3 runs only in make daily and make tag-check."""
        result = {"tier": "library", "targets": ["test-lib"],
                  "suites": [{"label": "targetsfast", "goals": ["test-lib"], "engine": "fast"},
                             {"label": "targets073", "goals": ["test-lib"], "engine": "073"}]}
        self.assertEqual(tt.engine_problems(result, {"test-lib"}.__contains__, set()),
                         ["a tier runs Gforth 0.7.3 (only make daily does)"])
        self.assertEqual([s["label"] for s in tt.DAILY_SUITES if s.get("engine") == "073"], ["test073"])

    def test_full_tier_runs_the_unit_tests_on_gforth_fast(self):
        full = {"tier": "full", "targets": [], "suites": [dict(s) for s in tt.FULL_SUITES]}
        self.assertEqual(tt.engine_problems(full, lambda u: True, set()), [])
        full["suites"] = [s for s in full["suites"] if s.get("engine") != "fast"]
        self.assertEqual(tt.engine_problems(full, lambda u: True, set()),
                         ["the full tier runs no make test-unit on gforth-fast"])


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


class BareWords(unittest.TestCase):
    """A quoted word equal to a folder's name is an input only when used as a path (2026-11-18:
    the mode "development" made test-cli read all of docs/development, ci-results.log too)."""
    TRACKED = {p: "0" for p in ("docs/development/ci-results.log", "docs/development/A.md", "docs/user/B.md",
                                "tests/cli/t.py", "tests/support/h.py", "src/lib/x.fs", "README.md")}

    def used(self, line, language=".py"):
        ct = tt.changed_tests
        at = line.index('"development"') if '"development"' in line else line.index('"')
        end = line.index('"', at + 1) + 1
        return ct.used_as_path(language, line, at, end)

    def inputs(self, code, path="tests/cli/t.py"):
        ct = tt.changed_tests
        runs, data, _ = ct.program_inputs(path, code, self.TRACKED, ct.file_index(self.TRACKED))
        return {p for p in runs | data if not p.startswith(os.path.dirname(path) + "/")}

    def test_values_are_not_paths(self):
        for line in ('self.assertEqual(loaded["mode"], "development")', 'd["check"].update(mode="development")',
                     'x = d["development"]', '{"str": "development", "in": 3}', '{"development": 1}',
                     'if mode == "development":', 'if "development" != mode:', 'ok = "development" in modes',
                     'if mode in ("user", "development"):', 'print("development")', 'p.get("development")'):
            self.assertFalse(self.used(line), line)

    def test_paths_and_doubt_are_inputs(self):
        for line in ('ROOT / "development" / "x.md"', 'os.path.join(ROOT, "docs", "development")',
                     'Path("development")', 'top = "development"', 'for p in ("development", "user"):',
                     'run(["check", "development"])', 'f(where="development")', 'self.repo.commit("development")'):
            self.assertTrue(self.used(line), line)
        for line in ('cd "development"', 'ls "$root"/"development"'):
            self.assertTrue(self.used(line, ".sh"), line)
        for line in ('[ "$mode" = "development" ]', 'case $m in "development") ;;'):
            self.assertFalse(self.used(line, ".sh"), line)

    def test_program_inputs(self):
        folder = {"docs/development/ci-results.log", "docs/development/A.md"}
        self.assertEqual(self.inputs('assert out["mode"] == "development"\n'), set())
        self.assertEqual(self.inputs('page = DOCS / "development" / name\n'), folder)
        self.assertEqual(self.inputs('check(root, "development/")\n'), folder, "a path separator")
        self.assertEqual(self.inputs('assertEqual(tier, "docs")\n'), set(), "a root folder's name as a value")
        self.assertEqual(self.inputs('walk("docs")\n'), folder | {"docs/user/B.md"})
        self.assertEqual(self.inputs('run("check", "README.md")\n'), {"README.md"}, "a file name stays")


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
        self.assertEqual(differs, ["test-cli-engines"])
        self.assertEqual(self.built(["test"]) & self.built(["check-rest"]), self.built(differs))

    def test_unit_and_end_to_end_cover_make_check(self):
        """make test-unit and make test-e2e are the table's classes; together they are make check."""
        unit, e2e = self.built(["test-unit"]) - {"test-unit"}, self.built(["test-e2e"]) - {"test-e2e"}
        self.assertFalse(unit & e2e)
        self.assertEqual(unit | e2e, self.built(["check"]))
        self.assertTrue({"test-cli-1", "test-front-e2e", "reference"} <= e2e)
        self.assertTrue({"test-cli-forth", "test-front", "smoke"} <= unit)

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
