#!/usr/bin/env python3
"""Tests of scripts/test-classes.py (owner, 2026-11-14: unit tests on both engines, end-to-end
tests once): the table's rows and their problems; on a throw-away repository
(tests/scripts/tier_fixture.py) a classified tree passes, and a target or test file in neither
class, a stale row and a malformed table fail; the Makefile's make test-unit and make test-e2e
are the table's classes."""
import importlib.util
import pathlib
import sys
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import tier_fixture  # noqa: E402

ROOT = tier_fixture.ROOT
spec = importlib.util.spec_from_file_location("test_classes", ROOT / "scripts/test-classes.py")
tc = importlib.util.module_from_spec(spec)
spec.loader.exec_module(tc)


class Rows(unittest.TestCase):
    def test_parse(self):
        rows, problems = tc.parse("# a comment\n\ntest-lib unit\nreference e2e   a note\n"
                                  "tests/lib/bench.fs manual by hand\n")
        self.assertEqual(problems, [])
        self.assertEqual(rows, {"test-lib": "unit", "reference": "e2e", "tests/lib/bench.fs": "manual"})
        self.assertEqual(tc.of_class(rows, "unit"), ["test-lib"])
        self.assertEqual(tc.of_class(rows, "manual"), [], "a path is no target")

    def test_malformed_rows(self):
        rows, problems = tc.parse("test-lib\ntest-core fast\ntest-cli e2e\ntest-cli unit\n")
        self.assertEqual(rows, {"test-cli": "e2e"})
        self.assertEqual(len(problems), 3)
        self.assertIn(":1: not 'NAME CLASS", problems[0])
        self.assertIn(":2: not 'NAME CLASS", problems[1])
        self.assertIn(":4: test-cli is given twice", problems[2])

    def test_problems(self):
        rows = {"test-lib": "unit", "reference": "e2e", "gone": "unit", "smoke": "manual",
                "tests/lib/bench.fs": "manual", "tests/lib/run.fs": "unit", "tests/lib/missing.fs": "manual"}
        leaves = ["test-lib", "reference", "test-new", "smoke"]
        reached = {"tests/lib/a.fs", "tests/lib/run.fs"}
        programs = ["tests/lib/a.fs", "tests/lib/bench.fs", "tests/lib/run.fs", "tests/lib/orphan.py"]
        found = tc.problems_of(rows, leaves, reached, programs)
        self.assertEqual(sorted(found), sorted([
            "target test-new: in no class (add a row to tests/test-classes.txt)",
            "row gone: no leaf target of make check has that name",
            "row smoke: a target is unit or e2e, never manual",
            "test file tests/lib/orphan.py: in neither class: no target of make check runs it and no row "
            "of tests/test-classes.txt names it",
            "row tests/lib/missing.fs: no such tracked test program",
            "row tests/lib/run.fs: a target already runs it; its class is that target's (stale row)",
        ]))

    def test_no_problems(self):
        self.assertEqual(tc.problems_of({"a": "unit", "tests/x.fs": "manual"}, ["a"], {"tests/y.fs"},
                                        ["tests/x.fs", "tests/y.fs"]), [])


class Tree(unittest.TestCase):
    """scripts/test-classes.py on a throw-away repository shaped like LeanForth's."""

    def setUp(self):
        self.repo = tier_fixture.Repo()

    def tearDown(self):
        self.repo.close()

    def check(self):
        return self.repo.script("test-classes.py")

    def test_classified_tree_passes(self):
        run = self.check()
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertIn("8 unit and 3 end-to-end targets", run.stdout)

    def test_unclassified_test_file_fails(self):
        self.repo.write("tests/lib/orphan.fs", "\\ no target runs me\n")
        self.repo.commit("orphan")
        run = self.check()
        self.assertEqual(run.returncode, 1)
        self.assertIn("test file tests/lib/orphan.fs: in neither class", run.stderr)
        self.repo.write("tests/test-classes.txt", tier_fixture.CLASSES + "tests/lib/orphan.fs manual by hand\n")
        self.assertEqual(self.check().returncode, 0)

    def test_unclassified_target_fails(self):
        makefile = (self.repo.path / "Makefile").read_text()
        self.repo.write("Makefile", makefile.replace("test: check-docs", "test: test-new check-docs")
                        + "test-new:\n\t$(GFORTH) tests/lib/a.fs\n")
        run = self.check()
        self.assertEqual(run.returncode, 1)
        self.assertIn("target test-new: in no class", run.stderr)

    def test_stale_and_malformed_rows_fail(self):
        self.repo.write("tests/test-classes.txt", tier_fixture.CLASSES + "test-gone unit\ntest-lib\n")
        run = self.check()
        self.assertEqual(run.returncode, 1)
        self.assertIn("row test-gone: no leaf target", run.stderr)
        self.assertIn("not 'NAME CLASS", run.stderr)

    def test_missing_table_fails(self):
        self.repo.remove("tests/test-classes.txt")
        run = self.check()
        self.assertEqual(run.returncode, 1)
        self.assertIn("missing", run.stderr)
        self.assertIn("target test-lib: in no class", run.stderr)

    def test_list(self):
        run = self.repo.script("test-classes.py", "--list", "e2e")
        self.assertEqual(run.stdout.split(), ["test-cli", "reference-front", "reference-core"])

    def test_makefile_reads_the_classes(self):
        run = self.repo.run("make", "-n", "--no-print-directory", "test-unit", "STUB_LOG=")
        self.assertEqual(run.returncode, 0, run.stderr)
        for name in ("tests/lib/a.fs", "tests/core/c.fs", "tests/front/f.fs"):
            self.assertIn(name, run.stdout)
        self.assertNotIn("tests/cli/cli.fs", run.stdout, "test-cli is end to end")
        run = self.repo.run("make", "-n", "--no-print-directory", "test-e2e")
        self.assertIn("tests/cli/cli.fs", run.stdout)
        self.assertNotIn("tests/lib/a.fs", run.stdout)


class Patterns(unittest.TestCase):
    """Tactic plug-in design, slice (a1): pattern rows class the targets the Makefile finds."""

    ROWS = {"test-tactic-*": "unit", "test-tactic-*-e2e": "e2e", "test-lib": "unit"}

    def test_longest_pattern_wins(self):
        self.assertEqual(tc.class_of(self.ROWS, "test-tactic-decide"), "unit")
        self.assertEqual(tc.class_of(self.ROWS, "test-tactic-decide-e2e"), "e2e")
        self.assertEqual(tc.class_of(self.ROWS, "test-lib"), "unit")
        self.assertIsNone(tc.class_of(self.ROWS, "test-other"))
        self.assertIn("test-tactic-x-e2e", tc.OfClass(self.ROWS, "e2e"))
        self.assertNotIn("test-tactic-x", tc.OfClass(self.ROWS, "e2e"))
        self.assertEqual(tc.of_class(self.ROWS, "unit"), ["test-lib"], "a pattern names no target itself")

    def test_a_pattern_may_match_nothing_and_classes_what_it_matches(self):
        self.assertEqual(tc.problems_of(self.ROWS, ["test-lib"], set(), []), [])
        self.assertEqual(tc.problems_of(self.ROWS, ["test-lib", "test-tactic-rfl", "test-tactic-rfl-e2e"], set(), []),
                         [])
        self.assertEqual(tc.problems_of({"test-tactic-*": "manual"}, ["test-tactic-rfl"], set(), []),
                         ["row test-tactic-*: a target is unit or e2e, never manual"])


class Discovery(unittest.TestCase):
    """The real Makefile finds a tactic's targets from tests/front/tactics/NAME/ (slice (a1)): in a
    copy holding the Makefile, the table and one tactic's test files, make test, test-unit and
    test-e2e name them; in the project's own tree there are none yet."""

    def test_tactic_targets_found_from_files(self):
        import shutil
        import tempfile
        top = pathlib.Path(tempfile.mkdtemp(prefix="lf-discovery-"))
        try:
            shutil.copy(ROOT / "Makefile", top / "Makefile")
            (top / "tests/front/tactics/decide").mkdir(parents=True)
            shutil.copy(ROOT / tc.TABLE, top / tc.TABLE)
            (top / "tests/front/tactics/decide/test.fs").write_text("\\ unit\n")
            (top / "tests/front/tactics/decide/check.py").write_text("# e2e\n")
            env = tier_fixture.make_env()
            run = lambda *goals: tier_fixture.subprocess.run(  # noqa: E731
                ["make", "-n", "--no-print-directory", "-j1", *goals], cwd=top, env=env,
                capture_output=True, text=True).stdout
            self.assertIn("tests/front/tactics/decide/test.fs", run("test-tactic-decide"))
            self.assertIn("python3 tests/front/tactics/decide/check.py", run("test-tactic-decide-e2e"))
            self.assertIn("tests/front/tactics/decide/test.fs", run("test-unit"))
            self.assertNotIn("tests/front/tactics/decide/check.py", run("test-unit"))
            self.assertIn("tests/front/tactics/decide/check.py", run("test-e2e"))
            both = run("test")
            self.assertIn("tests/front/tactics/decide/test.fs", both)
            self.assertIn("tests/front/tactics/decide/check.py", both)
        finally:
            shutil.rmtree(top, ignore_errors=True)

    def test_the_project_s_tactics(self):
        # The tactics of slice a2-iii (branch tactic-lib-a2ii), of tactic batch 1 (plan row
        # TB1) and by-decide (plan row S3, slice S3a), found from their folders, sorted.
        run = tier_fixture.subprocess.run(["make", "-s", "--no-print-directory", "--eval",
                                           "p: ; @echo [$(TACTIC_UNIT_TARGETS)][$(TACTIC_E2E_TARGETS)]", "p"],
                                          cwd=ROOT, env=tier_fixture.make_env(), capture_output=True, text=True)
        names = ["apply", "assumption", "clear", "constructor", "decide", "exfalso", "intros",
                 "left", "right"]
        self.assertEqual(run.stdout.strip(),
                         "[" + " ".join(f"test-tactic-{n}" for n in names) + "]["
                         + " ".join(f"test-tactic-{n}-e2e" for n in names) + "]")


class RealTree(unittest.TestCase):
    """The project's own table (read only): the e2e targets of make test are those the
    owner's decision names, and every unit target of make test runs on Gforth."""

    def test_real_table(self):
        rows, problems = tc.read(str(ROOT / tc.TABLE))
        self.assertEqual(problems, [])
        e2e = tc.of_class(rows, "e2e")
        for name in ("test-cli-1", "test-cli-4", "test-cli-engines", "test-front-e2e", "reference",
                     "reference-compact-init", "test-program-verify-command"):
            self.assertIn(name, e2e)
        for name in ("test-cli-forth", "test-front", "test-core", "test-lib", "smoke", "test-tiers"):
            self.assertEqual(rows[name], "unit", name)


if __name__ == "__main__":
    unittest.main()
