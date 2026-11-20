#!/usr/bin/env python3
"""Tests of the branch coverage check, scripts/coverage.py --changed (make cover-changed; owner,
2026-11-19, OWNER_DECISIONS.md "Coverage in the branch in seconds, the whole-suite ratchet at
night"), and of the unit-test selection it shares with make cover (--file).

End to end, in a throw-away git repository with a copy of scripts/ and a tiny Forth library,
src/lib/tiny.fs, whose word tiny-never no test runs (an old gap): a branch that adds an untested
branch of a word fails naming its line; adding the test makes it pass; a change to a line that
runs passes, and the old gap on an unchanged line is not reported; a touched file that only an
end-to-end test loads fails; a never-run changed line passes only by a baseline reason that
starts with "unreachable:" and names it; and a unit test that reaches the file only through text
(a file it includes, naming none of the library's words) counts, through the widening from the
narrowed set. In process: the selection rule, the hunk reading and the exception's reading; and
on the real tree, the selection that was missing tests/front/tactic-lib.fs for
src/front/tactics/case.fs. The end-to-end cases need Gforth 1.0 with coverage.fs
($LEANFORTH_GFORTH, .tools or PATH)."""
import importlib.util
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import tier_fixture  # noqa: E402

ROOT = HERE.parents[1]
spec = importlib.util.spec_from_file_location("coverage_tool", ROOT / "scripts/coverage.py")
tool = importlib.util.module_from_spec(spec)
spec.loader.exec_module(tool)


def real_gforth():
    local = ROOT / ".tools/gforth/bin/gforth"
    found = os.environ.get("LEANFORTH_GFORTH") or (str(local) if local.exists() else None)
    found = found or shutil.which("gforth")
    if found and "scripts/" in found:
        found = str(local) if local.exists() else shutil.which("gforth")
    return found


GFORTH = real_gforth()
HAS_COVERAGE = bool(GFORTH) and tool.has_coverage(GFORTH)

TINY = ("\\ A tiny word with a branch, for the branch coverage check's tests.\n"
        ": tiny-sign ( n -- c )\n"
        "  0= if [char] 0 else [char] + then ;\n"
        ": tiny-never ( -- ) 1 2 + drop ;   \\ never run: an old gap\n")
# The branch adds a negative case on line 3, which no unit test runs yet.
NEGATIVE = TINY.replace("( n -- c )\n", "( n -- c )\n  dup 0< if drop [char] - exit then\n")
TESTED = "require ../../src/lib/tiny.fs\n5 tiny-sign drop 0 tiny-sign drop bye\n"
MAKEFILE = """\
GFORTH ?= gforth
test: test-lib test-core test-other
check: test check-rest
check-rest: reference-e2e
test-lib:
\t$(GFORTH) tests/lib/tiny.fs
test-core:
\tfor f in tests/core/t*.fs; do $(GFORTH) $$f || exit 1; done
test-other:
\t$(GFORTH) tests/other/text.fs
reference-e2e:
\t$(GFORTH) tests/e2e/run.fs
.PHONY: test check check-rest test-lib test-core test-other reference-e2e
"""
FILES = {
    "Makefile": MAKEFILE,
    ".gitignore": "__pycache__/\n",
    "src/main.fs": "require ./lib/tiny.fs\n",
    "src/lib/tiny.fs": TINY,
    "tests/lib/tiny.fs": TESTED,
    "tests/other/text.fs": "require ../../src/main.fs\n1 drop bye\n",
    "tests/e2e/run.fs": "require ../../src/main.fs\n-3 tiny-sign drop bye\n",
    "tests/test-classes.txt": "test-lib unit\ntest-core unit\ntest-other unit\nreference-e2e e2e\n",
    "tests/coverage-baseline.json": '{"runs": 1, "files": {}}\n',
}


class Repo:
    """A repository on branch main (the fixture above and a copy of scripts/), then branch work."""

    def __init__(self, extra=None):
        self.top = tempfile.mkdtemp(prefix="lf-cover-changed-")
        self.path = Path(self.top)
        self.env = tier_fixture.make_env(HOME=self.top)
        tracked = subprocess.run(["git", "ls-files", "scripts"], cwd=ROOT, capture_output=True, text=True,
                                 check=True).stdout.split()
        for name in tracked:
            (self.path / name).parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(ROOT / name, self.path / name)
        for name, text in {**FILES, **(extra or {})}.items():
            self.write(name, text)
        self.git("init", "-q", "-b", "main")
        self.commit("base")
        self.git("checkout", "-q", "-b", "work")

    def write(self, name, text):
        (self.path / name).parent.mkdir(parents=True, exist_ok=True)
        (self.path / name).write_text(text, encoding="utf-8")

    def git(self, *args):
        return subprocess.run(["git", *args], cwd=self.path, env=self.env, capture_output=True, text=True,
                              check=True).stdout.strip()

    def commit(self, message, files=None):
        for name, text in (files or {}).items():
            self.write(name, text)
        self.git("add", "-A")
        self.git("commit", "-q", "--allow-empty", "-m", message)

    def check(self, *args):
        """(exit status, output) of the copied scripts/coverage.py --changed main in the repository."""
        run = subprocess.run([sys.executable, "scripts/coverage.py", "--gforth", GFORTH, "--jobs", "2",
                              "--changed", "main", *args], cwd=self.path, env=self.env, stdin=subprocess.DEVNULL,
                             capture_output=True, text=True, timeout=600)
        return run.returncode, run.stdout + run.stderr

    def cover(self, path):
        run = subprocess.run([sys.executable, "scripts/coverage.py", "--gforth", GFORTH, "--jobs", "2", "--file",
                              path], cwd=self.path, env=self.env, stdin=subprocess.DEVNULL, capture_output=True,
                             text=True, timeout=600)
        return run.returncode, run.stdout + run.stderr

    def close(self):
        shutil.rmtree(self.top, ignore_errors=True)


@unittest.skipUnless(HAS_COVERAGE, "needs Gforth 1.0 with coverage.fs")
class Changed(unittest.TestCase):
    def setUp(self):
        self.repo = Repo()

    def tearDown(self):
        self.repo.close()

    def test_nothing_touched_passes(self):
        self.repo.commit("a test only", {"tests/lib/tiny.fs": TESTED + "\\ more\n"})
        status, out = self.repo.check()
        self.assertEqual(status, 0, out)
        self.assertIn("no Forth file of src/ added or modified since", out)

    def test_an_untested_branch_fails_naming_its_line_until_tested(self):
        self.repo.commit("a negative case", {"src/lib/tiny.fs": NEGATIVE})
        status, out = self.repo.check()
        self.assertEqual(status, 1, out)
        self.assertIn("\nsrc/lib/tiny.fs:3: tiny-sign: drop [char] - exit then\n", out)
        self.assertIn("src/lib/tiny.fs: 1 changed code line(s), 3 block(s) on them, 1 never run", out)
        self.assertNotIn("tiny-never", out, "an old gap on an unchanged line is not the branch's")
        self.assertIn("cover-changed: FAILED: 1 never-run block(s) on changed lines", out)
        # The end-to-end test runs the negative case, and does not count: unit tests only.
        self.repo.commit("its test", {"tests/lib/tiny.fs": TESTED.replace("bye", "-3 tiny-sign drop bye")})
        status, out = self.repo.check()
        self.assertEqual(status, 0, out)
        self.assertIn("src/lib/tiny.fs: 1 changed code line(s), 3 block(s) on them, every one ran", out)
        self.assertIn("cover-changed: every block on a changed line ran", out)

    def test_a_changed_line_that_runs_passes_and_comments_need_no_run(self):
        self.repo.commit("a run line", {"src/lib/tiny.fs": TINY.replace("[char] +", "[char] p")})
        status, out = self.repo.check()
        self.assertEqual(status, 0, out)
        self.assertIn("src/lib/tiny.fs: 1 changed code line(s), 4 block(s) on them, every one ran", out)
        self.assertNotIn("tiny-never", out)
        self.repo.git("reset", "-q", "--hard", "main")
        # A comment line, a comment after code and a stack comment of a word no test runs, and its
        # indentation: no code changed.
        self.repo.commit("comments", {"src/lib/tiny.fs": TINY.replace("an old gap", "an old gap, still")
                                      .replace("A tiny word", "A small word").replace("( -- ) 1 2", "( -- )  1 2")})
        status, out = self.repo.check()
        self.assertEqual(status, 0, out)
        self.assertIn("src/lib/tiny.fs: only comments or white space changed: no block to run", out)

    def test_a_file_only_an_end_to_end_test_loads_fails(self):
        self.repo.commit("a lonely file", {"src/lib/lonely.fs": ": lonely ( -- n ) 1 ;\n",
                                           "tests/e2e/run.fs": "require ../../src/lib/lonely.fs\nlonely drop bye\n"})
        status, out = self.repo.check()
        self.assertEqual(status, 1, out)
        self.assertIn("src/lib/lonely.fs: FAILED: no unit test file loads it", out)
        self.assertIn("1 file(s) failing", out)
        # Uncommitted and untracked files count too: every line of a new file is the branch's.
        self.repo.write("src/lib/lonely.fs", ": lonely ( -- n ) 2 ;\n")
        self.repo.write("tests/lib/lonely.fs", "require ../../src/lib/lonely.fs\nlonely drop bye\n")
        self.repo.write("Makefile", MAKEFILE.replace("\t$(GFORTH) tests/lib/tiny.fs\n",
                                                     "\t$(GFORTH) tests/lib/tiny.fs\n\t$(GFORTH) tests/lib/lonely.fs\n"))
        status, out = self.repo.check()
        self.assertEqual(status, 0, out)
        self.repo.write("src/lib/new.fs", ": new-word ( -- ) 1 if 2 drop then ;\n")
        status, out = self.repo.check()
        self.assertEqual(status, 1, out)
        self.assertIn("src/lib/new.fs: FAILED: no unit test file loads it", out)

    def test_a_failing_unit_test_fails(self):
        self.repo.commit("a run line and a broken test", {"src/lib/tiny.fs": TINY.replace("[char] +", "[char] p"),
                                                          "tests/lib/tiny.fs": TESTED.replace("bye", "1 throw")})
        status, out = self.repo.check()
        self.assertEqual(status, 1, out)
        self.assertIn("test FAILED: tests/lib/tiny.fs", out)

    def test_only_an_unreachable_reason_naming_the_line_excuses_it(self):
        def baseline(reason):
            return ('{"runs": 1, "files": {"src/lib/tiny.fs": {"blocks": 11, "never_run": 2, "reason": "%s"}}}\n'
                    % reason)
        self.repo.commit("a negative case", {"src/lib/tiny.fs": NEGATIVE})
        for reason, status in (("unreachable: line 3, no caller passes a negative n (the fixture)", 0),
                               ("coverage debt: line 3", 1), ("unreachable: line 9 only", 1),
                               ("the negative case (line 3) is unreachable: no caller", 1)):
            with self.subTest(reason=reason):
                self.repo.commit("a reason", {"tests/coverage-baseline.json": baseline(reason)})
                found, out = self.repo.check()
                self.assertEqual(found, status, out)
                if status == 0:
                    self.assertIn('src/lib/tiny.fs:3: tiny-sign: drop [char] - exit then  [accepted: the baseline\'s '
                                  'reason for src/lib/tiny.fs starts with "unreachable:" and names line 3]', out)
                else:
                    self.assertIn("\nsrc/lib/tiny.fs:3: tiny-sign: drop [char] - exit then\n", out)


@unittest.skipUnless(HAS_COVERAGE, "needs Gforth 1.0 with coverage.fs")
class Selection(unittest.TestCase):
    """More than NARROW_ABOVE unit test files load the library; one reaches its negative case only
    through text it includes, naming none of its words, outside the library's test folders."""

    def setUp(self):
        extra = {f"tests/core/t{n}.fs": "require ../../src/main.fs\nbye\n" for n in range(1, 10)}
        extra["tests/other/text.fs"] = 'require ../../src/main.fs\ns" neg.txt" included bye\n'
        extra["tests/other/neg.txt"] = "-3 tiny-sign drop\n"
        self.repo = Repo(extra)

    def tearDown(self):
        self.repo.close()

    def test_a_test_reaching_the_file_only_through_text_counts(self):
        cwd = os.getcwd()
        os.chdir(self.repo.path)
        try:
            every = tool.UnitTests(tool.load_script("test-tier.py", self.repo.path)).loading("src/lib/tiny.fs")
            first = tool.narrowed_tests("src/lib/tiny.fs", every, self.repo.path)
        finally:
            os.chdir(cwd)
        self.assertEqual(len(every), 11)
        self.assertIn("tests/other/text.fs", every)
        self.assertEqual(first, ["tests/lib/tiny.fs"], "it names a word of the file and sits in tests/lib")
        self.repo.commit("a negative case", {"src/lib/tiny.fs": NEGATIVE})
        status, out = self.repo.check()
        self.assertEqual(status, 0, out)
        self.assertIn("src/lib/tiny.fs: 1 changed code line(s), 3 block(s) on them, every one ran "
                      "(11 of 11 unit test files that load it)", out)
        status, out = self.repo.cover("src/lib/tiny.fs")
        self.assertIn("widened: blocks were left never run, so the other 10 unit test files that load it ran too",
                      out)
        self.assertIn("never run now 1;", out, "only tiny-never")
        self.assertIn("src/lib/tiny.fs:5:", out)

    def test_a_change_the_narrowed_set_runs_needs_no_widening(self):
        self.repo.commit("a run line", {"src/lib/tiny.fs": TINY.replace("[char] +", "[char] p")})
        status, out = self.repo.check()
        self.assertEqual(status, 0, out)
        self.assertIn("(1 of 11 unit test files that load it)", out)


class Rules(unittest.TestCase):
    def test_module_folders(self):
        self.assertEqual(tool.module_folders("src/front/tactics/case.fs"), ("tests/front", "tests/front/tactics/case/"))
        self.assertEqual(tool.module_folders("src/lib/sort.fs"), ("tests/lib", "tests/lib/sort/"))
        self.assertEqual(tool.module_folders("src/main.fs"), (None, "tests/main/"))

    def test_few_tests_all_run_first(self):
        every = [f"tests/core/t{n}.fs" for n in range(tool.NARROW_ABOVE)]
        self.assertEqual(tool.narrowed_tests("src/lib/none.fs", every), every)

    def test_hunks_and_their_code(self):
        diff = ("--- a/src/x.fs\n+++ b/src/x.fs\n@@ -3,0 +4,2 @@\n+a\n+b\n@@ -9,2 +11,0 @@\n-c\n--- d\n"
                "@@ -20 +20 @@\n-: w ( n -- ) dup ;  \\ old\n+:  w ( x -- )  dup ;\n\\ No newline at end of file\n")
        hunks = tool.diff_hunks(diff)
        self.assertEqual(hunks, [(4, 5, "", "a\nb"), (11, 10, "c\n-- d", ""),
                                 (20, 20, ": w ( n -- ) dup ;  \\ old", ":  w ( x -- )  dup ;")])
        self.assertEqual(tool.code_of(hunks[2][2]), tool.code_of(hunks[2][3]), "a comment and spacing only")
        self.assertNotEqual(tool.code_of("1 if 2 then"), tool.code_of("1 if 3 then"))

    def test_changed_blocks_and_the_exception(self):
        blocks = {(2, 12): 1, (3, 1): 1, (3, 36): 0, (5, 13): 0}
        found = tool.changed_blocks(NEGATIVE, blocks, [3])
        self.assertEqual([(b[0], b[2], b[4]) for b in found], [((3, 1), "tiny-sign", 1), ((3, 36), "tiny-sign", 0)])
        self.assertEqual(tool.unreachable_lines({"reason": " Unreachable: lines 3 and 40 (2026-11-19)"}), {3, 40})
        self.assertEqual(tool.unreachable_lines({"reason": "debt: line 3, unreachable: no"}), set())
        self.assertEqual(tool.unreachable_lines(None), set())


class RealTree(unittest.TestCase):
    def test_a_plug_in_is_measured_with_its_module_tests(self):
        """2026-11-19: make cover FILE=src/front/tactics/case.fs ran only the three tests that name
        one of its words and reported 48 of 48 blocks never run; tests/front/tactic-lib.fs, which
        runs the case tactic from .lf text, is in the module's folder."""
        cwd = os.getcwd()
        os.chdir(ROOT)
        try:
            every = tool.UnitTests(tool.load_script("test-tier.py")).loading("src/front/tactics/case.fs")
        finally:
            os.chdir(cwd)
        self.assertIn("tests/front/tactic-lib.fs", every)
        self.assertIn("tests/front/tactic-lib.fs", tool.narrowed_tests("src/front/tactics/case.fs", every))


if __name__ == "__main__":
    unittest.main()
