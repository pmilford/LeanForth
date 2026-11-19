#!/usr/bin/env python3
"""Tests of the coverage-debt tools of scripts/coverage.py (make cover, make cover-debt; plan 9.4.8,
owner 2026-11-19 "Tools first"), on a tiny Forth tree with a known never-run branch:

  - --file (cover()): one file's never-run blocks over unit tests only, with lines, words and text,
    the baseline's count and whether its reason names each block, the last saved full run's marks;
    exit 0 when not above the baseline, 1 above it or when a test fails, 2 when no run loads it;
  - --set-baseline / --drop-baseline: one file's entry without a run, refusing to raise a count
    without a reason and new never-run blocks without a reason naming each line;
  - --uncovered refuses a source folder or a tracked file (it once overwrote a source file);
  - --debt lists the entries with never-run blocks, largest first.
The end-to-end cases need Gforth 1.0 with coverage.fs ($LEANFORTH_GFORTH, .tools or PATH)."""
import importlib.util
import io
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from contextlib import redirect_stdout
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("coverage_tool", ROOT / "scripts/coverage.py")
tool = importlib.util.module_from_spec(spec)
spec.loader.exec_module(tool)

TINY = (": tiny-sign ( n -- c )\n"
        "  dup 0< if drop [char] - exit then   \\ never run: no negative test\n"
        "  0= if [char] 0 else [char] + then ;\n"
        ": tiny-never ( -- ) 1 2 + drop ;\n")
# Gforth's blocks of TINY (line, column), as a run under coverage.fs places them.
PLACES = [(1, 12), (2, 1), (2, 12), (2, 36), (3, 1), (3, 8), (3, 22), (3, 36), (4, 13)]
TEST = "require ../src/tiny.fs\n5 tiny-sign drop 0 tiny-sign drop bye\n"


def real_gforth():
    local = ROOT / ".tools/gforth/bin/gforth"
    found = os.environ.get("LEANFORTH_GFORTH") or (str(local) if local.exists() else None)
    found = found or shutil.which("gforth")
    if found and "scripts/" in found:
        found = str(local) if local.exists() else shutil.which("gforth")
    return found


GFORTH = real_gforth()
HAS_COVERAGE = bool(GFORTH) and tool.has_coverage(GFORTH)


def tiny_tree(folder, test=TEST):
    root = Path(folder)
    (root / "src").mkdir()
    (root / "tests").mkdir()
    (root / "src/tiny.fs").write_text(TINY)
    (root / "tests/tiny-test.fs").write_text(test)
    return root


def run_main(*args):
    out = io.StringIO()
    with redirect_stdout(out):
        status = tool.main(list(args))
    return status, out.getvalue()


class Blocks(unittest.TestCase):
    def test_comments_are_blanked_in_place(self):
        text = ": a ( x -- y ) dup \\ note\n  drop ;"
        clean = tool.blank_comments(text)
        self.assertEqual(len(clean), len(text))
        self.assertEqual(clean.split(), [":", "a", "dup", "drop", ";"])

    def test_a_block_has_its_lines_word_and_text(self):
        about = tool.describe_blocks(TINY, [(1, 12), (2, 12), (2, 36), (3, 1), (4, 13)])
        self.assertEqual(about[(2, 12)], (2, "tiny-sign", "drop [char] - exit then"))
        self.assertEqual(about[(4, 13)], (4, "tiny-never", "1 2 + drop ;"))
        self.assertEqual(about[(3, 1)][1:], ("tiny-sign", "0= if [char] 0 else [char] + then ;"))

    def test_a_block_spanning_lines(self):
        text = ": w ( -- )\n  1 if\n    2\n    3 then ;\n"
        self.assertEqual(tool.describe_blocks(text, [(2, 7)])[(2, 7)], (4, "w", "2 3 then ;"))

    def test_reason_line_numbers_skip_dates_and_versions(self):
        self.assertEqual(tool.reason_lines("lines 205: x (99: y) 2026-11-14 4.35.0 3ac0558"), {205, 99})


class Baseline(unittest.TestCase):
    def base(self):
        return {"runs": 3, "files": {"src/a.fs": {"blocks": 10, "never_run": 2, "reason": "two (4, 7)"},
                                     "src/b.fs": {"blocks": 5, "never_run": 0}}}

    def test_lowering_needs_no_reason_and_keeps_it(self):
        base = self.base()
        old, new = tool.set_entry(base, "src/a.fs", 1)
        self.assertEqual(old["never_run"], 2)
        self.assertEqual(new, {"blocks": 10, "never_run": 1, "reason": "two (4, 7)"})
        self.assertEqual(tool.set_entry(base, "src/a.fs", 0)[1], {"blocks": 10, "never_run": 0})

    def test_raising_needs_a_reason(self):
        with self.assertRaises(tool.Refused):
            tool.set_entry(self.base(), "src/a.fs", 3)
        new = tool.set_entry(self.base(), "src/a.fs", 3, reason="three: 4, 7, 9")[1]
        self.assertEqual(new["reason"], "three: 4, 7, 9")

    def test_a_file_without_gaps_needs_each_line_named(self):
        with self.assertRaises(tool.Refused):
            tool.set_entry(self.base(), "src/b.fs", 2, reason="the heap refusing")
        with self.assertRaises(tool.Refused):
            tool.set_entry(self.base(), "src/b.fs", 2, reason="line 12 only")
        self.assertEqual(tool.set_entry(self.base(), "src/b.fs", 2, reason="lines 12 and 30")[1]["never_run"], 2)

    def test_a_new_entry_needs_the_file_and_its_total(self):
        with tempfile.TemporaryDirectory() as folder:
            root = tiny_tree(folder)
            base = self.base()
            with self.assertRaises(tool.Refused):
                tool.set_entry(base, "src/tiny.fs", 0, root=root)
            with self.assertRaises(tool.Refused):
                tool.set_entry(base, "src/none.fs", 0, total=3, root=root)
            with self.assertRaises(tool.Refused):
                tool.set_entry(base, "src/tiny.fs", 4, total=3, reason="1 2 3 4", root=root)
            tool.set_entry(base, "src/tiny.fs", 0, total=9, root=root)
            self.assertEqual(list(base["files"]), ["src/a.fs", "src/b.fs", "src/tiny.fs"])

    def test_drop(self):
        base = self.base()
        self.assertEqual(tool.drop_entry(base, "src/a.fs")["never_run"], 2)
        with self.assertRaises(tool.Refused):
            tool.drop_entry(base, "src/a.fs")

    def test_main_prints_old_and_new_and_writes_one_entry(self):
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder) / "baseline.json"
            path.write_text(json.dumps(self.base(), indent=1) + "\n")
            status, out = run_main("--baseline", str(path), "--set-baseline", "src/a.fs", "--blocks", "1")
            self.assertEqual(status, 0, out)
            self.assertIn('old {"blocks": 10, "never_run": 2', out)
            self.assertIn('new {"blocks": 10, "never_run": 1', out)
            written = json.loads(path.read_text())
            self.assertEqual(written["files"]["src/a.fs"]["never_run"], 1)
            self.assertEqual(written["files"]["src/b.fs"], self.base()["files"]["src/b.fs"])
            self.assertEqual(written["runs"], 3)
            before = path.read_text()
            status, out = run_main("--baseline", str(path), "--set-baseline", "src/a.fs", "--blocks", "5")
            self.assertEqual((status, path.read_text()), (1, before), "a refused raise writes nothing")
            self.assertIn("refused", out)
            status, out = run_main("--baseline", str(path), "--drop-baseline", "src/b.fs")
            self.assertEqual(status, 0, out)
            self.assertNotIn("src/b.fs", json.loads(path.read_text())["files"])

    def test_debt_lists_gaps_largest_first(self):
        base = self.base()
        base["files"]["src/c/d.fs"] = {"blocks": 9, "never_run": 5, "reason": "five"}
        lines = tool.debt_lines(base)
        self.assertIn("7 never-run blocks in 2 files", lines[0])
        self.assertIn("src/c/d.fs", lines[1])
        self.assertIn("src/a.fs", lines[3])
        self.assertNotIn("src/b.fs", "\n".join(lines))
        self.assertEqual(lines[-1], "by folder: src/c 5, src 2")


class Uncovered(unittest.TestCase):
    def test_sources_and_tracked_files_are_refused(self):
        for folder, name in (("src", "lib"), ("src", "new.txt"), ("tests", "x.txt"), ("scripts", "y"),
                             ("docs", "new-output.txt")):
            with self.subTest(folder=folder, name=name):
                self.assertIsNotNone(tool.output_problem(ROOT / folder / name))
        self.assertIn("tracks", tool.output_problem(ROOT / "Makefile"))
        with tempfile.TemporaryDirectory() as folder:
            self.assertIsNone(tool.output_problem(Path(folder) / "uncovered.txt"))

    def test_main_refuses_before_running_anything(self):
        status, out = run_main("--uncovered", str(ROOT / "src/lib/bounds.fs"), "--", "false")
        self.assertEqual(status, 2)
        self.assertIn("names an output file", out)

    def test_help_says_it_names_an_output_file(self):
        out = io.StringIO()
        with redirect_stdout(out), self.assertRaises(SystemExit):
            tool.main(["--help"])
        self.assertIn("--uncovered OUTPUT", out.getvalue())


class Marks(unittest.TestCase):
    def test_same_file_by_place_changed_file_by_word_and_text(self):
        about = tool.describe_blocks(TINY, PLACES)
        saved = {"files": {"src/tiny.fs": {"sha256": tool.file_digest(TINY), "blocks": 2,
                                           "never_run": [[2, 12, "tiny-sign", "drop [char] - exit then"]]}}}
        marks = tool.full_run_marks("src/tiny.fs", TINY, [(2, 12), (4, 13)], about, saved)
        self.assertEqual(marks, {(2, 12): "also never run in the last full run",
                                 (4, 13): "ran in the last full run"})
        moved = "\n" + TINY
        about = tool.describe_blocks(moved, [(line + 1, column) for line, column in PLACES])
        marks = tool.full_run_marks("src/tiny.fs", moved, [(3, 12), (5, 13)], about, saved)
        self.assertTrue(marks[(3, 12)].startswith("also never run"))
        self.assertTrue(marks[(5, 13)].startswith("ran in the last full run"))
        self.assertEqual(tool.full_run_marks("src/other.fs", TINY, [(2, 12)], about, saved), {})


@unittest.skipUnless(HAS_COVERAGE, "needs Gforth 1.0 with coverage.fs")
class Cover(unittest.TestCase):
    def cover(self, root, baseline=None, saved=None, tests=("tests/tiny-test.fs",)):
        return tool.cover("src/tiny.fs", list(tests), GFORTH, root=root, jobs=2, baseline=baseline, saved=saved)

    def test_never_run_blocks_are_listed_against_the_baseline(self):
        with tempfile.TemporaryDirectory() as folder:
            root = tiny_tree(folder)
            base = {"files": {"src/tiny.fs": {"blocks": 9, "never_run": 2, "reason": "negative (line 2)"}}}
            status, lines = self.cover(root, base)
            text = "\n".join(lines)
            self.assertEqual(status, 0, text)
            self.assertIn("blocks 9, never run now 2; baseline 9 blocks, 2 never run", text)
            self.assertIn("src/tiny.fs:2:12 in tiny-sign: drop [char] - exit then", text)
            self.assertIn("src/tiny.fs:4:13 in tiny-never: 1 2 + drop ;", text)
            self.assertIn("baseline reason names line 2", text)
            self.assertIn("only unit tests ran", text)
            self.assertIn("no saved full run", text)

    def test_above_the_baseline_fails(self):
        with tempfile.TemporaryDirectory() as folder:
            root = tiny_tree(folder)
            status, lines = self.cover(root, {"files": {"src/tiny.fs": {"blocks": 9, "never_run": 1}}})
            self.assertEqual(status, 1)
            self.assertIn("ABOVE the baseline: 2 never-run blocks, the baseline allows 1", lines[-1])
            self.assertEqual(self.cover(root, None)[0], 1, "no entry allows none")

    def test_a_saved_full_run_marks_each_block(self):
        with tempfile.TemporaryDirectory() as folder:
            root = tiny_tree(folder)
            blocks = {("src/tiny.fs", line, column): 3 for line, column in PLACES}
            blocks[("src/tiny.fs", 2, 12)] = 0
            saved = tool.full_run_record(blocks, ["make", "test"], root)
            self.assertEqual(saved["files"]["src/tiny.fs"]["never_run"],
                             [[2, 12, "tiny-sign", "drop [char] - exit then"]])
            text = "\n".join(self.cover(root, None, saved)[1])
            self.assertIn("also never run in the last full run", text)
            self.assertIn("ran in the last full run]", text)

    def test_a_failing_test_fails_and_an_unloaded_file_is_named(self):
        with tempfile.TemporaryDirectory() as folder:
            root = tiny_tree(folder, "require ../src/tiny.fs\n1 throw\n")
            status, lines = self.cover(root, {"files": {"src/tiny.fs": {"blocks": 9, "never_run": 9}}})
            self.assertEqual(status, 1, "\n".join(lines))
            self.assertIn("FAILED", lines[-1])
        with tempfile.TemporaryDirectory() as folder:
            root = tiny_tree(folder, "1 drop bye\n")
            status, lines = self.cover(root)
            self.assertEqual(status, 2)
            self.assertIn("no test run loaded src/tiny.fs", lines[-1])

    def test_the_command_line_runs_named_tests(self):
        """make cover's command with TESTS on the real tree: a library file and its unit test."""
        result = subprocess.run([sys.executable, str(ROOT / "scripts/coverage.py"), "--gforth", GFORTH,
                                 "--file", "src/lib/sort.fs", "--tests", "tests/lib/sort.fs"],
                                cwd=ROOT, stdin=subprocess.DEVNULL, capture_output=True, text=True, timeout=300)
        self.assertIn(result.returncode, (0, 1), result.stdout + result.stderr)
        self.assertIn("cover src/lib/sort.fs: 1 unit test file(s)", result.stdout)
        self.assertRegex(result.stdout, r"blocks \d+, never run now \d+; baseline")


if __name__ == "__main__":
    unittest.main()
