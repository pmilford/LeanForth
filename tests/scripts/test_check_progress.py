#!/usr/bin/env python3
"""Tests of scripts/check-progress.py's stage-word rule (the range rules need git history; push.sh runs them)."""
import importlib.util
import pathlib
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("cp", ROOT / "scripts/check-progress.py")
cp = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cp)


class Stages(unittest.TestCase):
    def row(self, status, extra=""):
        return f"| 9.9.9 | **Status (2026-11-13): {status}.** text {extra} | x |"

    def test_stage_words_pass(self):
        for stage in cp.STAGES[:-1]:
            self.assertEqual(cp.stage_problems(self.row(stage)), [], stage)

    def test_unknown_word_fails(self):
        for word in ("implemented", "merged", "in progress", "complete"):
            self.assertEqual(len(cp.stage_problems(self.row(word))), 1, word)

    def test_done_needs_report(self):
        self.assertEqual(len(cp.stage_problems(self.row("done"))), 1)
        self.assertEqual(cp.stage_problems(self.row("done", "[check](../development/done-checks/x.md)")), [])

    def test_older_rows_are_checked_too(self):
        self.assertEqual(len(cp.stage_problems("| 1.1 | **Status (2026-11-05): implemented.** x |")), 1)
        self.assertEqual(cp.stage_problems("| 1.1 | **Status (2026-11-05): integrated (was \"implemented\").** x |"), [])

    def test_undated_status_is_checked(self):
        self.assertEqual(cp.stage_problems("| 8.2.1b | **Status: not started.** x |"), [])
        self.assertEqual(len(cp.stage_problems("| 8.2.1b | **Status: planned.** x |")), 1)

    def test_every_plan_row_uses_a_stage_word(self):
        self.assertEqual(cp.stage_problems((cp.ROOT / cp.PLAN).read_text(encoding="utf-8")), [])


class MathlibLine(unittest.TestCase):
    GOOD = ("**Mathlib checked:** 729,263 of 729,263 declarations accepted on build b74a04d "
            "(run record `.claude/work/overnight/full-b74a04d.txt`).")

    def test_good_line(self):
        self.assertEqual(cp.mathlib_problems("text\n" + self.GOOD + "\nmore"), [])

    def test_missing_line(self):
        self.assertEqual(len(cp.mathlib_problems("Mathlib is checked: 729,263 of 729,263, run record x.log")), 1)

    def test_no_denominator(self):
        text = "**Mathlib checked:** all declarations accepted (run record done-checks/x.md)."
        self.assertEqual(len(cp.mathlib_problems(text)), 1)

    def test_no_run_cited(self):
        self.assertEqual(len(cp.mathlib_problems("**Mathlib checked:** 5 of 6 accepted.")), 1)
        self.assertEqual(len(cp.mathlib_problems("**Mathlib checked:** 5 of 6 accepted, run record somewhere.")), 1)
        self.assertEqual(len(cp.mathlib_problems("**Mathlib checked:** 5 of 6 accepted, see x.log.")), 1)

    def test_nothing_cited_nor_counted(self):
        self.assertEqual(len(cp.mathlib_problems("**Mathlib checked:** most of it.")), 2)

    def test_real_progress_file(self):
        text = (cp.ROOT / cp.PROGRESS).read_text(encoding="utf-8")
        self.assertEqual(cp.mathlib_problems(text), [])


if __name__ == "__main__":
    unittest.main()
