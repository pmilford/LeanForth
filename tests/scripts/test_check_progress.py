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

    def test_older_rows_exempt(self):
        self.assertEqual(cp.stage_problems("| 1.1 | **Status (2026-11-12): implemented.** x |"), [])


if __name__ == "__main__":
    unittest.main()
