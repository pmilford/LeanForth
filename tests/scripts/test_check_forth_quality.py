#!/usr/bin/env python3
"""Tests of scripts/check-forth-quality.py (make check-forth-quality): the ratchet flags growth in any counted
signal, a new file gets the strict allowance, the review log's ranges are parsed, and a check of today's tree holds."""
import importlib.util
import pathlib
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("cfq", ROOT / "scripts/check-forth-quality.py")
cfq = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cfq)

FILE = {"words": 100, "long words": 2, "shuffles": 10, "rstack": 40, "globals": 1, "long lines": 0}


class Ratchet(unittest.TestCase):
    def run_with(self, now, base):
        saved = cfq.counts, cfq.BASELINE.read_text
        cfq.counts = lambda: now
        try:
            import json
            original = cfq.json.loads
            cfq.json.loads = lambda _text: base
            try:
                return cfq.ratchet()
            finally:
                cfq.json.loads = original
        finally:
            cfq.counts = saved[0]

    def test_equal_counts_pass(self):
        self.assertEqual(self.run_with({"src/a.fs": dict(FILE)}, {"src/a.fs": dict(FILE)}), [])

    def test_each_signal_growing_fails(self):
        for key in ("long words", "shuffles", "rstack", "globals", "long lines"):
            grown = dict(FILE, **{key: FILE[key] + 1})
            problems = self.run_with({"src/a.fs": grown}, {"src/a.fs": dict(FILE)})
            self.assertEqual(len(problems), 1, key)
            self.assertIn(key, problems[0])

    def test_shrinking_passes(self):
        smaller = dict(FILE, shuffles=3, rstack=10)
        self.assertEqual(self.run_with({"src/a.fs": smaller}, {"src/a.fs": dict(FILE)}), [])

    def test_new_file_strict_allowance(self):
        clean = {"words": 20, "long words": 0, "shuffles": 3, "rstack": 10, "globals": 0, "long lines": 0}
        self.assertEqual(self.run_with({"src/new.fs": clean}, {}), [])
        for key, value in (("long words", 1), ("shuffles", 4), ("rstack", 11), ("globals", 1), ("long lines", 1)):
            problems = self.run_with({"src/new.fs": dict(clean, **{key: value})}, {})
            self.assertEqual(len(problems), 1, key)


class LogRanges(unittest.TestCase):
    def test_range_pattern(self):
        row = "| 2026-11-12 | `390197d..af64e27` | scope | reviewer | report | 0 | 0 |"
        self.assertEqual(cfq.RANGE.findall(row), [("390197d", "af64e27")])
        self.assertEqual(cfq.RANGE.findall("no range `abc..def` here"), [])


class Tree(unittest.TestCase):
    def test_todays_tree_holds_its_baseline(self):
        self.assertEqual(cfq.ratchet(), [])


if __name__ == "__main__":
    unittest.main()
