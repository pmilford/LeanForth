#!/usr/bin/env python3
"""Run one part of tests/cli/test_leanforth.py, so make can run the parts at once (make test-cli).

Usage: python3 tests/cli/run_group.py N      (N = 1..4, or engines)

Parts 1-3 name their slow classes (measured 2026-11-12: MemoryPerCheck 36 s, Jobs 24 s, Imports 13 s on one core;
since the evening the slowest tests of MemoryPerCheck and Jobs run their cases two at a time, about half as long;
OlderSnapshots, the snapshots of older verdict versions, about 90 s, joined part 1 that night); part engines is
the Engines class, which compares gforth-fast with the checking engine and so is run again outside make
coverage (the Makefile's COVERAGE_ENGINE_DIFFERS; owner, 2026-11-14: every other part runs once);
part 4 runs every other class, so a new class always runs somewhere and nothing is skipped."""
import pathlib
import sys
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import test_leanforth as cli  # noqa: E402

PARTS = {
    1: ["MemoryPerCheck", "Progress", "Slice", "VerdictGuard", "OlderSnapshots"],
    2: ["Jobs", "TextJobs", "Fuel", "Resources"],
    3: ["Imports", "Snapshots", "Layers", "AsCopied"],
    "engines": ["Engines"],
}


def classes():
    return [v for v in vars(cli).values()
            if isinstance(v, type) and issubclass(v, unittest.TestCase) and v.__module__ == cli.__name__]


def part(n):
    named = {c for p in PARTS.values() for c in p}
    return [c for c in classes() if (c.__name__ in PARTS[n] if n in PARTS else c.__name__ not in named)]


if __name__ == "__main__":
    n = int(sys.argv[1]) if sys.argv[1].isdigit() else sys.argv[1]
    if n not in PARTS and n != 4:
        sys.exit(f"run_group: no part {n}")
    suite = unittest.TestSuite(unittest.defaultTestLoader.loadTestsFromTestCase(c) for c in part(n))
    result = unittest.TextTestRunner(verbosity=1).run(suite)
    sys.exit(0 if result.wasSuccessful() else 1)
