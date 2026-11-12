#!/usr/bin/env python3
"""Run one part of tests/cli/test_leanforth.py, so make can run the parts at once (make test-cli).

Usage: python3 tests/cli/run_group.py N      (N = 1..4)

Parts 1-3 name their slow classes (measured 2026-11-12: MemoryPerCheck 36 s, Jobs 24 s, Imports 13 s on one core);
part 4 runs every other class, so a new class always runs somewhere and nothing is skipped."""
import pathlib
import sys
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import test_leanforth as cli  # noqa: E402

PARTS = {
    1: ["MemoryPerCheck", "Progress", "Slice", "VerdictGuard"],
    2: ["Jobs", "Engines", "Fuel", "Resources"],
    3: ["Imports", "Snapshots", "Layers", "AsCopied"],
}


def classes():
    return [v for v in vars(cli).values()
            if isinstance(v, type) and issubclass(v, unittest.TestCase) and v.__module__ == cli.__name__]


def part(n):
    named = {c for p in PARTS.values() for c in p}
    return [c for c in classes() if (c.__name__ in PARTS[n] if n in PARTS else c.__name__ not in named)]


if __name__ == "__main__":
    n = int(sys.argv[1])
    suite = unittest.TestSuite(unittest.defaultTestLoader.loadTestsFromTestCase(c) for c in part(n))
    result = unittest.TextTestRunner(verbosity=1).run(suite)
    sys.exit(0 if result.wasSuccessful() else 1)
