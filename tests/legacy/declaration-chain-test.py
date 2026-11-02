"""Private fixture experiment: conditional diagnostics, never theorem acceptance.

Run from the repository root with GFORTH selecting the pinned development host.
The stream consumes bounded integers as data; it never evaluates input as code.
Output rows are step, phase (1 pair / 2 candidate staging), status, index count.
Status 3 is unknown, including unresolved dependencies; it is not rejection.
Each operation internally verifies rollback of term, level and reference counts.
"""
import hashlib
import importlib.util
import os
from pathlib import Path
import struct
import subprocess
import unittest

spec = importlib.util.spec_from_file_location(
    "constant_fixture", "tests/core/constant-term-fixture-test.py")
fixture = importlib.util.module_from_spec(spec)
spec.loader.exec_module(fixture)


class DeclarationChain(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        raw = Path("tests/reference/constant-fixture.ndjson").read_bytes()
        if hashlib.sha256(raw).hexdigest() != (
                "b6444346ee56d77f6936fb1bdca389b25bc76330b146fb7612fb6fc5c1be0249"):
            raise RuntimeError("Unexpected constant fixture hash")
        encoded, _ = fixture.encode(raw)
        cls.data = struct.pack("<IIII", 50000, 50000, 50000, 50000) + encoded
        cls.start = len(cls.data) - 19 * 16

    def run_stream(self, data):
        result = subprocess.run(
            [os.environ.get("GFORTH", ".tools/gforth/bin/gforth"),
             "tests/legacy/declaration-chain-stream.fs"],
            input=data, capture_output=True)
        rows = [tuple(map(int, line.split())) for line in result.stdout.splitlines()]
        return result, rows

    def mutate(self, node, field, value):
        data = bytearray(self.data)
        struct.pack_into("<I", data, self.start + node * 16 + field * 4, value)
        return data

    def test_conditional_chain(self):
        result, rows = self.run_stream(self.data)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(rows, [(1, 1, 0, 0), (1, 2, 0, 1),
                                (2, 1, 0, 1), (2, 2, 0, 2),
                                (3, 1, 0, 2), (3, 2, 0, 3)])

    def test_bad_pairs_stop_without_staging(self):
        # Both are scoped, but inference currently reports unknown for these
        # ill-typed pairs. Never promote unknown to a rejection or a success.
        for node, expected in [(6, [(1, 1, 3, 0)]),
                               (9, [(1, 1, 0, 0), (1, 2, 0, 1),
                                    (2, 1, 3, 1)])]:
            with self.subTest(node=node):
                result, rows = self.run_stream(self.mutate(node, 3, 3 if node == 6 else 2))
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(rows, expected)

    def test_unavailable_dependencies_stop_at_current_step(self):
        prefix = [(1, 1, 0, 0), (1, 2, 0, 1)]
        # fixturePoly references itself, the later fixtureUse, or P (missing).
        for name in (5, 6, 7):
            with self.subTest(name=name):
                result, rows = self.run_stream(self.mutate(7, 2, name))
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(rows, prefix + [(2, 1, 3, 1)])
        # fixtureUse referencing itself stops only after two conditional stages.
        result, rows = self.run_stream(self.mutate(14, 2, 6))
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(rows, prefix + [(2, 1, 0, 1), (2, 2, 0, 2),
                                         (3, 1, 3, 2)])

    def test_corruption_fails_before_any_step(self):
        corruptions = [self.data[:-1], self.data + b"\0", self.data[:16] + b"bye\n" + self.data[20:],
                       self.mutate(8, 2, 8), self.mutate(7, 2, 99),
                       self.mutate(17, 2, 2), self.mutate(0, 1, 99)]
        for data in corruptions:
            with self.subTest(data=data[:12]):
                result, rows = self.run_stream(data)
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(rows, [])

    def test_exhaustion_stops_without_staging(self):
        pair_exhausted = bytearray(self.data)
        struct.pack_into("<I", pair_exhausted, 0, 0)
        result, rows = self.run_stream(pair_exhausted)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(rows, [(1, 1, 2, 0)])

        staging_exhausted = bytearray(self.data)
        struct.pack_into("<I", staging_exhausted, 4, 0)
        result, rows = self.run_stream(staging_exhausted)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(rows, [(1, 1, 0, 0), (1, 2, 2, 0)])

        later_staging_exhausted = bytearray(self.data)
        struct.pack_into("<I", later_staging_exhausted, 8, 0)
        result, rows = self.run_stream(later_staging_exhausted)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(rows, [(1, 1, 0, 0), (1, 2, 0, 1),
                                (2, 1, 0, 1), (2, 2, 2, 1)])


if __name__ == "__main__":
    unittest.main()
