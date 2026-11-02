"""Test-only Lean-export staging; no declaration or proof is checked."""
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


class ContextConstantFixture(unittest.TestCase):
    def test_fixture_application_under_binders(self):
        data, _ = fixture.encode(Path("tests/reference/constant-fixture.ndjson").read_bytes())
        result = subprocess.run(
            [os.environ.get("GFORTH", "gforth"), "tests/legacy/context-constant-fixture-stream.fs"],
            input=data, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stderr.decode())
        self.assertEqual(result.stdout.strip(), b"2 1")

    def test_truncated_or_extra_input_fails_without_output(self):
        data, _ = fixture.encode(Path("tests/reference/constant-fixture.ndjson").read_bytes())
        changed = bytearray(data)
        node_start = len(data) - 19 * 16
        # Node 9's argument changes from x (#0) to A (#1), preserving valid
        # backwards references but changing the exported application.
        struct.pack_into("<I", changed, node_start + 9 * 16 + 12, 2)
        changed_value = bytearray(data)
        # Replace fixtureId's lambda body with an earlier, valid Pi node.
        struct.pack_into("<I", changed_value, node_start + 6 * 16 + 12, 3)
        for bad in (data[:-1], data + b"\x00", changed_value):
            with self.subTest(size=len(bad)):
                result = subprocess.run(
                    [os.environ.get("GFORTH", "gforth"), "tests/legacy/context-constant-fixture-stream.fs"],
                    input=bad, capture_output=True)
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout.strip(), b"")
        result = subprocess.run(
            [os.environ.get("GFORTH", "gforth"), "tests/legacy/context-constant-fixture-stream.fs"],
            input=changed, capture_output=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(result.stdout.strip(), b"")
        self.assertIn(b"definition pair inconclusive", result.stderr)

    def test_unscoped_theorem_annotation_is_rejected(self):
        data, _ = fixture.encode(Path("tests/reference/constant-fixture.ndjson").read_bytes())
        changed = bytearray(data)
        node_start = len(data) - 19 * 16
        # Node 17 is nested under one lambda. Make its domain refer to #1,
        # which is a valid earlier node but escapes the available binder.
        # The other fixture link checks do not inspect node 17.
        struct.pack_into("<I", changed, node_start + 17 * 16 + 8, 2)
        result = subprocess.run(
            [os.environ.get("GFORTH", "gforth"), "tests/legacy/context-constant-fixture-stream.fs"],
            input=changed, capture_output=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(result.stdout.strip(), b"")

    def test_wrong_theorem_argument_is_rejected(self):
        data, _ = fixture.encode(Path("tests/reference/constant-fixture.ndjson").read_bytes())
        changed = bytearray(data)
        node_start = len(data) - 19 * 16
        # Use P instead of h as the second argument to fixtureId. Both are
        # in scope and reference earlier nodes, but their types differ.
        struct.pack_into("<I", changed, node_start + 16 * 16 + 12, 2)
        result = subprocess.run(
            [os.environ.get("GFORTH", "gforth"), "tests/legacy/context-constant-fixture-stream.fs"],
            input=changed, capture_output=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(result.stdout.strip(), b"")
        self.assertIn(b"theorem pair inconclusive", result.stderr)

    def test_theorem_body_must_match_exported_application(self):
        data, _ = fixture.encode(Path("tests/reference/constant-fixture.ndjson").read_bytes())
        changed = bytearray(data)
        node_start = len(data) - 19 * 16
        # Replacing fixtureId's application by h is still well-typed but is
        # not the exported graph this test claims to exercise.
        struct.pack_into("<I", changed, node_start + 17 * 16 + 12, 1)
        result = subprocess.run(
            [os.environ.get("GFORTH", "gforth"), "tests/legacy/context-constant-fixture-stream.fs"],
            input=changed, capture_output=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(result.stdout.strip(), b"")


if __name__ == "__main__":
    unittest.main()
