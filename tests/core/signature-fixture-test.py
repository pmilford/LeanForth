"""Fixture-to-raw-signature syntax differential; no import or proof check."""
import os
from pathlib import Path
import struct
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, "tests/core")
from test_tagged_poly_fixture import encode, FIXTURE

LEAN = os.environ.get("LEAN", "lean")
GFORTH = os.environ.get("GFORTH", "gforth")
REVISION = "eb6cafb7290e8bd5f2937522d8d804f58f02bafc"


def run_forth(data):
    return subprocess.run([GFORTH, "tests/core/signature-fixture-stream.fs"],
                          input=data, capture_output=True)


def shapes(output):
    lines = iter(output.decode().splitlines())
    results = []
    for expected in range(2):
        level, root, count = map(int, next(lines).split())
        if level != expected or not 0 <= root < count:
            raise ValueError("invalid output header")
        nodes = []
        for i in range(count):
            index, tag, a, b = map(int, next(lines).split())
            if index != i:
                raise ValueError("invalid node index")
            if tag == 6:
                shape = f"s{a}"
            elif tag == 2:
                shape = f"v{a}"
            elif tag in (3, 4, 5) and 0 <= a < i and 0 <= b < i:
                shape = f"{ {3: 'a', 4: 'l', 5: 'p'}[tag]}({nodes[a]},{nodes[b]})"
            else:
                raise ValueError("invalid node")
            nodes.append(shape)
        if "s-1" in nodes[root]:
            raise ValueError("unresolved universe in result")
        results.append(f"{level} {nodes[root]}")
    if next(lines, None) is not None:
        raise ValueError("unexpected output")
    return results


class SignatureFixture(unittest.TestCase):
    def test_differential_and_guards(self):
        version = subprocess.check_output([LEAN, "--version"], text=True)
        self.assertTrue(version.startswith("Lean (version 4.35.0,"), version)
        self.assertEqual(subprocess.check_output([LEAN, "--githash"], text=True).strip(), REVISION)
        data, _ = encode(FIXTURE.read_bytes())
        result = run_forth(data)
        self.assertEqual(result.returncode, 0, result.stderr.decode())
        with tempfile.TemporaryDirectory() as temp:
            subprocess.run([LEAN, "-o", str(Path(temp) / "LeanForthPolyIdentity.olean"),
                            "tests/reference/poly-identity.lean"], check=True)
            env = dict(os.environ, LEAN_PATH=temp)
            oracle = subprocess.check_output([LEAN, "tests/reference/signature-fixture.lean"],
                                             env=env, text=True).splitlines()
        self.assertEqual(len(oracle), 2)
        self.assertEqual(shapes(result.stdout), oracle)

    def test_bad_transport_fails_before_output(self):
        data, _ = encode(FIXTURE.read_bytes())
        broken = bytearray(data)
        struct.pack_into("<I", broken, 20, 99)
        for bad in (data[:12], data[:-1], data + b"\0", broken):
            with self.subTest(length=len(bad)):
                result = run_forth(bad)
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, b"")


if __name__ == "__main__":
    unittest.main()
