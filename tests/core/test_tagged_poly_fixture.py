"""Untrusted fixture staging and declaration diagnostics; no theorem acceptance."""
import io
import json
import os
from pathlib import Path
import struct
import subprocess
import sys
import unittest

sys.path.insert(0, "tests/support")
from ndjson_preview import PreviewError, preview

FIXTURE = Path("tests/reference/poly-identity.ndjson")
COMMAND = [os.environ.get("GFORTH", "gforth"), "tests/core/tagged-poly-fixture-stream.fs"]


def encode(raw):
    decoded = preview(io.BytesIO(raw))
    declarations = decoded["declarations"]
    if (len(declarations) != 1 or declarations[0].get("kind") != "thm"
            or len(declarations[0]["levelParams"]) != 1):
        raise ValueError("expected one declaration and one parameter")
    parameter = declarations[0]["levelParams"][0]
    levels = decoded["levelExpressions"]
    # The narrow transport intentionally supports only zero and this parameter.
    if levels != [{"tag": "zero"}, {"tag": "param", "name": parameter}]:
        raise ValueError("unsupported level graph")
    nodes = []
    for node in decoded["expressions"]:
        tag = node["tag"]
        if tag == "sort":
            fields = (1, node["levelIndex"], 0)
        elif tag == "bvar":
            fields = (2, node["index"], 0)
        elif tag == "app":
            fields = (3, node["fn"], node["arg"])
        elif tag in ("lam", "forallE"):
            fields = (4 if tag == "lam" else 5, node["type"], node["body"])
        else:
            raise ValueError("unsupported expression kind")
        nodes.append(fields)
    decl = declarations[0]
    values = [len(nodes), decl["type"], decl["value"], parameter]
    for index, fields in enumerate(nodes):
        values.extend((index, *fields))
    return struct.pack("<" + "I" * len(values), *values), nodes


def run(data):
    return subprocess.run(COMMAND, input=data, capture_output=True)


class TaggedPolyFixtureTests(unittest.TestCase):
    def test_preview_and_transport_encoding(self):
        data, nodes = encode(FIXTURE.read_bytes())
        self.assertEqual(struct.unpack_from("<IIII", data), (16, 11, 15, 2))
        self.assertEqual(nodes[0], (1, 1, 0))
        self.assertEqual(nodes[2], (1, 0, 0))
        self.assertEqual(len(data), 16 + 16 * len(nodes))

    def test_preview_rejects_mutated_input(self):
        raw = FIXTURE.read_bytes()
        for bad in (raw[:-5], b"\n".join(raw.splitlines()[:-1]) + b"\n",
                    raw.replace(b'"sort":1', b'"sort":99'),
                    raw.replace(b'"levelParams":[2]', b'"levelParams":[]')):
            with self.subTest(bad=bad[-40:]), self.assertRaises(PreviewError):
                encode(bad)

    def test_fixture_stages_all_nodes_and_checks_roots(self):
        data, nodes = encode(FIXTURE.read_bytes())
        result = run(data)
        self.assertEqual(result.returncode, 0, result.stderr)
        rows = result.stdout.splitlines()
        self.assertEqual(list(map(int, rows[0].split())), [0, 0])
        staged = [tuple(map(int, row.split())) for row in rows[1:-1]]
        # Sorts have the distinct symbolic tag and refer to their level slots.
        expected = [(i, 6 if tag == 1 else tag, a, b)
                    for i, (tag, a, b) in enumerate(nodes)]
        self.assertEqual(staged, expected)
        self.assertEqual(len(nodes), 16)
        statuses = list(map(int, rows[-1].split()))
        self.assertEqual(statuses, [0, 0, 0])

    def test_untrusted_ndjson_mutations_fail(self):
        raw = FIXTURE.read_bytes()
        lines = raw.splitlines()
        for bad in (raw[:-5], b"\n".join(lines[:-1]) + b"\n",
                    raw.replace(b'"sort":1', b'"sort":99'),
                    raw.replace(b'"levelParams":[2]', b'"levelParams":[]')):
            with self.subTest(bad=bad[-40:]), self.assertRaises(PreviewError):
                encode(bad)
        changed = json.loads(lines[-1])
        changed["thm"]["value"] = 11
        lines[-1] = json.dumps(changed).encode()
        data, _ = encode(b"\n".join(lines) + b"\n")
        result = run(data)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(list(map(int, result.stdout.splitlines()[0].split())), [0, 0])
        statuses = list(map(int, result.stdout.splitlines()[-1].split()))
        self.assertNotEqual(statuses[-1], 0)

        # A well-formed but wrong declared type must not produce a positive
        # diagnostic. Transport fields are little-endian test data, not code.
        data, _ = encode(FIXTURE.read_bytes())
        changed_claim = bytearray(data)
        struct.pack_into("<I", changed_claim, 4, 0)
        result = run(changed_claim)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertNotEqual(int(result.stdout.splitlines()[-1].split()[-1]), 0)

    def test_transport_rejects_bad_and_truncated_data_without_output(self):
        data, _ = encode(FIXTURE.read_bytes())
        corruptions = [data + b"\x00", data[:12], data[:-1]]
        for offset, value in ((0, 0), (4, 99), (12, 0), (16, 1),
                              (20, 99), (24, 2), (28, 1)):
            changed = bytearray(data)
            struct.pack_into("<I", changed, offset, value)
            corruptions.append(changed)
        for bad in corruptions:
            with self.subTest(length=len(bad), prefix=bad[:32]):
                result = run(bad)
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout.strip(), b"")


if __name__ == "__main__":
    unittest.main()
