"""Untrusted fixture preview and bounded data staging; no declaration checking."""
import io
import os
from pathlib import Path
import struct
import subprocess
import sys
import unittest

sys.path.insert(0, "tests/support")
from ndjson_preview import PreviewError, preview

FIXTURE = Path("tests/reference/constant-fixture.ndjson")

def encode(raw):
    data = preview(io.BytesIO(raw))
    names, levels, nodes, decls = (data[k] for k in
        ("names", "levelExpressions", "expressions", "declarations"))
    if (len(names) != 9 or levels != [{"tag": "zero"}, {"tag": "param", "name": 2}]
        or [(d["kind"], d["type"], d["value"], d["levelParams"]) for d in decls]
        != [("def", 4, 6, [2]), ("def", 4, 11, [2]), ("thm", 13, 18, [])]
        or len(nodes) != 19):
        raise ValueError("unsupported fixture layout")
    if [n["component"] for n in names[1:]] != ["fixtureId", "u", "α", "x", "fixturePoly", "fixtureUse", "P", "h"]:
        raise ValueError("unexpected fixture names")
    fields = [8]
    for name in names[1:]:
        if name["kind"] != "str" or name["prefix"] != 0:
            raise ValueError("unsupported name")
        value = name["component"].encode("utf-8")
        if len(value) > 255:
            raise ValueError("name too long")
        fields.extend((len(value), *value))
    fields.append(len(nodes))
    expected = []
    for i, node in enumerate(nodes):
        tag = node["tag"]
        if tag == "sort": row = (1, node["levelIndex"], 0)
        elif tag == "bvar": row = (2, node["index"], 0)
        elif tag in ("app", "lam", "forallE"):
            row = ({"app": 3, "lam": 4, "forallE": 5}[tag],
                   node["fn"] if tag == "app" else node["type"],
                   node["arg"] if tag == "app" else node["body"])
        elif tag == "const" and len(node["us"]) == 1:
            row = (7, node["name"], node["us"][0])
        else: raise ValueError("unsupported node")
        fields.extend((i, *row))
        expected.append(row)
    return struct.pack("<" + "I" * len(fields), *fields), expected

def run(data):
    return subprocess.run([os.environ.get("GFORTH", "gforth"),
                           "tests/core/constant-term-fixture-stream.fs"],
                          input=data, capture_output=True)

class Fixture(unittest.TestCase):
    def test_staging(self):
        data, expected = encode(FIXTURE.read_bytes())
        self.assertEqual(expected, [(1, 1, 0), (2, 0, 0), (2, 1, 0),
            (5, 1, 2), (5, 0, 3), (4, 1, 1), (4, 0, 5),
            (7, 1, 1), (3, 7, 2), (3, 8, 1), (4, 1, 9),
            (4, 0, 10), (1, 0, 0), (5, 12, 3), (7, 1, 0),
            (3, 14, 2), (3, 15, 1), (4, 1, 16), (4, 12, 17)])
        result = run(data)
        self.assertEqual(result.returncode, 0, result.stderr)
        lines = result.stdout.splitlines()
        self.assertEqual(len(lines), 22)
        for i, row in enumerate(expected):
            actual = tuple(map(int, lines[i].split()))
            if row[0] == 7:
                # Constant payload is a live reference pair, checked by boundary.
                self.assertEqual(actual[:2], (i, 7))
                self.assertEqual(actual[2], (0 if i == 7 else 1))
                self.assertGreater(actual[3], 0)
            else:
                self.assertEqual(actual, (i, 6 if row[0] == 1 else row[0], *row[1:]))
        self.assertEqual([list(map(int, line.split())) for line in lines[19:21]], [[1, 1], [1, 0]])
        self.assertEqual(list(map(int, lines[-1].split())), [0] * 6)

    def test_invalid_input_fails_closed(self):
        raw = FIXTURE.read_bytes()
        for bad in (raw[:-5], raw.replace(b'"sort":1', b'"sort":99'),
                    raw.replace(b'"name":1,"us":[1]', b'"name":999,"us":[1]')):
            with self.assertRaises((PreviewError, ValueError)):
                encode(bad)
        data, _ = encode(raw)
        corruptions = [data[:-1], data + b'\0', b'\xff\xff\xff\xff' + data[4:]]
        start = len(data) - 19 * 16
        for offset, value in ((start, 1), (start + 4, 99),
                              (start + 7 * 16 + 8, 99),
                              (start + 7 * 16 + 12, 2),
                              (start + 8 * 16 + 8, 8)):
            changed = bytearray(data)
            struct.pack_into('<I', changed, offset, value)
            corruptions.append(changed)
        for bad in corruptions:
            result = run(bad)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, b'')

if __name__ == "__main__":
    unittest.main()
