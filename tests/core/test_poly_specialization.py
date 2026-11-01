"""End-to-end test of untrusted specialization of one Lean export fixture."""
import io
import json
import os
from pathlib import Path
import struct
import subprocess
import sys
import unittest

sys.path.insert(0, "tests/support")
from ndjson_preview import preview


def specialization_stream(decoded, assignments, value_override=None):
    """Encode fixture data and explicit assignments; never generate Forth code."""
    if decoded.get("checked") is not False:
        raise ValueError("expected unchecked preview data")
    declaration = decoded["declarations"][0]
    if declaration.get("kind") != "thm":
        raise ValueError("only theorem fixtures are supported by this transport")
    context = declaration["levelParams"]
    levels = decoded["levelExpressions"]
    expressions = decoded["expressions"]
    # Normalize equivalent structured Lean names to the same opaque context ID.
    name_keys = [()]
    for name in decoded["names"][1:]:
        name_keys.append(name_keys[name["prefix"]] + ((name["kind"], name["component"]),))
    context_ids = {name_keys[index]: index for index in context}
    if len(context_ids) != len(context):
        raise ValueError("duplicate structured universe parameter")
    value = declaration["value"] if value_override is None else value_override
    fields = [len(levels), len(expressions), declaration["type"], value,
              len(context), len(assignments), *context]
    level_tags = {"zero": 0, "succ": 1, "max": 2, "imax": 3, "param": 4}
    for index, node in enumerate(levels):
        tag = node["tag"]
        first = node.get("of", node.get("name", node.get("left", 0)))
        if tag == "param":
            if name_keys[first] not in context_ids:
                raise ValueError("unlisted universe parameter")
            first = context_ids[name_keys[first]]
        fields.extend((index, level_tags[tag], first, node.get("right", 0)))
    for name, value in assignments:
        fields.extend((name, value))
    for index, node in enumerate(expressions):
        tag = node["tag"]
        if tag == "sort":
            row = (1, node["levelIndex"], 0)
        elif tag == "bvar":
            row = (2, node["index"], 0)
        elif tag == "app":
            row = (3, node["fn"], node["arg"])
        elif tag in ("lam", "forallE"):
            row = (4 if tag == "lam" else 5, node["type"], node["body"])
        else:
            raise ValueError("unsupported expression kind")
        fields.extend((index, *row))
    return struct.pack(f"<{len(fields)}I", *fields)


class SpecializationTests(unittest.TestCase):
    def setUp(self):
        raw = Path("tests/reference/poly-identity.ndjson").read_bytes()
        self.decoded = preview(io.BytesIO(raw))
        self.command = [os.environ.get("GFORTH", "gforth"),
                        "tests/core/specialize-fixture-stream.fs"]

    def test_four_explicit_instances(self):
        self.assertIs(self.decoded["checked"], False)
        self.assertEqual(self.decoded["declarations"][0]["levelParams"], [2])
        for level in range(4):
            with self.subTest(level=level):
                data = specialization_stream(self.decoded, [(2, level)])
                result = subprocess.run(self.command, input=data, capture_output=True, check=True)
                rows = result.stdout.splitlines()
                self.assertEqual(rows[0].split(), [b"0"])
                self.assertEqual(tuple(map(int, rows[1].split())), (0, 1, level, 0))
                self.assertEqual(tuple(map(int, rows[3].split())), (2, 1, 0, 0))
                if level == 1:
                    # An independent Lean export of the same Type-level theorem
                    # supplies the complete expected concrete expression DAG.
                    other = preview(io.BytesIO(Path("tests/reference/type-identity.ndjson").read_bytes()))
                    expected = []
                    for index, node in enumerate(other["expressions"]):
                        tag = node["tag"]
                        if tag == "sort":
                            fields = (1, node["level"], 0)
                        elif tag == "bvar":
                            fields = (2, node["index"], 0)
                        elif tag == "app":
                            fields = (3, node["fn"], node["arg"])
                        else:
                            fields = (4 if tag == "lam" else 5, node["type"], node["body"])
                        expected.append((index, *fields))
                    self.assertEqual([tuple(map(int, row.split())) for row in rows[1:]], expected)

    def test_incomplete_duplicate_and_wrong_value_fail_closed(self):
        for assignments in ([], [(2, 0), (2, 1)], [(3, 0)]):
            with self.subTest(assignments=assignments):
                result = subprocess.run(self.command,
                                        input=specialization_stream(self.decoded, assignments),
                                        capture_output=True)
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout.strip(), b"")
        claim = self.decoded["declarations"][0]["type"]
        result = subprocess.run(self.command,
                                input=specialization_stream(self.decoded, [(2, 1)], claim),
                                capture_output=True, check=True)
        self.assertNotEqual(result.stdout.splitlines()[0].split(), [b"0"])

    def test_forged_tag_and_unused_unassigned_parameter_fail(self):
        self.decoded["expressions"][3]["tag"] = "const"
        with self.assertRaises(ValueError):
            specialization_stream(self.decoded, [(2, 1)])
        self.decoded = preview(io.BytesIO(Path("tests/reference/poly-identity.ndjson").read_bytes()))
        self.decoded["declarations"][0]["levelParams"] = [2, 3]
        result = subprocess.run(self.command,
                                input=specialization_stream(self.decoded, [(2, 1)]),
                                capture_output=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(result.stdout.strip(), b"")

    def test_equivalent_name_indices_share_assignment(self):
        lines = Path("tests/reference/poly-identity.ndjson").read_text().splitlines()
        lines.insert(-1, '{"in":12,"str":{"pre":0,"str":"u"}}')
        record = json.loads(lines[-1])
        record["thm"]["levelParams"] = [12]
        lines[-1] = json.dumps(record)
        decoded = preview(io.BytesIO(("\n".join(lines) + "\n").encode()))
        result = subprocess.run(self.command, input=specialization_stream(decoded, [(12, 1)]),
                                capture_output=True, check=True)
        self.assertEqual(result.stdout.splitlines()[0].split(), [b"0"])

    def test_truncation_and_trailing_data_fail_without_status(self):
        data = specialization_stream(self.decoded, [(2, 1)])
        # First sort's level index occurs after the six-field header, one
        # context ID, two level rows, one assignment pair, index and tag.
        invalid_level = bytearray(data)
        struct.pack_into("<I", invalid_level, 76, 2)
        for bad in (data[:2], data[:-1], data + b"\0", invalid_level):
            with self.subTest(length=len(bad)):
                result = subprocess.run(self.command, input=bad, capture_output=True)
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout.strip(), b"")


if __name__ == "__main__":
    unittest.main()
