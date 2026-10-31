"""Test-only integration of exported names and symbolic universe graphs."""
import io
import copy
import json
import os
from pathlib import Path
import subprocess
import sys
import unittest

sys.path.insert(0, "tests/support")
from ndjson_preview import preview


def encode_named_levels(decoded, context, left, right):
    """Build bounded test data, retaining export indices for Forth to map."""
    names = decoded["names"]
    levels = decoded["levelExpressions"]
    if decoded.get("checked") is not False:
        raise ValueError("expected unchecked preview data")

    def byte(value):
        if type(value) is not int or not 0 <= value <= 255:
            raise ValueError("field outside byte range")
        return value

    if not 1 <= len(names) <= 64 or not 1 <= len(levels) <= 64 or len(context) > 64:
        raise ValueError("test transport limit exceeded")
    for value in (left, right, *context):
        byte(value)
    data = bytearray((len(names), len(levels), len(context), left, right))
    for index, name in enumerate(names[1:], start=1):
        if not isinstance(name, dict) or set(name) != {"kind", "prefix", "component"}:
            raise ValueError("ambiguous name record")
        component = name["component"]
        prefix = byte(name["prefix"])
        if prefix >= index:
            raise ValueError("forward name prefix")
        if name["kind"] == "str" and isinstance(component, str):
            component = component.encode("utf-8")
            data.extend((index, 1, prefix, byte(len(component))))
            data.extend(component)
        elif name["kind"] == "num":
            data.extend((index, 2, prefix, byte(component)))
        else:
            raise ValueError("unsupported name kind")
    tags = {"zero": 0, "succ": 1, "max": 2, "imax": 3, "param": 4}
    for index, level in enumerate(levels):
        kind = level["tag"]
        keys = {"zero": {"tag"}, "succ": {"tag", "of"}, "param": {"tag", "name"},
                "max": {"tag", "left", "right"}, "imax": {"tag", "left", "right"}}
        if kind not in keys or set(level) != keys[kind]:
            raise ValueError("unsupported or ambiguous level record")
        if kind == "zero":
            if index != 0:
                raise ValueError("unexpected zero level")
            first, second = 0, 0
        elif kind == "param":
            first, second = byte(level["name"]), 0
            if not 0 < first < len(names):
                raise ValueError("invalid parameter name")
        elif kind == "succ":
            first, second = byte(level["of"]), 0
            if first >= index:
                raise ValueError("forward universe reference")
        else:
            first, second = byte(level["left"]), byte(level["right"])
            if first >= index or second >= index:
                raise ValueError("forward universe reference")
        data.extend((index, tags[kind], first, second))
    data.extend(context)
    return data


class NamedLevelTests(unittest.TestCase):
    def setUp(self):
        lines = Path("tests/reference/poly-identity.ndjson").read_text().splitlines()
        lines.insert(-1, '{"in":12,"str":{"pre":0,"str":"u"}}')
        lines.insert(-1, '{"in":13,"str":{"pre":0,"str":"v"}}')
        lines.insert(-1, '{"il":2,"param":12}')
        lines.insert(-1, '{"il":3,"param":13}')
        lines.insert(-1, '{"in":14,"str":{"pre":2,"str":"leaf"}}')
        lines.insert(-1, '{"in":15,"str":{"pre":12,"str":"leaf"}}')
        lines.insert(-1, '{"il":4,"param":14}')
        lines.insert(-1, '{"il":5,"param":15}')
        theorem = json.loads(lines[-1])
        theorem["thm"]["levelParams"] = [12]  # Alias of the reachable param at index 2.
        lines[-1] = json.dumps(theorem)
        self.decoded = preview(io.BytesIO(("\n".join(lines) + "\n").encode()))
        self.command = [os.environ.get("GFORTH", "gforth"), "tests/core/named-level-stream.fs"]

    def run_stream(self, context, left, right):
        stream = encode_named_levels(self.decoded, context, left, right)
        result = subprocess.run(self.command, input=stream, capture_output=True, check=True)
        lines = result.stdout.splitlines()
        status = int(lines[0])
        names = dict(tuple(map(int, line.split())) for line in lines[1:])
        return status, names

    def test_equal_aliases_and_different_names(self):
        context = self.decoded["declarations"][0]["levelParams"]
        status, mapping = self.run_stream(context, 1, 2)
        self.assertEqual(status, 0)
        self.assertEqual(mapping[2], mapping[12])
        self.assertNotEqual(mapping[2], mapping[13])
        status, _ = self.run_stream([12, 13], 1, 3)
        self.assertEqual(status, 3)  # Unknown is not an inequality judgment.
        status, mapping = self.run_stream([14], 4, 5)
        self.assertEqual(status, 0)
        self.assertEqual(mapping[14], mapping[15])

    def test_unbound_and_duplicate_context_fail(self):
        status, _ = self.run_stream([], 1, 2)
        self.assertEqual(status, 1)
        data = encode_named_levels(self.decoded, [2, 12], 1, 2)
        result = subprocess.run(self.command, input=data, capture_output=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(result.stdout.strip(), b"")

    def test_malformed_stream_fails_without_partial_result(self):
        data = encode_named_levels(self.decoded, [12, 13], 1, 2)
        for bad in (data[:4], data[:-1], data + b"\0"):
            with self.subTest(length=len(bad)):
                result = subprocess.run(self.command, input=bad, capture_output=True)
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout.strip(), b"")

    def test_forged_ambiguous_level_fields_are_rejected(self):
        for change in ({"of": 13}, {"name": True}, {"name": 999}):
            decoded = copy.deepcopy(self.decoded)
            decoded["levelExpressions"][1].update(change)
            with self.subTest(change=change), self.assertRaises(ValueError):
                encode_named_levels(decoded, [12, 13], 1, 2)

    def test_disconnected_unscoped_level_is_not_a_root_judgment(self):
        # The stream compares selected roots, not every stored level record.
        status, _ = self.run_stream([], 0, 0)
        self.assertEqual(status, 0)


if __name__ == "__main__":
    unittest.main()
