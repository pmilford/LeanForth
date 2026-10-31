"""Tests for the untrusted bounded development export preview."""

import io
import json
import os
from pathlib import Path
import subprocess
import sys
import unittest

sys.path.insert(0, str(Path("tests/support")))
from ndjson_preview import MAX_LINE, PreviewError, preview
from check_composition_fixture import fixture_nodes


class PreviewTests(unittest.TestCase):
    def setUp(self):
        self.raw = Path("tests/reference/composition.ndjson").read_bytes()
        self.lines = self.raw.decode().splitlines()

    def parse(self, lines):
        return preview(io.BytesIO(("\n".join(lines) + "\n").encode()))

    def alter(self, needle, change):
        lines = self.lines.copy()
        index = next(i for i, line in enumerate(lines) if needle in line)
        record = json.loads(lines[index])
        change(record)
        lines[index] = json.dumps(record)
        return lines

    def test_fixture_matches_independent_inspector(self):
        result = preview(io.BytesIO(self.raw))
        self.assertIs(result["checked"], False)
        self.assertEqual(result["declarations"][0]["type"], 10)
        self.assertEqual(result["declarations"][0]["value"], 20)
        nodes = []
        for node in result["expressions"]:
            tag = node["tag"]
            if tag == "sort":
                nodes.append((1, node["level"], 0))
            elif tag == "bvar":
                nodes.append((2, node["index"], 0))
            elif tag == "app":
                nodes.append((3, node["fn"], node["arg"]))
            else:
                nodes.append((4 if tag == "lam" else 5, node["type"], node["body"]))
        self.assertEqual(nodes, fixture_nodes(self.lines))
        # Feed decoded node data, never Forth source, into the existing probe.
        stream = bytes(value for index, node in enumerate(nodes) for value in (index, *node))
        result = subprocess.run([os.environ.get("GFORTH", "gforth"),
                                 "tests/core/load-fixture-stream.fs"],
                                input=stream, capture_output=True, check=True)
        rows = [tuple(map(int, line.split())) for line in result.stdout.splitlines()]
        self.assertEqual(rows, [(index, *node) for index, node in enumerate(nodes)])

    def test_other_declaration_name_is_not_hardcoded(self):
        lines = self.alter('"composition"', lambda r: r["str"].update(str="other"))
        self.assertEqual(self.parse(lines)["names"][1]["component"], "other")

    def test_bad_json_and_duplicate_keys_fail(self):
        for line in (b'{"x":', b'{"x":0,"x":1}', b'\xff', b'NaN'):
            with self.subTest(line=line), self.assertRaises(PreviewError):
                preview(io.BytesIO(line + b"\n"))

    def test_versions_and_unsupported_nodes(self):
        lines = self.alter('"meta"', lambda r: r["meta"]["format"].update(version="9"))
        with self.assertRaises(PreviewError) as raised:
            self.parse(lines)
        self.assertEqual(raised.exception.code, "LF_PREVIEW_UNSUPPORTED")
        lines = self.alter('"ie":0', lambda r: (r.pop("sort"), r.update(const={"name": 1})))
        with self.assertRaises(PreviewError) as raised:
            self.parse(lines)
        self.assertEqual(raised.exception.code, "LF_PREVIEW_UNSUPPORTED")
        lines = self.alter('"ie":0', lambda r: r.update(sort=1))
        with self.assertRaises(PreviewError) as raised:
            self.parse(lines)
        self.assertEqual(raised.exception.code, "LF_PREVIEW_UNSUPPORTED")

    def test_invalid_references_and_boolean_integers(self):
        mutations = [
            ('"ie":0', lambda r: r.update(sort=False)),
            ('"forallE"', lambda r: r["forallE"].update(body=r["ie"])),
            ('"forallE"', lambda r: r["forallE"].update(name=999)),
            ('"thm"', lambda r: r["thm"].update(value=999)),
        ]
        for needle, mutate in mutations:
            with self.subTest(needle=needle), self.assertRaises(PreviewError):
                self.parse(self.alter(needle, mutate))

    def test_limits_and_missing_declaration(self):
        with self.assertRaises(PreviewError) as raised:
            preview(io.BytesIO(b" " * (MAX_LINE + 1)))
        self.assertEqual(raised.exception.code, "LF_PREVIEW_LIMIT")
        with self.assertRaises(PreviewError):
            self.parse(self.lines[:-1])
        lines = [self.lines[0]] + [json.dumps({"ie": i, "sort": 0}) for i in range(65)]
        with self.assertRaises(PreviewError) as raised:
            self.parse(lines)
        self.assertEqual(raised.exception.code, "LF_PREVIEW_LIMIT")

    def test_cli_failure_has_no_partial_output(self):
        result = subprocess.run([sys.executable, "tests/support/ndjson_preview.py"],
                                input=self.raw + b"{\n", capture_output=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(result.stdout, b"")
        self.assertEqual(json.loads(result.stderr)["code"], "LF_PREVIEW_MALFORMED")

    def test_duplicate_resolved_names_fail(self):
        lines = self.lines + [
            json.dumps({"in": 13, "str": {"pre": 0, "str": "composition"}}),
            json.dumps({"thm": {"all": [13], "levelParams": [], "name": 13,
                                "type": 10, "value": 20}}),
        ]
        with self.assertRaises(PreviewError):
            self.parse(lines)

    def test_preview_does_not_claim_scope_or_typing(self):
        lines = self.alter('"thm"', lambda r: r["thm"].update(type=1))
        result = self.parse(lines)
        self.assertIs(result["checked"], False)
        self.assertEqual(result["expressions"][1], {"tag": "bvar", "index": 2})


if __name__ == "__main__":
    unittest.main()
