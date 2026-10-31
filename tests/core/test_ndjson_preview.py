"""Tests for the untrusted bounded development export preview."""

import io
import json
import os
from pathlib import Path
import subprocess
import struct
import sys
import unittest

sys.path.insert(0, str(Path("tests/support")))
from ndjson_preview import MAX_LINE, PreviewError, preview
from fixture_transport import encode_concrete
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
        self.assertEqual(raised.exception.code, "LF_PREVIEW_MALFORMED")

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

    def test_universe_indices_resolve_successors_not_index_numbers(self):
        lines = self.lines.copy()
        position = next(i for i, line in enumerate(lines) if '"ie":0' in line)
        lines[position:position] = [
            '{"il":1,"succ":0}', '{"il":2,"succ":0}', '{"il":3,"succ":1}',
        ]
        lines[position + 3] = '{"ie":0,"sort":2}'
        result = self.parse(lines)
        self.assertEqual(result["levels"], [0, 1, 1, 2])
        self.assertEqual(result["expressions"][0]["level"], 1)
        self.assertEqual(result["expressions"][0]["levelIndex"], 2)

    def test_invalid_and_unsupported_universe_records(self):
        position = next(i for i, line in enumerate(self.lines) if '"ie":0' in line)
        for record in ('{"il":1,"succ":1}', '{"il":2,"succ":0}',
                       '{"il":1,"succ":true}'):
            lines = self.lines.copy()
            lines.insert(position, record)
            with self.subTest(record=record), self.assertRaises(PreviewError):
                self.parse(lines)
        lines = self.lines.copy()
        lines.insert(position, '{"il":1,"mvar":1}')
        with self.assertRaises(PreviewError) as raised:
            self.parse(lines)
        self.assertEqual(raised.exception.code, "LF_PREVIEW_UNSUPPORTED")
        # Exactly 256 successor records are allowed by the preview.
        lines = self.lines.copy()
        levels = [json.dumps({"il": i, "succ": i - 1}) for i in range(1, 257)]
        lines[position:position] = levels
        lines[position + len(levels)] = '{"ie":0,"sort":256}'
        self.assertEqual(self.parse(lines)["expressions"][0]["level"], 256)
        lines = [self.lines[0]] + [json.dumps({"il": i, "succ": i - 1})
                                   for i in range(1, 258)]
        with self.assertRaises(PreviewError) as raised:
            self.parse(lines)
        self.assertEqual(raised.exception.code, "LF_PREVIEW_LIMIT")

    def test_concrete_max_imax_and_malformed_pairs(self):
        position = next(i for i, line in enumerate(self.lines) if '"ie":0' in line)
        lines = self.lines.copy()
        lines[position:position] = [
            '{"il":1,"succ":0}', '{"il":2,"succ":1}',
            '{"il":3,"max":[1,2]}', '{"il":4,"imax":[2,0]}',
            '{"il":5,"imax":[1,2]}',
        ]
        self.assertEqual(self.parse(lines)["levels"], [0, 1, 2, 2, 0, 2])
        for kind in ("max", "imax"):
            for value in ([], [0], [0, 0, 0], [True, 0], [0, 1], "bad"):
                lines = self.lines.copy()
                lines.insert(position, json.dumps({"il": 1, kind: value}))
                with self.subTest(kind=kind, value=value), self.assertRaises(PreviewError):
                    self.parse(lines)

    def test_nested_universe_sorts_reach_forth(self):
        raw = Path("tests/reference/identity.ndjson").read_text().splitlines()
        position = next(i for i, line in enumerate(raw) if '"thm"' in line)
        raw[position:position] = [
            '{"il":1,"succ":0}', '{"il":2,"succ":1}',
            '{"il":3,"imax":[2,0]}', '{"il":4,"max":[3,1]}',
            '{"il":5,"imax":[2,3]}', '{"ie":7,"sort":5}',
            '{"ie":8,"sort":4}',
        ]
        decoded = self.parse(raw)
        self.assertEqual(decoded["levels"], [0, 1, 2, 0, 1, 0])
        nodes = [(1, 0, 0), (2, 0, 0), (2, 1, 0), (5, 1, 2),
                 (5, 0, 3), (4, 1, 1), (4, 0, 5)]
        nodes += [(1, node["level"], 0) for node in decoded["expressions"][-2:]]
        stream = bytearray(struct.pack("<III", len(nodes), 4, 6))
        for index, fields in enumerate(nodes):
            stream.extend(struct.pack("<IIII", index, *fields))
        command = [os.environ.get("GFORTH", "gforth"), "tests/core/load-declaration-stream.fs"]
        result = subprocess.run(command, input=stream, capture_output=True, check=True)
        rows = result.stdout.splitlines()
        self.assertEqual(rows[0].split(), [b"0"])
        self.assertEqual(tuple(map(int, rows[-2].split())), (7, 1, 0, 0))
        self.assertEqual(tuple(map(int, rows[-1].split())), (8, 1, 1, 0))

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

    def test_exported_names_intern_with_structured_aliases(self):
        lines = self.lines.copy()
        lines.insert(-1, '{"in":13,"str":{"pre":0,"str":"composition"}}')
        lines.insert(-1, '{"in":14,"str":{"pre":1,"str":"leaf"}}')
        lines.insert(-1, '{"in":15,"str":{"pre":13,"str":"leaf"}}')
        result = self.parse(lines)
        names = result["names"]
        stream = bytearray((len(names) - 1,))
        keys = [()]
        expected = [0]
        interned = {(): 0}
        for index, name in enumerate(names[1:], start=1):
            component = name["component"]
            prefix = name["prefix"]
            kind = name["kind"]
            key = keys[prefix] + ((kind, component),)
            keys.append(key)
            if key not in interned:
                interned[key] = len(interned)
            expected.append(interned[key])
            if kind == "str":
                encoded = component.encode("utf-8")
                stream.extend((index, 1, prefix, len(encoded)))
                stream.extend(encoded)
            else:
                stream.extend((index, 2, prefix, component))
        command = [os.environ.get("GFORTH", "gforth"), "tests/core/name-fixture-stream.fs"]
        output = subprocess.run(command, input=stream, capture_output=True, check=True).stdout
        rows = [tuple(map(int, line.split())) for line in output.splitlines()]
        self.assertEqual(rows, list(enumerate(expected)))
        self.assertEqual(expected[1], expected[13])
        self.assertEqual(expected[14], expected[15])
        for bad in (stream[:-1], stream + b"\0", bytes((1, 1, 1, 1, 1, 65))):
            failed = subprocess.run(command, input=bad, capture_output=True)
            self.assertNotEqual(failed.returncode, 0)
            self.assertEqual(failed.stdout.strip(), b"")

    def test_preview_does_not_claim_scope_or_typing(self):
        lines = self.alter('"thm"', lambda r: r["thm"].update(type=1))
        result = self.parse(lines)
        self.assertIs(result["checked"], False)
        self.assertEqual(result["expressions"][1], {"tag": "bvar", "index": 2})

    def test_polymorphic_export_is_preserved_but_not_forth_concrete(self):
        raw = Path("tests/reference/poly-identity.ndjson").read_bytes()
        result = preview(io.BytesIO(raw))
        self.assertIs(result["checked"], False)
        self.assertIs(result["concreteLevelDataOnly"], False)
        self.assertEqual(result["levels"], [0, None])
        self.assertEqual(result["levelExpressions"][1], {"tag": "param", "name": 2})
        self.assertEqual(result["declarations"][0]["levelParams"], [2])
        self.assertEqual(result["expressions"][0]["levelIndex"], 1)
        self.assertIsNone(result["expressions"][0]["level"])
        with self.assertRaises(ValueError):
            encode_concrete(result)
        result["concreteLevelDataOnly"] = True  # A forged flag is insufficient.
        result["expressions"][0]["level"] = 0
        with self.assertRaises(ValueError):
            encode_concrete(result)
        result["declarations"][0]["levelParams"] = []
        with self.assertRaises(ValueError):
            encode_concrete(result)  # The symbolic graph is still present.

    def test_symbolic_universe_graph_stages_in_forth(self):
        raw = Path("tests/reference/poly-identity.ndjson").read_text().splitlines()
        position = next(i for i, line in enumerate(raw) if '"ie":0' in line)
        raw[position:position] = [
            '{"il":2,"succ":1}', '{"il":3,"max":[0,2]}',
            '{"il":4,"imax":[3,1]}',
        ]
        result = self.parse(raw)
        expected = [(0, 0, 0, 0), (1, 4, 2, 0), (2, 1, 1, 0),
                    (3, 2, 0, 2), (4, 3, 3, 1)]
        graph = result["levelExpressions"]
        tags = {"zero": 0, "succ": 1, "max": 2, "imax": 3, "param": 4}
        rows = []
        for index, node in enumerate(graph):
            tag = node["tag"]
            first = node.get("of", node.get("name", node.get("left", 0)))
            rows.append((index, tags[tag], first, node.get("right", 0)))
        self.assertEqual(rows, expected)
        context = result["declarations"][0]["levelParams"]
        stream = bytes([len(rows), len(context), *context] + [value for row in rows for value in row])
        command = [os.environ.get("GFORTH", "gforth"), "tests/core/level-fixture-stream.fs"]
        output = subprocess.run(command, input=stream, capture_output=True, check=True).stdout
        self.assertEqual([tuple(map(int, line.split())) for line in output.splitlines()], expected)
        wrong_context = bytearray(stream)
        wrong_context[2] = 3
        for bad in (stream[:-1], stream + b"\x00", bytes((1, 0, 0, 4, 2, 0)), wrong_context):
            result = subprocess.run(command, input=bad, capture_output=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout.strip(), b"")

    def test_concrete_transport_rejects_inconsistent_sort_level(self):
        result = preview(io.BytesIO(Path("tests/reference/type-identity.ndjson").read_bytes()))
        result["expressions"][0]["level"] = 0
        with self.assertRaises(ValueError):
            encode_concrete(result)

    def test_symbolic_levels_remain_symbolic_and_keep_their_structure(self):
        raw = Path("tests/reference/poly-identity.ndjson").read_text().splitlines()
        position = next(i for i, line in enumerate(raw) if '"ie":0' in line)
        raw[position:position] = [
            '{"il":2,"succ":1}', '{"il":3,"max":[0,2]}',
            '{"il":4,"imax":[3,0]}',
        ]
        result = self.parse(raw)
        self.assertEqual(result["levels"], [0, None, None, None, None])
        self.assertEqual(result["levelExpressions"][4], {"tag": "imax", "left": 3, "right": 0})
        self.assertIs(result["concreteLevelDataOnly"], False)

    def test_invalid_symbolic_parameter_references_fail(self):
        raw = Path("tests/reference/poly-identity.ndjson").read_text().splitlines()
        position = next(i for i, line in enumerate(raw) if '"param"' in line)
        for name in (0, 999, True):
            lines = raw.copy()
            lines[position] = json.dumps({"il": 1, "param": name})
            with self.subTest(name=name), self.assertRaises(PreviewError):
                self.parse(lines)
        for params in ([2, 2], [0], [999], [True], "bad"):
            lines = raw.copy()
            record = json.loads(lines[-1])
            record["thm"]["levelParams"] = params
            lines[-1] = json.dumps(record)
            with self.subTest(params=params), self.assertRaises(PreviewError):
                self.parse(lines)

    def test_preview_rejects_undeclared_universe_parameter(self):
        raw = Path("tests/reference/poly-identity.ndjson").read_text().splitlines()
        record = json.loads(raw[-1])
        record["thm"]["levelParams"] = []
        raw[-1] = json.dumps(record)
        with self.assertRaises(PreviewError):
            self.parse(raw)

    def test_parameter_scope_uses_reconstructed_names_and_reachable_levels(self):
        raw = Path("tests/reference/poly-identity.ndjson").read_text().splitlines()
        # A second name index for the same Lean name is a valid scope match.
        raw.insert(-1, '{"in":12,"str":{"pre":0,"str":"u"}}')
        record = json.loads(raw[-1])
        record["thm"]["levelParams"] = [12]
        raw[-1] = json.dumps(record)
        self.assertIs(self.parse(raw)["checked"], False)
        # A distinct symbolic record unrelated to either root need not be listed.
        raw.insert(-1, '{"in":13,"str":{"pre":0,"str":"v"}}')
        raw.insert(-1, '{"il":2,"param":13}')
        self.assertIs(self.parse(raw)["checked"], False)
        record = json.loads(raw[-1])
        record["thm"]["levelParams"] = [13]
        raw[-1] = json.dumps(record)
        with self.assertRaises(PreviewError):
            self.parse(raw)

    def test_theorem_all_allows_equivalent_name_index(self):
        raw = Path("tests/reference/poly-identity.ndjson").read_text().splitlines()
        raw.insert(-1, '{"in":12,"str":{"pre":0,"str":"poly_identity"}}')
        record = json.loads(raw[-1])
        record["thm"]["all"] = [12]
        raw[-1] = json.dumps(record)
        self.assertIs(self.parse(raw)["checked"], False)
        record["thm"]["all"] = [True]
        raw[-1] = json.dumps(record)
        with self.assertRaises(PreviewError):
            self.parse(raw)

    def test_parameter_scope_traverses_nested_level_graph(self):
        raw = Path("tests/reference/poly-identity.ndjson").read_text().splitlines()
        position = next(i for i, line in enumerate(raw) if '"ie":0' in line)
        raw[position:position] = ['{"il":2,"succ":1}', '{"il":3,"max":[0,2]}',
                                  '{"il":4,"imax":[3,0]}']
        raw[position + 3] = '{"ie":0,"sort":4}'
        self.assertIs(self.parse(raw)["checked"], False)
        record = json.loads(raw[-1])
        record["thm"]["levelParams"] = []
        raw[-1] = json.dumps(record)
        with self.assertRaises(PreviewError):
            self.parse(raw)

    def test_each_declaration_and_value_has_its_own_parameter_scope(self):
        raw = Path("tests/reference/poly-identity.ndjson").read_text().splitlines()
        record = json.loads(raw[-1])
        record["thm"]["type"] = 2  # Sort 0 has no parameters; value still uses u.
        raw[-1] = json.dumps(record)
        self.assertIs(self.parse(raw)["checked"], False)
        record["thm"]["levelParams"] = []
        raw[-1] = json.dumps(record)
        with self.assertRaises(PreviewError):
            self.parse(raw)
        # A prior declaration's successful check cannot authorize a second one.
        original = Path("tests/reference/poly-identity.ndjson").read_text().splitlines()
        original.extend(['{"in":12,"str":{"pre":0,"str":"other"}}',
                         '{"thm":{"all":[12],"levelParams":[],"name":12,"type":2,"value":15}}'])
        with self.assertRaises(PreviewError):
            self.parse(original)

    def test_multiple_real_lean_exports_reach_forth_probe(self):
        for name in ("identity", "composition", "type-identity"):
            with self.subTest(name=name):
                raw = Path(f"tests/reference/{name}.ndjson").read_bytes()
                decoded = preview(io.BytesIO(raw))
                declaration = decoded["declarations"][0]
                stream = encode_concrete(decoded)
                expected = []
                for index, node in enumerate(decoded["expressions"]):
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
                command = [os.environ.get("GFORTH", "gforth"),
                           "tests/core/load-declaration-stream.fs"]
                result = subprocess.run(command, input=stream, capture_output=True, check=True)
                rows = result.stdout.splitlines()
                self.assertEqual(rows[0].split(), [b"0"])
                self.assertEqual([tuple(map(int, row.split())) for row in rows[1:]], expected)
                # Use the root of the claim as the proof value; its type does not
                # match the claim, so no successful diagnostic is possible.
                stream[8:12] = stream[4:8]
                result = subprocess.run(command, input=stream, capture_output=True, check=True)
                self.assertNotEqual(result.stdout.splitlines()[0].split(), [b"0"])
                # A truncated or extended stream must emit no diagnostic.
                for malformed in (stream[:-1], stream + b"\x00"):
                    result = subprocess.run(command, input=malformed, capture_output=True)
                    self.assertNotEqual(result.returncode, 0)
                    self.assertEqual(result.stdout.strip(), b"")

    def test_wide_transport_stages_universe_256(self):
        raw = Path("tests/reference/identity.ndjson").read_text().splitlines()
        position = next(i for i, line in enumerate(raw) if '"thm"' in line)
        records = [json.dumps({"il": i, "succ": i - 1}) for i in range(1, 257)]
        raw[position:position] = records + ['{"ie":7,"sort":256}']
        decoded = self.parse(raw)
        self.assertEqual(decoded["expressions"][-1]["level"], 256)
        nodes = [(1, 0, 0), (2, 0, 0), (2, 1, 0), (5, 1, 2),
                 (5, 0, 3), (4, 1, 1), (4, 0, 5),
                 (1, decoded["expressions"][-1]["level"], 0)]
        stream = bytearray(struct.pack("<III", 8, 4, 6))
        for index, fields in enumerate(nodes):
            stream.extend(struct.pack("<IIII", index, *fields))
        command = [os.environ.get("GFORTH", "gforth"), "tests/core/load-declaration-stream.fs"]
        result = subprocess.run(command, input=stream, capture_output=True, check=True)
        rows = result.stdout.splitlines()
        self.assertEqual(rows[0].split(), [b"0"])
        self.assertEqual(tuple(map(int, rows[-1].split())), (7, 1, 256, 0))
        # Values outside signed 32-bit range cannot be passed to a 32-bit host.
        stream[-1] = 128
        bad = subprocess.run(command, input=stream, capture_output=True)
        self.assertNotEqual(bad.returncode, 0)
        self.assertEqual(bad.stdout.strip(), b"")
        # Truncation inside every header field and node field must fail without
        # emitting a status; a rejected stream cannot leave a partial result.
        for length in (0, 1, 3, 4, 7, 8, 11, 12, 13, 15, 16, len(stream) - 1):
            bad = subprocess.run(command, input=stream[:length], capture_output=True)
            self.assertNotEqual(bad.returncode, 0, msg=f"accepted length {length}")
            self.assertEqual(bad.stdout.strip(), b"")


if __name__ == "__main__":
    unittest.main()
