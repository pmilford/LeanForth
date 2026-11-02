"""Real pinned Lean exports through the current checker (untrusted).

Each export is staged as handle terms with symbolic levels by
tests/core/export-definition-stream.fs and checked by
lf-mixed-definition-probe with an empty signature index. Status 0 is an
untrusted diagnostic, never theorem acceptance. This replaces the checks that
the superseded concrete declaration probe made on the same exports.
"""
import io
import json
from pathlib import Path
import sys
import unittest

sys.path.insert(0, "tests/support")
from export_definition import decode, encode, run, succ_chain  # noqa: E402
from ndjson_preview import preview  # noqa: E402

OK, INVALID, EXHAUSTED, UNKNOWN = 0, 1, 2, 3
EXPORTS = ("identity", "composition", "type-identity", "poly-identity")


def status(data):
    result = run(data)
    if result.returncode != 0:
        raise AssertionError(result.stderr.decode() or "stream failed")
    return int(result.stdout.split()[0])


class ExportDefinitions(unittest.TestCase):
    def test_exports_check_and_swapped_values_do_not(self):
        for name in EXPORTS:
            decoded = decode(name)
            claim = decoded["declarations"][0]["type"]
            with self.subTest(name=name):
                self.assertEqual(status(encode(decoded)), OK)
                # The claim is a type, not a proof of itself.
                self.assertEqual(status(encode(decoded, value=claim)), UNKNOWN)
                # Node 0 is a Sort, which is not the claim's value either way.
                self.assertNotEqual(status(encode(decoded, claim=0)), OK)

    def test_altered_composition_is_invalid(self):
        decoded = decode("composition")
        # Give the outer lambda the wrong body while keeping a DAG: the
        # value refers to a variable its binders do not provide.
        decoded["expressions"][-1]["body"] = 18
        self.assertEqual(status(encode(decoded)), INVALID)

    def test_nested_universe_levels_stage(self):
        raw = Path("tests/reference/identity.ndjson").read_text().splitlines()
        position = next(i for i, line in enumerate(raw) if '"thm"' in line)
        raw[position:position] = [
            '{"il":1,"succ":0}', '{"il":2,"succ":1}',
            '{"il":3,"imax":[2,0]}', '{"il":4,"max":[3,1]}',
            '{"il":5,"imax":[2,3]}', '{"ie":7,"sort":5}',
            '{"ie":8,"sort":4}',
        ]
        decoded = preview(io.BytesIO(("\n".join(raw) + "\n").encode()))
        # The extra Sorts of max and imax levels are staged but unused.
        self.assertEqual(status(encode(decoded)), OK)
        # Sort (imax 2 0) is Sort 0, the claim's own Sort, not the claim.
        self.assertNotEqual(status(encode(decoded, value=7)), OK)

    def test_poly_identity_specializes_at_concrete_universes(self):
        decoded = decode("poly-identity")
        count = len(decoded["levelExpressions"])
        rows, records = succ_chain(0, count, 3)
        for k, record in enumerate(records):
            with self.subTest(level=k):
                data = encode(decoded, actuals=[record], extra_levels=rows)
                lines = run(data).stdout.decode().split()
                self.assertEqual(int(lines[0]), OK)
                claim = decoded["declarations"][0]["type"]
                data = encode(decoded, value=claim, actuals=[record], extra_levels=rows)
                self.assertEqual(int(run(data).stdout.split()[0]), UNKNOWN)

    def test_poly_identity_at_one_is_the_type_identity_export(self):
        # A separately exported concrete theorem fixes the expected syntax.
        concrete = decode("type-identity")
        nodes = concrete["expressions"]

        def shape(index):
            node = nodes[index]
            tag = node["tag"]
            if tag == "sort":
                return f"s{node['level']}"
            if tag == "bvar":
                return f"v{node['index']}"
            if tag == "app":
                return f"a({shape(node['fn'])},{shape(node['arg'])})"
            letter = "l" if tag == "lam" else "p"
            return f"{letter}({shape(node['type'])},{shape(node['body'])})"
        declaration = concrete["declarations"][0]
        decoded = decode("poly-identity")
        rows, records = succ_chain(0, len(decoded["levelExpressions"]), 1)
        lines = run(encode(decoded, actuals=[records[1]], extra_levels=rows)).stdout.split()
        self.assertEqual([line.decode() for line in lines],
                         ["0", shape(declaration["type"]), shape(declaration["value"])])

    def test_equivalent_parameter_names_and_counts(self):
        lines = Path("tests/reference/poly-identity.ndjson").read_text().splitlines()
        lines.insert(-1, '{"in":12,"str":{"pre":0,"str":"u"}}')
        record = json.loads(lines[-1])
        record["thm"]["levelParams"] = [12]
        lines[-1] = json.dumps(record)
        decoded = preview(io.BytesIO(("\n".join(lines) + "\n").encode()))
        # The alias names the same parameter u, so the export still checks.
        self.assertEqual(status(encode(decoded)), OK)
        # An unused extra parameter needs its own replacement too.
        decoded = decode("poly-identity")
        decoded["declarations"][0]["levelParams"] = [2, 3]
        rows, records = succ_chain(0, len(decoded["levelExpressions"]), 1)
        self.assertNotEqual(run(encode(decoded, actuals=[records[1]], extra_levels=rows))
                            .returncode, 0)

    def test_small_fuel_is_exhausted_not_ok(self):
        decoded = decode("composition")
        self.assertEqual(status(encode(decoded, fuel=10)), EXHAUSTED)

    def test_malformed_streams_print_nothing(self):
        for name in EXPORTS:
            data = encode(decode(name))
            # Truncated, extended, a child that is not earlier, and a
            # replacement count that differs from the parameter count.
            bad = [data[:-1], data + b"\x00"]
            decoded = decode(name)
            changed = json.loads(json.dumps(decoded))
            changed["expressions"][1] = {"tag": "app", "fn": 1, "arg": 0}
            bad.append(encode(changed))
            params = len(decoded["declarations"][0]["levelParams"])
            bad.append(encode(decoded, actuals=[0] * (params + 1)))
            for stream in bad:
                with self.subTest(name=name, size=len(stream)):
                    result = run(stream)
                    self.assertNotEqual(result.returncode, 0)
                    self.assertEqual(result.stdout.strip(), b"")


if __name__ == "__main__":
    unittest.main()
