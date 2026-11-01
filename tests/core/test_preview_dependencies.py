"""Untrusted dependency observations over bounded NDJSON preview records."""
import io
import json
from pathlib import Path
import sys
import unittest

sys.path.insert(0, "tests/support")
from ndjson_preview import preview


class DependencyObservationTests(unittest.TestCase):
    def records(self):
        return [json.loads(line) for line in
                Path("tests/reference/constant-fixture.ndjson").read_text().splitlines()]

    def parse(self, records):
        data = "\n".join(json.dumps(record) for record in records) + "\n"
        return preview(io.BytesIO(data.encode()))

    def test_fixture_observes_dependencies_without_checking_them(self):
        result = self.parse(self.records())
        self.assertFalse(result["checked"])
        self.assertFalse(result["dependenciesChecked"])
        self.assertFalse(result["cyclesChecked"])
        observations = result["dependencyDiagnostics"]
        self.assertEqual(observations[0]["references"], [])
        self.assertEqual(observations[1]["references"], [{
            "expression": 7, "name": 1, "inType": False, "inValue": True,
            "targetRecord": 0, "status": "earlier_in_stream",
            "providedUniverses": 1, "declaredUniverses": 1, "arityMatches": True,
        }])
        self.assertEqual(observations[2]["references"][0]["expression"], 14)
        self.assertEqual(observations[2]["references"][0]["targetRecord"], 0)

    def test_missing_self_forward_and_wrong_arity_are_diagnostics(self):
        records = self.records()
        const = next(record["const"] for record in records if record.get("ie") == 7)
        for name, universes, expected, target, arity in (
            (3, [1], "missing", None, None),
            (5, [1], "self", 1, True),
            (1, [], "earlier_in_stream", 0, False),
        ):
            const.update(name=name, us=universes)
            result = self.parse(records)
            reference = result["dependencyDiagnostics"][1]["references"][0]
            self.assertEqual((reference["status"], reference["targetRecord"],
                              reference["arityMatches"]), (expected, target, arity))
            self.assertFalse(result["dependenciesChecked"])
        records = self.records()
        dependency = next(i for i, record in enumerate(records)
                          if record.get("def", {}).get("name") == 1)
        deferred = records.pop(dependency)
        dependent = next(i for i, record in enumerate(records)
                         if record.get("def", {}).get("name") == 5)
        records.insert(dependent + 1, deferred)
        reference = self.parse(records)["dependencyDiagnostics"][0]["references"][0]
        self.assertEqual((reference["status"], reference["targetRecord"]),
                         ("later_in_stream", 1))

    def test_structural_name_aliases_and_both_roots(self):
        meta = self.records()[0]
        records = [meta,
                   {"in": 1, "str": {"pre": 0, "str": "dep"}},
                   {"in": 2, "str": {"pre": 0, "str": "dep"}},
                   {"in": 3, "str": {"pre": 0, "str": "user"}},
                   {"ie": 0, "sort": 0},
                   {"def": {"name": 1, "all": [1], "levelParams": [],
                            "type": 0, "value": 0, "hints": "abbrev", "safety": "safe"}},
                   {"ie": 1, "const": {"name": 2, "us": []}},
                   {"thm": {"name": 3, "all": [3], "levelParams": [], "type": 1, "value": 1}}]
        reference = self.parse(records)["dependencyDiagnostics"][1]["references"][0]
        self.assertEqual(reference["targetRecord"], 0)
        self.assertEqual(reference["status"], "earlier_in_stream")
        self.assertTrue(reference["inType"] and reference["inValue"])
        self.assertTrue(reference["arityMatches"])

    def test_nested_aliases_distinct_name_kinds_and_shared_subgraphs(self):
        meta = self.records()[0]
        records = [meta,
                   {"in": 1, "str": {"pre": 0, "str": "ns"}},
                   {"in": 2, "str": {"pre": 0, "str": "ns"}},
                   {"in": 3, "num": {"pre": 1, "i": 1}},
                   {"in": 4, "str": {"pre": 2, "str": "1"}},
                   {"in": 5, "num": {"pre": 2, "i": 1}},
                   {"in": 6, "str": {"pre": 0, "str": "user"}},
                   {"ie": 0, "sort": 0},
                   {"def": {"name": 3, "all": [3], "levelParams": [],
                            "type": 0, "value": 0, "hints": "abbrev", "safety": "safe"}},
                   {"ie": 1, "const": {"name": 5, "us": []}},
                   {"ie": 2, "const": {"name": 4, "us": []}},
                   {"ie": 3, "app": {"fn": 1, "arg": 1}},
                   {"ie": 4, "lam": {"name": 0, "binderInfo": "default", "type": 0, "body": 3}},
                   {"ie": 5, "app": {"fn": 4, "arg": 2}},
                   {"ie": 6, "const": {"name": 6, "us": []}},  # unreachable
                   {"thm": {"name": 6, "all": [6], "levelParams": [], "type": 4, "value": 5}}]
        first = self.parse(records)
        references = first["dependencyDiagnostics"][1]["references"]
        self.assertEqual([ref["expression"] for ref in references], [1, 2])
        self.assertEqual((references[0]["status"], references[0]["targetRecord"]),
                         ("earlier_in_stream", 0))
        self.assertTrue(references[0]["inType"] and references[0]["inValue"])
        self.assertEqual((references[1]["status"], references[1]["targetRecord"]),
                         ("missing", None))
        self.assertFalse(references[1]["inType"])
        self.assertTrue(references[1]["inValue"])
        self.assertEqual(json.dumps(first, sort_keys=True),
                         json.dumps(self.parse(records), sort_keys=True))


if __name__ == "__main__":
    unittest.main()
