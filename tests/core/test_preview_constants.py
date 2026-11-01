"""Tests of untrusted Lean NDJSON constant/definition preview support."""
import io
import json
from pathlib import Path
import sys
import unittest

sys.path.insert(0, "tests/support")
from fixture_transport import encode_concrete
from ndjson_preview import PreviewError, preview


class ConstantPreviewTests(unittest.TestCase):
    def setUp(self):
        self.lines = Path("tests/reference/constant-fixture.ndjson").read_text().splitlines()

    def parse(self, records):
        data = "\n".join(json.dumps(record, ensure_ascii=False) for record in records) + "\n"
        return preview(io.BytesIO(data.encode()))

    def records(self):
        return [json.loads(line) for line in self.lines]

    def test_pinned_export_preserves_constants_and_definitions(self):
        result = self.parse(self.records())
        self.assertFalse(result["checked"])
        self.assertFalse(result["dependenciesChecked"])
        self.assertEqual([d["kind"] for d in result["declarations"]], ["def", "def", "thm"])
        self.assertEqual(result["declarations"][0]["hints"], {"regular": 1})
        self.assertEqual(result["declarations"][0]["safety"], "safe")
        self.assertEqual(result["expressions"][7], {"tag": "const", "name": 1, "us": [1]})
        self.assertEqual(result["expressions"][14], {"tag": "const", "name": 1, "us": [0]})
        # Existing concrete Forth transport cannot stage a constant or a def.
        with self.assertRaises(ValueError):
            encode_concrete(result, 0)

        concrete = preview(io.BytesIO(Path("tests/reference/identity.ndjson").read_bytes()))
        concrete["declarations"][0]["kind"] = "def"
        with self.assertRaises(ValueError):
            encode_concrete(concrete, 0)

        # Exercise the unsupported-constant branch with a concrete theorem,
        # not the symbolic fixture's earlier transport rejection.
        lines = Path("tests/reference/identity.ndjson").read_text().splitlines()
        records = [json.loads(line) for line in lines]
        theorem = next(i for i, record in enumerate(records) if "thm" in record)
        records.insert(theorem, {"ie": 7, "const": {"name": 1, "us": []}})
        with_constant = self.parse(records)
        self.assertTrue(with_constant["concreteLevelDataOnly"])
        with self.assertRaisesRegex(ValueError, "unsupported expression"):
            encode_concrete(with_constant, 0)

    def test_constant_shape_and_index_validation(self):
        for replacement in ({"name": 0, "us": []}, {"name": 999, "us": []},
                            {"name": 1, "us": [True]}, {"name": 1, "us": [999]},
                            {"name": 1, "us": "bad"}, {"name": 1},
                            {"name": 1, "us": [], "extra": 0},
                            {"name": 1, "us": [0] * 257}):
            records = self.records()
            record = next(record for record in records if record.get("ie") == 7)
            record["const"] = replacement
            with self.subTest(replacement=replacement), self.assertRaises(PreviewError):
                self.parse(records)

    def test_constant_universe_parameters_obey_declaration_scope(self):
        records = self.records()
        definition = next(record["def"] for record in records if record.get("def", {}).get("name") == 5)
        definition.update(levelParams=[], type=7, value=7)
        # Its constant argument references u, so a missing declaration parameter
        # must not be hidden by an otherwise valid constant name.
        with self.assertRaises(PreviewError):
            self.parse(records)

    def test_universe_arguments_keep_order_without_assuming_arity(self):
        records = self.records()
        constant = next(record["const"] for record in records if record.get("ie") == 7)
        constant["us"] = [0, 1, 0]
        result = self.parse(records)
        self.assertEqual(result["expressions"][7]["us"], [0, 1, 0])
        self.assertFalse(result["dependenciesChecked"])

    def test_definition_metadata_is_preserved_not_authorized(self):
        for hints in ("opaque", "abbrev", {"regular": 9}):
            for safety in ("safe", "unsafe", "partial"):
                records = self.records()
                definition = next(record["def"] for record in records if "def" in record)
                definition.update(hints=hints, safety=safety)
                result = self.parse(records)
                self.assertEqual(result["declarations"][0]["hints"], hints)
                self.assertEqual(result["declarations"][0]["safety"], safety)
                self.assertFalse(result["checked"])
        for hints in ("bogus", {"regular": True}, {"regular": 1, "extra": 0}, []):
            records = self.records()
            next(record["def"] for record in records if "def" in record)["hints"] = hints
            with self.subTest(hints=hints), self.assertRaises(PreviewError):
                self.parse(records)
        records = self.records()
        next(record["def"] for record in records if "def" in record)["safety"] = "bogus"
        with self.assertRaises(PreviewError):
            self.parse(records)

    def test_unresolved_dependency_is_explicitly_unchecked(self):
        records = self.records()
        next(record for record in records if record.get("ie") == 7)["const"]["name"] = 3
        result = self.parse(records)
        self.assertFalse(result["dependenciesChecked"])
        self.assertFalse(result["checked"])


if __name__ == "__main__":
    unittest.main()
