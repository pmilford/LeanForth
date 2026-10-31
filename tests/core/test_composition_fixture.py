"""Negative checks for the test-only composition fixture inspector."""

import json
from pathlib import Path
import unittest

from check_composition_fixture import fixture_nodes


class FixtureTests(unittest.TestCase):
    def setUp(self):
        self.lines = Path("tests/reference/composition.ndjson").read_text(encoding="utf-8").splitlines()

    def test_valid_fixture_has_expected_node_count(self):
        self.assertEqual(len(fixture_nodes(self.lines)), 21)

    def test_duplicate_expression_index_fails(self):
        altered = self.lines.copy()
        index = next(i for i, line in enumerate(altered) if '"ie":0' in line)
        altered.insert(index, altered[index])
        with self.assertRaises(ValueError):
            fixture_nodes(altered)

    def test_forward_reference_fails(self):
        altered = self.lines.copy()
        index = next(i for i, line in enumerate(altered) if '"forallE"' in line)
        record = json.loads(altered[index])
        record["forallE"]["body"] = record["ie"]
        altered[index] = json.dumps(record)
        with self.assertRaises(ValueError):
            fixture_nodes(altered)

    def test_bad_metadata_and_missing_theorem_fail(self):
        altered = self.lines.copy()
        metadata = json.loads(altered[0])
        metadata["meta"]["format"]["version"] = "999"
        altered[0] = json.dumps(metadata)
        with self.assertRaises(ValueError):
            fixture_nodes(altered)
        with self.assertRaises(ValueError):
            fixture_nodes(self.lines[:-1])

    def test_unknown_and_malformed_records_fail(self):
        with self.assertRaises(ValueError):
            fixture_nodes(self.lines + ['{"unexpected": 1}'])
        with self.assertRaises(ValueError):
            fixture_nodes(self.lines + ['{'])

    def test_metadata_must_be_first_and_well_formed(self):
        with self.assertRaises(ValueError):
            fixture_nodes(self.lines[1:])
        with self.assertRaises(ValueError):
            fixture_nodes(['{"meta": null}'] + self.lines[1:])

    def test_theorem_must_be_an_object(self):
        with self.assertRaises(ValueError):
            fixture_nodes(self.lines[:-1] + ['{"thm": null}'])

    def test_boolean_sort_is_not_an_integer(self):
        altered = self.lines.copy()
        index = next(i for i, line in enumerate(altered) if '"ie":0' in line)
        record = json.loads(altered[index])
        record["sort"] = False
        altered[index] = json.dumps(record)
        with self.assertRaises(ValueError):
            fixture_nodes(altered)

    def test_malformed_name_records_fail(self):
        altered = self.lines.copy()
        altered.insert(1, '{"in":"not-a-name","unexpected":true}')
        with self.assertRaises(ValueError):
            fixture_nodes(altered)
        altered = self.lines.copy()
        altered[1] = '{"in":1,"str":{"pre":1,"str":"bad"}}'
        with self.assertRaises(ValueError):
            fixture_nodes(altered)


if __name__ == "__main__":
    unittest.main()
