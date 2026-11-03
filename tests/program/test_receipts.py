"""Program receipt schema 0.1: examples, mutations and the validator itself.

``make test`` runs this file (target test-program-receipts). It needs only
the Python standard library; tests/support/schema_subset.py is the
validator. Every rejected receipt pins the reason it must be rejected for,
so a receipt cannot pass this test by failing for an unrelated reason.
"""
from pathlib import Path
import re
import sys
import unittest

sys.path.insert(0, str(Path("tests/support")))
from schema_subset import (InstanceError, SchemaError, Validator, load_strict,
                           validate_file)

SCHEMA = Path("schemas/program-receipt-0.1.schema.json")
EXAMPLES = Path("tests/program/receipts")
DOC = Path("docs/programming/PROGRAM_RECEIPTS.md")
BASE = EXAMPLES / "valid-clamp-lean-reference.json"

# Each invalid example file and the error it must produce.
INVALID_EXAMPLES = {
    "invalid-merged-verified-flag.json": "$: additional property 'verified' is not allowed",
    "invalid-leanforth-without-label.json":
        '$.check.label: must equal "experimental — not independently audited"',
    "invalid-lean-check-claimed-by-leanforth.json": '$.check.checker.name: must equal "lean"',
    "invalid-discharged-without-check.json": "$.check.status: \"not-checked\" is not one of",
}


def schema_validator():
    return Validator(load_strict(SCHEMA.read_text(encoding="utf-8")))


def base_receipt():
    return load_strict(BASE.read_text(encoding="utf-8"))


def at(receipt, path):
    """The container and key that a dotted path such as 'run.cases' names."""
    *parents, last = path.split(".")
    node = receipt
    for part in parents:
        node = node[int(part)] if isinstance(node, list) else node[part]
    return node, (int(last) if isinstance(node, list) else last)


def mutated(path, value=None, delete=False):
    receipt = base_receipt()
    node, key = at(receipt, path)
    if delete:
        del node[key]
    else:
        node[key] = value
    return receipt


def remove_assumption(kind):
    receipt = base_receipt()
    receipt["assumptions"] = [a for a in receipt["assumptions"] if a["kind"] != kind]
    return receipt


# One rule each: the change to the valid clamp receipt and the error it must
# cause. Together with the invalid example files these reach every
# cross-field rule of the schema.
MUTATIONS = [
    ("merged status", lambda: mutated("status", "verified"),
     "$: additional property 'status' is not allowed"),
    ("nested verified flag", lambda: mutated("check.verified", True),
     "$.check: additional property 'verified' is not allowed"),
    ("schema version", lambda: mutated("schemaVersion", "1.0"),
     '$.schemaVersion: must equal "0.1"'),
    ("short hash", lambda: mutated("program.source.sha256", "abc123"),
     "$.program.source.sha256: does not match pattern"),
    ("uppercase hash", lambda: mutated("program.source.sha256", "A" * 64),
     "$.program.source.sha256: does not match pattern"),
    ("hash with newline", lambda: mutated("program.source.sha256", "a" * 64 + "\n"),
     "$.program.source.sha256: does not match pattern"),
    ("absolute path", lambda: mutated("program.source.path", "/home/user/clamp.fs"),
     "$.program.source.path: does not match pattern"),
    ("line zero", lambda: mutated("program.source.line", 0), "$.program.source.line: less than"),
    ("boolean line", lambda: mutated("program.source.line", True),
     "$.program.source.line: expected type integer, got boolean"),
    ("missing stack effect", lambda: mutated("program.stackEffect", delete=True),
     "$.program: missing required property 'stackEffect'"),
    ("forbidden axiom", lambda: mutated("check.axioms", ["propext", "sorryAx"]),
     '$.check.axioms[1]: "sorryAx" is not one of'),
    ("trusted compiler axiom", lambda: mutated("check.axioms", ["Lean.ofReduceBool"]),
     '$.check.axioms[0]: "Lean.ofReduceBool" is not one of'),
    ("lean check without theorems", lambda: mutated("check.theorems", []),
     "$.check.theorems: fewer than 1 item(s)"),
    ("lean check without evidence", lambda: mutated("check.evidence", []),
     "$.check.evidence: fewer than 1 item(s)"),
    ("lean check with other label", lambda: mutated("check.label", "verified"),
     '$.check.label: must equal "checked by the Lean reference, not by LeanForth"'),
    ("unchecked with axioms", lambda: mutated("check", {
        "status": "not-checked", "label": "not checked", "axioms": ["propext"], "evidence": []}),
     "$.check.axioms: more than 0 item(s)"),
    ("not generated with obligations", lambda: mutated("verify.obligations", [
        {"id": "O1", "statement": "x", "status": "open"}]),
     "$.verify.obligations: more than 0 item(s)"),
    ("passed with failures", lambda: mutated("run.failures", 2), "$.run.failures: must equal 0"),
    ("passed with no cases", lambda: mutated("run.cases", 0),
     "$.run.cases: less than the minimum 1"),
    ("passed without label", lambda: mutated("run.label", delete=True),
     "$.run: missing required property 'label'"),
    ("passed without host", lambda: mutated("run.host", delete=True),
     "$.run: missing required property 'host'"),
    ("cells below Forth minimum", lambda: mutated("run.host.cellBits", 8),
     "$.run.host.cellBits: less than the minimum 16"),
    ("no runtime assumption", lambda: remove_assumption("trusted-runtime"),
     "$.assumptions: no item matches #/$defs/kindTrustedRuntime"),
    ("no cell assumption", lambda: remove_assumption("host-cells"),
     "$.assumptions: no item matches #/$defs/kindHostCells"),
    ("lean check without lean assumption", lambda: remove_assumption("trusted-lean"),
     "$.assumptions: no item matches #/$defs/kindTrustedLean"),
    ("IR without reader assumption", lambda: remove_assumption("trusted-reader"),
     "$.assumptions: no item matches #/$defs/kindTrustedReader"),
    ("floating point without caveat", lambda: mutated("program.floatingPoint", True),
     "$.assumptions: no item matches #/$defs/kindFloatingPoint"),
    ("unknown assumption kind", lambda: mutated("assumptions.0.kind", "magic"),
     '$.assumptions[0].kind: "magic" is not one of'),
    ("generated without generator", lambda: mutated("provenance.kind", "generated"),
     "$.provenance: missing required property 'generator'"),
    ("IR of another version", lambda: mutated("program.ir.version", "0.2"),
     "$.program.ir: matches none of the allowed forms"),
]


class SchemaShape(unittest.TestCase):
    def test_schema_loads_with_supported_keywords_only(self):
        schema_validator()

    def test_no_merged_verdict_field_exists(self):
        schema = load_strict(SCHEMA.read_text(encoding="utf-8"))
        self.assertFalse(set(schema["properties"]) & {"verified", "status", "ok", "success"})
        self.assertIs(schema["additionalProperties"], False)


class Examples(unittest.TestCase):
    def test_valid_examples(self):
        validator = schema_validator()
        valid = sorted(EXAMPLES.glob("valid-*.json"))
        self.assertGreaterEqual(len(valid), 3)
        for path in valid:
            with self.subTest(path=path.name):
                self.assertEqual(validate_file(validator, path), [])

    def test_invalid_examples_fail_for_their_reason(self):
        validator = schema_validator()
        files = {p.name for p in EXAMPLES.glob("invalid-*.json")}
        self.assertEqual(files, set(INVALID_EXAMPLES))
        for name, expected in INVALID_EXAMPLES.items():
            with self.subTest(name=name):
                problems = validate_file(validator, EXAMPLES / name)
                self.assertTrue(any(p.startswith(expected) for p in problems), problems)

    def test_documented_example_is_valid(self):
        blocks = re.findall(r"```json\n(.*?)```", DOC.read_text(encoding="utf-8"), re.S)
        self.assertTrue(blocks, f"{DOC} has no JSON example")
        self.assertEqual(schema_validator().errors(load_strict(blocks[0])), [])

    def test_every_mutation_fails_for_its_reason(self):
        validator = schema_validator()
        self.assertEqual(validator.errors(base_receipt()), [])
        for name, make, expected in MUTATIONS:
            with self.subTest(name=name):
                problems = validator.errors(make())
                self.assertTrue(any(p.startswith(expected) for p in problems), problems)


class ValidatorFailsClosed(unittest.TestCase):
    def test_unsupported_keywords_are_refused(self):
        for keyword in ("format", "dependentRequired", "unevaluatedProperties", "$dynamicRef",
                        "patternProperties", "exclusiveMinimum", "uniqueItems"):
            with self.subTest(keyword=keyword):
                with self.assertRaises(SchemaError):
                    Validator({"properties": {"x": {keyword: 1}}})

    def test_bad_references_are_refused(self):
        for ref in ("#/$defs/missing", "other.json#/x", "https://example.org/s.json"):
            with self.subTest(ref=ref):
                with self.assertRaises(SchemaError):
                    Validator({"$ref": ref})

    def test_malformed_keyword_values_are_refused(self):
        for schema in ({"type": "text"}, {"required": "x"}, {"additionalProperties": {}},
                       {"enum": []}, {"minItems": -1}, {"allOf": []}, {"pattern": "("}):
            with self.subTest(schema=schema):
                with self.assertRaises((SchemaError, re.error)):
                    Validator(schema)

    def test_strict_json(self):
        for text in ('{"a": 1, "a": 2}', '{"a": NaN}', '[Infinity]', '{"a": -Infinity}'):
            with self.subTest(text=text):
                with self.assertRaises(InstanceError):
                    load_strict(text)

    def test_types(self):
        integer = Validator({"type": "integer"})
        self.assertEqual(integer.errors(3), [])
        self.assertEqual(integer.errors(3.0), [])
        self.assertTrue(integer.errors(True))
        self.assertTrue(integer.errors(3.5))
        self.assertEqual(Validator({"type": "number"}).errors(3), [])
        self.assertTrue(Validator({"type": "boolean"}).errors(0))

    def test_const_and_enum_distinguish_booleans_from_numbers(self):
        self.assertTrue(Validator({"const": 1}).errors(True))
        self.assertEqual(Validator({"const": 1}).errors(1.0), [])
        self.assertTrue(Validator({"enum": [0, "x"]}).errors(False))
        self.assertTrue(Validator({"const": {"a": [1]}}).errors({"a": [True]}))

    def test_conditionals_and_combinators(self):
        schema = {"if": {"const": 1}, "then": {"type": "integer"}, "else": {"type": "string"}}
        validator = Validator(schema)
        self.assertEqual(validator.errors(1), [])
        self.assertEqual(validator.errors("x"), [])
        self.assertTrue(validator.errors(2))
        self.assertTrue(Validator({"not": {"type": "null"}}).errors(None))
        self.assertTrue(Validator({"anyOf": [{"type": "null"}, {"const": 2}]}).errors(3))
        self.assertTrue(Validator({"contains": {"const": 2}}).errors([1, 3]))
        self.assertEqual(Validator({"contains": {"const": 2}}).errors([1, 2]), [])

    def test_false_schema_and_additional_properties(self):
        self.assertTrue(Validator(False).errors(1))
        closed = Validator({"properties": {"a": True}, "additionalProperties": False})
        self.assertEqual(closed.errors({"a": 1}), [])
        self.assertTrue(closed.errors({"a": 1, "b": 2}))

    def test_a_planted_validator_fault_is_detected(self):
        """Disabling one keyword check makes the mutation suite fail."""
        original = Validator._kw_contains
        try:
            Validator._kw_contains = lambda *args: None
            validator = schema_validator()
            missed = [name for name, make, _ in MUTATIONS if not validator.errors(make())]
            self.assertIn("no runtime assumption", missed)
        finally:
            Validator._kw_contains = original


if __name__ == "__main__":
    unittest.main()
