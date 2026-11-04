"""Program receipt schemas 0.2 and 0.1: examples, mutations, rules and the validator itself.

``make test`` runs this file (target test-program-ir). It needs only
the Python standard library; tests/support/schema_subset.py is the
validator and scripts/program_receipt.py the reader (schema plus the rules
JSON Schema cannot state). Every rejected receipt pins the reason it must
be rejected for, so a receipt cannot pass this test by failing for an
unrelated reason. Schema 0.1 is published (a generated receipt named it),
so it is pinned by hash and its examples are kept in receipts/0.1/.
"""
import copy
import hashlib
from pathlib import Path
import re
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path("tests/support")))
sys.path.insert(0, str(Path("scripts")))
from schema_subset import (MAX_DEPTH, InstanceError, SchemaError, Validator,  # noqa: E402
                           load_strict, validate_file)
import program_receipt  # noqa: E402

SCHEMA = Path("schemas/program-receipt-0.2.schema.json")
SCHEMA_01 = Path("schemas/program-receipt-0.1.schema.json")
SCHEMA_01_SHA256 = "ed8f25a7a3fd2b71c99f966d52d4d1415644cc894567d004c3c687c90d472218"
EXAMPLES = Path("tests/program/receipts")
EXAMPLES_01 = EXAMPLES / "0.1"
GENERATED = EXAMPLES / "generated" / "lf-clamp.json"
DOC = Path("docs/programming/PROGRAM_RECEIPTS.md")
AI_DOC = Path("docs/user/AI_TOOLS.md")
BASE = EXAMPLES / "valid-clamp-lean-reference.json"
FUTURE = EXAMPLES / "valid-clamp-future-leanforth.json"
GCD = EXAMPLES / "valid-gcd-nothing-yet.json"

# Each invalid example file and the error it must produce, in both versions.
INVALID_EXAMPLES = {
    "invalid-merged-verified-flag.json": "$: additional property 'verified' is not allowed",
    "invalid-leanforth-without-label.json":
        '$.check.label: must equal "experimental — not independently audited"',
    "invalid-lean-check-claimed-by-leanforth.json": '$.check.checker.name: must equal "lean"',
    "invalid-discharged-without-check.json": "$.check.status: \"not-checked\" is not one of",
}


def schema_validator(path=SCHEMA):
    return Validator(load_strict(path.read_text(encoding="utf-8")))


def load(path=BASE):
    return load_strict(path.read_text(encoding="utf-8"))


def base_receipt():
    return load(BASE)


def at(receipt, path):
    """The container and key that a dotted path such as 'run.cases' names."""
    *parents, last = path.split(".")
    node = receipt
    for part in parents:
        node = node[int(part)] if isinstance(node, list) else node[part]
    return node, (int(last) if isinstance(node, list) else last)


def mutated(path, value=None, delete=False, base=BASE):
    receipt = load(base)
    node, key = at(receipt, path)
    if delete:
        del node[key]
    else:
        node[key] = value
    return receipt


def edited(edit, base=BASE):
    """A receipt changed by edit(receipt), which may change several fields."""
    receipt = load(base)
    edit(receipt)
    return receipt


def remove_assumption(kind, base=BASE):
    return edited(lambda r: r.update(assumptions=[a for a in r["assumptions"]
                                                  if a["kind"] != kind]), base)


def remove_tool(name, base=BASE):
    return edited(lambda r: r.update(tools=[t for t in r["tools"] if t["name"] != name]), base)


def add_assumption(kind, text, base=BASE):
    return edited(lambda r: r["assumptions"].append({"id": "A99", "kind": kind, "text": text}),
                  base)


NOT_CHECKED = {"status": "not-checked", "label": "not checked", "axioms": [], "evidence": []}


def with_check(check, verify=None):
    """The clamp receipt with another check part, and another verify part."""
    receipt = base_receipt()
    receipt["check"] = dict(check)
    if verify is not None:
        receipt["verify"] = verify
    return receipt


def negative(status, label, **fields):
    """A check part with a negative status, checked by LeanForth."""
    return {"status": status, "checker": {"name": "leanforth", "version": "1"},
            "label": label, "axioms": [], "evidence": [], **fields}


def obligations(*statuses, theorem=True):
    """A verify part with one obligation per status."""
    items = [{"id": f"O{i}", "statement": "x", "status": s} for i, s in enumerate(statuses, 1)]
    for item in items:
        if theorem and item["status"] != "open":
            item["theorem"] = f"T{item['id']}"
    status = "open" if "open" in statuses else statuses[0]
    return {"status": status, "generator": {"name": "leanforth", "version": "1"},
            "obligations": items}


def failed_run(**fields):
    """The clamp receipt's run, failed."""
    return edited(lambda r: r["run"].update({"status": "failed", "failures": 1,
                                             "label": "runtime tests failed", **fields}))


def open_verify(receipt):
    receipt["verify"] = {"status": "open", "generator": {"name": "leanforth", "version": "1"},
                         "obligations": [{"id": "O1", "statement": "x", "status": "open"}]}


# One rule each: the change to a valid receipt and the error it must cause.
# Together with the invalid example files these reach every rule of schema
# 0.2. Comments name the finding of the 2026-11-03 review each group answers.
MUTATIONS = [
    ("merged status", lambda: mutated("status", "verified"),
     "$: additional property 'status' is not allowed"),
    ("nested verified flag", lambda: mutated("check.verified", True),
     "$.check: additional property 'verified' is not allowed"),
    ("schema version", lambda: mutated("schemaVersion", "1.0"),
     '$.schemaVersion: must equal "0.2"'),
    ("schema version 0.1", lambda: mutated("schemaVersion", "0.1"),
     '$.schemaVersion: must equal "0.2"'),
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
    # Obligations are settled only by named, checked theorems.
    ("discharged obligation without theorem",
     lambda: with_check(base_receipt()["check"], obligations("discharged", "open", theorem=False)),
     "$.verify.obligations[0]: missing required property 'theorem'"),
    ("refuted obligation without theorem",
     lambda: with_check(base_receipt()["check"], obligations("refuted", theorem=False)),
     "$.verify.obligations[0]: missing required property 'theorem'"),
    ("open obligation naming a theorem",
     lambda: with_check(base_receipt()["check"], dict(obligations("open"), obligations=[
         {"id": "O1", "statement": "x", "status": "open", "theorem": "T"}])),
     "$.verify.obligations[0].theorem: no value is allowed here"),
    ("discharged obligation while nothing is checked",
     lambda: with_check(NOT_CHECKED, obligations("discharged", "open")),
     '$.check.status: "not-checked" is not one of'),
    ("unsupported verify with discharged obligations and nothing checked",
     lambda: with_check(NOT_CHECKED, dict(obligations("discharged"), status="unsupported")),
     '$.check.status: "not-checked" is not one of'),
    ("refuted while nothing is checked", lambda: with_check(NOT_CHECKED, obligations("refuted")),
     '$.check.status: "not-checked" is not one of'),
    # A checked theorem is tied to the source through the IR.
    ("checked without IR", lambda: mutated("program.ir", None),
     "$.program.ir: expected type object, got null"),
    # A failed check carries its own label, names its checker, and no axioms.
    ("rejected with the accepted label",
     lambda: with_check(negative("rejected", "experimental — not independently audited")),
     '$.check.label: must equal "rejected by the checker"'),
    ("failed with the Lean label",
     lambda: with_check(negative("failed", "checked by the Lean reference, not by LeanForth")),
     '$.check.label: must equal "check did not complete"'),
    ("unsupported with another label", lambda: with_check(negative("unsupported", "ok")),
     '$.check.label: must equal "not supported by the checker"'),
    ("rejected with an allowed axiom",
     lambda: with_check(negative("rejected", "rejected by the checker", axioms=["propext"])),
     "$.check.axioms: more than 0 item(s)"),
    ("failed with forbidden axioms",
     lambda: with_check(negative("failed", "check did not complete",
                                 axioms=["sorryAx", "Lean.ofReduceBool"])),
     '$.check.axioms[0]: "sorryAx" is not one of'),
    ("rejected without its checker",
     lambda: with_check({k: v for k, v in negative("rejected", "rejected by the checker").items()
                         if k != "checker"}),
     "$.check: missing required property 'checker'"),
    ("not checked naming theorems",
     lambda: with_check(dict(NOT_CHECKED, theorems=[{"name": "T", "axioms": []}])),
     "$.check.theorems: no value is allowed here"),
    ("not checked with evidence", lambda: with_check(dict(
        NOT_CHECKED, evidence=base_receipt()["check"]["evidence"])),
     "$.check.evidence: more than 0 item(s)"),
    ("check by a tool that is no checker",
     lambda: with_check(dict(negative("rejected", "rejected by the checker"),
                             checker={"name": "python", "version": "x"})),
     '$.check.checker.name: "python" is not one of'),
    # LeanForth's own checker is a named trusted component.
    ("leanforth check without its assumption",
     lambda: remove_assumption("trusted-leanforth", base=FUTURE),
     "$.assumptions: no item matches #/$defs/kindTrustedLeanForth"),
    ("leanforth check without the leanforth tool", lambda: remove_tool("leanforth", base=FUTURE),
     "$.tools: no item matches #/$defs/toolLeanForth"),
    ("lean check without the lean tool", lambda: remove_tool("lean"),
     "$.tools: no item matches #/$defs/toolLean"),
    # Paths stay inside the repository.
    ("path up out of the repository",
     lambda: mutated("check.evidence.0.path", "../../../etc/passwd"),
     "$.check.evidence[0].path: does not match pattern"),
    ("path through a parent segment", lambda: mutated("program.source.path", "src/../x.fs"),
     "$.program.source.path: does not match pattern"),
    ("path into .git", lambda: mutated("program.source.path", ".git/config"),
     "$.program.source.path: does not match pattern"),
    ("path with an empty segment", lambda: mutated("run.evidence.0.path", "tests//x.sh"),
     "$.run.evidence[0].path: does not match pattern"),
    # Further rules the schema can express.
    ("word not in the IR's lower-case spelling", lambda: mutated("program.word", "LF-Clamp"),
     "$.program.word: does not match pattern"),
    ("blank assumption text", lambda: mutated("assumptions.2.text", " "),
     "$.assumptions[2].text: does not match pattern [!-~]"),
    ("impossible date", lambda: mutated("provenance.createdAt", "2026-99-99"),
     "$.provenance.createdAt: does not match pattern"),
    ("passed without evidence", lambda: mutated("run.evidence", delete=True),
     "$.run: missing required property 'evidence'"),
    # Finding 1: a failed or missing run never carries a pass's label.
    ("failed run with the pass label",
     lambda: failed_run(label="runtime-tested; testing is not proof"),
     '$.run.label: must equal "runtime tests failed"'),
    ("failed run labelled all tests passed", lambda: failed_run(label="all tests passed"),
     '$.run.label: must equal "runtime tests failed"'),
    ("failed run without a failure", lambda: failed_run(failures=0),
     "$.run.failures: less than the minimum 1"),
    ("failed run without evidence", lambda: edited(
        lambda r: (r["run"].update(status="failed", failures=1, label="runtime tests failed"),
                   r["run"].pop("evidence"))),
     "$.run: missing required property 'evidence'"),
    ("not run with the pass label",
     lambda: mutated("run.label", "runtime-tested; testing is not proof", base=GCD),
     '$.run.label: must equal "not run"'),
    ("not run without a label", lambda: mutated("run.label", delete=True, base=GCD),
     "$.run: missing required property 'label'"),
    ("not run with a host", lambda: mutated("run.host", base_receipt()["run"]["host"], base=GCD),
     "$.run.host: no value is allowed here"),
    ("not run with evidence",
     lambda: mutated("run.evidence", base_receipt()["run"]["evidence"], base=GCD),
     "$.run.evidence: more than 0 item(s)"),
    ("not run with cases", lambda: mutated("run.cases", 5, base=GCD), "$.run.cases: must equal 0"),
    # Finding 3: verify says which check discharged it, and rests on the generator.
    ("discharged without settledBy", lambda: mutated("verify.settledBy", delete=True,
                                                    base=GENERATED),
     "$.verify: missing required property 'settledBy'"),
    ("Lean's discharge claimed for LeanForth",
     lambda: mutated("verify.settledBy", "accepted-by-leanforth", base=GENERATED),
     '$.verify.settledBy: must equal "checked-by-lean-reference"'),
    ("LeanForth's discharge claimed for Lean",
     lambda: mutated("verify.settledBy", "checked-by-lean-reference", base=FUTURE),
     '$.verify.settledBy: must equal "accepted-by-leanforth"'),
    ("settledBy naming no check", lambda: mutated("verify.settledBy", "lean", base=GENERATED),
     '$.verify.settledBy: "lean" is not one of'),
    ("settledBy with nothing settled",
     lambda: mutated("verify.settledBy", "checked-by-lean-reference"),
     "$.verify.settledBy: no value is allowed here"),
    ("discharged without the contract theorem",
     lambda: mutated("contract.lean", delete=True, base=GENERATED),
     "$.contract: missing required property 'lean'"),
    ("discharged without the contract file",
     lambda: mutated("contract.file", delete=True, base=GENERATED),
     "$.contract: missing required property 'file'"),
    ("generator without its assumption",
     lambda: remove_assumption("untrusted-generator", base=GENERATED),
     "$.assumptions: no item matches #/$defs/kindUntrustedGenerator"),
    ("the review's repro: no contract theorem, contract file or generator assumption",
     lambda: edited(lambda r: (r["contract"].pop("lean"), r["contract"].pop("file"),
                               r.update(assumptions=[a for a in r["assumptions"]
                                                     if a["id"] != "A7"])), GENERATED),
     "$.assumptions: no item matches #/$defs/kindUntrustedGenerator"),
    ("open without a generator",
     lambda: edited(lambda r: (open_verify(r), r["verify"].pop("generator"))),
     "$.verify: missing required property 'generator'"),
    ("not generated naming a generator",
     lambda: mutated("verify.generator", {"name": "python", "version": "1"}),
     "$.verify.generator: no value is allowed here"),
    ("unsupported listing obligations", lambda: mutated("verify.status", "unsupported",
                                                       base=GENERATED),
     "$.verify.obligations: more than 0 item(s)"),
    # Finding 7: texts show what they say; LeanForth's trust only where it checked.
    ("assumption text only a zero-width space", lambda: mutated("assumptions.0.text", "​"),
     "$.assumptions[0].text: does not match pattern [!-~]"),
    ("assumption text only a byte-order mark", lambda: mutated("assumptions.0.text", "﻿"),
     "$.assumptions[0].text: does not match pattern [!-~]"),
    ("assumption text only a braille blank", lambda: mutated("assumptions.0.text", "⠀"),
     "$.assumptions[0].text: does not match pattern [!-~]"),
    ("assumption text only a hangul filler", lambda: mutated("assumptions.0.text", "ㅤ"),
     "$.assumptions[0].text: does not match pattern [!-~]"),
    ("tool version only a zero-width space", lambda: mutated("tools.0.version", "​"),
     "$.tools[0].version: does not match pattern"),
    ("empty note", lambda: mutated("check.note", ""), "$.check.note: does not match pattern [!-~]"),
    ("stack effect with a second line after U+2028",
     lambda: mutated("program.stackEffect", "( a -- b ) verified ( c -- d )"),
     "$.program.stackEffect: does not match pattern ^\\( .* \\)$"),
    ("stack effect with a carriage return",
     lambda: mutated("program.stackEffect", "( value lower upper -- x )\r( verified )"),
     "$.program.stackEffect: does not match pattern ^\\( .* \\)$"),
    ("statement with a right-to-left override",
     lambda: mutated("contract.statement", "returns ‮min‬ and true"),
     "$.contract.statement: does not match pattern ^[^"),
    ("note with an ANSI escape",
     lambda: mutated("check.note", "\x1b[2K\x1b[1Gaccepted-by-leanforth"),
     "$.check.note: does not match pattern ^[^"),
    ("note with invisible tag characters",
     lambda: mutated("check.note", "Lean proved it\U000e0041\U000e0042"),
     "$.check.note: does not match pattern ^[^"),
    ("note with a soft hyphen", lambda: mutated("run.note", "ac­cepted"),
     "$.run.note: does not match pattern ^[^"),
    ("note with a lone surrogate", lambda: mutated("run.note", "\ud800 passed"),
     "$.run.note: does not match pattern ^[^"),
    ("theorem name with a newline", lambda: mutated("check.theorems.0.name", "T\nVERIFIED"),
     "$.check.theorems[0].name: does not match pattern ^[^"),
    ("Lean-checked receipt claiming LeanForth's checker",
     lambda: add_assumption("trusted-leanforth", "LeanForth's checker accepted the proofs."),
     "$.assumptions[6]: matches a forbidden form"),
    ("unchecked receipt claiming LeanForth's checker",
     lambda: add_assumption("trusted-leanforth", "LeanForth's checker accepted it.", base=GCD),
     "$.assumptions[4]: matches a forbidden form"),
    # Finding 8: each theorem lists its own axioms.
    ("theorem as a bare name", lambda: mutated("check.theorems.0", "ProgramIR.clamp_correct"),
     "$.check.theorems[0]: expected type object, got string"),
    ("theorem without its axioms", lambda: mutated("check.theorems.0.axioms", delete=True),
     "$.check.theorems[0]: missing required property 'axioms'"),
    ("theorem with a forbidden axiom", lambda: mutated("check.theorems.0.axioms", ["sorryAx"]),
     '$.check.theorems[0].axioms[0]: "sorryAx" is not one of'),
    ("rejected theorem with an axiom",
     lambda: with_check(negative("rejected", "rejected by the checker",
                                 theorems=[{"name": "T", "axioms": ["propext"]}])),
     "$.check.theorems[0].axioms: more than 0 item(s)"),
    # Finding 9: the stack and two's-complement assumptions; no verify without IR.
    ("no stack-capacity assumption", lambda: remove_assumption("stack-capacity"),
     "$.assumptions: no item matches #/$defs/kindStackCapacity"),
    ("no two's-complement assumption", lambda: remove_assumption("twos-complement"),
     "$.assumptions: no item matches #/$defs/kindTwosComplement"),
    ("open verify without IR", lambda: edited(open_verify, GCD),
     "$.program.ir: expected type object, got null"),
]


def receipt_rule(edit, base=GENERATED):
    return lambda: edited(edit, base)


def append_copy(items, index):
    items.append(copy.deepcopy(items[index]))


# Rules beyond JSON Schema (scripts/program_receipt.py rule_problems): each
# change keeps the receipt valid under the schema and must break one rule.
RULE_MUTATIONS = [
    ("duplicate assumption id",
     receipt_rule(lambda r: r["assumptions"][1].update(id="A1")),
     'rule: $.assumptions: id "A1" appears more than once'),
    ("duplicate obligation id",
     receipt_rule(lambda r: r["verify"]["obligations"][1].update(id="O1")),
     'rule: $.verify.obligations: id "O1" appears more than once'),
    ("duplicate theorem", receipt_rule(lambda r: append_copy(r["check"]["theorems"], 1)),
     'rule: $.check.theorems: theorem "ProgramVC.LfClamp0.O1" appears more than once'),
    ("duplicate axiom", receipt_rule(lambda r: r["check"]["axioms"].append("propext")),
     'rule: $.check.axioms: axiom "propext" appears more than once'),
    ("duplicate axiom of a theorem",
     receipt_rule(lambda r: r["check"]["theorems"][1]["axioms"].append("propext")),
     'rule: $.check.theorems[1].axioms: axiom "propext" appears more than once'),
    ("axioms under-reported", receipt_rule(lambda r: r["check"].update(axioms=["propext"])),
     "rule: $.check.axioms: not the union of the theorems' axioms"),
    ("axioms over-reported",
     receipt_rule(lambda r: [t.update(axioms=["propext"]) for t in r["check"]["theorems"]]),
     "rule: $.check.axioms: not the union of the theorems' axioms"),
    ("obligation's theorem not checked",
     receipt_rule(lambda r: r["verify"]["obligations"][0].update(theorem="Anything.at.all")),
     "rule: $.verify.obligations[0].theorem: not among check.theorems"),
    ("contract theorem not checked",
     receipt_rule(lambda r: r["contract"].update(lean="ProgramVC.Other.contract")),
     "rule: $.contract.lean: the contract's theorem is not among check.theorems"),
    ("more failures than cases",
     receipt_rule(lambda r: r["run"].update(status="failed", cases=0, failures=5,
                                            label="runtime tests failed")),
     "rule: $.run.failures: more failures than cases"),
    ("checker not among the tools",
     receipt_rule(lambda r: r["check"]["checker"].update(version="4.34.0")),
     "rule: $.check.checker: not among tools"),
    ("generator not among the tools",
     receipt_rule(lambda r: r["verify"]["generator"].update(version="program_vc.py 9")),
     "rule: $.verify.generator: not among tools"),
]


class SchemaShape(unittest.TestCase):
    def test_schema_loads_with_supported_keywords_only(self):
        schema_validator()
        schema_validator(SCHEMA_01)

    def test_no_merged_verdict_field_exists(self):
        schema = load_strict(SCHEMA.read_text(encoding="utf-8"))
        self.assertFalse(set(schema["properties"]) & {"verified", "status", "ok", "success"})
        self.assertIs(schema["additionalProperties"], False)

    def test_reader_knows_both_versions(self):
        self.assertEqual(set(program_receipt.SCHEMAS), {"0.1", "0.2"})
        self.assertEqual(program_receipt.SCHEMAS["0.2"].resolve(), SCHEMA.resolve())
        self.assertEqual(program_receipt.SCHEMA_VERSION, "0.2")


class Examples(unittest.TestCase):
    def test_valid_examples(self):
        valid = sorted(EXAMPLES.glob("valid-*.json")) + [GENERATED]
        self.assertGreaterEqual(len(valid), 4)
        for path in valid:
            with self.subTest(path=path.name):
                self.assertEqual(program_receipt.read_file(path)[1], [])

    def test_invalid_examples_fail_for_their_reason(self):
        validator = schema_validator()
        files = {p.name for p in EXAMPLES.glob("invalid-*.json")}
        self.assertEqual(files, set(INVALID_EXAMPLES))
        for name, expected in INVALID_EXAMPLES.items():
            with self.subTest(name=name):
                problems = validate_file(validator, EXAMPLES / name)
                self.assertTrue(any(p.startswith(expected) for p in problems), problems)

    def test_every_mutation_fails_for_its_reason(self):
        validator = schema_validator()
        for base in (BASE, FUTURE, GCD, GENERATED):
            self.assertEqual(validator.errors(load(base)), [], base)
        for name, make, expected in MUTATIONS:
            with self.subTest(name=name):
                problems = validator.errors(make())
                self.assertTrue(any(p.startswith(expected) for p in problems), problems)

    def test_every_rule_mutation_fails_for_its_rule(self):
        for name, make, expected in RULE_MUTATIONS:
            with self.subTest(name=name):
                receipt = make()
                self.assertEqual(schema_validator().errors(receipt), [])
                problems = program_receipt.receipt_problems(receipt)
                self.assertTrue(any(p.startswith(expected) for p in problems), problems)

    def test_a_planted_rule_fault_is_detected(self):
        """Disabling the duplicate check makes the rule suite miss duplicates."""
        original = program_receipt.repeated
        try:
            program_receipt.repeated = lambda *args: []
            missed = [name for name, make, expected in RULE_MUTATIONS
                      if not any(p.startswith(expected)
                                 for p in program_receipt.receipt_problems(make()))]
            self.assertIn("duplicate assumption id", missed)
        finally:
            program_receipt.repeated = original


class Documentation(unittest.TestCase):
    """Finding 2: the documents an AI reads describe the generated receipt."""

    def test_documented_receipt_is_the_generated_one(self):
        blocks = re.findall(r"```json\n(.*?)```", DOC.read_text(encoding="utf-8"), re.S)
        self.assertTrue(blocks, f"{DOC} has no JSON example")
        self.assertEqual(load_strict(blocks[0]), load(GENERATED))

    def test_documented_figures_are_the_generated_ones(self):
        text = DOC.read_text(encoding="utf-8")
        receipt = load(GENERATED)
        for figure in (f"{receipt['run']['cases']} cases", receipt["contract"]["lean"],
                       f"verify: `{receipt['verify']['status']}`",
                       f"`{receipt['verify']['settledBy']}`",
                       f"schema version {receipt['schemaVersion']}"):
            with self.subTest(figure=figure):
                self.assertIn(figure, text)

    def test_ai_guide_names_the_current_schema(self):
        text = AI_DOC.read_text(encoding="utf-8")
        self.assertIn(str(SCHEMA), text)
        self.assertNotIn("no receipt is generated yet", text)


class Reader(unittest.TestCase):
    """Finding 4 and the version rule: one strict reader for every receipt."""

    def test_unknown_versions_are_refused(self):
        for version in ("0.3", "1.0", 0.2, None):
            with self.subTest(version=version):
                receipt = mutated("schemaVersion", version)
                problems = program_receipt.receipt_problems(receipt)
                self.assertTrue(problems and problems[0].startswith("unknown-version: "), problems)

    def test_texts_that_are_not_strict_json_are_refused(self):
        text = GENERATED.read_text(encoding="utf-8")
        for name, old, new in (
                ("duplicate key", '"status": "checked-by-lean-reference",',
                 '"status": "accepted-by-leanforth",\n    "status": "checked-by-lean-reference",'),
                ("fraction", '"cases": 986', '"cases": 986.0'),
                ("exponent read as zero", '"failures": 0', '"failures": 1e-400'),
                ("integer beyond 2**53", '"cases": 986', '"cases": 9007199254740992'),
                ("lone surrogate", '"note": "Lean proved', '"note": "\\ud800 Lean proved'),
                ("NaN", '"cases": 986', '"cases": NaN')):
            with self.subTest(name=name):
                changed = text.replace(old, new, 1)
                self.assertNotEqual(changed, text)
                receipt, problems = program_receipt.read_text(changed)
                self.assertIsNone(receipt)
                self.assertTrue(problems[0].startswith("not-strict-json: "), problems)

    def test_version_01_receipts_are_read_with_schema_01(self):
        receipt, problems = program_receipt.read_file(EXAMPLES_01 / "generated-lf-clamp.json")
        self.assertEqual(problems, [])
        self.assertEqual(receipt["schemaVersion"], "0.1")


class Version01(unittest.TestCase):
    """Schema 0.1 stays readable exactly as it was."""

    def test_schema_01_is_unchanged(self):
        self.assertEqual(hashlib.sha256(SCHEMA_01.read_bytes()).hexdigest(), SCHEMA_01_SHA256)

    def test_01_examples_keep_their_results(self):
        validator = schema_validator(SCHEMA_01)
        valid = sorted(EXAMPLES_01.glob("valid-*.json")) + [EXAMPLES_01 / "generated-lf-clamp.json"]
        self.assertEqual(len(valid), 4)
        for path in valid:
            with self.subTest(path=path.name):
                self.assertEqual(validate_file(validator, path), [])
        for name, expected in INVALID_EXAMPLES.items():
            with self.subTest(name=name):
                problems = validate_file(validator, EXAMPLES_01 / name)
                self.assertTrue(any(p.startswith(expected) for p in problems), problems)

    def test_versions_do_not_mix(self):
        old = load(EXAMPLES_01 / "generated-lf-clamp.json")
        self.assertIn('$.schemaVersion: must equal "0.2"', schema_validator().errors(old))
        self.assertIn('$.schemaVersion: must equal "0.1"',
                      schema_validator(SCHEMA_01).errors(load(GENERATED)))


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

    def test_references_must_point_at_schemas(self):
        """Finding 5: a $ref into a properties map would silently drop its rules."""
        defs = {"x": {"properties": {"type": {"const": 1}, "format": {"const": 2}},
                      "required": ["a"], "enum": [{"type": "string"}]}}
        for ref in ("#/$defs/x/properties", "#/$defs/x/required", "#/$defs/x/enum",
                    "#/$defs/x/enum/0", "#/$defs"):
            with self.subTest(ref=ref):
                with self.assertRaises(SchemaError):
                    Validator({"$defs": defs, "$ref": ref})
        for ref in ("#/$defs/x", "#/$defs/x/properties/type"):
            with self.subTest(ref=ref):
                Validator({"$defs": defs, "$ref": ref})
        escaped = Validator({"$defs": {"a/b~c": {"const": 1}}, "$ref": "#/$defs/a~1b~0c"})
        self.assertTrue(escaped.errors(2))

    def test_malformed_keyword_values_are_refused(self):
        for schema in ({"type": "text"}, {"required": "x"}, {"additionalProperties": {}},
                       {"enum": []}, {"minItems": -1}, {"allOf": []}, {"pattern": "("},
                       {"pattern": "(?x)a b"}, {"pattern": "(?s:a.b)"}, {"pattern": "[]a]"},
                       {"pattern": "[^]a]"}):
            with self.subTest(schema=schema):
                with self.assertRaises((SchemaError, re.error)):
                    Validator(schema)

    def test_patterns_have_ecma_anchors_and_dot(self):
        """Finding 7: ^...$ matches the whole string and . stops at line terminators."""
        dot = Validator({"pattern": "^a.b$"})
        self.assertEqual(dot.errors("axb"), [])
        for text in ("a\nb", "a\rb", "a b", "a b", "axb\n", "\naxb"):
            with self.subTest(text=text):
                self.assertTrue(dot.errors(text))
        backslash = Validator({"pattern": "^a\\\\$"})
        self.assertEqual(backslash.errors("a\\"), [])
        self.assertTrue(backslash.errors("a\\\n"))
        either = Validator({"pattern": "^a$|^b$"})
        self.assertEqual(either.errors("b"), [])
        self.assertTrue(either.errors("a\n"))
        literal = Validator({"pattern": "^[.$^]+$"})
        self.assertEqual(literal.errors("$.^"), [])
        self.assertTrue(literal.errors("x"))
        self.assertEqual(Validator({"pattern": "a"}).errors("xay"), [])

    def test_strict_json(self):
        """Findings 4, 6, 7 and 9: what the strict loader refuses."""
        for text in ('{"a": 1, "a": 2}', '{"a": NaN}', '[Infinity]', '{"a": -Infinity}',
                     '{"a": 1.0}', '{"a": 1e3}', '{"a": 1e-400}', '{"a": 12.0000000000000001}',
                     '{"a": -0.0}', '{"a": 9007199254740992}', '{"a": -9007199254740992}',
                     '{"a": 1' + '0' * 5000 + '}', '"\\ud800"', '{"\\udc00": 1}',
                     '[' * (MAX_DEPTH + 2) + ']' * (MAX_DEPTH + 2),
                     '[' * 200000 + ']' * 200000, '{"a": 1} {}', '﻿{}', '{"a": 1'):
            with self.subTest(text=text[:40]):
                with self.assertRaises(InstanceError):
                    load_strict(text)
        self.assertEqual(load_strict('[9007199254740991, -9007199254740991]'),
                         [2 ** 53 - 1, -(2 ** 53 - 1)])
        self.assertIsInstance(load_strict('[' * MAX_DEPTH + ']' * MAX_DEPTH), list)
        self.assertEqual(load_strict('[-9223372036854775808]', max_integer=2 ** 64),
                         [-2 ** 63])

    def test_deep_nesting_is_a_structured_error(self):
        """Finding 9: a file nested 200000 deep gives one error line, not a traceback."""
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "deep.json"
            path.write_text('{"x":' + "[" * 200000 + "]" * 200000 + "}", encoding="utf-8")
            problems = validate_file(schema_validator(), path)
            self.assertEqual(len(problems), 1)
            self.assertIn("nested deeper than", problems[0])
            self.assertTrue(program_receipt.read_file(path)[1][0].startswith("not-strict-json"))

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
            missed = [name for name, make, expected in MUTATIONS
                      if not any(p.startswith(expected) for p in validator.errors(make()))]
            self.assertIn("no runtime assumption", missed)
        finally:
            Validator._kw_contains = original


if __name__ == "__main__":
    unittest.main()
