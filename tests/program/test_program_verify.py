"""leanforth verify's driver v0 without Lean (plan 8.4.1b; docs/programming/PROGRAM_VERIFY.md).

Usage (from the repository root; make test):
  GFORTH=... python3 tests/program/test_program_verify.py [CLASS[.TEST]...]

Runs scripts/program_verify.py with the real program words (Gforth) and the
real generator, and with tests/program/verify/fake_lean.py standing in for
pinned Lean, its exporter and LeanForth's checker (the checker inside this
process only: the driver has no option or variable that changes its
checker). tests/program/verify_lean_check.py runs it with the real tools.

1. Every outcome: discharged (the four words), refuted (the three wrong
   contracts), unsupported (gcd, factorial, a literal 2), the SHA words
   refused as needing receipt 0.4; Lean failed or out of time (open, nothing
   checked); each verdict of LeanForth's (rejected, unknown, unsupported,
   exhausted, full, invalid, missing, a declaration other than a theorem,
   a report that stops or is missing); NOT PROVED (6); LeanForth's axioms
   other than Lean's, Lean's print-back other than the IR, a missing axiom
   report, the export failing (5). Each receipt the strict reader accepts;
   none says discharged or refuted unless LeanForth accepted the theorems.
2. Malformed input: the command line, paths outside the checkout, the
   source (missing, refused, too long a path), the contract (missing, not
   UTF-8, each parse error, an input named c), the word, a stale or missing
   IR file, Gforth or Lean missing or of another version (4); the program
   words ending without an outcome (5).
3. Limits: the path and search limits (3), Lean's time limit (3).
4. Workflow and state: from another folder; the default --out; an earlier
   run's files removed by name and nothing else; the source changed while
   read; the export removed unless --keep-export; a failed write leaves no
   receipt and no partial file; two runs give the same bytes.
5. The shared helpers of scripts/program_receipt.py the driver uses.
"""
import contextlib
import copy
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))
import program_receipt  # noqa: E402
import program_verify  # noqa: E402
sys.path.insert(0, str(ROOT / "tests" / "program"))
import verify_lean_check  # noqa: E402

DRIVER = ROOT / "scripts" / "program_verify.py"
FAKE = ROOT / "tests" / "program" / "verify" / "fake_lean.py"
CONTRACTS = ROOT / "tests" / "program" / "contracts"
GOLDEN = ROOT / "tests" / "program" / "verify" / "golden"
PINNED_GFORTH = ROOT / ".tools" / "gforth" / "bin" / "gforth"
GFORTH = os.environ.get("GFORTH") or (str(PINNED_GFORTH) if PINNED_GFORTH.is_file() else "gforth")
SOURCES = {"lf-clamp": "src/program/clamp.fs", "wrong-clamp-swapped": "src/program/clamp.fs"}
DISCHARGED = ("lf-clamp", "lf-checked-add", "lf-checked-abs", "lf-in-range")
REFUTED = ("wrong-clamp-swapped", "wrong-checked-add-total", "wrong-in-range-exclusive")
UNSUPPORTED = ("lf-gcd", "lf-factorial")
SHA = ("sha-rotr", "sha-ch", "sha-maj", "sha-big-sigma0")


def source_of(contract):
    if contract.startswith("sha-"):
        return "src/program/sha-words.fs"
    return SOURCES.get(contract, "src/program/examples.fs")


def scratch():
    """A folder inside the checkout (receipt 0.3 names files inside it only), under build/."""
    (ROOT / "build").mkdir(exist_ok=True)
    return tempfile.TemporaryDirectory(dir=ROOT / "build", prefix="v-")


def rel(path):
    return Path(path).resolve().relative_to(ROOT).as_posix()


def run(argv, fake=None, lean=str(FAKE), env=None):
    """The driver inside this process with the stand-ins: (exit status, printed text)."""
    variables = {"GFORTH": GFORTH, "LEAN": lean, "LEANEXPORT": str(FAKE),
                 "VERIFY_FAKE": json.dumps(fake or {}), **(env or {})}
    printed = io.StringIO()
    with mock.patch.dict(os.environ, variables), \
            mock.patch.object(program_receipt, "LEANFORTH",
                              [sys.executable, str(FAKE), "leanforth"]), \
            contextlib.redirect_stdout(printed):
        status = program_verify.main([str(a) for a in argv])
    return status, printed.getvalue()


def cli(argv, cwd=ROOT, env=None):
    """The driver as a command (no stand-in checker): (exit status, standard output)."""
    variables = {**os.environ, "GFORTH": GFORTH, **(env or {})}
    done = subprocess.run([sys.executable, "-I", str(DRIVER), *map(str, argv)], cwd=cwd,
                          env=variables, capture_output=True, text=True, timeout=600,
                          stdin=subprocess.DEVNULL)
    return done.returncode, done.stdout + done.stderr


def verify(contract, out, fake=None, extra=(), lean=str(FAKE), env=None):
    return run([source_of(contract), "--contract", CONTRACTS / f"{contract}.contract",
                "--out", out, *extra], fake, lean, env)


def receipt_at(out, word):
    """The receipt verify wrote for word in out, read strictly (schema, rules), or None."""
    path = Path(out) / f"{program_verify.safe_name(word)}.receipt.json"
    if not path.exists():
        return None
    receipt, problems = program_receipt.read_file(path)
    if problems:
        raise AssertionError(f"{path}: {problems}")
    return receipt


def kinds(receipt):
    return [a["kind"] for a in receipt["assumptions"]]


def problem_codes(text):
    return [line.split(": ")[1] for line in text.splitlines() if line.startswith("error: ")]


class Fixture:
    """A source, its IR and a contract written into a scratch folder of the checkout."""

    def __init__(self, folder, source, contract, word=None):
        self.folder = Path(folder)
        self.source = self.folder / "w.fs"
        self.source.write_text(source, encoding="utf-8")
        done = subprocess.run(program_receipt.program_words_args(GFORTH, rel(self.source)),
                              cwd=ROOT, capture_output=True, text=True, timeout=120,
                              stdin=subprocess.DEVNULL)
        outcome, text, _ = program_receipt.program_words_output(done.stdout)
        self.ir = self.folder / "w.ir"
        self.ir.write_text(text, encoding="utf-8")
        self.contract = self.folder / "w.contract"
        self.contract.write_text(contract.replace("IR", rel(self.ir)), encoding="utf-8")
        self.out = self.folder / "out"

    def argv(self, *extra):
        return [self.source, "--contract", self.contract, "--out", self.out, *extra]


ONE_INPUT = """lf-contract 0.1
id w/0
word {word}
ir IR
stack ( n -- m )
inputs {inputs}
statement A test word.
case true
  out m
"""


def contract_text(word="w", inputs="n"):
    return ONE_INPUT.format(word=word, inputs=inputs)


class Discharged(unittest.TestCase):
    """The four discharged words, with every theorem accepted by the stand-in checker."""

    def test_four_words(self):
        for contract in DISCHARGED:
            with self.subTest(contract), scratch() as out:
                status, text = verify(contract, out)
                self.assertEqual(status, 0, text)
                word = contract
                receipt = receipt_at(out, word)
                self.assertEqual(receipt["check"]["status"], "accepted-by-leanforth")
                self.assertEqual(receipt["verify"]["status"], "discharged")
                self.assertEqual(receipt["verify"]["settledBy"], "accepted-by-leanforth")
                obligations = receipt["verify"]["obligations"]
                self.assertTrue(obligations)
                self.assertTrue(all(o["status"] == "discharged" and o["theorem"]
                                    for o in obligations))
                names = [t["name"] for t in receipt["check"]["theorems"]]
                self.assertEqual(names[0], receipt["contract"]["lean"])
                self.assertEqual(len(names), len(obligations) + 1)
                self.assertEqual(receipt["run"], {
                    "status": "not-run", "cases": 0, "failures": 0, "label": "not run",
                    "note": receipt["run"]["note"]})
                for kind in ("host-cells", "twos-complement", "trusted-reader",
                             "trusted-runtime", "stack-capacity", "trusted-lean",
                             "untrusted-generator", "trusted-leanforth"):
                    self.assertIn(kind, kinds(receipt))
                self.assertIn(f"{word}: contract {receipt['contract']['id']} discharged (",
                              text)
                self.assertIn("compiled code is not covered", text)
                self.assertNotIn("NOT VERIFIED", text)

    def test_says_who_proved_what(self):
        with scratch() as out:
            verify("lf-clamp", out)
            receipt = receipt_at(out, "lf-clamp")
            text = json.dumps(receipt)
            note = receipt["check"]["note"]
            self.assertIn("wrote the proofs", note)
            self.assertIn("LeanForth's checker re-checked that export", note)
            self.assertIn("LeanForth has no tactics yet and wrote no proof", note)
            self.assertNotIn("LeanForth proved", text)
            self.assertNotIn("verified", receipt)
            self.assertEqual(receipt["provenance"]["generator"]["version"],
                             f"program_verify.py {program_verify.VERSION}")
            evidence = [e["path"] for e in receipt["check"]["evidence"]]
            self.assertEqual(evidence, [rel(Path(out) / "obligations.lean"),
                                        "scripts/program_vc.py", "scripts/export.sh",
                                        rel(Path(out) / "lf-clamp.ndjson.manifest.json")])
            for item in receipt["check"]["evidence"]:
                self.assertEqual(item["sha256"], program_verify.file_sha(item["path"]))
            self.assertEqual(receipt["program"]["source"],
                             {"path": "src/program/clamp.fs", "line": 12,
                              "sha256": program_verify.file_sha("src/program/clamp.fs")})
            self.assertEqual(receipt["program"]["ir"]["sha256"],
                             program_verify.file_sha("tests/program/ir/clamp.ir"))
            self.assertEqual(receipt["contract"]["file"]["sha256"],
                             program_verify.file_sha("tests/program/contracts/lf-clamp.contract"))

    def test_calls_followed_in_the_runtime_assumption(self):
        with scratch() as out:
            verify("lf-checked-add", out)
            runtime = [a["text"] for a in receipt_at(out, "lf-checked-add")["assumptions"]
                       if a["kind"] == "trusted-runtime"][0]
            self.assertIn("RSHIFT", runtime)    # lf-example-max, a constant it calls
            self.assertIn("0>", runtime)        # lf-add-overflow?, a word it calls
            self.assertNotIn("CALL", runtime)
            self.assertNotIn("LIT", runtime)


class Refuted(unittest.TestCase):
    def test_three_wrong_contracts(self):
        for contract in REFUTED:
            with self.subTest(contract), scratch() as out:
                status, text = verify(contract, out)
                self.assertEqual(status, 1, text)
                word = program_receipt.program_vc.parse_contract(
                    (CONTRACTS / f"{contract}.contract").read_text(encoding="utf-8"),
                    contract)["word"]
                receipt = receipt_at(out, word)
                self.assertEqual(receipt["check"]["status"], "accepted-by-leanforth")
                self.assertEqual(receipt["verify"]["status"], "refuted")
                [obligation] = receipt["verify"]["obligations"]
                self.assertEqual(obligation["status"], "refuted")
                self.assertTrue(obligation["theorem"].endswith(".refuted"))
                self.assertEqual([t["name"] for t in receipt["check"]["theorems"]],
                                 [obligation["theorem"]])
                self.assertNotIn("lean", receipt["contract"])
                self.assertIn("The contract is false: on 64-bit cells with", obligation[
                    "statement"])
                self.assertIn("NOT VERIFIED: refuted: on 64-bit cells with", text)

    def test_swapped_counterexample(self):
        with scratch() as out:
            _, text = verify("wrong-clamp-swapped", out)
            self.assertIn("refuted: on 64-bit cells with value = -3, lower = -3, upper = -2, "
                          "the word leaves -3, -1 (true) (bottom first); the postcondition "
                          "fails", text)


class Unsupported(unittest.TestCase):
    def test_loop_words(self):
        for contract in UNSUPPORTED:
            with self.subTest(contract), scratch() as out:
                # no Lean is needed: a missing one changes nothing
                status, text = verify(contract, out, lean="/nonexistent/lean")
                self.assertEqual(status, 2, text)
                self.assertEqual(problem_codes(text), ["generator-unsupported"])
                receipt = receipt_at(out, contract)
                self.assertEqual(receipt["check"], {
                    "status": "not-checked", "axioms": [], "evidence": [],
                    "note": receipt["check"]["note"]})
                self.assertEqual(receipt["verify"]["status"], "unsupported")
                self.assertEqual(receipt["verify"]["obligations"], [])
                self.assertNotIn("trusted-lean", kinds(receipt))
                self.assertNotIn("trusted-leanforth", kinds(receipt))
                self.assertEqual([t["name"] for t in receipt["tools"]], ["gforth", "python"])
                self.assertFalse((Path(out) / "obligations.lean").exists())
                self.assertIn("NOT VERIFIED: unsupported: loops need invariants", text)

    def test_golden_receipts(self):
        for contract in UNSUPPORTED:
            with self.subTest(contract), scratch() as out:
                verify(contract, out)
                found = verify_lean_check.normalized(
                    (Path(out) / f"{contract}.receipt.json").read_text(encoding="utf-8"),
                    Path(out).resolve())
                self.assertEqual(found, (GOLDEN / f"{contract}.receipt.json").read_text(
                    encoding="utf-8"))

    def test_literal_two(self):
        with scratch() as folder:
            fixture = Fixture(folder, ": w ( n -- m ) 2 + ;\n", contract_text())
            status, text = run(fixture.argv())
            self.assertEqual(status, 2, text)
            self.assertIn("a literal outside -1..1", text)
            self.assertEqual(receipt_at(fixture.out, "w")["verify"]["status"], "unsupported")

    def test_sha_words_need_receipt_04(self):
        for contract in SHA:
            with self.subTest(contract), scratch() as out:
                status, text = verify(contract, out)
                self.assertEqual(status, 2, text)
                self.assertEqual(problem_codes(text), ["ir-needs-receipt-0.4"])
                self.assertIn("needs receipt schema 0.4", text)
                self.assertEqual(sorted(p.name for p in Path(out).iterdir()), [])


class Lean(unittest.TestCase):
    """Lean's own failures: nothing is checked, and the receipt says so."""

    def test_lean_failed(self):
        for contract, word in (("lf-clamp", "lf-clamp"), ("wrong-clamp-swapped", "lf-clamp")):
            with self.subTest(contract), scratch() as out:
                status, text = verify(contract, out, {"lean": "fail"})
                self.assertEqual(status, 2, text)
                self.assertEqual(problem_codes(text), ["lean-failed"])
                receipt = receipt_at(out, word)
                self.assertEqual(receipt["check"]["status"], "not-checked")
                self.assertEqual(receipt["verify"]["status"], "open")
                self.assertTrue(all(o["status"] == "open" and "theorem" not in o
                                    for o in receipt["verify"]["obligations"]))
                self.assertNotIn("trusted-lean", kinds(receipt))
                self.assertEqual([t["name"] for t in receipt["tools"]],
                                 ["lean", "gforth", "python"])
                self.assertIn("NOT VERIFIED: open", text)

    def test_time_limit(self):
        for fake in ({"lean": "sleep"}, {"export": "sleep"}):
            with self.subTest(fake), scratch() as out:
                status, text = verify("lf-clamp", out, fake, ["--lean-time-limit", "1"])
                self.assertEqual(status, 3, text)
                self.assertEqual(problem_codes(text), ["lean-time-limit"])
                receipt = receipt_at(out, "lf-clamp")
                self.assertEqual((receipt["check"]["status"], receipt["verify"]["status"]),
                                 ("not-checked", "open"))
                self.assertFalse((Path(out) / "lf-clamp.ndjson").exists())
                self.assertFalse((Path(out) / "lf-clamp.ndjson.partial").exists())

    def test_no_receipt(self):
        cases = [({"lean": "mutate"}, 5, "program-print-back-differs"),
                 ({"lean": "no-axioms"}, 5, "internal"),
                 ({"export": "fail"}, 5, "export-failed"),
                 ({"export": "no-manifest"}, 5, "export-failed"),
                 ({"version": "4.34.0"}, 4, "lean-not-found")]
        for fake, expected, code in cases:
            with self.subTest(fake), scratch() as out:
                status, text = verify("lf-clamp", out, fake)
                self.assertEqual((status, problem_codes(text)), (expected, [code]), text)
                self.assertIsNone(receipt_at(out, "lf-clamp"))
                self.assertIn("NOT VERIFIED", text)
                self.assertFalse((Path(out) / "lf-clamp.ndjson").exists())

    def test_files_changed_during_the_run(self):
        for fake in ({"lean": "touch"}, {"check": "touch"}):
            with self.subTest(fake), scratch() as out:
                status, text = verify("lf-clamp", out, fake)
                self.assertEqual((status, problem_codes(text)), (4, ["file-changed"]), text)
                self.assertIsNone(receipt_at(out, "lf-clamp"))

    def test_lean_not_found(self):
        with scratch() as out:
            status, text = verify("lf-clamp", out, lean="/nonexistent/lean")
            self.assertEqual((status, problem_codes(text)), (4, ["lean-not-found"]))
            self.assertIsNone(receipt_at(out, "lf-clamp"))


class Checker(unittest.TestCase):
    """LeanForth's verdicts as the receipt's check status: only all accepted is positive."""

    CASES = [  # (stand-in, exit status, problem, check status)
        ({"verdicts": {"contract": "rejected"}}, 1, "proof-rejected", "rejected"),
        ({"verdicts": {"O2": "rejected"}}, 1, "proof-rejected", "rejected"),
        ({"other": "rejected"}, 1, "proof-rejected", "rejected"),
        ({"verdicts": {"contract": "unknown"}}, 2, "proof-undecided", "unsupported"),
        ({"verdicts": {"O1": "unsupported"}}, 2, "proof-undecided", "unsupported"),
        ({"verdicts": {"contract": "exhausted"}, "exit": 3}, 3, "proof-exhausted", "failed"),
        ({"other": "full", "exit": 3}, 3, "proof-exhausted", "failed"),
        ({"verdicts": {"O1": "invalid"}, "exit": 5}, 5, "internal", "failed"),
        ({"verdicts": {"O2": "not-checked"}}, 5, "internal", "failed"),
        ({"verdicts": {"O2": "absent"}}, 5, "internal", "failed"),
        ({"check": "stopped", "exit": 5}, 5, "internal", "failed"),
        ({"check": "not-run"}, 5, "internal", "failed"),
        ({"exit": 1}, 5, "internal", "failed"),
        ({"check": "no-report"}, 5, "internal", "failed"),
    ]

    def test_verdicts(self):
        for fake, expected, code, check in self.CASES:
            with self.subTest(fake), scratch() as out:
                status, text = verify("lf-clamp", out, fake)
                self.assertEqual((status, problem_codes(text)), (expected, [code]), text)
                receipt = receipt_at(out, "lf-clamp")
                self.assertEqual(receipt["check"]["status"], check)
                self.assertEqual(receipt["verify"]["status"], "open")
                self.assertNotIn("settledBy", receipt["verify"])
                self.assertTrue(all(o["status"] == "open"
                                    for o in receipt["verify"]["obligations"]))
                self.assertEqual(receipt["check"]["axioms"], [])
                self.assertNotIn("trusted-leanforth", kinds(receipt))
                self.assertIn("NOT VERIFIED: open", text)

    def test_refuted_not_accepted(self):
        with scratch() as out:
            status, text = verify("wrong-clamp-swapped", out, {"verdicts": {"refuted": "rejected"}})
            self.assertEqual(status, 1, text)
            receipt = receipt_at(out, "lf-clamp")
            self.assertEqual((receipt["check"]["status"], receipt["verify"]["status"]),
                             ("rejected", "open"))
            self.assertEqual(receipt["verify"]["obligations"][0]["status"], "open")

    def test_no_receipt(self):
        cases = [  # NOT PROVED: LeanForth and Lean both name sorryAx
            ({"bits": {"contract": 13}, "notProvedBy": {"contract": ["sorryAx"]},
              "axioms": {"contract": ["propext", "sorryAx", "Quot.sound"]}}, 6, "not-proved"),
            ({"axioms": {"O1": ["propext", "Classical.choice", "Quot.sound"]}}, 5,
             "axioms-differ"),
            ({"check": "invalid-read"}, 4, "export-invalid"),
        ]
        for fake, expected, code in cases:
            with self.subTest(fake), scratch() as out:
                status, text = verify("lf-clamp", out, fake)
                self.assertEqual((status, problem_codes(text)), (expected, [code]), text)
                self.assertIsNone(receipt_at(out, "lf-clamp"))
                self.assertIn("no receipt written", text)

    def test_options_reach_the_checker(self):
        seen = []
        real = program_receipt.leanforth_args
        with mock.patch.object(program_receipt, "leanforth_args",
                               lambda export, options: seen.append(options) or
                               real(export, options)), scratch() as out:
            verify("lf-clamp", out, extra=["--fuel", "30", "--jobs", "1",
                                           "--memory-per-check", "64", "--checked"])
        self.assertEqual(seen, [["--jobs", "1", "--fuel", "30", "--memory-per-check", "64",
                                 "--checked"]])


class Malformed(unittest.TestCase):
    """Malformed input and missing tools: exit status 4 (5 for an internal fault), no receipt."""

    def test_command_line(self):
        for argv in ([], ["src/program/clamp.fs"], ["--contract", "x"],
                     ["a.fs", "b.fs", "--contract", "c"],
                     ["src/program/clamp.fs", "--contract", "c", "--fuel", "0"],
                     ["src/program/clamp.fs", "--contract", "c", "--jobs", "-1"],
                     ["src/program/clamp.fs", "--contract", "c", "--fuel", "1e3"],
                     ["src/program/clamp.fs", "--contract", "c", "--lean-time-limit", "x"],
                     ["src/program/clamp.fs", "--contract", "c", "--nothing"]):
            with self.subTest(argv):
                status, text = cli(argv)
                self.assertEqual((status, problem_codes(text)), (4, ["usage"]), text)
                self.assertTrue(text.startswith("error: usage: "), text)

    def test_outside_the_checkout(self):
        with tempfile.TemporaryDirectory() as outside:
            source = Path(outside) / "w.fs"
            shutil.copy(ROOT / "src/program/clamp.fs", source)
            contract = "tests/program/contracts/lf-clamp.contract"
            for argv in ([source, "--contract", contract],
                         ["src/program/clamp.fs", "--contract", Path(outside) / "c"],
                         ["src/program/clamp.fs", "--contract", contract, "--out", outside],
                         ["src/program/clamp.fs", "--contract", contract, "--out",
                          ".claude/work/x"],
                         ["src/program/clamp.fs", "--contract", contract, "--out", "."]):
                with self.subTest(argv):
                    status, text = cli(argv)
                    self.assertEqual((status, problem_codes(text)), (4, ["outside-folder"]),
                                     text)
            status, text = cli(["src/program/clamp.fs", "--contract", contract], cwd=outside)
            self.assertEqual((status, problem_codes(text)), (4, ["outside-folder"]), text)

    def test_source(self):
        with scratch() as folder:
            cases = [(": w ( n -- m ) here + ;\n", 2, "unsupported @1:16: a Forth word "
                      "outside IR 0.2: here"),
                     (": w ( n -- m ) 1 +\n", 4, "invalid @1:0: definition not closed")]
            for source, expected, diagnostic in cases:
                with self.subTest(source):
                    fixture = Fixture(folder, source, contract_text())
                    status, text = cli(fixture.argv())
                    self.assertEqual((status, problem_codes(text)),
                                     (expected, ["source-refused"]), text)
                    self.assertIn(diagnostic, text)
                    self.assertIsNone(receipt_at(fixture.out, "w"))
            status, text = cli([Path(folder) / "none.fs", "--contract", "c"])
            self.assertEqual((status, problem_codes(text)), (4, ["source-unreadable"]), text)
            deep = Path(folder) / ("d" * 90)
            deep.mkdir()
            shutil.copy(ROOT / "src/program/clamp.fs", deep / "w.fs")
            status, text = cli([deep / "w.fs", "--contract",
                                "tests/program/contracts/lf-clamp.contract"])
            self.assertEqual((status, problem_codes(text)), (3, ["source-refused"]), text)
            self.assertIn("full", text)

    def test_contract(self):
        clamp = (CONTRACTS / "lf-clamp.contract").read_text(encoding="utf-8")
        cases = [
            ("not a contract", clamp.replace("lf-contract 0.1", "lf-contract 0.2")),
            ("no id", clamp.replace("id lf-clamp/0\n", "")),
            ("no ir", clamp.replace("ir tests/program/ir/clamp.ir\n", "")),
            ("an input named c", clamp.replace("inputs value lower upper",
                                               "inputs value c upper")),
            ("a bad expression", clamp.replace("ensure r = min(", "ensure r = min((")),
            ("an unknown line", clamp + "frobnicate\n"),
            ("an indented line outside a case", clamp.replace("id lf-clamp/0", "  out x")),
            ("a case without out", clamp.replace("  out false\n", "")),
            ("min with one argument", clamp.replace("min(max(value, lower), upper)",
                                                    "min(value)")),
            ("an ir line outside the checkout", clamp.replace(
                "ir tests/program/ir/clamp.ir", "ir ../clamp.ir")),
            ("deep nesting", clamp.replace("ensure r = min(", "ensure r = " + "(" * 5000 +
                                           "min(").replace("upper)\n", "upper)" + ")" * 5000 +
                                                           "\n", 1)),
        ]
        with scratch() as folder:
            path = Path(folder) / "c.contract"
            for name, text in cases:
                with self.subTest(name):
                    path.write_text(text, encoding="utf-8")
                    status, out = cli(["src/program/clamp.fs", "--contract", path, "--out",
                                       Path(folder) / "out"])
                    self.assertEqual((status, problem_codes(out)), (4, ["contract-malformed"]),
                                     out)
            path.write_bytes(clamp.encode("utf-8").replace(b"lf-clamp/0", b"lf-clamp/\xff"))
            status, out = cli(["src/program/clamp.fs", "--contract", path])
            self.assertEqual((status, problem_codes(out)), (4, ["contract-unreadable"]), out)
            status, out = cli(["src/program/clamp.fs", "--contract", Path(folder) / "none"])
            self.assertEqual((status, problem_codes(out)), (4, ["contract-unreadable"]), out)

    def test_word_and_ir(self):
        clamp = (CONTRACTS / "lf-clamp.contract").read_text(encoding="utf-8")
        with scratch() as folder:
            stale = Path(folder) / "stale.ir"
            stale.write_text((ROOT / "tests/program/ir/clamp.ir").read_text(encoding="utf-8")
                             .replace("prim max", "prim min", 1), encoding="utf-8")
            cases = [
                ("a word the file lacks", clamp.replace("word lf-clamp", "word lf-clamp2"),
                 "word-not-found"),
                ("a word in upper case", clamp.replace("word lf-clamp", "word LF-CLAMP"),
                 "word-not-found"),
                ("a constant", clamp.replace("word lf-clamp", "word lf-example-max").replace(
                    "clamp.ir", "examples.ir"), "word-not-found"),
                ("a stale IR file", clamp.replace("tests/program/ir/clamp.ir", rel(stale)),
                 "contract-ir-differs"),
                ("another file's IR", clamp.replace("tests/program/ir/clamp.ir",
                                                    "tests/program/ir/examples.ir"),
                 "contract-ir-differs"),
                ("a missing IR file", clamp.replace("tests/program/ir/clamp.ir",
                                                    "tests/program/ir/none.ir"),
                 "contract-ir-differs"),
            ]
            path = Path(folder) / "c.contract"
            for name, text, code in cases:
                with self.subTest(name):
                    path.write_text(text, encoding="utf-8")
                    source = "src/program/" + ("examples.fs" if "examples.ir" in text and
                                               name == "a constant" else "clamp.fs")
                    status, out = cli([source, "--contract", path, "--out",
                                       Path(folder) / "out"])
                    self.assertEqual((status, problem_codes(out)), (4, [code]), out)
                    self.assertIsNone(receipt_at(Path(folder) / "out", "lf-clamp"))

    def test_gforth(self):
        clamp = ["src/program/clamp.fs", "--contract", "tests/program/contracts/lf-clamp.contract"]
        status, text = cli(clamp, env={"GFORTH": "/nonexistent/gforth"})
        self.assertEqual((status, problem_codes(text)), (4, ["gforth-not-found"]), text)
        with scratch() as folder:
            silent = Path(folder) / "gforth"
            silent.write_text("#!/bin/sh\nexit 3\n", encoding="utf-8")
            silent.chmod(0o755)
            status, text = cli(clamp + ["--out", Path(folder) / "out"],
                               env={"GFORTH": str(silent)})
            self.assertEqual((status, problem_codes(text)), (5, ["internal"]), text)

    def test_source_changed_while_read(self):
        with scratch() as folder:
            fixture = Fixture(folder, ": w ( n -- m ) 1 + ;\n", contract_text())
            changer = Path(folder) / "gforth"
            changer.write_text(f'#!/bin/sh\nprintf "\\n" >> {fixture.source}\n'
                               f'exec {GFORTH} "$@"\n', encoding="utf-8")
            changer.chmod(0o755)
            status, text = cli(fixture.argv(), env={"GFORTH": str(changer)})
            self.assertEqual((status, problem_codes(text)), (4, ["source-changed"]), text)
            self.assertIsNone(receipt_at(fixture.out, "w"))


class Limits(unittest.TestCase):
    def test_paths_limit(self):
        with scratch() as out:
            status, text = verify("lf-clamp", out, extra=["--paths-limit", "1"])
            self.assertEqual((status, problem_codes(text)), (3, ["paths-limit"]), text)
            self.assertIsNone(receipt_at(out, "lf-clamp"))
            self.assertFalse((Path(out) / "obligations.lean").exists())
        with scratch() as folder:   # 2^10 paths, above the default limit of 256
            body = "\n".join(["dup 0< if 1+ then"] * 10)
            fixture = Fixture(folder, f": w ( n -- m ) {body} ;\n", contract_text())
            status, text = run(fixture.argv())
            self.assertEqual((status, problem_codes(text)), (3, ["paths-limit"]), text)
            self.assertIn("more than 256 paths", text)

    def test_search_limit(self):
        with scratch() as out:
            status, text = verify("lf-clamp", out, extra=["--search-limit", "1727"])
            self.assertEqual((status, problem_codes(text)), (3, ["search-limit"]), text)
            self.assertIn("would try 1,728 input combinations", text)
            self.assertIsNone(receipt_at(out, "lf-clamp"))
        with scratch() as out:   # exactly at the limit: searched
            status, text = verify("lf-clamp", out, extra=["--search-limit", "1728"])
            self.assertEqual(status, 0, text)
        with scratch() as folder:   # six inputs: 12^6 combinations, above the default
            fixture = Fixture(folder, ": w ( a b c d e f -- m ) + + + + + ;\n",
                              contract_text(inputs="a b d e j k"))
            status, text = run(fixture.argv())
            self.assertEqual((status, problem_codes(text)), (3, ["search-limit"]), text)


class Workflow(unittest.TestCase):
    def test_from_another_folder(self):
        with scratch() as folder:
            status, text = cli(["../src/program/examples.fs", "--contract",
                                "program/contracts/lf-gcd.contract", "--out",
                                os.path.relpath(folder, ROOT / "tests")], cwd=ROOT / "tests")
            self.assertEqual(status, 2, text)
            self.assertEqual(receipt_at(folder, "lf-gcd")["program"]["source"]["path"],
                             "src/program/examples.fs")

    def test_default_out(self):
        with scratch() as folder:
            status, text = cli([ROOT / "src/program/examples.fs", "--contract",
                                CONTRACTS / "lf-factorial.contract"], cwd=folder)
            self.assertEqual(status, 2, text)
            out = Path(folder) / "verify-out" / "lf-factorial"
            self.assertIn(f"receipt: {rel(out)}/lf-factorial.receipt.json (schema 0.3)", text)
            self.assertIsNotNone(receipt_at(out, "lf-factorial"))

    def test_safe_names(self):
        self.assertEqual(program_verify.safe_name("lf-clamp"), "lf-clamp")
        self.assertEqual(program_verify.safe_name("lf-add-above?"), "lf-add-above_")
        self.assertEqual(program_verify.safe_name("lf-clamp'1"), "lf-clamp_1")
        self.assertEqual(program_verify.safe_name("-x"), "_-x")
        self.assertEqual(program_verify.safe_name(".x"), "_.x")

    def test_earlier_files_removed_by_name(self):
        with scratch() as out:
            names = ["obligations.lean", "lf-clamp.ndjson", "lf-clamp.ndjson.manifest.json",
                     "lf-clamp.evidence.json", "lf-clamp.receipt.json",
                     "lf-clamp.receipt.json.partial", "lf-clamp.ndjson.partial"]
            for name in names + ["keep.txt", "lf-gcd.receipt.json"]:
                (Path(out) / name).write_text("earlier\n", encoding="utf-8")
            clamp = (CONTRACTS / "lf-clamp.contract").read_text(encoding="utf-8")
            stale = Path(out) / "c.contract"
            stale.write_text(clamp.replace("clamp.ir", "examples.ir"), encoding="utf-8")
            status, text = cli(["src/program/clamp.fs", "--contract", stale, "--out", out])
            self.assertEqual((status, problem_codes(text)), (4, ["contract-ir-differs"]))
            self.assertEqual(sorted(p.name for p in Path(out).iterdir()),
                             ["c.contract", "keep.txt", "lf-gcd.receipt.json"])

    def test_export_kept_only_when_asked(self):
        with scratch() as out:
            verify("lf-clamp", out)
            self.assertFalse((Path(out) / "lf-clamp.ndjson").exists())
            self.assertTrue((Path(out) / "lf-clamp.ndjson.manifest.json").exists())
        with scratch() as out:
            verify("lf-clamp", out, extra=["--keep-export"])
            self.assertTrue((Path(out) / "lf-clamp.ndjson").exists())

    def test_failed_write_leaves_nothing(self):
        with scratch() as out, mock.patch.object(program_verify.os, "fsync",
                                                 side_effect=OSError(28, "No space left")):
            status, text = verify("lf-clamp", out)
            self.assertEqual((status, problem_codes(text)), (4, ["receipt-not-written"]), text)
            left = sorted(p.name for p in Path(out).iterdir())
            self.assertEqual(left, ["lf-clamp.ndjson.manifest.json", "obligations.lean"])

    def test_two_runs_same_bytes(self):
        for contract, fake in (("lf-clamp", None), ("wrong-in-range-exclusive", None),
                               ("lf-gcd", None), ("lf-clamp", {"verdicts": {"O1": "rejected"}})):
            with self.subTest(contract), scratch() as first, scratch() as second:
                results = []
                for out in (first, second):
                    status, text = verify(contract, out, fake, extra=["--jobs", "1"]
                                          if out == first else [])
                    files = {p.name: p.read_bytes() for p in Path(out).iterdir()}
                    results.append((status, text.replace(rel(out), "OUT"), files))
                self.assertEqual(results[0][:2], results[1][:2])
                self.assertEqual(results[0][2].keys(), results[1][2].keys())
                for name in results[0][2]:
                    if name.endswith((".receipt.json", ".evidence.json")):
                        texts = [r[2][name].decode().replace(rel(o), "OUT")
                                 for r, o in zip(results, (first, second))]
                        self.assertEqual(texts[0], texts[1], name)

    def test_invalid_receipt_never_written(self):
        real = program_receipt.assumptions
        without_runtime = lambda *a, **k: [x for x in real(*a, **k)  # noqa: E731
                                           if x["kind"] != "trusted-runtime"]
        with scratch() as out, mock.patch.object(program_receipt, "assumptions",
                                                 without_runtime):
            status, text = verify("lf-clamp", out)
            self.assertEqual((status, problem_codes(text)), (5, ["internal"]), text)
            self.assertIn("the receipt built is not valid", text)
            self.assertIsNone(receipt_at(out, "lf-clamp"))

    def test_expect_note(self):
        with scratch() as folder:
            clamp = (CONTRACTS / "lf-clamp.contract").read_text(encoding="utf-8")
            path = Path(folder) / "c.contract"
            path.write_text(clamp.replace("expect discharged", "expect refuted"),
                            encoding="utf-8")
            status, text = run(["src/program/clamp.fs", "--contract", path, "--out",
                                Path(folder) / "out"])
            self.assertEqual(status, 0, text)
            self.assertIn("note: the contract expects refuted; verify found discharged", text)


class Shared(unittest.TestCase):
    """The helpers of scripts/program_receipt.py that the driver shares with the clamp receipt."""

    def test_program_words_output(self):
        self.assertEqual(program_receipt.program_words_output("lf-ir 0.1\nsource s\n0 \n"),
                         (0, "lf-ir 0.1\nsource s\n", None))
        self.assertEqual(program_receipt.program_words_output(
            "lf-ir 0.1\nsource s\nunsupported @1:2: x\n5 \n"),
            (5, "lf-ir 0.1\nsource s\n", "unsupported @1:2: x"))
        self.assertEqual(program_receipt.program_words_output("crash\n")[0], None)

    def test_export_verdicts(self):
        accepted = {"declarations": 3, "accepted": 3, "counts": {
            "declarations": 3, "accepted": 3, "rejected": 0, "notProved": 0}}
        self.assertEqual(program_receipt.export_verdicts(accepted), {"accepted"})
        self.assertEqual(program_receipt.export_verdicts(
            {"declarations": 3, "accepted": 2}), {"unaccounted"})
        other = copy.deepcopy(accepted)
        other["counts"].update(accepted=2, notChecked=1)
        self.assertEqual(program_receipt.export_verdicts(other), {"accepted", "not-checked"})

    def test_check_status_reads_the_whole_export(self):
        leanforth = {"declarations": 3, "accepted": 2, "counts": {
            "declarations": 3, "accepted": 2, "rejected": 1},
            "theorems": {"T": {"verdict": "accepted", "axioms": []}}}
        self.assertEqual(program_receipt.check_status(leanforth, ["T"]), "rejected")
        leanforth["counts"] = {"declarations": 3, "accepted": 2, "exhausted": 1}
        self.assertEqual(program_receipt.check_status(leanforth, ["T"]), "failed")

    def test_refusal_codes(self):
        for call, code in ((lambda: program_receipt.refuse_ir_02("lf-ir 0.2\n", "x.ir"),
                            "ir-needs-receipt-0.4"),
                           (lambda: program_receipt.word_line("lf-ir 0.1\n", "w"),
                            "word-not-found")):
            with self.assertRaises(program_receipt.Refusal) as caught:
                call()
            self.assertEqual(caught.exception.problem, code)
            self.assertIsInstance(caught.exception, SystemExit)

    def test_every_code_documented_and_reached(self):
        doc = (ROOT / "docs/programming/PROGRAM_VERIFY.md").read_text(encoding="utf-8")
        tests = Path(__file__).read_text(encoding="utf-8")
        for code in program_verify.CODES:
            self.assertIn(f"`{code}`", doc, code)
            self.assertIn(f'"{code}"', tests.replace(f'"{code}": (', ""), code)


if __name__ == "__main__":
    os.chdir(ROOT)
    unittest.main(verbosity=1)
