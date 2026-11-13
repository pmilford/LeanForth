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
6. The command (plan 8.4.1c): bin/leanforth verify, its exit statuses (any
   other status of the interpreter is 5), --json (one report the schema
   accepts, its statuses the receipt's, its exit status the command's, the
   same on every run but for measured), --write-ir.
7. Replay (plan 8.4.1d): a receipt replays clean, also with --rerun; each
   tampering is refused with its code: the source, the contract, its IR
   file, the generated Lean file, the manifest, the evidence record (by its
   hash), a status, an axiom, an added field, a duplicate id, an old or
   unknown version, a duplicate key, a missing file, a receipt verify did
   not write; a receipt and its evidence changed together replay clean and
   --rerun refuses them.
"""
import contextlib
import copy
import io
import json
import os
from pathlib import Path
import re
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
sys.path.insert(0, str(ROOT / "tests" / "support"))
from schema_subset import Validator, load_strict  # noqa: E402
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
                 program_verify.TEST_TOOLS: "1", "VERIFY_FAKE": json.dumps(fake or {}),
                 **(env or {})}
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
                                        rel(Path(out) / "lf-clamp.ndjson.manifest.json"),
                                        rel(Path(out) / "lf-clamp.evidence.json")])
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
                golden = (GOLDEN / f"{contract}.receipt.json").read_text(encoding="utf-8")
                # the Gforth that ran (a coverage wrapper under make coverage) aside
                self.assertEqual(*(re.sub(r'("name": "gforth",\n\s*"version": ")[^"]*"',
                                          r'\1GFORTH"', text) for text in (found, golden)))

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

    def test_post_printed_by_lean(self):
        """Review B1: the postcondition comes from Lean's own print in this run, recorded and
        hashed in the evidence; --detail prints it."""
        with scratch() as out:
            status, text = verify("lf-clamp", out, extra=["--detail"])
            self.assertEqual(status, 0, text)
            self.assertIn("post, as Lean printed it in this run:\n"
                          "  def ProgramVC.LfClamp0.post : Cells → List Int → Prop :=", text)
            self.assertIn("the theorem, as Lean printed it in this run:\n"
                          "  ProgramVC.LfClamp0.contract (c : Cells) (pre1 : True)", text)
            evidence = json.loads((Path(out) / "lf-clamp.evidence.json").read_text())
            for key, start in (("post", "def ProgramVC.LfClamp0.post"),
                               ("statement", "ProgramVC.LfClamp0.contract")):
                self.assertTrue(evidence["lean"][key].startswith(start))
                self.assertEqual(evidence["lean"][f"{key}Sha256"],
                                 program_verify.digest(evidence["lean"][key].encode("utf-8")))
            lean = (Path(out) / "obligations.lean").read_text()
            self.assertIn("#print ProgramVC.LfClamp0.post", lean)
            self.assertIn("#check ProgramVC.LfClamp0.contract", lean)
        with scratch() as out:
            verify("wrong-clamp-swapped", out)
            self.assertIn("#check ProgramVC.LfClampWrongSwapped.refuted",
                          (Path(out) / "obligations.lean").read_text())
        with scratch() as out:
            status, text = verify("lf-clamp", out, {"lean": "no-post"})
            self.assertEqual((status, problem_codes(text)), (5, ["internal"]), text)

    def test_pinned_tools_unless_testing(self):
        """Review M3: without the test switch LEAN and LEANEXPORT are ignored and the
        checkout's pinned Lean runs; the evidence names every tool with its SHA-256."""
        with scratch() as out, mock.patch.object(program_verify, "PINNED_LEAN",
                                                 Path("/nonexistent/lean")):
            status, text = verify("lf-clamp", out, env={program_verify.TEST_TOOLS: "0"})
            self.assertEqual((status, problem_codes(text)), (4, ["lean-not-found"]), text)
            self.assertIn("/nonexistent/lean", text)
        with scratch() as out:   # a toolchain folder of stand-ins in place of the pinned one
            toolchain = Path(out) / "bin"
            toolchain.mkdir()
            for name in ("lean", "leanexport"):
                (toolchain / name).symlink_to(FAKE)
            with mock.patch.object(program_verify, "PINNED_LEAN", toolchain / "lean"):
                status, text = verify("lf-clamp", Path(out) / "o", lean="/nonexistent/lean",
                                      env={program_verify.TEST_TOOLS: "0", "LEANEXPORT": "/no"})
            self.assertEqual(status, 0, text)
            evidence = json.loads((Path(out) / "o" / "lf-clamp.evidence.json").read_text())
            self.assertFalse(evidence["testTools"])
            for name in ("lean", "leanexport"):
                self.assertEqual(evidence["tools"][name], {
                    "path": rel(toolchain) + "/" + name,
                    "sha256": program_verify.digest(FAKE.read_bytes())})
            self.assertEqual(set(evidence["tools"]), {"gforth", "lean", "leanexport"})

    def test_lean_not_found(self):
        with scratch() as out:
            status, text = verify("lf-clamp", out, lean="/nonexistent/lean")
            self.assertEqual((status, problem_codes(text)), (4, ["lean-not-found"]))
            self.assertIsNone(receipt_at(out, "lf-clamp"))


class Checker(unittest.TestCase):
    """LeanForth's verdicts as the receipt's check status: only all accepted is positive."""

    CASES = [  # (stand-in, exit status, problem, check status)
        ({"verdicts": {"contract": "rejected"}}, 5, "checkers-disagree", "rejected"),
        ({"verdicts": {"O2": "rejected"}}, 5, "checkers-disagree", "rejected"),
        ({"other": "rejected"}, 5, "checkers-disagree", "rejected"),
        ({"verdicts": {"contract": "unknown"}}, 2, "proof-undecided", "unsupported"),
        ({"verdicts": {"O1": "unsupported"}}, 2, "proof-undecided", "unsupported"),
        ({"verdicts": {"contract": "exhausted"}, "exit": 3}, 3, "proof-exhausted", "failed"),
        ({"other": "full", "exit": 3}, 3, "proof-exhausted", "failed"),
        ({"verdicts": {"O1": "invalid"}, "exit": 5}, 5, "internal", "failed"),
        ({"verdicts": {"O2": "not-checked"}}, 5, "internal", "failed"),
        ({"check": "stopped", "exit": 5}, 5, "internal", "failed"),
        ({"check": "not-run"}, 5, "internal", "failed"),
        ({"exit": 1}, 5, "internal", "failed"),
        ({"check": "no-report"}, 5, "internal", "failed"),
    ]

    def test_every_kind_reported(self):
        """Verdicts of several kinds: each kind is a problem, the exit status the most severe
        in the CLI's order (as bin/leanforth check's)."""
        cases = [({"verdicts": {"contract": "unknown"}, "other": "exhausted", "exit": 3}, 3,
                  ["proof-undecided", "proof-exhausted"], "unsupported"),
                 ({"verdicts": {"O1": "rejected", "O2": "exhausted"}, "exit": 1}, 5,
                  ["checkers-disagree", "proof-exhausted"], "rejected"),
                 ({"verdicts": {"O1": "invalid", "O2": "unknown"}, "exit": 5}, 5,
                  ["proof-undecided", "internal"], "unsupported")]
        for fake, expected, codes, check in cases:
            with self.subTest(fake), scratch() as out:
                status, text = verify("lf-clamp", out, fake)
                self.assertEqual((status, problem_codes(text)), (expected, codes), text)
                self.assertEqual(receipt_at(out, "lf-clamp")["check"]["status"], check)

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
            self.assertEqual((status, problem_codes(text)), (5, ["checkers-disagree"]), text)
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

    def test_final_run_report_only(self):
        """Review M2: only a final run's check report 0.4 is read; no receipt otherwise."""
        for fake in ({"reportVersion": "0.3"}, {"snapshot": True}):
            with self.subTest(fake), scratch() as out:
                status, text = verify("lf-clamp", out, fake)
                self.assertEqual((status, problem_codes(text)), (5, ["internal"]), text)
                self.assertIn("not a final run's check report 0.4", text)
                self.assertIsNone(receipt_at(out, "lf-clamp"))

    def test_namespace_is_the_generators(self):
        """Review B1: the export's ProgramVC declarations are exactly the generator's, with
        only Lean's auxiliary lemmas under them."""
        cases = [({"extra": ["ProgramVC.LfClamp0.sneaky"]}, 5),
                 ({"extra": ["ProgramVC.ir_evil"]}, 5),
                 ({"extra": ["ProgramVC.LfClamp0.O1.sneaky"]}, 5),
                 ({"drop": ["post"]}, 5), ({"drop": ["program"]}, 5),
                 ({"verdicts": {"O2": "absent"}, "extra": []}, 5),
                 ({"extra": ["ProgramVC.LfClamp0.contract._simp_x"]}, 5),
                 ({"extra": ["ProgramVC.LfClamp0.O1._proof_1_4", "ProgramVC.ir_max._proof_1_1",
                             "ProgramVC.LfClamp0.contract._simp_1_7", "ProgramIR.anything"]}, 0)]
        for fake, expected in cases:
            with self.subTest(fake), scratch() as out:
                status, text = verify("lf-clamp", out, fake)
                self.assertEqual(status, expected, text)
                if expected:
                    self.assertEqual(problem_codes(text)[:1], ["export-differs"], text)
                    self.assertIsNone(receipt_at(out, "lf-clamp"))

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
            ("an unbound name", clamp.replace("-> r = upper", "-> r = default")),
            ("no case", clamp.split("case lower > upper", 1)[0]),
            ("a second word line", clamp + "word lf-clamp\n"),
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

    def test_evidence_named_in_the_receipt(self):
        """Review M3: the receipt names the evidence record with its SHA-256: in check.evidence
        when something was checked, and always in its provenance note."""
        for contract, word, checked in (("lf-clamp", "lf-clamp", True),
                                        ("lf-gcd", "lf-gcd", False)):
            with self.subTest(contract), scratch() as out:
                verify(contract, out)
                path = Path(out) / f"{word}.evidence.json"
                sha = program_verify.digest(path.read_bytes())
                receipt = receipt_at(out, word)
                self.assertIn(f"{rel(path)}, SHA-256 {sha}", receipt["provenance"]["note"])
                refs = [e for e in receipt["check"]["evidence"] if e["path"] == rel(path)]
                self.assertEqual(refs, [{"path": rel(path), "sha256": sha}] if checked else [])

    def test_a_python_fault_is_5(self):
        """Review M1: a fault of the driver's ends with status 5, never 1."""
        with scratch() as out, mock.patch.object(
                program_verify.program_vc, "generate_parsed", side_effect=RuntimeError("boom")):
            status, text = verify("lf-clamp", out)
            self.assertEqual((status, problem_codes(text)), (5, ["internal"]), text)
        done = subprocess.run([sys.executable, "-I", "-c", "import sys; sys.path.insert(0, "
                               "'scripts'); import program_verify; raise RuntimeError('boom')"],
                              cwd=ROOT, capture_output=True, text=True, timeout=60)
        self.assertEqual(done.returncode, 5, done.stdout + done.stderr)
        self.assertIn("error: internal: RuntimeError: boom", done.stdout)

    def test_search_notes_printed(self):
        clamp = (CONTRACTS / "lf-clamp.contract").read_text(encoding="utf-8")
        with scratch() as folder:
            path = Path(folder) / "c.contract"
            path.write_text(clamp.split("case lower <= upper", 1)[0], encoding="utf-8")
            status, text = run(["src/program/clamp.fs", "--contract", path, "--out",
                                Path(folder) / "out"])
            self.assertIn("note: search: inputs no case covers: 936 of the 1,728", text)

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

    def test_gforth_without_a_version(self):
        """A Gforth (a wrapper, as under make coverage) whose --version names no version is
        recorded as version unknown, never as its text."""
        with scratch() as folder:
            wrapper = Path(folder) / "gforth"
            wrapper.write_text(f'#!/bin/sh\nif [ "$1" = --version ]; then echo "error: no"; '
                               f'exit 0; fi\nexec {GFORTH} "$@"\n', encoding="utf-8")
            wrapper.chmod(0o755)
            status, text = cli(["src/program/examples.fs", "--contract",
                                CONTRACTS / "lf-gcd.contract", "--out", Path(folder) / "out"],
                               env={"GFORTH": str(wrapper)})
            self.assertEqual(status, 2, text)
            tools = receipt_at(Path(folder) / "out", "lf-gcd")["tools"]
            self.assertIn({"name": "gforth", "version": "unknown"}, tools)

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
        other["accepted"] = 2
        other["counts"].update(accepted=2, notChecked=1)
        self.assertEqual(program_receipt.export_verdicts(other), {"accepted", "not-checked"})
        other["counts"]["notChecked"] = 0     # counts that do not name every declaration
        self.assertEqual(program_receipt.export_verdicts(other), {"accepted", "unaccounted"})

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


REPORT_SCHEMA = Validator(load_strict(
    (ROOT / "schemas" / "verify-report-0.1.schema.json").read_text(encoding="utf-8")))


def report_of(text):
    """The one JSON text --json printed, read strictly and checked against the schema."""
    report = load_strict(text)
    errors = REPORT_SCHEMA.errors(report)
    if errors:
        raise AssertionError(f"report refused by its schema: {errors[:3]}")
    return report


class Report(unittest.TestCase):
    """--json (plan 8.4.1c): one report the schema accepts, consistent with the run."""

    CASES = [("lf-clamp", None, 0), ("wrong-clamp-swapped", None, 1), ("lf-gcd", None, 2),
             ("lf-clamp", {"lean": "fail"}, 2), ("lf-clamp", {"verdicts": {"O1": "rejected"}}, 5),
             ("lf-clamp", {"axioms": {"O1": ["propext"]}, "bits": {"O1": 7}}, 5),
             ("sha-ch", None, 2)]

    def test_reports(self):
        for contract, fake, expected in self.CASES:
            with self.subTest((contract, fake)), scratch() as out:
                status, text = verify(contract, out, fake, extra=["--json"])
                self.assertEqual(status, expected, text)
                report = report_of(text)
                self.assertEqual(report["exitStatus"], status)
                word = "lf-gcd" if contract == "lf-gcd" else "sha-ch" if contract == "sha-ch" \
                    else "lf-clamp"
                receipt = receipt_at(out, word)
                if receipt is None:
                    self.assertIsNone(report["receipt"])
                    self.assertEqual((report["check"], report["verify"]), (None, None))
                    self.assertTrue(report["problems"])
                    continue
                self.assertEqual((report["check"], report["verify"], report["run"]),
                                 (receipt["check"]["status"], receipt["verify"]["status"],
                                  receipt["run"]["status"]))
                path = Path(out) / f"{word}.receipt.json"
                self.assertEqual(report["receipt"], {
                    "path": rel(path), "schemaVersion": "0.3",
                    "sha256": program_verify.digest(path.read_bytes())})
                self.assertEqual([o["id"] for o in report["obligations"]],
                                 [o["id"] for o in receipt["verify"]["obligations"]])

    def test_same_on_every_run_but_measured(self):
        with scratch() as out:
            reports = []
            for _ in range(2):
                status, text = verify("lf-clamp", out, extra=["--json"])
                report = report_of(text)
                report.pop("measured")
                reports.append(report)
            self.assertEqual(reports[0], reports[1])
            self.assertEqual([s["step"] for s in reports[0]["steps"]],
                             ["command-line", "read-word", "read-contract", "generate", "prove",
                              "check", "write"])
            self.assertTrue(all(s["outcome"] == "ok" for s in reports[0]["steps"]))
            self.assertTrue(reports[0]["contract"]["theorem"].startswith(
                "ProgramVC.LfClamp0.contract"))

    def test_a_usage_error_is_text(self):
        status, text = cli(["--json"])
        self.assertEqual((status, problem_codes(text)), (4, ["usage"]), text)


class WriteIr(unittest.TestCase):
    def test_write_ir(self):
        with scratch() as folder:
            fixture = Fixture(folder, ": w ( n -- n n ) dup ;\n", ONE_INPUT.format(
                word="w", inputs="n").replace("  out m\n", "  out n n\n"))
            fixture.ir.unlink()
            status, text = run(fixture.argv("--write-ir"))
            self.assertEqual(status, 0, text)
            self.assertIn(f"ir: wrote {rel(fixture.ir)}", text)
            self.assertFalse(fixture.out.exists())
            done = subprocess.run(program_receipt.program_words_args(GFORTH, rel(fixture.source)),
                                  cwd=ROOT, capture_output=True, text=True, timeout=120,
                                  stdin=subprocess.DEVNULL)
            self.assertEqual(fixture.ir.read_text(), program_receipt.program_words_output(
                done.stdout)[1])
            status, text = run(fixture.argv())
            self.assertEqual(status, 0, text)
            fixture.ir.unlink()
            status, text = run(fixture.argv())
            self.assertEqual((status, problem_codes(text)), (4, ["contract-ir-differs"]), text)

    def test_write_ir_inside_the_checkout_only(self):
        clamp = (CONTRACTS / "lf-clamp.contract").read_text(encoding="utf-8")
        with scratch() as folder:
            path = Path(folder) / "c.contract"
            path.write_text(clamp.replace("ir tests/program/ir/clamp.ir", "ir ../x.ir"),
                            encoding="utf-8")
            status, text = cli(["src/program/clamp.fs", "--contract", path, "--write-ir"])
            self.assertEqual((status, problem_codes(text)), (4, ["contract-malformed"]), text)


class Command(unittest.TestCase):
    """bin/leanforth verify (plan 8.4.1c)."""

    def leanforth(self, argv, env=None):
        variables = {**os.environ, "GFORTH": GFORTH, **(env or {})}
        done = subprocess.run(["bash", str(ROOT / "bin" / "leanforth"), "verify", *map(str, argv)],
                              cwd=ROOT, env=variables, capture_output=True, text=True,
                              timeout=600, stdin=subprocess.DEVNULL)
        return done.returncode, done.stdout + done.stderr

    def test_statuses(self):
        status, text = self.leanforth([])
        self.assertEqual((status, problem_codes(text)), (4, ["usage"]), text)
        self.assertIn("try: leanforth verify --help", text)
        with scratch() as out:
            status, text = self.leanforth(["src/program/examples.fs", "--contract",
                                           CONTRACTS / "lf-gcd.contract", "--out", out])
            self.assertEqual(status, 2, text)
            self.assertIsNotNone(receipt_at(out, "lf-gcd"))
        status, text = self.leanforth(["--help"])
        self.assertEqual(status, 0, text)
        self.assertIn("usage: leanforth verify", text)

    def test_any_other_status_is_5(self):
        with scratch() as folder:
            fake = Path(folder) / "python3"
            fake.write_text("#!/bin/sh\nexit 9\n", encoding="utf-8")
            fake.chmod(0o755)
            status, text = self.leanforth(["--help"], env={
                "PATH": f"{folder}:{os.environ['PATH']}"})
            self.assertEqual(status, 5, text)
            self.assertIn("error: internal: leanforth verify ended with status 9", text)


class Replay(unittest.TestCase):
    """--replay and --replay --rerun (plan 8.4.1d)."""

    def made(self, folder):
        """A discharged receipt (stand-in tools) of a word of the folder's own, whose
        source, contract and IR file a test may change."""
        fixture = Fixture(folder, ": w ( n -- n n ) dup ;\n", ONE_INPUT.format(
            word="w", inputs="n").replace("  out m\n", "  out n n\n"))
        status, text = run(fixture.argv())
        self.assertEqual(status, 0, text)
        return fixture, rel(fixture.out / "w.receipt.json")

    def replay(self, receipt, *extra):
        return run(["--replay", receipt, *extra])

    def test_clean(self):
        with scratch() as folder:
            _, receipt = self.made(folder)
            for extra in ((), ("--rerun",)):
                status, text = self.replay(receipt, *extra)
                self.assertEqual((status, problem_codes(text)), (0, []), text)
                self.assertIn("the receipt is what its files and its evidence give", text)
            status, text = self.replay(receipt, "--json")
            self.assertEqual(report_of(text)["mode"], "replay")
            status, text = self.replay(receipt, "--rerun", "--json")
            self.assertEqual(report_of(text)["mode"], "rerun")

    def tamper(self, change, expected, code):
        with scratch() as folder:
            fixture, receipt = self.made(folder)
            change(fixture, ROOT / receipt)
            status, text = self.replay(receipt)
            self.assertEqual(status, expected, text)
            self.assertIn(code, problem_codes(text), text)
            return text

    def test_files_changed_after_the_receipt(self):
        def append(path, text="\n"):
            with open(path, "a", encoding="utf-8") as file:
                file.write(text)
        cases = [
            ("the source", lambda f, r: append(f.source, "\\ a comment\n"),
             "$.program.source.sha256"),
            ("the contract", lambda f, r: f.contract.write_text(
                f.contract.read_text().replace("A test word.", "Another word."))),
            ("the IR file", lambda f, r: append(f.ir)),
            ("the generated Lean file", lambda f, r: append(f.out / "obligations.lean",
                                                             "-- changed\n"),
             "is not the file the generator writes"),
            ("the manifest", lambda f, r: (f.out / "w.ndjson.manifest.json").write_text(
                (f.out / "w.ndjson.manifest.json").read_text().replace('"bytes": ', '"bytes": 1')),
             "is not the manifest"),
            ("the manifest's bytes only", lambda f, r: append(f.out / "w.ndjson.manifest.json"),
             "$.check.evidence[3].sha256"),
            ("the evidence record", lambda f, r: append(f.out / "w.evidence.json"),
             "the evidence record"),
        ]
        for name, change, *said in cases:
            with self.subTest(name):
                text = self.tamper(change, 1, "replay")
                for words in said:
                    self.assertIn(words, text)

    def test_receipts_changed(self):
        def edited(edit):
            def change(fixture, receipt):
                data = json.loads(receipt.read_text())
                edit(data)
                receipt.write_text(program_receipt.dump(data))
            return change
        cases = [
            ("a theorem's axioms under-reported", edited(
                lambda r: r["check"]["theorems"][0].update(axioms=["propext"])), 1, "replay"),
            ("verify said open", edited(lambda r: r["verify"].update(status="open")), 4,
             "schema"),
            ("an added verified field", edited(lambda r: r.update(verified=True)), 4, "schema"),
            ("a duplicate assumption id", edited(
                lambda r: r["assumptions"][1].update(id="A1")), 4, "rule"),
            ("an unknown version", edited(lambda r: r.update(schemaVersion="9.9")), 4,
             "unknown-version"),
            ("a duplicate key", lambda f, r: r.write_text(r.read_text().replace(
                '"schemaVersion": "0.3",', '"schemaVersion": "0.3", "schemaVersion": "0.3",')),
             4, "not-strict-json"),
            ("the receipt removed", lambda f, r: r.unlink(), 4, "unreadable"),
        ]
        for name, change, expected, code in cases:
            with self.subTest(name):
                self.tamper(change, expected, code)

    def test_other_receipts(self):
        for path, expected, code in (
                ("tests/program/receipts/0.1/generated-lf-clamp.json", 4, "superseded-version"),
                ("tests/program/receipts/generated/lf-clamp.json", 1, "replay")):
            with self.subTest(path):
                status, text = self.replay(path)
                self.assertEqual((status, problem_codes(text)), (expected, [code]), text)

    def test_receipt_and_evidence_changed_together(self):
        """Changed consistently, they replay clean: only --rerun refuses them (review M3)."""
        with scratch() as folder:
            fixture, receipt = self.made(folder)
            evidence = fixture.out / "w.evidence.json"
            data = json.loads(evidence.read_text())
            data["lean"]["axioms"] = {k: ["propext"] for k in data["lean"]["axioms"]}
            evidence.write_text(program_receipt.dump(data))
            sha = program_verify.digest(evidence.read_bytes())
            text = (ROOT / receipt).read_text()
            old = re.search(r"evidence\.json, SHA-256 ([0-9a-f]{64})", text).group(1)
            (ROOT / receipt).write_text(text.replace(old, sha))
            status, text = self.replay(receipt)
            self.assertEqual((status, problem_codes(text)), (0, []), text)
            status, text = self.replay(receipt, "--rerun")
            self.assertEqual(status, 1, text)
            self.assertIn("running every step again records", text)


if __name__ == "__main__":
    os.chdir(ROOT)
    unittest.main(verbosity=1)
