"""The command line end to end (plan tasks 3.4.1-3.4.2): bin/leanforth.

1. Every exit code, with the exact text printed:
   0 every declaration accepted (composition; the constant fixture's three);
   1 rejected (composition with the wrong argument);
   2 unsupported (an axiom; a literal; an inductive type, refused while
     reading) and unknown (tests/cli/unfold.ndjson: a proof that needs a
     definition unfolded, which the first checker does not do yet);
   3 a resource limit (tests/cli/chain.ndjson, a correct theorem larger
     than today's stores, ends full while reading, and so does a name
     part of 2^64; fuel 0 and 30 end exhausted);
   4 malformed (a variable without its binder; a missing manifest; a file
     that is not an export; a file that does not open; every kind of
     mistake on the command line; a copy that would overwrite its export,
     also under another name);
   5 an internal fault (a Gforth that ends with a status of its own, and
     the real Gforth with an allocation made to throw, while staging and
     inside a check).
2. "accepted" is printed only on a declaration's line, each with the
   experimental label and its axioms, and only when the code is 0 or that
   line's declaration is accepted while another is not.
3. The tool works from any folder, with relative and absolute names, and
   prints the same bytes on every run.
4. count prints what src/import/ndjson-count.fs prints, and reexport writes
   a copy equal to the export, byte for byte, for every reference export.
5. version, capabilities and help exit 0; capabilities states the limits.

Run with GFORTH set to the Forth binary (the Makefile does this).
"""
import json
import os
from pathlib import Path
import re
import stat
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tests" / "support"))
from schema_subset import Validator  # noqa: E402
TOOL = ROOT / "bin" / "leanforth"
_gforth = os.environ.get("GFORTH", "gforth")
GFORTH = str(Path(_gforth).resolve()) if os.sep in _gforth else _gforth
CASES = "tests/core/check-declaration-cases"
COMPOSITION = "tests/reference/composition.ndjson"
FIXTURE = "tests/reference/constant-fixture.ndjson"
LABEL = "accepted (experimental, not independently audited); axioms: none"
NO_MANIFEST = "note: the export's manifest is not checked (--no-manifest)"
LIMITS = [
    "note: today's check holds at most 64 names, 64 levels, 64 term nodes and "
    "32 declarations per export,",
    "note: so only small exports, such as the test fixtures, fit; larger ones end full",
]
MANIFEST_HINT = [
    "note: the export is checked against EXPORT.manifest.json, which "
    "scripts/export.sh writes;",
    "note: --no-manifest skips that check",
]


def run(*args, cwd=ROOT, gforth=GFORTH, tool=TOOL):
    """The exit status and everything printed, standard output first."""
    result = subprocess.run([str(tool), *args], cwd=cwd, env=dict(os.environ, GFORTH=gforth),
                            stdin=subprocess.DEVNULL, capture_output=True, timeout=300)
    return result.returncode, result.stdout.decode(), result.stderr.decode()


class ExitCodes(unittest.TestCase):
    def expect(self, args, code, lines):
        status, out, err = run(*args)
        self.assertEqual((status, out.splitlines(), err), (code, lines, ""), args)

    def test_0_accepted(self):
        self.expect(["check", COMPOSITION], 0,
                    [f"composition: {LABEL}", "1 declaration: 1 accepted"])
        self.expect(["check", FIXTURE], 0,
                    [f"fixtureId: {LABEL}", f"fixturePoly: {LABEL}", f"fixtureUse: {LABEL}",
                     "3 declarations: 3 accepted"])

    def test_1_rejected(self):
        self.expect(["check", "--no-manifest", f"{CASES}/composition-wrong-argument.ndjson"], 1,
                    [NO_MANIFEST, "composition: rejected",
                     "  rejected: argument type mismatch (D1-D5); diagnostic 59 at mixed-infer "
                     "lf-mixed-infer: 4 0",
                     "1 declaration: 1 rejected"])

    def test_2_unsupported_and_unknown(self):
        self.expect(["check", "--no-manifest", f"{CASES}/composition-postulate.ndjson"], 2,
                    [NO_MANIFEST, "composition: unsupported",
                     "  unsupported: declaration kind (U1); diagnostic 42 at check-declaration "
                     "lf-check-declaration: 3 0",
                     "1 declaration: 1 unsupported"])
        status, out, _ = run("check", "--no-manifest", f"{CASES}/composition-literal.ndjson")
        self.assertEqual((status, out.splitlines()[1]), (2, "composition: unsupported"))
        self.expect(["check", "--no-manifest", "tests/core/reexport/kinds.ndjson"], 2,
                    [NO_MANIFEST,
                     "error: unsupported: an inductive type (not supported yet) (line 51)"])
        self.expect(["check", "tests/cli/unfold.ndjson"], 2,
                    [f"Implies: {LABEL}", "impliesSelf: unknown",
                     "  undecided: terms or levels differ; diagnostic 30 at mixed-convert "
                     "lf-mixed-convert: 16 10",
                     "2 declarations: 1 accepted, 1 unknown"])

    def test_3_limits(self):
        self.expect(["check", "tests/cli/chain.ndjson"], 3,
                    ["error: full: too many expression nodes or constant references for the "
                     "check's stores (line 97)", *LIMITS])
        self.expect(["check", "--no-manifest", "tests/cli/composition-huge-number.ndjson"], 3,
                    [NO_MANIFEST, "error: full: a numeric name part larger than the check "
                     "holds (line 12)", *LIMITS])
        exhausted = ["  fuel exhausted; diagnostic 1 at check-declaration "
                     "lf-check-declaration: 0 0"]
        self.expect(["check", "--fuel", "0", FIXTURE], 3,
                    ["fixtureId: exhausted", *exhausted, "fixturePoly: exhausted", *exhausted,
                     "fixtureUse: exhausted", *exhausted, "3 declarations: 3 exhausted",
                     "note: a check ran out of fuel (0 steps each); --fuel N gives each more"])
        status, out, _ = run("check", "--fuel", "30", COMPOSITION)
        self.assertEqual((status, out.splitlines()[0]), (3, "composition: exhausted"))

    def test_4_malformed(self):
        self.expect(["check", "--no-manifest", f"{CASES}/composition-loose.ndjson"], 4,
                    [NO_MANIFEST, "composition: invalid",
                     "  invalid input: out of scope; diagnostic 23 at constant-term-scope "
                     "lf-constant-term-scope: 7 6",
                     "1 declaration: 1 invalid"])
        self.expect(["check", f"{CASES}/composition-loose.ndjson"], 4,
                    ["error: invalid: manifest missing, unreadable or too large (line 0)",
                     *MANIFEST_HINT])
        self.expect(["check", "--no-manifest", "README.md"], 4,
                    [NO_MANIFEST, "error: invalid: unexpected character (line 1)"])
        self.expect(["check", "tests/cli/no-such.ndjson"], 4, ["error: cannot open the export"])
        self.expect(["count", "tests/cli/no-such.ndjson"], 4, ["error: cannot open the export"])

    def test_4_command_line(self):
        hint = "try: leanforth help"
        for args, error in [
            (["check"], "error: a wrong number of file names"),
            (["check", "a", "b"], "error: a wrong number of file names"),
            (["check", "a", "b", "c"], "error: one file name too many: c"),
            (["reexport", COMPOSITION], "error: a wrong number of file names"),
            (["version", "x"], "error: a wrong number of file names"),
            (["check", "--fuel", "x", COMPOSITION], "error: not a fuel amount: x"),
            (["check", "--fuel", "-1", COMPOSITION], "error: not a fuel amount: -1"),
            (["check", "--fuel", "99999999999999999999", COMPOSITION],
             "error: not a fuel amount: 99999999999999999999"),
            (["check", COMPOSITION, "--fuel"], "error: an option without its value: --fuel"),
            (["check", "--bogus", COMPOSITION], "error: an unknown option: --bogus"),
            (["count", "--fuel", "3", COMPOSITION],
             "error: an option this command does not take: --fuel"),
            (["frobnicate"], "error: an unknown command: frobnicate"),
            ([""], "error: an unknown command"),
        ]:
            self.expect(args, 4, [error, hint])
        status, out, _ = run()
        self.assertEqual((status, out.splitlines()[0]),
                         (4, "usage: leanforth COMMAND [OPTION]... [FILE]..."))

    def test_4_copy_over_export(self):
        self.expect(["reexport", COMPOSITION, COMPOSITION], 4, ["error: COPY must not be EXPORT"])
        self.expect(["reexport", COMPOSITION, "tests/../" + COMPOSITION], 4,
                    ["error: COPY must not be EXPORT"])
        with tempfile.TemporaryDirectory() as folder:
            self.expect(["reexport", COMPOSITION, f"{folder}/missing/copy.ndjson"], 4,
                        ["error: cannot create the copy"])

    def test_4_record_over_export(self):
        self.expect(["check", "--record", COMPOSITION, COMPOSITION], 4,
                    ["error: RECORD must not be EXPORT"])
        self.expect(["check", "--record", "tests/../" + COMPOSITION, COMPOSITION], 4,
                    ["error: RECORD must not be EXPORT"])
        with tempfile.TemporaryDirectory() as folder:
            self.expect(["check", "--record", f"{folder}/missing/run.json", COMPOSITION], 4,
                        [f"composition: {LABEL}", "1 declaration: 1 accepted",
                         "error: the run record was not written: invalid"])

    def test_5_broken_gforth(self):
        with tempfile.TemporaryDirectory() as folder:
            stub = Path(folder) / "gforth"
            stub.write_text("#!/bin/sh\necho 'composition: accepted'\nexit 0\n")
            stub.chmod(stub.stat().st_mode | stat.S_IXUSR)
            status, out, err = run("check", COMPOSITION, gforth=str(stub))
            self.assertEqual((status, err), (5, "leanforth: internal fault: Gforth ended with "
                                                "status 0\n"))
            stub.write_text("#!/bin/sh\nexit 1\n")
            self.assertEqual(run("check", COMPOSITION, gforth=str(stub))[0], 5)

    def test_5_thrown(self):
        """The real Gforth, an allocation made to throw (tests/support/
        alloc-fail.fs, loaded before src/main.fs): at the first, while
        staging; at the 63rd, the first in composition's check (staging it
        makes 62, which tests/cli/leanforth.fs counts afresh)."""
        with tempfile.TemporaryDirectory() as folder:
            stub = Path(folder) / "gforth"
            for k, lines in [
                (1, ["internal fault: a Forth exception (THROW -4150)"]),
                (63, ["composition: invalid",
                      "  invalid: internal fault; diagnostic 29 at env-publish lf-env-step: "
                      "0 -4150",
                      "internal fault: the run stopped: a check threw, or publishing failed",
                      "1 declaration: 1 invalid"]),
            ]:
                stub.write_text(f'#!/bin/sh\nmain=$1\nshift\nexec "{GFORTH}" '
                                f'"{ROOT}/tests/support/alloc-fail.fs" "$main" '
                                f'-e "{k} af-arm-throw" "$@"\n')
                stub.chmod(stub.stat().st_mode | stat.S_IXUSR)
                status, out, err = run("check", COMPOSITION, gforth=str(stub))
                self.assertEqual((status, out.splitlines(), err), (5, lines, ""), k)


def git_source():
    """The commit and modified flag bin/leanforth records, or (None, None)."""
    head = subprocess.run(["git", "-C", str(ROOT), "rev-parse", "HEAD"], capture_output=True,
                          text=True)
    if head.returncode != 0:
        return None, None
    same = subprocess.run(["git", "-C", str(ROOT), "diff", "--quiet", "HEAD"]).returncode == 0
    return head.stdout.strip(), not same


class RunRecords(unittest.TestCase):
    """check --record writes the run record of tests/support/run-records.fs's
    run (src/import/run-record.fs), with the manifest checked and the commit
    named; replay checks again and confirms it, or refuses a changed one."""

    def record(self, folder, export, *options):
        path = Path(folder) / "run.json"
        status, out, err = run("check", *options, "--record", str(path), export)
        return status, out, json.loads(path.read_text())

    def test_record_as_the_driver(self):
        schema = Validator(json.loads((ROOT / "schemas/run-record-0.1.schema.json").read_text()))
        commit, modified = git_source()
        for name in ["composition", "constant-fixture", "identity"]:
            with tempfile.TemporaryDirectory() as folder:
                status, out, got = self.record(folder, f"tests/reference/{name}.ndjson")
            self.assertEqual(status, 0, out)
            self.assertEqual(schema.errors(got), [], name)
            self.assertEqual(got["leanforth"], {"commit": commit, "modified": modified})
            golden = json.loads((ROOT / f"tests/core/run-records/{name}.json").read_text())
            for section in ["input", "export", "settings", "check", "declarations"]:
                self.assertEqual(got[section], golden[section], f"{name} {section}")

    def test_replay(self):
        with tempfile.TemporaryDirectory() as folder:
            wrong = f"{CASES}/composition-wrong-argument.ndjson"
            status, _, record = self.record(folder, wrong, "--no-manifest")
            self.assertEqual((status, record["declarations"][0]["verdict"]), (1, "rejected"))
            path = str(Path(folder) / "run.json")
            confirmed = '{"schema":"leanforth-replay-report","schemaVersion":"0.1",' \
                        '"result":"confirmed","findings":[],"findingsTotal":0}\n'
            self.assertEqual(run("replay", "--no-manifest", wrong, path), (0, confirmed, ""))
            record["declarations"][0]["verdict"] = "accepted"
            Path(path).write_text(json.dumps(record))
            status, out, _ = run("replay", "--no-manifest", wrong, path)
            report = json.loads(out)
            self.assertEqual((status, report["result"], report["findings"][0]["code"]),
                             (1, "refused", "accepted-not-established"))
            status, out, _ = run("replay", wrong, path)     # read without the manifest before
            self.assertEqual((status, json.loads(out)["result"]), (1, "refused"))
            status, out, _ = run("replay", COMPOSITION, str(Path(folder) / "missing.json"))
            self.assertEqual((status, json.loads(out)["findings"][0]["code"]), (4, "unreadable"))
            self.assertEqual(run("replay", COMPOSITION)[0], 4)


class Behaviour(unittest.TestCase):
    def test_accepted_only_from_slots(self):
        """Every "accepted" is a declaration's line with the label."""
        for args in [["check", COMPOSITION], ["check", "tests/cli/unfold.ndjson"],
                     ["check", "--no-manifest", f"{CASES}/composition-wrong-argument.ndjson"]]:
            _, out, _ = run(*args)
            for line in out.splitlines():
                if "accepted" in line and not re.match(r"^\d+ declarations?: ", line):
                    self.assertRegex(line, r"^\S+: " + re.escape(LABEL) + "$")

    def test_any_folder_and_deterministic(self):
        first = run("check", COMPOSITION)
        self.assertEqual(run("check", COMPOSITION), first)
        self.assertEqual(run("check", "reference/composition.ndjson", cwd=ROOT / "tests"), first)
        with tempfile.TemporaryDirectory() as folder:
            self.assertEqual(run("check", str(ROOT / COMPOSITION), cwd=folder), first)
            link = Path(folder) / "leanforth"
            link.symlink_to(TOOL)
            self.assertEqual(run("check", str(ROOT / COMPOSITION), cwd=folder, tool=link), first)

    def test_count_as_the_counter(self):
        for export in sorted((ROOT / "tests" / "reference").glob("*.ndjson")):
            name = str(export.relative_to(ROOT))
            counter = subprocess.run(
                [GFORTH, "src/import/ndjson-count.fs", "-e", f's" {name}" count-export bye'],
                cwd=ROOT, stdin=subprocess.DEVNULL, capture_output=True, timeout=300)
            self.assertEqual(run("count", name)[:2], (0, counter.stdout.decode()), name)

    def test_reexport_identical(self):
        with tempfile.TemporaryDirectory() as folder:
            for export in sorted((ROOT / "tests" / "reference").glob("*.ndjson")):
                copy = Path(folder) / export.name
                status, out, _ = run("reexport", str(export), str(copy))
                lines = len(export.read_bytes().splitlines())
                self.assertEqual((status, out), (0, f"reexported {lines} lines\n"))
                self.assertEqual(copy.read_bytes(), export.read_bytes())
            copy = Path(folder) / "kinds.ndjson"
            kinds = ROOT / "tests" / "core" / "reexport" / "kinds.ndjson"
            self.assertEqual(run("reexport", str(kinds), str(copy))[0], 4)   # no manifest
            status, _, _ = run("reexport", "--no-manifest", str(kinds), str(copy))
            self.assertEqual((status, copy.read_bytes()), (0, kinds.read_bytes()))

    def test_informational(self):
        status, out, _ = run("version")
        self.assertEqual(status, 0)
        self.assertRegex(out, r"^leanforth 0\.1\.0-dev \(development version; experimental, "
                              r"not independently audited\)\nforth: Gforth \S+\nreads: "
                              r"lean4export 3\.1\.0, format 3\.1\.0, Lean 4\.35\.0 "
                              r"\(eb6cafb7290e8bd5f2937522d8d804f58f02bafc\)\ncommit: ")
        self.assertEqual(run("--version")[:2], (0, out))
        status, out, _ = run("capabilities")
        self.assertEqual(status, 0)
        self.assertIn("  64 names (2048 bytes), 64 levels, 64 term nodes, 32 declarations per "
                      "export\n", out)
        status, out, _ = run("help")
        self.assertEqual((status, run("--help")[1], run("-h")[1]), (0, out, out))


if __name__ == "__main__":
    unittest.main()
