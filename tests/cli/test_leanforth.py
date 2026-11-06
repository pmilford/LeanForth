"""The command line end to end (plan tasks 3.4.1-3.4.3, 6.5.2 in part): bin/leanforth.

1. Every exit code, with the exact text printed:
   0 every declaration accepted (composition; the constant fixture's three;
     tests/cli/chain.ndjson, larger than --record holds; tests/cli/
     inductive.ndjson, an inductive type and a theorem by its recursor);
   1 rejected (composition with the wrong argument);
   2 unsupported (an axiom; a literal; with --record an inductive type,
     refused while reading) and unknown (UNKNOWN, a block whose check needs
     a recursor reduction the checker does not port yet; tests/cli/
     unfold.ndjson, which needs a definition unfolded, is accepted since
     plan task 4.2.2d, and tests/cli/irrelevance.ndjson, a proof that needs
     proof irrelevance, since plan task 4.2.5); every record kind
     (tests/core/reexport/kinds.ndjson) counted;
   3 a resource limit (chain with --record ends full while reading; a
     name part of 2^64 is beyond the stage's 32 bits; fuel 0 and 30 end
     exhausted);
   4 malformed (a variable without its binder; a missing manifest; a file
     that is not an export; a file that does not open; a tampered or cut
     export, with and without its manifest; a constant no declaration has;
     every kind of mistake on the command line, --json with --record
     too, and a fuel amount above 2^53 - 1; a copy that would overwrite
     its export, also under another name);
   5 an internal fault (a Gforth that ends with a status of its own, and
     the real Gforth with an allocation made to throw, while feeding and
     inside a check, or with the publisher made to throw mid-run);
   6 all accepted but some NOT PROVED, only with --strict-axioms (by
     default NOT PROVED keeps Lean's 0): no check can make one yet, so
     tests/cli/leanforth.fs plants an axiom in a slot, and the schema is
     tested here with planted reports.
2. "accepted" is printed only on a declaration's line, each with the
   experimental label and its axioms, and only when the code is 0 or that
   line's declaration is accepted while another is not.
3. The tool works from any folder, with relative and absolute names, and
   prints the same bytes on every run.
4. count prints what src/import/ndjson-count.fs prints, and reexport writes
   a copy equal to the export, byte for byte, for every reference export.
5. version, capabilities and help exit 0; capabilities states the limits.
6. print prints each declaration's proof outline exactly as the outline's
   golden file has it (all five reference exports, one declaration by
   name, every step with --detail); a declaration not accepted is refused,
   with its outcome's code, and no outline appears except below the
   experimental label; a name no declaration has, and print's command-line
   mistakes, are 4.
7. --json prints one report that the schema (schemas/check-report-0.1)
   accepts, for every case of 1, with the exit status, every verdict and
   the counts the text gives; it is the same on every run but for
   "measured", and its counts and fuel add up as the schema's $comment
   says. --resources adds the resource report, the same on every run but
   for its time and memory lines. The fuel each check used is exact: a
   budget of that much gives the same verdict, one less runs out.
8. Names are shown as Lean's Name.toString shows them, with escapes for
   control, format and separator characters, so that no name can forge a
   line; of any depth; the export's file name with the same escapes.
9. The engine: Gforth's checking engine by default; --fast runs the
   gforth-fast beside it, with the same text and the same JSON report but
   for "measured", which names the engine; with no gforth-fast the run
   says so on standard error and uses the default.

Run with GFORTH set to the Forth binary (the Makefile does this).
"""
import json
import os
from pathlib import Path
import re
import shutil
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
INDUCTIVE = "tests/cli/inductive.ndjson"
CHAIN = "tests/cli/chain.ndjson"
EMPTY_BLOCK = "tests/core/check-block-cases/names.empty-block.ndjson"
# Unknown: a block whose positivity check needs iota on Lean's generated
# recursor, which LeanForth does not port yet (diagnostic 81; closed by a
# follow-up of plan task 5.2.1b, tests/core/inductive-table.py).
UNKNOWN = "tests/core/check-block-cases/after.list-left-out-then-lookup-during-param-block.ndjson"


def accepted(n):
    """The summary line of n accepted declarations, none NOT PROVED."""
    return f"accepted: {n} (experimental, not independently audited); axioms: none"



NO_MANIFEST = "note: the export's manifest is not checked (--no-manifest)"
LIMITS = [
    "note: check --record and replay hold at most 64 names, 64 levels,",
    "note: 64 term nodes and 32 declarations per export; check without --record holds "
    "any size",
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
                    [f"composition: {LABEL}", "1 declaration: 1 accepted", accepted(1)])
        self.expect(["check", FIXTURE], 0,
                    [f"fixtureId: {LABEL}", f"fixturePoly: {LABEL}", f"fixtureUse: {LABEL}",
                     "3 declarations: 3 accepted", accepted(3)])
        self.expect(["check", CHAIN], 0,
                    [f"chain: {LABEL}", "1 declaration: 1 accepted", accepted(1)])
        # An inductive type, a theorem and a definition by its recursor:
        # Lean's verdicts, accepted, not unsupported (as --record answers).
        self.expect(["check", INDUCTIVE], 0,
                    [f"Two: {LABEL}", f"Two.first: {LABEL}", f"Two.second: {LABEL}",
                     f"Two.rec: {LABEL}", f"Two.cases: {LABEL}", f"Two.swap: {LABEL}",
                     "6 declarations: 6 accepted", accepted(6)])

    def test_1_forged_quotient(self):
        """Lean's export of propext, Classical.choice and Quot.sound
        (tests/reference/inductive/axioms.ndjson) is accepted, the three
        counted as proved; with Quot.mk's record given Quot's type, that
        record is rejected (Q1, diagnostic 96: not Lean's own constant)
        and so is Quot.sound, which names it. Lean's replay ignores a
        quotient record's type (a gap of plan task 5.2.4; no export Lean
        writes has another)."""
        source = ROOT / "tests" / "reference" / "inductive" / "axioms.ndjson"
        status, out, _ = run("check", "--no-manifest", str(source))
        self.assertEqual((status, out.splitlines()[-2]), (0, "16 declarations: 16 accepted"))
        self.assertIn("Quot.sound: accepted (experimental, not independently audited); "
                      "axioms: Quot.sound", out.splitlines())
        text = source.read_text(encoding="utf-8")
        forged = text.replace('"name":31,"type":121}', '"name":31,"type":115}')
        self.assertNotEqual(forged, text)
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder) / "forged.ndjson"
            path.write_text(forged, encoding="utf-8")
            status, out, _ = run("check", "--no-manifest", str(path))
        lines = out.splitlines()
        self.assertEqual((status, lines[-2]), (1, "16 declarations: 14 accepted, 2 rejected"))
        at = lines.index("Quot.mk: rejected")
        self.assertTrue(lines[at + 1].startswith(
            "  rejected: not one of Lean's four quotient constants (Q1); diagnostic 96 at quot "
            "lf-quot-check: "), lines[at + 1])
        self.assertIn("Quot.sound: rejected", lines)

    def test_1_rejected(self):
        self.expect(["check", "--no-manifest", f"{CASES}/composition-wrong-argument.ndjson"], 1,
                    [NO_MANIFEST, "composition: rejected",
                     "  rejected: argument type mismatch (D1-D5); diagnostic 59 at mixed-infer "
                     "lf-mixed-infer: 0 0",
                     "1 declaration: 1 rejected"])
        # An empty inductive block, which Lean's kernel rejects (emptyBlock):
        # it has no name, Lean's anonymous one.
        self.expect(["check", "--no-manifest", EMPTY_BLOCK], 1,
                    [NO_MANIFEST, "[anonymous]: rejected",
                     "  rejected: an inductive block without types; diagnostic 78 at check-block "
                     "lf-block-check: 0 0",
                     "1 declaration: 1 rejected"])

    def test_0_not_proved(self):
        """An axiom (plan task 5.3.1): Lean's verdict, accepted, marked NOT
        PROVED with the axiom named; status 0 as Lean, 6 under
        --strict-axioms."""
        postulate = f"{CASES}/composition-postulate.ndjson"
        line = (f"composition: accepted (experimental, not independently audited); axioms: unlisted; NOT PROVED: depends on composition")
        lines = [NO_MANIFEST, line, "1 declaration: 1 accepted",
                 "accepted: 1 (experimental, not independently audited); axioms: 1 NOT PROVED (they depend on an axiom)"]
        note = ["note: NOT PROVED declarations keep Lean's exit status; --strict-axioms",
                "note: makes it 6"]
        self.expect(["check", "--no-manifest", postulate], 0, lines + note)
        self.expect(["check", "--no-manifest", "--strict-axioms", postulate], 6, lines)
        # Every axiom a declaration rests on, through its type and value, as
        # Lean's #print axioms lists them; propext with another statement
        # than Lean's is no allowlisted axiom (inductive-table rows).
        blocks = "tests/core/check-block-cases"
        for case, line in [
                ("postulate.declared-and-used", "IE.usesSecret: accepted (experimental, not "
                 "independently audited); axioms: unlisted; NOT PROVED: depends on IE.Secret, "
                 "IE.secret"),
                ("postulate.propext-altered", "IE.anything: accepted (experimental, not "
                 "independently audited); axioms: unlisted; NOT PROVED: depends on propext")]:
            status, out, _ = run("check", "--no-manifest", f"{blocks}/{case}.ndjson")
            self.assertEqual(status, 0, case)
            self.assertIn(line, out.splitlines(), case)

    def test_2_unsupported_and_unknown(self):
        status, out, _ = run("check", "--no-manifest", f"{CASES}/composition-literal.ndjson")
        self.assertEqual((status, out.splitlines()[1]), (2, "composition: unsupported"))
        status, out, _ = run("check", "--no-manifest", "tests/core/reexport/kinds.ndjson")
        self.assertEqual((status, out.splitlines()[-2:]),
                         (2, ["106 declarations: 89 accepted, 17 unsupported",
                              accepted(89)]))
        self.expect(["check", "--no-manifest", "--record", "/dev/null",
                     "tests/core/reexport/kinds.ndjson"], 2,
                    [NO_MANIFEST,
                     "error: unsupported: an inductive type (not supported yet) (line 51)"])
        self.expect(["check", "tests/cli/unfold.ndjson"], 0,
                    [f"Implies: {LABEL}", f"impliesSelf: {LABEL}",
                     "2 declarations: 2 accepted", accepted(2)])
        self.expect(["check", "tests/cli/irrelevance.ndjson"], 0,
                    [f"irrelevant: {LABEL}", "1 declaration: 1 accepted", accepted(1)])
        recursor = ("  undecided: a recursor reduction LeanForth does not port yet; "
                    "diagnostic 81 at whnf lf-whnf: 17 0")
        self.expect(["check", "--no-manifest", UNKNOWN], 2,
                    [NO_MANIFEST, f"IE.L: {LABEL}", f"IE.L.nil: {LABEL}", f"IE.L.cons: {LABEL}",
                     "IE.W: unknown", recursor, "IE.W.mk: unknown", recursor,
                     "5 declarations: 3 accepted, 2 unknown", accepted(3)])

    def test_3_limits(self):
        self.expect(["check", "--record", "/dev/null", CHAIN], 3,
                    ["error: full: too many expression nodes or constant references for the "
                     "check's stores (line 97)", *LIMITS])
        self.expect(["check", "--no-manifest", "tests/cli/composition-huge-number.ndjson"], 3,
                    [NO_MANIFEST, "error: full: number beyond 32 bits (line 12)"])
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
                    [NO_MANIFEST, "error: invalid: unexpected character (line 1, byte 0)"])
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
            (["check", "--fuel", str(2**53), COMPOSITION],
             f"error: a fuel amount above {2**53 - 1}: {2**53}"),
            (["replay", "--fuel", str(2**63 - 1), COMPOSITION, "r.json"],
             f"error: a fuel amount above {2**53 - 1}: {2**63 - 1}"),
            (["check", COMPOSITION, "--fuel"], "error: an option without its value: --fuel"),
            (["check", "--bogus", COMPOSITION], "error: an unknown option: --bogus"),
            (["check", "--json", "--record", "r.json", COMPOSITION],
             "error: --json and --resources do not go with --record"),
            (["check", "--record", "r.json", "--resources", COMPOSITION],
             "error: --json and --resources do not go with --record"),
            (["print", "--json", COMPOSITION],
             "error: an option this command does not take: --json"),
            (["print", "--strict-axioms", COMPOSITION],
             "error: an option this command does not take: --strict-axioms"),
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
                        [f"composition: {LABEL}", "1 declaration: 1 accepted", accepted(1),
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
        """The real Gforth, an allocation of the stores made to throw
        (tests/support/alloc-fail.fs, loaded before src/main.fs): at the
        first, while feeding; at the 24th, the first in composition's check
        (feeding it and making the environment make 23, which
        tests/cli/leanforth.fs counts afresh)."""
        with tempfile.TemporaryDirectory() as folder:
            stub = Path(folder) / "gforth"
            for k, lines in [
                (1, ["internal fault: a Forth exception (THROW -4150)"]),
                (24, ["composition: invalid",
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
                # With --json: a THROW outside a check leaves no report; one
                # inside a check, a whole report of a run that stopped.
                status, out, err = run("check", "--json", COMPOSITION, gforth=str(stub))
                if k == 1:
                    self.assertEqual((status, out.splitlines(), err), (5, lines, ""))
                    continue
                got = json.loads(out)
                schema = Validator(json.loads(
                    (ROOT / "schemas/check-report-0.1.schema.json").read_text()))
                self.assertEqual((status, schema.errors(got), got["stopped"], got["exitStatus"],
                                  got["declarations"][0]["diagnostic"]["code"]),
                                 (5, [], True, 5, 29))

    def test_5_stopped_mid_run(self):
        """The real Gforth with the publisher's test hook
        (lf-env-before-final, a DEFER when lf-env-fault-hooks is defined
        before src/main.fs) made to throw before the fixture's second
        declaration's slot is final: the first stays accepted, the second
        is invalid, the third not checked; the JSON report is whole."""
        with tempfile.TemporaryDirectory() as folder:
            stub = Path(folder) / "gforth"
            stub.write_text(f'#!/bin/sh\nmain=$1\nshift\nexec "{GFORTH}" '
                            f'-e ": lf-env-fault-hooks ;" "$main" '
                            f'-e ": throw-at-1 lf-env-limit 1 = if 4242 throw then ;" '
                            f'''-e "' throw-at-1 is lf-env-before-final" "$@"\n''')
            stub.chmod(stub.stat().st_mode | stat.S_IXUSR)
            status, out, err = run("check", FIXTURE, gforth=str(stub))
            lines = out.splitlines()
            self.assertEqual((status, lines[0], lines[1], lines[-4:], err),
                             (5, f"fixtureId: {LABEL}", "fixturePoly: invalid",
                              ["internal fault: the run stopped: a check threw, or publishing "
                               "failed", "fixtureUse: not checked",
                               "3 declarations: 1 accepted, 1 invalid, 1 not checked",
                               accepted(1)], ""))
            status, out, err = run("check", "--json", FIXTURE, gforth=str(stub))
            got = json.loads(out)
            self.assertEqual((status, err, JsonReport.schema.errors(got), got["run"],
                              got["stopped"], got["exitStatus"],
                              [d["verdict"] for d in got["declarations"]]),
                             (5, "", [], "invalid", True, 5,
                              ["accepted", "invalid", "not-checked"]))
            JsonReport().sums(got, "stopped")


OUTLINES = ROOT / "tests" / "present" / "outlines.golden"
LATEX_OUTLINES = ROOT / "tests" / "present" / "outlines-latex.golden"
REFUSED = "No proof outline: the declaration was not accepted."


def golden(section):
    """A section of the outlines' golden file (tests/present/outlines.golden,
    printed by tests/present/outline-cases.fs), as lines."""
    parts = re.split(r"^== (.*)$", OUTLINES.read_text(encoding="utf-8"), flags=re.M)
    return dict(zip(parts[1::2], parts[2::2]))[section].strip("\n").splitlines()


class Print(unittest.TestCase):
    """print (plan task 2.4.4): each declaration's proof outline, printed
    from the checker's derivation log right after its check; never one for
    a declaration that is not accepted. The text equals the outline's
    golden file, which the outline printer's own test pins."""

    def lines(self, *args):
        status, out, err = run("print", *args)
        self.assertEqual(err, "", args)
        return status, out.strip("\n").splitlines()

    def test_0_outlines(self):
        for name in ("identity", "composition", "type-identity", "poly-identity",
                     "constant-fixture"):
            self.assertEqual(self.lines(f"tests/reference/{name}.ndjson"), (0, golden(name)))
        self.assertEqual(self.lines("--detail", COMPOSITION), (0, golden("composition --detail")))

    def test_0_statement_forms(self):
        """--statement picks the forms of the statement the header shows (plan task
        8.6.2): each alone, in any order and all (the default); a form that is no
        form, or an empty list, is a command-line mistake (status 4)."""
        full = golden("composition")
        math = next(i for i, l in enumerate(full) if l.startswith("  Statement in mathematics:"))
        forth = next(i for i, l in enumerate(full) if l.startswith("  Statement in LeanForth"))
        end = full.index("    end composition")
        parts = {"lean": full[math - 1:math], "mathematics": full[math:math + 1],
                 "leanforth": full[forth:end + 1]}
        before, after = full[:math - 1], full[end + 1:]
        for forms in ("lean", "mathematics", "leanforth", "lean,leanforth", "leanforth,lean",
                      "mathematics,lean", "all"):
            wanted = [name for name in parts if name in forms.split(",") or forms == "all"]
            expected = before + [l for name in wanted for l in parts[name]] + after
            self.assertEqual(self.lines("--statement", forms, COMPOSITION), (0, expected), forms)
        for bad in ("", "lean,", "latin", "lean,,mathematics", "Lean"):
            status, out, err = run("print", "--statement", bad, COMPOSITION)
            self.assertEqual((status, out.startswith("error:")), (4, True), bad)
        status, out, err = run("check", "--statement", "lean", COMPOSITION)
        self.assertEqual((status, out.startswith("error: an option this command does not take")),
                         (4, True))

    def test_0_beyond_the_small_reader(self):
        """print holds what check holds (the stage and the feed, plan task 3.4.1), not the
        64 names and 32 declarations of the first reader: chain.ndjson has 81 expressions,
        inductive.ndjson has inductive types. Each declaration check reports has its
        header, and the status is check's; chain's line is read from the stage."""
        for path in ("tests/cli/chain.ndjson", "tests/cli/inductive.ndjson",
                     "tests/cli/unfold.ndjson"):
            check_status, check_out, _ = run("check", path)
            status, out = self.lines(path)
            self.assertEqual(status, check_status, path)
            names = [l.split(": ")[0] for l in check_out.splitlines()
                     if re.match(r"^\S+: (accepted|rejected|unknown|unsupported)", l)]
            self.assertTrue(names, path)
            heads = {l.split(" ", 1)[1] for l in out if re.match(
                r"^(Theorem|Definition|Axiom|Opaque|Declaration) ", l)}
            # An inductive block's later members are published with its first and
            # printed once, under it.
            members = {"Two.first", "Two.second", "Two.rec"} if "inductive" in path else set()
            self.assertEqual(sorted(set(names) - members), sorted(heads), path)
        status, out = self.lines("tests/cli/chain.ndjson")
        self.assertIn("  Input:     tests/cli/chain.ndjson line 114", out)
        self.assertIn("      L M -> explicit: f12", out)
        self.assertEqual(out[-1], "Templates: let-props/v0, assume/v0, implies-elim/v0, "
                                  "discharge/v0, statement/v0.")

    def test_0_binder_kinds(self):
        """The binder kinds the feed's hook keeps reach the printer: implicit and instance
        binders print in their brackets (declarations that print as types, from an export
        of kinds of declarations; its manifest is not checked)."""
        status, out = self.lines("--no-manifest", "--statement", "lean",
                                 "tests/core/reexport/kinds.ndjson")
        self.assertIn("  Type in Lean:             {α : Type u} → (x : Nat) → [self : OfNat α x] → α",
                      out)
        self.assertIn("  Type in Lean:             {α : Type u_1} → [Add α] → HAdd α α α", out)

    def test_0_latex(self):
        """--latex prints the outlines as the LaTeX fragments of tests/present/
        outlines-latex.golden (plan task 8.6.1); with --detail the steps stay plain."""
        parts = re.split(r"^== (.*)$", LATEX_OUTLINES.read_text(encoding="utf-8"), flags=re.M)
        fragments = dict(zip(parts[1::2], parts[2::2]))
        for name in ("identity", "composition", "constant-fixture"):
            self.assertEqual(self.lines("--latex", f"tests/reference/{name}.ndjson"),
                             (0, fragments[name].strip("\n").splitlines()), name)
        self.assertEqual(self.lines("--latex", "--detail", COMPOSITION),
                         (0, golden("composition --detail")))

    def test_0_named(self):
        fixture = golden("constant-fixture")
        use = fixture[fixture.index("Theorem fixtureUse"):]
        self.assertEqual(self.lines("--name", "fixtureUse", FIXTURE), (0, use))
        poly = fixture[fixture.index("Definition fixturePoly"):fixture.index("Theorem fixtureUse")]
        self.assertEqual(self.lines("--name", "fixturePoly", FIXTURE), (0, poly[:-1]))

    def test_refused(self):
        status, out = self.lines("--no-manifest", f"{CASES}/composition-wrong-argument.ndjson")
        self.assertEqual((status, out), (1, [NO_MANIFEST, *golden("composition-wrong-argument")]))
        status, out = self.lines("--no-manifest", UNKNOWN)
        self.assertEqual(status, 2)
        self.assertEqual(out[out.index("Declaration IE.W"):][1], "  unknown")
        self.assertEqual(out[-1], REFUSED)
        status, out = self.lines("--fuel", "0", FIXTURE)
        self.assertEqual((status, out.count(REFUSED), out.count("  exhausted")), (3, 3, 3))
        status, out = self.lines("--no-manifest", f"{CASES}/composition-postulate.ndjson")
        self.assertEqual((status, out[1:3], out[-1]),
                         (0, ["Axiom composition", f"  accepted (experimental, not independently audited); axioms: unlisted"],
                          "No proof outline: an axiom or a quotient constant has no proof;"
                          " Lean's kernel takes it as given."))
        for args, code in [((FIXTURE,), 0), (("--no-manifest", UNKNOWN), 2),
                           (("--fuel", "0", FIXTURE), 3),
                           (("--no-manifest", f"{CASES}/composition-wrong-argument.ndjson"), 1)]:
            status, out = self.lines(*args)
            self.assertEqual(status, code, args)
            # Each verdict, the line after a declaration's title, is the label
            # or a failure; an outline appears only below the label.
            titles = [i for i, line in enumerate(out)
                      if re.match(r"(Theorem|Definition|Axiom|Opaque|Declaration) ", line)]
            verdicts = [out[i + 1] for i in titles]
            self.assertTrue(all(v == f"  {LABEL}" or "accepted" not in v for v in verdicts),
                            verdicts)
            shown = sum(line.startswith(("Proof (", "Construction (", "No outline template"))
                        for line in out)
            self.assertEqual(shown, out.count(f"  {LABEL}"), args)

    def test_4_mistakes(self):
        self.assertEqual(self.lines("--name", "noSuch", FIXTURE),
                         (4, ["error: no declaration named noSuch"]))
        self.assertEqual(self.lines("tests/cli/no-such.ndjson"),
                         (4, ["error: cannot open the export"]))
        hint = "try: leanforth help"
        for args, error in [
            ([], "error: a wrong number of file names"),
            ([FIXTURE, "--name"], "error: an option without its value: --name"),
            (["--record", "r.json", FIXTURE], "error: an option this command does not take: "
                                              "--record"),
        ]:
            self.assertEqual(self.lines(*args), (4, [error, hint]), args)
        status, out, _ = run("check", "--detail", COMPOSITION)
        self.assertEqual((status, out.splitlines()),
                         (4, ["error: an option this command does not take: --detail", hint]))


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
            # The command line enforces the manifest; the driver that wrote
            # the golden records does not, and each record says so.
            self.assertEqual((got["input"]["manifest"]["enforced"],
                              golden["input"]["manifest"]["enforced"]), (True, False))
            golden["input"]["manifest"]["enforced"] = True
            for section in ["input", "export", "settings", "check", "declarations"]:
                self.assertEqual(got[section], golden[section], f"{name} {section}")

    def test_replay(self):
        with tempfile.TemporaryDirectory() as folder:
            wrong = f"{CASES}/composition-wrong-argument.ndjson"
            status, _, record = self.record(folder, wrong, "--no-manifest")
            self.assertEqual((status, record["declarations"][0]["verdict"]), (1, "rejected"))
            self.assertIs(record["input"]["manifest"]["enforced"], False)   # --no-manifest
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
        """Every "accepted" is a declaration's line with the label, or a
        summary line that counts them with the label."""
        for args in [["check", COMPOSITION], ["check", "tests/cli/unfold.ndjson"],
                     ["check", "--no-manifest", f"{CASES}/composition-wrong-argument.ndjson"],
                     ["check", INDUCTIVE]]:
            _, out, _ = run(*args)
            for line in out.splitlines():
                if "accepted" in line and not re.match(r"^\d+ declarations?: ", line):
                    self.assertRegex(line, r"^(\S+: " + re.escape(LABEL) + r"|accepted: \d+ "
                                     r"\(experimental, not independently audited\); "
                                     r"axioms: none)$")

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
        self.assertIn("  check --record, replay: 64 names, 64 levels, 64 term nodes,\n"
                      "    32 declarations per export\n", out)
        status, out, _ = run("help")
        self.assertEqual((status, run("--help")[1], run("-h")[1]), (0, out, out))


class Tampered(unittest.TestCase):
    """An export changed after it was made is never accepted: with its
    manifest it is refused before anything is checked (invalid, 4); without
    it, a change that breaks the file is invalid too, and one that keeps it
    well formed gets the verdict of what it now says."""

    def copies(self, folder, source, change):
        """source and its manifest copied into folder, the copy changed."""
        text = (ROOT / source).read_text()
        export = Path(folder) / Path(source).name
        export.write_text(change(text))
        manifest = ROOT / f"{source}.manifest.json"
        Path(f"{export}.manifest.json").write_text(manifest.read_text())
        return str(export)

    def refused(self, export, code, error):
        """With the manifest: invalid (the reader's own refusal, or the
        manifest's SHA-256 at the end of the read). Without it: code, and
        error as the line after the note."""
        for options in [[], ["--no-manifest"]]:
            status, out, err = run("check", *options, export)
            self.assertNotIn(LABEL, out, (options, export))
            if not options:
                self.assertEqual((status, out.splitlines()[0][:16]), (4, "error: invalid: "),
                                 export)
            else:
                self.assertEqual((status, out.splitlines()[1:2]), (code, error), export)

    def test_tampered(self):
        with tempfile.TemporaryDirectory() as folder:
            # The proof replaced by the statement: rejected without the manifest.
            proof = self.copies(folder, COMPOSITION,
                                lambda t: t.replace('"value":20', '"value":10'))
            self.refused(proof, 1, ["composition: rejected"])
            self.assertEqual(run("check", proof)[1].splitlines()[0],
                             "error: invalid: export differs from its manifest "
                             "(field sha256, line 0)")
            # A reference to an expression that does not exist.
            dangling = self.copies(folder, COMPOSITION,
                                   lambda t: t.replace('"arg":12,"fn":1}', '"arg":12,"fn":99}'))
            self.refused(dangling, 4, ["error: invalid: bad reference (field fn, line 27)"])
            # Cut inside its last line; and the fixture cut after its
            # second-last line, a shorter library that reads well: only its
            # manifest tells (without it, its two declarations are accepted).
            cut = self.copies(folder, COMPOSITION, lambda t: t[:-5])
            self.refused(cut, 4,
                         ["error: invalid: missing final line feed, or a read error (line 35)"])
            shorter = self.copies(folder, FIXTURE,
                                  lambda t: t[:t.rstrip("\n").rindex("\n") + 1])
            status, out, _ = run("check", shorter)
            self.assertEqual((status, out.split(" (")[0]),
                             (4, "error: invalid: export differs from its manifest"))
            self.assertEqual(run("check", "--no-manifest", shorter)[0], 0)
            # Another Lean version than the pinned one: unsupported, 2.
            other = self.copies(folder, COMPOSITION,
                                lambda t: t.replace('"version":"4.35.0"', '"version":"4.36.0"'))
            status, out, _ = run("check", "--no-manifest", other)
            self.assertEqual((status, out.splitlines()[1][:20]), (2, "error: unsupported: "))
            # A constant no declaration has: the stage refuses it at sealing.
            lines = (ROOT / FIXTURE).read_text().splitlines(keepends=True)
            unknown = Path(folder) / "unknown.ndjson"
            unknown.write_text("".join(line for line in lines if '"def":{"all":[1]' not in line))
            self.assertEqual(run("check", "--no-manifest", str(unknown)),
                             (4, f"{NO_MANIFEST}\nerror: invalid: unknown constant (line 0)\n",
                                 ""))


def report(*args):
    """The exit status and the JSON report of check --json."""
    status, out, err = run("check", "--json", *args)
    return status, json.loads(out), err


CASES_ALL = [
    [COMPOSITION], [FIXTURE], [CHAIN], [INDUCTIVE], ["tests/cli/unfold.ndjson"],
    [f"{CASES}/composition-wrong-argument.ndjson"],
    ["--no-manifest", f"{CASES}/composition-wrong-argument.ndjson"],
    ["--no-manifest", f"{CASES}/composition-postulate.ndjson"],
    ["--no-manifest", f"{CASES}/composition-loose.ndjson"],
    ["--no-manifest", "README.md"], ["tests/cli/no-such.ndjson"],
    ["--no-manifest", "tests/cli/composition-huge-number.ndjson"],
    ["--no-manifest", "tests/core/reexport/kinds.ndjson"], ["--fuel", "0", FIXTURE],
    ["--no-manifest", EMPTY_BLOCK],
]


class JsonReport(unittest.TestCase):
    """check --json (plan task 3.4.3): one report the schema accepts, which
    says what the text says, the same on every run but for "measured"."""

    schema = Validator(json.loads((ROOT / "schemas/check-report-0.1.schema.json").read_text()))
    VERDICTS = {"accepted": "accepted", "rejected": "rejected", "unknown": "unknown",
                "unsupported": "unsupported", "invalid": "invalid", "exhausted": "exhausted",
                "full": "full", "notChecked": "not-checked"}

    def sums(self, got, args):
        """The rules the schema cannot state (its $comment): the counts, the
        fuel and the most fuel used agree with the declarations."""
        decls, counts, fuel = got["declarations"], got["counts"], got["fuel"]
        if counts is not None:
            self.assertEqual(counts["declarations"], len(decls), args)
            self.assertEqual(counts["declarations"],
                             sum(counts[key] for key in self.VERDICTS), args)
            for key, verdict in self.VERDICTS.items():
                self.assertEqual(counts[key], sum(d["verdict"] == verdict for d in decls),
                                 (args, key))
            self.assertEqual(counts["notProved"], sum(d.get("notProved", False) for d in decls),
                             args)
            if got["input"] is not None:
                self.assertEqual(got["input"]["declarations"], counts["declarations"], args)
        self.assertEqual([d["index"] for d in decls], list(range(len(decls))), args)
        known = [d["fuel"] for d in decls if d["fuel"] is not None]
        self.assertEqual((fuel["unknown"], fuel["total"]),
                         (len(decls) - len(known), sum(known)), args)
        tops = [t["fuel"] for t in fuel["top"]]
        self.assertEqual(tops, sorted(tops, reverse=True), args)
        for top in fuel["top"]:
            d = decls[top["index"]]
            self.assertEqual((top["name"], top["fuel"], top["verdict"]),
                             (d["name"], d["fuel"], d["verdict"]), args)

    def test_valid_and_as_the_text(self):
        for args in CASES_ALL:
            status, got, err = report(*args)
            self.assertEqual((self.schema.errors(got), err), ([], ""), args)
            self.sums(got, args)
            text_status, text, _ = run("check", *args)
            self.assertEqual((status, got["exitStatus"]), (text_status, text_status), args)
            self.assertEqual(got["stopped"], "internal fault: the run stopped" in text, args)
            # Each declaration's line, in order, says the report's verdict.
            # An accepted one's line names its axioms and, when NOT PROVED,
            # says so (plan task 5.3.1).
            words = {"accepted": "accepted (experimental, not independently audited); axioms: ",
                     "not-checked": "not checked"}
            lines = text.splitlines()
            at = 0
            for d in got["declarations"]:
                line = f"{d['name']}: {words.get(d['verdict'], d['verdict'])}"
                accepted_one = d["verdict"] == "accepted"
                found = [k for k in range(at, len(lines))
                         if lines[k] == line or (accepted_one and lines[k].startswith(line))]
                self.assertTrue(found, (line, args))
                at = found[0] + 1
                self.assertEqual("; NOT PROVED: depends on " in lines[at - 1],
                                 bool(d.get("notProved")), args)
            shown = [line for line in lines if re.match(r"^\d+ declarations?: ", line)]
            counts = got["counts"]
            self.assertEqual(len(shown), int(counts is not None), args)
            if counts is not None:
                words = {"accepted": "accepted", "rejected": "rejected", "unknown": "unknown",
                         "unsupported": "unsupported", "invalid": "invalid",
                         "exhausted": "exhausted", "full": "full", "notChecked": "not checked"}
                summary = ", ".join(f"{counts[k]} {w}" for k, w in words.items() if counts[k])
                plural = "" if counts["declarations"] == 1 else "s"
                self.assertEqual(shown[0], f"{counts['declarations']} declaration{plural}: "
                                           f"{summary}", args)

    def test_schema_refuses(self):
        """The schema refuses a report whose parts disagree."""
        _, good, _ = report(INDUCTIVE)
        _, unread, _ = report("--no-manifest", "README.md")

        def changed(base, edit):
            copy = json.loads(json.dumps(base))
            edit(copy)
            return self.schema.errors(copy)

        def not_proved(r, strict=True):
            """Declaration 0 NOT PROVED and counted; under --strict-axioms
            the status 6, else Lean's 0."""
            r["declarations"][0].update(axiomBits=8, notProved=True, notProvedBy=["sorryAx"])
            r["counts"].update(notProved=1)
            r["settings"].update(strictAxioms=strict)
            r.update(exitStatus=6 if strict else 0)

        def rejected(r, status):
            """Declaration 5 rejected, counted, and the status given."""
            d = r["declarations"][5]
            for key in ("label", "axiomBits", "notProved", "notProvedBy"):
                d.pop(key, None)
            d.update(verdict="rejected", diagnostic=None)
            r["counts"].update(accepted=5, rejected=1)
            r.update(exitStatus=status)
        cases = [
            (good, lambda r: r["declarations"][4].update(verdict="rejected")),   # status 0
            (good, lambda r: r["declarations"][0].update(axiomBits=8)),          # notProved false
            (good, lambda r: r["declarations"][0].pop("label")),
            (good, lambda r: r["declarations"][1].update(diagnostic=None)),      # accepted
            (good, lambda r: r.update(run="not-run")),                           # read ok
            (good, lambda r: r["fuel"]["top"].append(r["fuel"]["top"][0]) or
             r["fuel"]["top"].extend(r["fuel"]["top"] * 5)),                    # more than 10
            (good, lambda r: r.update(extra=1)),
            (good, lambda r: r.update(stopped=True)),                            # status 0
            (good, lambda r: r["declarations"][4].update(verdict="not-checked")),  # run ok
            (unread, lambda r: r.update(counts=good["counts"])),                 # not read
            (unread, lambda r: r["read"].update(phase=None)),                    # failed read
            # Status 0 only with every count but the accepted 0, at least one
            # declaration, every fuel known, and a run that did not stop.
            (good, lambda r: r["counts"].update(rejected=1)),
            (good, lambda r: r["counts"].update(notChecked=1)),
            (good, lambda r: r["fuel"].update(unknown=1)),
            (good, lambda r: r.update(declarations=[])),
            (good, lambda r: r["counts"].update(declarations=0, accepted=0)),
            (good, lambda r: r.update(counts=None)),
            # A run that stopped did not end ok; status 6 needs
            # --strict-axioms and a NOT PROVED declaration, all accepted;
            # under --strict-axioms a NOT PROVED one never leaves status 0;
            # there is no status 7; settings say whether it is strict.
            (good, lambda r: r.update(stopped=True, exitStatus=5)),
            (good, lambda r: r.update(exitStatus=6)),
            (good, lambda r: r.update(exitStatus=7)),
            (good, lambda r: not_proved(r) or r.update(exitStatus=0)),
            (good, lambda r: not_proved(r, strict=False) or r.update(exitStatus=6)),
            (good, lambda r: not_proved(r) or rejected(r, 6)),
            (good, lambda r: r["settings"].pop("strictAxioms")),
            (good, lambda r: r["measured"].pop("engine")),
            (good, lambda r: r["measured"].update(engine="")),
        ]
        for base, edit in cases:
            self.assertNotEqual(changed(base, edit), [], cases.index((base, edit)))
        self.assertEqual(changed(good, lambda r: None), [])
        # Planted reports, since no check can make a NOT PROVED declaration
        # yet: status 6 under --strict-axioms, Lean's 0 without it, and a
        # rejected declaration beside a NOT PROVED one (1 outranks 6), all
        # accepted; so is a report whose engine is not known.
        self.assertEqual(changed(good, not_proved), [])
        self.assertEqual(changed(good, lambda r: not_proved(r, strict=False)), [])
        self.assertEqual(changed(good, lambda r: not_proved(r) or rejected(r, 1)), [])
        self.assertEqual(changed(good, lambda r: r["measured"].update(engine=None)), [])

    def test_deterministic(self):
        for args in [[INDUCTIVE], ["--no-manifest", "tests/core/reexport/kinds.ndjson"]]:
            first, second = report(*args)[1], report(*args)[1]
            for got in (first, second):
                self.assertIsInstance(got.pop("measured")["peakResidentBytes"], (int, type(None)))
            self.assertEqual(first, second, args)

    def test_strict_axioms(self):
        """settings records --strict-axioms; with no NOT PROVED declaration
        (none can be yet) it changes nothing else."""
        status, got, _ = report(INDUCTIVE)
        strict_status, strict, _ = report("--strict-axioms", INDUCTIVE)
        self.assertEqual((got["settings"]["strictAxioms"], strict["settings"]["strictAxioms"],
                          self.schema.errors(strict)), (False, True, []))
        for one in (got, strict):
            one.pop("measured")
            one["settings"].pop("strictAxioms")
        self.assertEqual((strict_status, strict), (status, got))
        self.assertEqual(run("check", "--strict-axioms", INDUCTIVE), run("check", INDUCTIVE))

    def test_contents(self):
        status, got, _ = report(INDUCTIVE)
        self.assertEqual((status, got["run"], got["read"]["outcome"], got["manifest"]),
                         (0, "ok", "ok", "checked"))
        self.assertEqual([d["fuel"] > 0 for d in got["declarations"]],
                         [True, False, False, False, True, True])   # the block's is Two's
        self.assertEqual((got["fuel"]["total"], got["fuel"]["unknown"]),
                         (sum(d["fuel"] for d in got["declarations"]), 0))
        self.assertEqual([t["name"] for t in got["fuel"]["top"]],
                         ["Two.cases", "Two", "Two.swap"])
        self.assertEqual((got["input"]["declarations"], got["stopped"]), (6, False))
        # Fuel not known: a check that failed in inference gave its counter
        # up; it is in no total and never among the most fuel used.
        _, got, _ = report("--no-manifest", "tests/core/reexport/kinds.ndjson")
        unknown = [d for d in got["declarations"] if d["fuel"] is None]
        self.assertEqual(len(unknown), got["fuel"]["unknown"])
        self.assertTrue(unknown and all(d["verdict"] not in ("accepted", "exhausted")
                                        for d in unknown))
        self.assertEqual(got["fuel"]["total"],
                         sum(d["fuel"] for d in got["declarations"] if d["fuel"] is not None))
        fuels = [t["fuel"] for t in got["fuel"]["top"]]
        self.assertEqual(fuels, sorted(fuels, reverse=True))
        self.assertEqual(fuels[0], max(d["fuel"] or 0 for d in got["declarations"]))
        status, got, _ = report("--no-manifest", "README.md")
        self.assertEqual((status, got["read"]["phase"], got["read"]["line"], got["run"]),
                         (4, "stage", 1, "not-run"))
        status, got, _ = report("tests/cli/no-such.ndjson")
        self.assertEqual((status, got["read"]["phase"], got["input"]), (4, "open", None))


class Names(unittest.TestCase):
    """Names as Lean's Name.toString shows them (src/cli/name-text.fs), in
    the text and the JSON report alike: a component that is not an
    identifier between « and », and every character the text rule bans
    escaped, so that no name can start a line of its own or reorder the
    text after it; names of any depth. composition's theorem renamed, its
    proof unchanged, so every case is accepted."""

    def renamed(self, folder, records):
        """composition with its theorem's name made of records, name
        records ("str" or "num" and "pre") given ids after its own 12, the
        last the theorem's name."""
        lines = (ROOT / COMPOSITION).read_text().splitlines()
        names = [json.dumps({"in": 13 + i, **record}, ensure_ascii=False)
                 for i, record in enumerate(records)]
        last = 12 + len(records)
        thm = lines[-1].replace('"all":[1]', f'"all":[{last}]').replace('"name":1,', f'"name":{last},')
        path = Path(folder) / "renamed.ndjson"
        path.write_text("\n".join(lines[:-1] + names + [thm]) + "\n")
        return str(path)

    def shown(self, records, shown):
        with tempfile.TemporaryDirectory() as folder:
            export = self.renamed(folder, records)
            status, out, err = run("check", "--no-manifest", export)
            self.assertEqual((status, out.splitlines(), err),
                             (0, [NO_MANIFEST, f"{shown}: {LABEL}", "1 declaration: 1 accepted",
                                  accepted(1)], ""), shown)
            status, got, err = report("--no-manifest", export)
            self.assertEqual((status, got["declarations"][0]["name"], err,
                              JsonReport.schema.errors(got)), (0, shown, "", []), shown)

    def test_escaped(self):
        forged = f"composition: rejected\nforged: {LABEL}\nx"
        for text, shown in [
            ("composition", "composition"),
            (forged, "«composition: rejected\\u{A}forged: " + LABEL + "\\u{A}x»"),
            ("a\r\x1b[2Kb", "«a\\u{D}\\u{1B}[2Kb»"),
            ("ab‮cd⁦", "«ab\\u{202E}cd\\u{2066}»"),     # bidirectional controls
            ("a\x00b\x85c ", "«a\\u{0}b\\u{85}c\\u{2028}»"),  # NUL, C1, line separator
            ("a\\u{A}", "«a\\\\u{A}»"),                            # a backslash, not an escape
            ("with space", "«with space»"),
            ("", "«»"),
            ("αβ₁", "αβ₁"),                                         # an identifier as it is
            ("x₊", "«x₊»"),                                         # a subscript sign
            # Lean shows these without « »: here the component is always
            # between « », a » in it escaped, so no line starts "fake: ".
            (f"fake: {LABEL}\n» x", "«fake: " + LABEL + "\\u{A}\\u{BB} x»"),
            (f"fake: {LABEL}✝", f"«fake: {LABEL}✝»"),         # inaccessible
            ("#fake: x", "«#fake: x»"),                            # pseudo-syntax
        ]:
            self.shown([{"str": {"pre": 0, "str": text}}], shown)
        # Macro scopes: Lean shows fake: x._@._hyg bare.
        self.shown([{"str": {"pre": 0, "str": f"fake: {LABEL}"}},
                    {"str": {"pre": 13, "str": "_@"}}, {"str": {"pre": 14, "str": "_hyg"}}],
                   f"«fake: {LABEL}».«_@»._hyg")

    def test_print_escaped(self):
        """print shows every declaration name as check does (name-text.fs): a name
        holding a newline cannot start a line of the outline, in the header, the
        statement or the input line."""
        forged = f"composition: rejected\nforged: {LABEL}\nx"
        shown = "«composition: rejected\\u{A}forged: " + LABEL + "\\u{A}x»"
        with tempfile.TemporaryDirectory() as folder:
            export = self.renamed(folder, [{"str": {"pre": 0, "str": forged}}])
            status, out, err = run("print", "--no-manifest", export)
            lines = out.splitlines()
            self.assertEqual((status, err), (0, ""))
            self.assertIn("Theorem " + shown, lines)
            self.assertFalse([l for l in lines if l.startswith("forged")], lines)
            self.assertEqual(sum(l.startswith("Theorem ") for l in lines), 1)
            # a name no word of LeanForth can spell is not printed as words
            self.assertTrue(any("(not complete:" in l for l in lines))
            status, out, err = run("print", "--no-manifest", "--name", forged, export)
            self.assertEqual((status, err), (0, ""))
            self.assertIn("Theorem " + shown, out.splitlines())
            status, out, err = run("print", "--no-manifest", "--name", "x\ny", export)
            self.assertEqual((status, out.splitlines()[-1], err),
                             (4, "error: no declaration named x\\u{A}y", ""))

    def test_print_crafted_binder_and_constant(self):
        """A binder name and a referenced constant's name holding LF and U+202E (and
        an invalid byte) cannot forge an outline line, reorder text or reach the output
        raw, in every statement form, in --detail and in the LaTeX style (review rvPR B1)."""
        forged = "q\nTheorem forged\n  accepted (experimental)‮"
        cases = [("tests/reference/identity.ndjson", '"str":"P"'),
                 ("tests/reference/constant-fixture.ndjson", '"str":"fixtureId"')]
        for forged, (source, old) in [(f, c) for f in (forged, "r\u202es") for c in cases]:
            text = (ROOT / source).read_text(encoding="utf-8")
            self.assertEqual(text.count(old), 1, source)
            crafted = text.replace(old, '"str":' + json.dumps(forged, ensure_ascii=False))
            with tempfile.TemporaryDirectory() as folder:
                export = Path(folder) / "crafted.ndjson"
                export.write_text(crafted, encoding="utf-8")
                for options in ([], ["--detail"], ["--statement", "mathematics"],
                                ["--statement", "leanforth"], ["--statement", "lean"],
                                ["--latex"], ["--latex", "--statement", "mathematics"]):
                    status, out, err = run("print", "--no-manifest", *options, str(export))
                    where = (source, options)
                    self.assertEqual((status, err), (0, ""), where)
                    self.assertNotIn("‮", out, where)
                    lines = out.splitlines()
                    self.assertEqual([l for l in lines if l.startswith(("Theorem forged",
                                                                       "  accepted (experimental)",
                                                                       "forged"))], [], where)
                    heads = [l for l in lines if re.match(r"^(\\textbf\{)?(Theorem|Definition)", l)]
                    self.assertEqual(len(heads), 1 if "identity" in source else 3, where)

    def test_print_latex_odd_names(self):
        """LaTeX specials and a long binder name keep the fragment well formed: braces and
        environments balance, and a name of 1,100 bytes is not cut (the line buffer grows)."""
        text = (ROOT / "tests/reference/identity.ndjson").read_text(encoding="utf-8")
        for name in ["a_b#c%d&e{f}g$h^i~j\\k", "x" * 1100, "p\n\nq"]:
            crafted = text.replace('"str":"P"', '"str":' + json.dumps(name))
            with tempfile.TemporaryDirectory() as folder:
                export = Path(folder) / "odd.ndjson"
                export.write_text(crafted, encoding="utf-8")
                status, out, err = run("print", "--no-manifest", "--latex", str(export))
                self.assertEqual((status, err), (0, ""), name[:20])
                plain = re.sub(r"\\[{}$%&#_ ]", "", out)
                self.assertEqual(plain.count("{"), plain.count("}"), name[:20])
                self.assertEqual(out.count("\\begin{"), out.count("\\end{"), name[:20])
                if shutil.which("pdflatex"):
                    tex = Path(folder) / "odd.tex"
                    tex.write_text("\\documentclass{article}\n\\usepackage[utf8]{inputenc}\n"
                                   "\\usepackage{amsmath,amssymb}\n\\begin{document}\n"
                                   + out.split("\n", 1)[1] + "\n\\end{document}\n")
                    run_tex = subprocess.run(["pdflatex", "-no-shell-escape", "-halt-on-error",
                                              "-interaction=nonstopmode", tex.name], cwd=folder,
                                             capture_output=True, text=True,
                                             stdin=subprocess.DEVNULL, timeout=120)
                    self.assertEqual(run_tex.returncode, 0, run_tex.stdout[-800:])
                if len(name) > 1000:
                    self.assertIn("x" * 1100, out)
                    status, plain_out, err = run("print", "--no-manifest", str(export))
                    self.assertIn("x" * 1100, plain_out)

    def test_print_long_names(self):
        """--name picks a declaration by its whole name, however long: no fixed
        buffer (review B-L3: a 256-byte one dropped components, so a long name
        could select the wrong declaration)."""
        long = "a" * 300
        deep = [{"str": {"pre": 12 + i if i else 0, "str": "b" * 100}} for i in range(5)]
        for records, name in [([{"str": {"pre": 0, "str": long}}], long),
                              (deep, ".".join(["b" * 100] * 5))]:
            with tempfile.TemporaryDirectory() as folder:
                export = self.renamed(folder, records)
                status, out, err = run("print", "--no-manifest", "--name", name, export)
                self.assertEqual((status, err), (0, ""), name[:20])
                self.assertIn(f"Theorem {name}", out.splitlines())
                # the first 256 characters, or all but the last component, name nothing
                for wrong in (name[:256], name[:-1], name[1:]):
                    status, out, err = run("print", "--no-manifest", "--name", wrong, export)
                    self.assertEqual(status, 4, wrong[:20])

    def test_components(self):
        # A numeric component in decimal, an empty one as «», and a name
        # deeper than any fixed limit: 100 components.
        self.shown([{"str": {"pre": 0, "str": "a"}}, {"num": {"pre": 13, "i": 7}},
                    {"str": {"pre": 14, "str": ""}}], "a.7.«»")
        deep = [{"str": {"pre": 12 + i if i else 0, "str": f"a{i}"}} for i in range(100)]
        self.shown(deep, ".".join(f"a{i}" for i in range(100)))

    def test_export_name(self):
        """The export's file name in the report: the same escapes, without
        « »; the check is unchanged."""
        with tempfile.TemporaryDirectory() as folder:
            export = Path(folder) / "caf\udcff\n.ndjson"
            export.write_bytes((ROOT / COMPOSITION).read_bytes())
            status, got, err = report("--no-manifest", str(export))
            self.assertEqual((status, got["export"], err, JsonReport.schema.errors(got)),
                             (0, f"{folder}/caf\\x{{FF}}\\u{{A}}.ndjson", "", []))


class Resources(unittest.TestCase):
    """check --resources (plan task 6.5.2, the command line's part)."""

    def test_report(self):
        status, out, err = run("check", "--resources", INDUCTIVE)
        lines = out.splitlines()
        self.assertEqual((status, err, lines[:9]),
                         (0, "", run("check", INDUCTIVE)[1].splitlines() + ["resources:"]))
        rest = lines[9:]
        self.assertEqual(rest[0], "  time (s)     wall      cpu")
        self.assertEqual([line.split()[0] for line in rest[1:5]],
                         ["stage", "feed", "check", "total"])
        self.assertRegex(rest[5], r"^  memory: peak resident \d+(\.\d)? [kM]B; "
                                  r"the stage's heap blocks \d+(\.\d)? [kM]B$")
        # The engine bin/leanforth ran: the file name of GFORTH here.
        self.assertEqual(rest[6], "  engine: " + os.path.basename(GFORTH))
        self.assertEqual(rest[7:], [
            "  input: 6 declarations, 46 term nodes, 3 levels, 5 constant references, 31 names",
            "  fuel: 1136 steps in all, at most 100000 per declaration",
            "  most fuel used:",
            "       552 Two.cases (accepted)",
            "       336 Two (accepted)",
            "       248 Two.swap (accepted)"])

    def test_stable_but_for_time_and_memory(self):
        def steady(out):
            return [line for line in out.splitlines()
                    if not re.match(r"^  (stage|feed|check|total) |^  memory: ", line)]
        args = ["--resources", "--no-manifest", "tests/core/reexport/kinds.ndjson"]
        self.assertEqual(steady(run("check", *args)[1]), steady(run("check", *args)[1]))


def fast_engine():
    """The gforth-fast bin/leanforth finds beside GFORTH (in its folder:
    scripts/gforth-fast under make), or None."""
    folder = os.path.dirname(GFORTH)
    if not folder:
        return shutil.which("gforth-fast")
    path = os.path.join(folder, "gforth-fast")
    return path if os.access(path, os.X_OK) else None


class Engines(unittest.TestCase):
    """Gforth's checking engine by default; --fast runs gforth-fast with the
    same verdicts, the same report but for "measured" (owner, 2026-11-04)."""

    def test_fast_same_reports(self):
        fast = fast_engine()
        for args in [[COMPOSITION], [FIXTURE], [CHAIN], [INDUCTIVE], ["tests/cli/unfold.ndjson"],
                     ["--no-manifest", f"{CASES}/composition-wrong-argument.ndjson"],
                     ["--no-manifest", "tests/core/reexport/kinds.ndjson"],
                     ["--fuel", "0", FIXTURE]]:
            status, got, err = report(*args)
            fast_status, fast_got, fast_err = report("--fast", *args)
            engines = got.pop("measured")["engine"], fast_got.pop("measured")["engine"]
            self.assertEqual((fast_status, fast_got), (status, got), args)
            self.assertEqual(run("check", "--fast", *args)[1], run("check", *args)[1], args)
            if fast:
                self.assertEqual((engines, fast_err), ((os.path.basename(GFORTH),
                                                        os.path.basename(fast)), ""), args)
            else:   # no gforth-fast beside GFORTH (such as Gforth 0.7.3's wrapper)
                self.assertEqual(engines, (os.path.basename(GFORTH),) * 2, args)
                self.assertRegex(fast_err, r"^leanforth: note: --fast: no .* found; "
                                           r"checking with .*\n$")

    def test_fast_missing(self):
        """--fast with no gforth-fast beside GFORTH: the run uses GFORTH and
        says so on standard error."""
        with tempfile.TemporaryDirectory() as folder:
            stub = Path(folder) / "myforth"
            stub.write_text(f'#!/bin/sh\nexec "{GFORTH}" "$@"\n')
            stub.chmod(stub.stat().st_mode | stat.S_IXUSR)
            status, out, err = run("check", "--fast", "--json", COMPOSITION, gforth=str(stub))
            note = (f"leanforth: note: --fast: no {folder}/gforth-fast found; "
                    f"checking with {stub}\n")
            self.assertEqual((status, json.loads(out)["measured"]["engine"], err),
                             (0, "myforth", note))

    def test_gforth_unset(self):
        """With GFORTH unset the wrapper finds the engines itself, in this
        checkout's .tools or on PATH: gforth, and gforth-fast with --fast."""
        tools = ROOT / ".tools" / "gforth" / "bin"

        def found(name):
            return (tools / name).exists() or shutil.which(name)
        if not (found("gforth") and found("gforth-fast")):
            self.skipTest("no gforth and gforth-fast to find without GFORTH")
        env = {key: value for key, value in os.environ.items() if key != "GFORTH"}
        for options, engine in [([], "gforth"), (["--fast"], "gforth-fast")]:
            result = subprocess.run([str(TOOL), "check", "--json", *options, COMPOSITION],
                                    cwd=ROOT, env=env, stdin=subprocess.DEVNULL,
                                    capture_output=True, timeout=300)
            self.assertEqual((result.returncode, json.loads(result.stdout)["measured"]["engine"],
                              result.stderr), (0, engine, b""), options)

    def test_options(self):
        """--fast goes with check, replay and print; it is no file name,
        and the value of --fuel is not the option."""
        for args in [["check", "--fast", COMPOSITION], ["print", "--fast", COMPOSITION]]:
            self.assertEqual(run(*args)[0], 0, args)
        self.assertEqual(run("count", "--fast", COMPOSITION)[:2],
                         (4, "error: an option this command does not take: --fast\n"
                             "try: leanforth help\n"))
        self.assertEqual(run("check", "--fuel", "--fast", COMPOSITION)[:2],
                         (4, "error: not a fuel amount: --fast\ntry: leanforth help\n"))


class Fuel(unittest.TestCase):
    """The fuel an accepted declaration's check used is exactly what it
    needs: with a budget of that much it is accepted, with one less it runs
    out. Taken for the accepted declaration that used the most, so every
    accepted one before it, its dependencies among them, used less and
    stays accepted."""

    def test_exact(self):
        for export in [COMPOSITION, FIXTURE, CHAIN, INDUCTIVE, "tests/cli/unfold.ndjson"]:
            _, got, _ = report(export)
            accepted = [d for d in got["declarations"] if d["verdict"] == "accepted"]
            most = max(accepted, key=lambda d: d["fuel"])
            self.assertEqual(sum(d["fuel"] == most["fuel"] for d in accepted), 1, export)
            for budget, verdict in [(most["fuel"], "accepted"),
                                    (most["fuel"] - 1, "exhausted")]:
                _, again, _ = report("--fuel", str(budget), export)
                self.assertEqual(again["declarations"][most["index"]]["verdict"], verdict,
                                 (export, budget))

    def test_most(self):
        """--fuel takes at most 2^53 - 1, the largest integer every JSON
        reader holds exactly; a report with it is valid and says it."""
        status, got, _ = report("--fuel", str(2**53 - 1), INDUCTIVE)
        self.assertEqual((status, got["settings"]["fuel"], got["fuel"]["perDeclaration"],
                          JsonReport.schema.errors(got)), (0, 2**53 - 1, 2**53 - 1, []))
        self.assertEqual(run("check", "--fuel", str(2**53), INDUCTIVE)[0], 4)


if __name__ == "__main__":
    unittest.main()
