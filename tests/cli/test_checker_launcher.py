#!/usr/bin/env python3
"""bin/leanforth-checker against bin/leanforth (make test-cli-checker; branch layered-loads).

bin/leanforth-checker runs the command line on the checker's load alone
(src/load/cli-checker.fs), and the export-only tests and pinned-Lean comparisons run it
(scripts/program_receipt.py's LEANFORTH, which its receipts name, the demos, the clamp's mutants, leanforth verify's
references), so that scripts/tested-tree.py reuses them across changes of the front end. This
test is what makes that sound: on every command below, exports and snapshots only, both
launchers give the same exit code, the same standard output and standard error and write the
same files, byte for byte; only the JSON report's "measured" part (wall and CPU time, peak
resident bytes) is left out, as it differs from run to run. It runs bin/leanforth, which loads
src/main.fs, so a change anywhere re-runs it, and a change of the front end that made the
whole load check an export otherwise than the checker's load fails here. A LeanForth text is
refused by bin/leanforth-checker (exit 4, said so) and checked by bin/leanforth.

GFORTH names the engine of both, as the Makefile passes it. Exit status 0 when all agree."""
import os
import pathlib
import re
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parent.parent.parent
sys.path.insert(0, str(ROOT / "tests" / "support"))
import toolchain  # noqa: E402

FULL, CHECKER = ROOT / "bin" / "leanforth", ROOT / "bin" / "leanforth-checker"
TEST_LIMIT = int(os.environ.get("TEST_TIMEOUT", "1800"))
C = "tests/reference/composition.ndjson"
F = "tests/reference/constant-fixture.ndjson"
B = "tests/reference/inductive/blocks.ndjson"
AX = "tests/reference/inductive/axioms.ndjson"
W = "tests/core/check-declaration-cases/composition-wrong-argument.ndjson"
U = "tests/core/check-declaration-cases/composition-unsafe.ndjson"
DEP = "tests/cli/dependent.ndjson"
ODD = "tests/cli/odd-names.ndjson"
IND = "tests/cli/inductive.ndjson"
LF = "tests/author/01-identity.lf"
# OUT stands for a folder of the run's own.
COMMANDS = [
    [], ["help"], ["--help"], ["version"], ["capabilities"], ["nonsense"], ["check"],
    ["check", "no-such.ndjson"], ["check", C], ["check", F], ["check", B], ["check", AX],
    ["check", "--no-manifest", W], ["check", "--no-manifest", U], ["check", DEP], ["check", ODD], ["check", IND],
    ["check", "--json", C], ["check", "--json", "--no-manifest", W], ["check", "--strict-axioms", AX],
    ["check", "--jobs", "2", B], ["check", "--fuel", "10", C], ["check", "--memory-per-check", "1", B],
    ["check", "--fast", "--checked", C], ["check", "--record", "OUT/r.rec", C], ["check", "--save-snapshot",
                                                                            "OUT/s.lfsnap", B],
    ["print", C], ["print", "--detail", C], ["print", "--latex", C], ["print", "--lf", B],
    ["print", "--name", "nosuch", C], ["count", B], ["reexport", C, "OUT/copy.ndjson"], ["reexport", C, C],
    ["check", "--steps", "-", C], ["check", "--env", C, C], ["verify"], ["verify", "--help"],
    ["verify", "src/program/clamp.fs"],
]
# Commands that read what an earlier command of the same run wrote.
FOLLOW_ON = [(["check", "--record", "OUT/r.rec", C], ["replay", C, "OUT/r.rec"]),
             (["check", "--save-snapshot", "OUT/s.lfsnap", B], ["check", "--snapshot", "OUT/s.lfsnap", AX])]
MEASURED = re.compile(r',"measured":\{"microseconds":\{.*?\},"peakResidentBytes":\d+,')


def run(tool, commands):
    """[(exit, stdout, stderr, {file: bytes})] of TOOL on each command list of COMMANDS (run in
    order, in one folder of their own, from the checkout)."""
    folder = tempfile.mkdtemp(prefix="lf-checker-launcher-")
    env = dict(os.environ, GFORTH=toolchain.gforth())
    found = []
    try:
        for argv in commands:
            done = subprocess.run([str(tool), *(a.replace("OUT", folder) for a in argv)], cwd=ROOT, env=env,
                                  capture_output=True, text=True, timeout=TEST_LIMIT, stdin=subprocess.DEVNULL)
            out, err = (MEASURED.sub(',"measured":?,', t).replace(folder, "OUT") for t in (done.stdout, done.stderr))
            files = {p.name: p.read_bytes() for p in sorted(pathlib.Path(folder).iterdir())}
            found.append((done.returncode, out, err, files))
    finally:
        shutil.rmtree(folder, ignore_errors=True)
    return found


class SameOutput(unittest.TestCase):
    def test_every_export_command_alike(self):
        for argv, full, checker in zip(COMMANDS, run(FULL, COMMANDS), run(CHECKER, COMMANDS)):
            with self.subTest(command=" ".join(argv)):
                self.assertEqual(full, checker)

    def test_commands_that_read_what_another_wrote(self):
        for pair in FOLLOW_ON:
            with self.subTest(command=" ".join(pair[1])):
                self.assertEqual(run(FULL, pair), run(CHECKER, pair))

    def test_the_comparison_sees_a_difference(self):
        full, checker = run(FULL, [["check", C]])[0], run(CHECKER, [["check", "--no-manifest", W]])[0]
        self.assertNotEqual(full, checker)


class Text(unittest.TestCase):
    def test_a_text_is_refused_by_the_checker_and_checked_by_leanforth(self):
        [(code, out, err, _)] = run(CHECKER, [["check", LF]])
        self.assertEqual(code, 4, out + err)
        self.assertEqual(out, "error: bin/leanforth-checker checks exports and snapshots only; check a LeanForth text with bin/leanforth\n")
        [(code, out, err, _)] = run(FULL, [["check", LF]])
        self.assertEqual(code, 0, out + err)
        self.assertIn("identity: accepted", out)


class BrokenCheckout(unittest.TestCase):
    """A checkout without scripts/leanforth-run.sh is an internal fault (exit 5), never a
    verdict (exit 1; review M1 of layered-loads)."""

    def test_a_missing_shared_script_is_an_internal_fault(self):
        folder = tempfile.mkdtemp(prefix="lf-broken-checkout-")
        try:
            shutil.copytree(ROOT / "bin", pathlib.Path(folder) / "bin")
            (pathlib.Path(folder) / "scripts").mkdir()
            shutil.copy(ROOT / "scripts" / "start-limit.sh", pathlib.Path(folder) / "scripts")
            for name in ("leanforth", "leanforth-checker"):
                done = subprocess.run(["bash", str(pathlib.Path(folder) / "bin" / name), "version"],
                                      cwd=folder, capture_output=True, text=True, timeout=TEST_LIMIT,
                                      stdin=subprocess.DEVNULL)
                self.assertEqual(done.returncode, 5, name + done.stdout + done.stderr)
                self.assertIn("leanforth: internal fault: cannot read scripts/leanforth-run.sh", done.stderr)
        finally:
            shutil.rmtree(folder, ignore_errors=True)


if __name__ == "__main__":
    unittest.main()
