"""make profile-check's tools (docs/development/PROFILING.md, "Where a check spends its
time"): scripts/profile-summary.py's families and words on a profile made by hand, exactly;
scripts/profile-check.sh on a small export (the sampler, the symbol table, the tables, the
slowest declarations), a well-formed report; scripts/slowest-declarations.py on a report
without times.

Usage (from the repository root): GFORTH_FAST=PATH python3 tests/scripts/test_profile_check.py
"""
import json
import os
import pathlib
import re
import subprocess
import sys
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
PYTHON = sys.executable
FAMILY_ROW = re.compile(r"^ *(\d+\.\d\d)% +(\d+\.\d\d)% +(\d+\.\d\d)%  (\S.*)$")
WORD_ROW = re.compile(r"^ *(\d+\.\d\d)%  (\S+)  (\S*)$")

SYMS = """\
100 c lf-check-declaration /x/src/kernel/check-declaration.fs:10
200 c lf-instantiate /x/src/kernel/mixed-instantiate.fs:20
300 c lf-term-cons /x/src/core/terms.fs:30
400 c htab-find /x/src/lib/htab.fs:40
500 c lf-env-current /x/src/kernel/environment.fs:50
600 c ck-check /x/src/cli/check-run.fs:60
RP0 1000
SP0 2000
"""
PROFILE = """\
# samples 10 wall 0.1 s interval 0.01
4\thtab-find;lf-term-cons;lf-instantiate;lf-check-declaration;ck-check
3\tlf-instantiate;lf-check-declaration;ck-check
2\tlf-env-current;lf-check-declaration;ck-check
1\t<libc>;lf-check-declaration;ck-check
"""


def summary(*args):
    return subprocess.run([PYTHON, str(ROOT / "scripts/profile-summary.py"), *args],
                          capture_output=True, text=True)


def section(text, title):
    """The rows under the line starting with "-- " + title, up to the next "--" line."""
    lines = text.splitlines()
    start = next(i for i, line in enumerate(lines) if line.startswith("-- " + title))
    rows = []
    for line in lines[start + 1:]:
        if line.startswith("--"):
            break
        rows.append(line)
    return rows


class Summary(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        base = pathlib.Path(self.tmp.name)
        self.prof, self.syms = base / "t.prof", base / "t.syms"
        self.prof.write_text(PROFILE)
        self.syms.write_text(SYMS)

    def tearDown(self):
        self.tmp.cleanup()

    def families(self, *extra):
        done = summary(str(self.prof), str(self.syms), *extra)
        self.assertEqual(done.returncode, 0, done.stderr)
        rows = [FAMILY_ROW.match(r) for r in section(done.stdout, "families")]
        self.assertTrue(all(rows), done.stdout)
        return {m.group(4): tuple(float(m.group(k)) for k in (1, 2, 3)) for m in rows}, done.stdout

    def test_families_by_file_and_name(self):
        """Exclusive: the innermost word's family (<libc> its own); inclusive: once per sample
        with the family on the stack; owner: the first non-service family outwards."""
        fam, out = self.families()
        self.assertEqual(fam["term construction and hashing (lf-term-cons, htab, hash32)"],
                         (40.0, 40.0, 0.0))
        self.assertEqual(fam["instantiation and abstraction (replace passes)"], (30.0, 70.0, 70.0))
        self.assertEqual(fam["validity checks"], (20.0, 20.0, 0.0))
        self.assertEqual(fam["C library"], (10.0, 10.0, 0.0))
        self.assertEqual(fam["type inference, declaration checks"], (0.0, 100.0, 30.0))
        self.assertAlmostEqual(sum(v[0] for v in fam.values()), 100.0, places=1)
        self.assertAlmostEqual(sum(v[2] for v in fam.values()), 100.0, places=1)
        self.assertIn("100.00%  check\n", out)

    def test_words_and_under(self):
        """The words' tables, exclusive and inclusive, with their files; --under keeps the
        samples with that word."""
        done = summary(str(self.prof), str(self.syms), "--top", "2")
        words = [WORD_ROW.match(r).groups() for r in section(done.stdout, "words, exclusive")]
        self.assertEqual(words, [("40.00", "htab-find", "src/lib/htab.fs"),
                                 ("30.00", "lf-instantiate", "src/kernel/mixed-instantiate.fs")])
        inner = [WORD_ROW.match(r).group(2) for r in section(done.stdout, "words, inclusive")]
        self.assertEqual(inner, ["lf-check-declaration", "lf-instantiate"])
        fam, out = self.families("--under", "lf-term-cons")
        self.assertIn("; 4 samples kept", out)
        self.assertEqual(fam["term construction and hashing (lf-term-cons, htab, hash32)"],
                         (100.0, 100.0, 0.0))

    def test_store_reads_family(self):
        """A word of lib/store.fs or lib/slab.fs counts with the core's reads (the family
        KERNEL_SPEED.md prints); a validity word of the same file stays a validity check."""
        self.syms.write_text(SYMS + "700 c store-slot /x/src/lib/store.fs:70\n"
                             "800 c store-count-valid? /x/src/lib/store.fs:80\n")
        self.prof.write_text("# samples 2\n1\tstore-slot;ck-check\n1\tstore-count-valid?;ck-check\n")
        fam, _ = self.families()
        self.assertEqual(fam["reads of terms, stores, slabs (src/core, store.fs, slab.fs)"],
                         (50.0, 50.0, 0.0))
        self.assertEqual(fam["validity checks"], (50.0, 50.0, 0.0))

    def test_empty(self):
        done = summary(str(self.prof), str(self.syms), "--under", "nowhere")
        self.assertEqual(done.returncode, 2)


class Slowest(unittest.TestCase):
    def test_refuses_a_report_without_times(self):
        """A report without declarationMicroseconds (no --resources) is refused, status 2."""
        report = {"declarations": [], "measured": {"microseconds": None}}
        with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as f:
            json.dump(report, f)
        try:
            done = subprocess.run([PYTHON, str(ROOT / "scripts/slowest-declarations.py"), f.name],
                                  capture_output=True, text=True)
        finally:
            os.unlink(f.name)
        self.assertEqual(done.returncode, 2)
        self.assertIn("--resources", done.stderr)


class Failures(unittest.TestCase):
    def test_no_engine(self):
        """A gforth-fast that is not there: status 5 and one line saying so, no traceback."""
        env = dict(os.environ, GFORTH_FAST="/nonexistent/gforth-fast")
        done = subprocess.run(["sh", str(ROOT / "scripts/profile-check.sh"),
                               "tests/reference/constant-fixture.ndjson"], cwd=ROOT, env=env,
                              capture_output=True, text=True, timeout=30)
        self.assertEqual(done.returncode, 5)
        self.assertNotIn("Traceback", done.stderr)
        self.assertIn("gforth-fast", done.stderr)

    def test_command_not_run(self):
        """The sampler given a command that cannot run: its exit status 127, one message."""
        with tempfile.TemporaryDirectory() as tmp:
            env = dict(os.environ, PROF_SYMS=os.path.join(tmp, "none.syms"))
            done = subprocess.run([PYTHON, str(ROOT / "scripts/profile-sample.py"),
                                   os.path.join(tmp, "samples"), "0.01", "--",
                                   "/nonexistent/command"], env=env,
                                  capture_output=True, text=True, timeout=30)
        self.assertEqual(done.returncode, 127)
        self.assertNotIn("Traceback", done.stderr)
        self.assertIn("cannot run /nonexistent/command", done.stderr)


@unittest.skipUnless(os.environ.get("GFORTH_FAST"), "GFORTH_FAST names no gforth-fast")
class Whole(unittest.TestCase):
    def test_small_export(self):
        """scripts/profile-check.sh on the 579-declaration S2 slice: status 0, the check's JSON
        report kept, the phases, a family table that sums to 100% (exclusive and owner), the
        word tables with their files, and the slowest declarations by time."""
        with tempfile.TemporaryDirectory() as tmp:
            env = dict(os.environ, PROFILE_OUT=tmp, PROFILE_INTERVAL="0.002", PROFILE_TOP="5")
            done = subprocess.run(["sh", str(ROOT / "scripts/profile-check.sh"),
                                   "tests/front/s2-slice.ndjson"], cwd=ROOT, env=env,
                                  capture_output=True, text=True, timeout=300)
            report = json.loads((pathlib.Path(tmp) / "check.json").read_text())
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertEqual(report["counts"]["accepted"], 579)
        out = done.stdout
        self.assertRegex(out, r"^# samples \d+ wall \d+\.\d s interval 0\.002; \d+ samples kept\n")
        self.assertTrue(any(re.match(r" *\d+\.\d\d%  check$", r) for r in section(out, "phases")),
                        out)
        rows = [FAMILY_ROW.match(r) for r in section(out, "families")]
        self.assertTrue(rows and all(rows), out)
        for k in (1, 3):
            self.assertAlmostEqual(sum(float(m.group(k)) for m in rows), 100.0, delta=0.1)
        words = [WORD_ROW.match(r) for r in section(out, "words, exclusive")]
        self.assertTrue(len(words) == 5 and all(words), out)
        slow = section(out, "slowest declarations by time")
        self.assertEqual(slow[0], "rank\tindex\tmicroseconds\tfuel\tns/fuel\tverdict\tname")
        self.assertEqual(len(slow), 7, out)
        self.assertRegex(slow[-1], r"^total \d+ us; the 5 listed \d+ us \(\d+\.\d%\)$")


if __name__ == "__main__":
    unittest.main()
