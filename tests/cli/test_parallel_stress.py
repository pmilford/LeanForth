"""check --jobs with more workers than cores, at scale (plan 9.4.8p; M2 of the
re-entrancy audit of 2026-11-18): make test-parallel-stress.

An export of 5,000 tiny declarations is generated here (never committed): two axioms,
then theorems that use an earlier theorem (so most wait for one), definitions, and
theorems whose type unfolds a definition, with a rejected theorem every 500. It is
checked once at --jobs 1 through bin/leanforth-checker (bin/leanforth's check of an export
on the checker's load alone, tests/cli/test_checker_launcher.py), then STRESS_REPEATS times (default 5,
make test-parallel-stress; 20 in make parallel-init, the daily run) with twice as many
workers as the machine has cores, and each run's text and exit status must be the
serial run's.

Workers above the cores: bin/leanforth cuts --jobs to the cores (lib/task.fs's
task-cores, check-run.fs's ck-jobs-most), so the parallel runs start Gforth on
src/load/cli-checker.fs themselves, as bin/leanforth-checker does, after defining task-cores-test, a
word lib/task.fs reads only when it is defined before the file loads (the test-only
override). bin/leanforth defines no such word, takes no option or environment variable
for it and runs Gforth with its start-up file turned off (GFORTH_ENV=off: Gforth 1.0
would otherwise load the file GFORTH_ENV names, or ~/.config/gforthrc0, before
src/main.fs, which could define the word): a test sets GFORTH_ENV to a file that defines
it and finds the workers still cut to the cores, through bin/leanforth and through
bin/leanforth-checker, each of which turns the file off itself.
Run from the repository root with GFORTH naming the engine; unittest.
"""
import os
import pathlib
import subprocess
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
GFORTH = os.environ.get("GFORTH", str(ROOT / ".tools/gforth/bin/gforth"))
DECLARATIONS = 5000
REPEATS = int(os.environ.get("STRESS_REPEATS", "5"))
META = ('{"meta":{"exporter":{"name":"lean4export","version":"3.1.0"},"format":{"version":'
        '"3.1.0"},"lean":{"githash":"eb6cafb7290e8bd5f2937522d8d804f58f02bafc",'
        '"version":"4.35.0"}}}')


class Export:
    """A lean4export 3.1.0 NDJSON text built record by record."""

    def __init__(self):
        self.lines, self.names, self.exprs = [META], 0, 0

    def name(self, text):
        self.names += 1
        self.lines.append(f'{{"in":{self.names},"str":{{"pre":0,"str":"{text}"}}}}')
        return self.names

    def expr(self, body):
        self.lines.append(f'{{{body},"ie":{self.exprs}}}')
        self.exprs += 1
        return self.exprs - 1

    def const(self, name):
        return self.expr(f'"const":{{"name":{name},"us":[]}}')

    def axiom(self, name, type_):
        self.lines.append(f'{{"axiom":{{"isUnsafe":false,"levelParams":[],"name":{name},'
                          f'"type":{type_}}}}}')

    def theorem(self, name, type_, value):
        self.lines.append(f'{{"thm":{{"all":[{name}],"levelParams":[],"name":{name},'
                          f'"type":{type_},"value":{value}}}}}')

    def definition(self, name, type_, value):
        self.lines.append(f'{{"def":{{"all":[{name}],"hints":{{"regular":1}},"levelParams":[],'
                          f'"name":{name},"safety":"safe","type":{type_},"value":{value}}}}}')


def generated(count):
    """The export's text: P : Prop, p : P, then count declarations."""
    out = Export()
    prop = out.expr('"sort":0')
    p_name = out.name("P")
    out.axiom(p_name, prop)
    p_type = out.const(p_name)
    proof = out.name("p")
    out.axiom(proof, p_type)
    proof_term, theorems, last_def = out.const(proof), [proof], None
    for i in range(count):
        if i % 500 == 499:      # rejected: P, a proposition, is no proof of P
            out.theorem(out.name(f"bad{i}"), p_type, p_type)
        elif i % 4 == 1:        # a definition, P again
            last_def = out.name(f"d{i}")
            out.definition(last_def, prop, p_type)
        elif i % 4 == 2 and last_def:   # its type unfolds the last definition
            out.theorem(out.name(f"u{i}"), out.const(last_def), proof_term)
        else:                   # a proof by an earlier theorem, half way back
            name = out.name(f"t{i}")
            out.theorem(name, p_type, out.const(theorems[len(theorems) // 2]))
            theorems.append(name)
    return "\n".join(out.lines) + "\n"


def leanforth(*args, launcher="bin/leanforth-checker", **env):
    result = subprocess.run([str(ROOT / launcher), "check", *args], capture_output=True,
                            text=True, stdin=subprocess.DEVNULL,
                            env=dict(os.environ, GFORTH=GFORTH, **env))
    return result.returncode, result.stdout


def oversubscribed(workers, *args):
    """check --jobs workers, Gforth started as bin/leanforth starts it but with the
    test-only task-cores-test defined first: (exit code, text)."""
    result = subprocess.run([GFORTH, "-e", f"{workers} constant task-cores-test",
                             str(ROOT / "src/load/cli-checker.fs"), "-e", "cli-main", "check",
                             "--jobs", str(workers), *args], capture_output=True, text=True,
                            stdin=subprocess.DEVNULL, env=dict(os.environ, GFORTH_ENV="off"))
    return result.returncode - 100, result.stdout


class Stress(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.dir = tempfile.TemporaryDirectory()
        cls.export = os.path.join(cls.dir.name, "stress.ndjson")
        with open(cls.export, "w", encoding="utf-8") as stream:
            stream.write(generated(DECLARATIONS))
        cls.serial = leanforth("--no-manifest", "--jobs", "1", cls.export)
        cls.workers = max(4, 2 * (os.cpu_count() or 1))

    @classmethod
    def tearDownClass(cls):
        cls.dir.cleanup()

    def test_serial_run(self):
        """The serial run checks every declaration: the rejected ones rejected (exit 1)."""
        status, out = self.serial
        self.assertEqual(status, 1, out[-500:])
        self.assertIn(f"{DECLARATIONS + 2} declarations: {DECLARATIONS + 2 - 10} accepted, "
                      "10 rejected", out)

    def test_more_workers_than_cores(self):
        """STRESS_REPEATS runs at twice the cores, each the serial run's text and status, and the
        workers really above the cores (the resource report names them)."""
        for k in range(REPEATS):
            with self.subTest(run=k):
                self.assertEqual(oversubscribed(self.workers, "--no-manifest", self.export),
                                 self.serial)
        status, out = oversubscribed(self.workers, "--no-manifest", "--resources", self.export)
        self.assertIn(f"  workers: {self.workers} (--jobs), on ", out)

    def test_users_cut_to_cores(self):
        """Without the override, as users run it, --jobs is cut to the cores."""
        status, out = leanforth("--no-manifest", "--resources", "--jobs", str(self.workers),
                                self.export)
        self.assertEqual(status, 1)
        self.assertNotIn(f"  workers: {self.workers} (--jobs)", out)

    def test_start_up_file_ignored(self):
        """A Gforth start-up file (GFORTH_ENV) that defines the test hook changes nothing
        a user runs: each launcher, bin/leanforth and bin/leanforth-checker, turns it off
        itself (neither leaves it to the other or to scripts/leanforth-run.sh), so --jobs is
        still cut to the cores."""
        rc0 = os.path.join(self.dir.name, "rc0.fs")
        with open(rc0, "w", encoding="utf-8") as stream:
            stream.write(f"{self.workers} constant task-cores-test\n")
        for launcher in ("bin/leanforth", "bin/leanforth-checker"):
            status, out = leanforth("--no-manifest", "--resources", "--jobs", str(self.workers),
                                    self.export, launcher=launcher, GFORTH_ENV=rc0)
            self.assertEqual(status, 1, launcher)
            self.assertIn("  workers: ", out, launcher)
            self.assertNotIn(f"  workers: {self.workers} (--jobs)", out, launcher)
            self.assertNotIn(f"on {self.workers} cores", out, launcher)


if __name__ == "__main__":
    unittest.main()
