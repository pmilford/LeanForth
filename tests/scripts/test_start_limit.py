"""A Gforth that could not be started is reported as such (review lib-tidy, note 9).

scripts/start-limit.sh's lf_start_report explains statuses 254 (bash could not fork: a
process limit) and 126/127 (an exec failed), with the user's threads and process limit, and
prints nothing for any other status. Then the real case: bin/leanforth runs a Gforth wrapper
that lowers its own process limit to 1 (`ulimit -u 1`, inherited only by that process, so
nothing else on the machine is touched) and execs scripts/gforth-strict.sh, whose first fork
is refused: the strict wrapper reports it, ends with 254, and bin/leanforth says "could not
start Gforth: resource limit", an internal fault (exit 5), instead of only "Gforth ended with
status 254". Bash retries a refused fork for about 15 seconds first.

Run from the repository root: python3 tests/scripts/test_start_limit.py
"""
import os
from pathlib import Path
import re
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
HELPER = ROOT / "scripts" / "start-limit.sh"


def report(status):
    run = subprocess.run(["sh", "-c", f'. "{HELPER}"; lf_start_report who {status}; echo "rc $?"'],
                         capture_output=True, text=True, timeout=60)
    return run.stdout, run.stderr


class Report(unittest.TestCase):
    def test_refused_fork(self):
        out, err = report(254)
        self.assertEqual(out, "rc 0\n")
        self.assertRegex(err, r"^who: could not start Gforth: resource limit \(a process could not "
                              r"be started\); the user has [1-9][0-9]* threads, process limit \S+\n$")

    def test_failed_exec(self):
        for status in (126, 127):
            out, err = report(status)
            self.assertEqual(out, "rc 0\n")
            self.assertIn(f"who: could not start Gforth: exec failed (status {status})", err)

    def test_other_statuses_say_nothing(self):
        for status in (0, 1, 5, 100, 137, 255):
            self.assertEqual(report(status), ("rc 1\n", ""))

    def test_threads_counted_without_a_process(self):
        # The count includes at least this shell's own thread, and the limit is the shell's.
        run = subprocess.run(["bash", "-c", f'. "{HELPER}"; lf_user_threads; '
                                            'echo "$lf_threads $lf_nproc $(ulimit -u)"'],
                             capture_output=True, text=True, timeout=60)
        threads, limit, shell_limit = run.stdout.split()
        self.assertGreaterEqual(int(threads), 1)
        self.assertEqual(limit, shell_limit)


class RefusedFork(unittest.TestCase):
    def test_leanforth_says_gforth_could_not_start(self):
        with tempfile.TemporaryDirectory() as tmp:
            wrapper = Path(tmp) / "gforth-limited"
            wrapper.write_text("#!/bin/bash\nulimit -u 1\n"
                               f'exec "{ROOT}/scripts/gforth-strict.sh" "$@"\n')
            wrapper.chmod(0o755)
            env = dict(os.environ, GFORTH=str(wrapper))
            env.pop("LEANFORTH_STRICT_DEPTH", None)
            run = subprocess.run([str(ROOT / "bin" / "leanforth"), "count", "--no-manifest",
                                  str(ROOT / "tests" / "reference" / "composition.ndjson")],
                                 capture_output=True, text=True, env=env, timeout=300,
                                 stdin=subprocess.DEVNULL)
        self.assertEqual(run.returncode, 5, run.stderr)
        self.assertIn("fork: Resource temporarily unavailable", run.stderr)
        self.assertRegex(run.stderr, r"gforth-strict: could not start Gforth: resource limit .*"
                                     r"the user has [1-9][0-9]* threads, process limit 1\n")
        self.assertRegex(run.stderr, r"leanforth: internal fault: could not start Gforth: resource "
                                     r"limit .*threads, process limit \S+\n")
        self.assertNotIn("Gforth ended with status", run.stderr)


if __name__ == "__main__":
    unittest.main()
