"""Per-run scratch folders for the Forth tests that write files (make test-sections).

scripts/with-scratch.sh COMMAND runs COMMAND with LF_TEST_SCRATCH naming a new,
empty folder of its own, passes COMMAND's exit status on and removes the
folder afterwards, also after a failure; two runs at once get two folders.
tests/support/scratch.fs's scratch-file puts a file name in that folder, or
in /tmp when LF_TEST_SCRATCH is unset or empty; its stack effect is checked.

Usage (from the repository root): GFORTH=... python3 tests/scripts/test_with_scratch.py
"""
import concurrent.futures
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = str(ROOT / "scripts" / "with-scratch.sh")
GFORTH = os.environ.get("GFORTH", "gforth")
LIMIT = 120


def wrapped(*command, env=None):
    return subprocess.run([SCRIPT, *command], capture_output=True, text=True, timeout=LIMIT,
                          stdin=subprocess.DEVNULL, env=env)


def scratch_name(value):
    """scratch-file of "a.bin" in Gforth, LF_TEST_SCRATCH set to value (None: unset), and
    the depth after it."""
    env = {k: v for k, v in os.environ.items() if k != "LF_TEST_SCRATCH"}
    if value is not None:
        env["LF_TEST_SCRATCH"] = value
    done = subprocess.run([GFORTH, "tests/support/scratch.fs", "-e",
                           's" a.bin" scratch-file type cr depth . cr bye'], cwd=ROOT, env=env,
                          capture_output=True, text=True, timeout=LIMIT, stdin=subprocess.DEVNULL)
    return [line.strip() for line in done.stdout.split("\n")[:2]]


class WithScratch(unittest.TestCase):
    def test_folder_given_and_removed(self):
        done = wrapped("sh", "-c", 'test -d "$LF_TEST_SCRATCH" && test -z "$(ls -A '
                                   '"$LF_TEST_SCRATCH")" && touch "$LF_TEST_SCRATCH/x" && '
                                   'echo "$LF_TEST_SCRATCH"')
        self.assertEqual(done.returncode, 0, done.stderr)
        folder = done.stdout.strip()
        self.assertTrue(folder.startswith(tempfile.gettempdir()), folder)
        self.assertFalse(os.path.exists(folder))

    def test_exit_status_kept_and_folder_removed(self):
        for status in (1, 3, 4):
            done = wrapped("sh", "-c", f'echo "$LF_TEST_SCRATCH"; exit {status}')
            self.assertEqual(done.returncode, status)
            self.assertFalse(os.path.exists(done.stdout.strip()))

    def test_runs_at_once_get_their_own(self):
        with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
            folders = list(pool.map(lambda _: wrapped(
                "sh", "-c", 'sleep 0.3; echo "$LF_TEST_SCRATCH"').stdout.strip(), range(4)))
        self.assertEqual(len(set(folders)), 4, folders)

    def test_missing_command(self):
        done = wrapped("/no/such/command")
        self.assertEqual(done.returncode, 127)


class ScratchFile(unittest.TestCase):
    def test_in_the_folder_or_tmp(self):
        self.assertEqual(scratch_name("/some/folder"), ["/some/folder/a.bin", "0"])
        self.assertEqual(scratch_name(None), ["/tmp/a.bin", "0"])
        self.assertEqual(scratch_name(""), ["/tmp/a.bin", "0"])


if __name__ == "__main__":
    unittest.main()
