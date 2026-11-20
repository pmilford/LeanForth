#!/usr/bin/env python3
"""Unit tests of scripts/mathlib-slice.py's cache (review data-bk L3): a cold entry is
built only when allowed, else SKIPPED (exit 3, never a pass); a run that loses the
rename to another filling the same entry keeps the other's folder; a cached entry is
not built again. No Mathlib, no Lean: the inputs are stand-ins. Beside them, the same
rule for the decide check against Init (tests/front/tactics/decide/check.py --init, make
reference-decide-init; review of ops-symbols B3 (c)): without Init's snapshot a user's run
skips and says so, a recorded run (REQUIRE_INIT_SNAPSHOT=1) fails, and a snapshot not of
this build's verdict version is told apart.

Usage: python3 tests/scripts/test_mathlib_slice.py
"""
import contextlib
import importlib.util
import io
import os
import pathlib
import sys
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parent.parent.parent
SPEC = importlib.util.spec_from_file_location("mathlib_slice", ROOT / "scripts/mathlib-slice.py")
slicer = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(slicer)


def write(folder, name="made"):
    (folder / name).write_text("x")


class Cached(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.cache = pathlib.Path(self.tmp.name) / "cache"

    def tearDown(self):
        self.tmp.cleanup()

    def test_cold_entry_not_allowed_is_skipped(self):
        with self.assertRaises(slicer.Skipped):
            slicer.cached(self.cache, "raw-1", self.fail, allowed=False)
        self.assertFalse(self.cache.exists())

    def test_cold_entry_allowed_is_built(self):
        final = slicer.cached(self.cache, "raw-1", write)
        self.assertEqual(final, self.cache / "raw-1")
        self.assertTrue((final / "made").is_file())
        self.assertEqual(sorted(p.name for p in self.cache.iterdir()), ["raw-1"])

    def test_cached_entry_is_not_built_again(self):
        (self.cache / "raw-1").mkdir(parents=True)
        for allowed in (True, False):
            self.assertEqual(slicer.cached(self.cache, "raw-1", self.fail, allowed),
                             self.cache / "raw-1")

    def test_lost_rename_keeps_the_winner(self):
        def other_run_wins(work):
            write(work, "mine")
            (self.cache / "raw-1").mkdir()
            write(self.cache / "raw-1", "theirs")
        final = slicer.cached(self.cache, "raw-1", other_run_wins)
        self.assertEqual(sorted(p.name for p in final.iterdir()), ["theirs"])
        self.assertEqual(sorted(p.name for p in self.cache.iterdir()), ["raw-1"])

    def test_failed_build_leaves_nothing(self):
        def broken(work):
            write(work)
            raise SystemExit("broken")
        with self.assertRaises(SystemExit):
            slicer.cached(self.cache, "raw-1", broken)
        self.assertEqual(list(self.cache.iterdir()), [])


class NoExport(unittest.TestCase):
    """tests/front/check_mathlib_slice.py on a machine without a Mathlib export: a user's
    make check skips it and says so; a recorded run (REQUIRE_MATHLIB=1) fails."""

    def run_check(self, require):
        import subprocess
        env = dict(os.environ, MATHLIB_EXPORT="/nonexistent/mathlib.ndjson")
        env.pop("REQUIRE_MATHLIB", None)
        if require:
            env["REQUIRE_MATHLIB"] = "1"
        return subprocess.run([sys.executable, "tests/front/check_mathlib_slice.py"], cwd=ROOT, env=env,
                              capture_output=True, text=True, timeout=120)

    def test_a_users_run_skips_and_says_so(self):
        done = self.run_check(False)
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertIn("SKIPPED, NOT RUN", done.stdout)
        self.assertIn("no Mathlib export", done.stdout)

    def test_a_recorded_run_fails(self):
        done = self.run_check(True)
        self.assertNotEqual(done.returncode, 0)
        self.assertIn("no fixture", done.stderr)

    def test_tested_tree_requires_it(self):
        text = (ROOT / "scripts/tested-tree.py").read_text(encoding="utf-8")
        self.assertIn('os.environ.setdefault("REQUIRE_MATHLIB", "1")', text)


DECIDE = ROOT / "tests/front/tactics/decide/check.py"


class NoInitSnapshot(unittest.TestCase):
    """tests/front/tactics/decide/check.py --init on a machine without Init's snapshot: a user's
    make reference-decide-init skips it and says so; a recorded run (REQUIRE_INIT_SNAPSHOT=1)
    fails."""

    def run_check(self, require, snapshot="/nonexistent/init-1.lfsn"):
        import subprocess
        env = dict(os.environ)
        env.pop("REQUIRE_INIT_SNAPSHOT", None)
        if require:
            env["REQUIRE_INIT_SNAPSHOT"] = "1"
        return subprocess.run([sys.executable, str(DECIDE), "--init", snapshot, str(DECIDE)], cwd=ROOT,
                              env=env, capture_output=True, text=True, timeout=120)

    def test_a_users_run_skips_and_says_so(self):
        done = self.run_check(False)
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertIn("check decide --init: SKIPPED, NOT RUN: no Init snapshot "
                      "(INIT_SNAPSHOT=/nonexistent/init-1.lfsn)", done.stdout)

    def test_a_recorded_run_fails(self):
        done = self.run_check(True)
        self.assertEqual(done.returncode, 1)
        self.assertIn("FAILED, NOT RUN: no Init snapshot", done.stderr)
        self.assertNotIn("SKIPPED", done.stdout)

    def test_missing_elaboration_data_is_named(self):
        import subprocess
        env = dict(os.environ)
        env.pop("REQUIRE_INIT_SNAPSHOT", None)
        done = subprocess.run([sys.executable, str(DECIDE), "--init", str(DECIDE), "/nonexistent/init.elab"],
                              cwd=ROOT, env=env, capture_output=True, text=True, timeout=120)
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertIn("no Init elaboration data (INIT_ELAB=/nonexistent/init.elab)", done.stdout)

    def test_tested_tree_requires_it(self):
        text = (ROOT / "scripts/tested-tree.py").read_text(encoding="utf-8")
        self.assertIn('os.environ.setdefault("REQUIRE_INIT_SNAPSHOT", "1")', text)

    def test_a_stale_snapshot_is_told_apart(self):
        spec = importlib.util.spec_from_file_location("decide_check", DECIDE)
        decide = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(decide)
        current = ("snapshot: init-1.lfsn (sha256 d964), export sha256 c1b2, verdict version 9, "
                   "written by LeanForth b9ba: 59349 results taken from it")
        older = ("snapshot: init-1.lfsn (sha256 d964), export sha256 c1b2, verdict version 8 (this build: "
                 "9), written by LeanForth b9ba: 0 results carried from it")
        refused = "note: this build reads snapshots of verdict versions 7 to 9: check the export"
        self.assertIsNone(decide.stale_line("sy_mul: accepted\n" + current))
        self.assertEqual(decide.stale_line("sy_mul: accepted\n" + older), older)
        self.assertEqual(decide.stale_line("error: ...\n" + refused + "\n"), refused)
        self.assertIn("carry:", decide.stale_line("carry: a snapshot of verdict version 8, this build's 9"))


class Main(unittest.TestCase):
    """main() on stand-in inputs and an empty cache: skipped without the opt-in."""

    def test_cold_cache_skips_without_opt_in(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmp = pathlib.Path(tmp)
            export = tmp / "mathlib.ndjson"
            export.write_text("")
            olean = tmp / "lake/build/lib/lean/Mathlib.olean"
            olean.parent.mkdir(parents=True)
            olean.write_text("")
            lean = tmp / "lean"
            lean.write_text("#!/bin/sh\necho 0\n")
            lean.chmod(0o755)
            argv = ["--export", str(export), "--lake", str(tmp / "lake"), "--lean", str(lean),
                    "--cache", str(tmp / "cache")]
            saved = os.environ.pop("MATHLIB_SLICE_BUILD", None)
            err = io.StringIO()
            try:
                with contextlib.redirect_stderr(err):
                    status = slicer.main(argv)
            finally:
                if saved is not None:
                    os.environ["MATHLIB_SLICE_BUILD"] = saved
            self.assertEqual(status, slicer.SKIPPED)
            self.assertIn("SKIPPED, NOT A PASS", err.getvalue())
            self.assertIn("MATHLIB_SLICE_BUILD=1", err.getvalue())
            self.assertFalse((tmp / "cache").exists())


if __name__ == "__main__":
    result = unittest.main(exit=False, verbosity=0).result
    if result.wasSuccessful():
        print(f"mathlib-slice: {result.testsRun} cache tests passed")
    sys.exit(0 if result.wasSuccessful() else 1)
