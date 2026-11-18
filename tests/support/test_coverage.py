#!/usr/bin/env python3
"""Tests of scripts/coverage.py (make coverage): it must never silently stop counting.

Needs Gforth 1.0 ($GFORTH, else .tools) for the end-to-end cases, which run a
tiny command under the counting wrapper:
  - a command that starts no Gforth leaves no counts: exit 1 (the 2026-11-12 fault);
  - a command that runs Gforth directly (bypassing $GFORTH) the same;
  - a command that runs $GFORTH counts, and --check / --update-baseline work on it;
  - the ratchet fails when a file's never-run blocks grow or a new file has some.
"""
import importlib.util
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
SCRIPT = ROOT / "scripts/coverage.py"
spec = importlib.util.spec_from_file_location("coverage_tool", SCRIPT)
tool = importlib.util.module_from_spec(spec)
spec.loader.exec_module(tool)


def real_gforth():
    local = ROOT / ".tools/gforth/bin/gforth"
    found = os.environ.get("LEANFORTH_GFORTH") or (str(local) if local.exists() else None)
    found = found or shutil.which("gforth")
    if found and "scripts/" in found:
        found = str(local) if local.exists() else shutil.which("gforth")
    return found


GFORTH = real_gforth()
HAS_COVERAGE = bool(GFORTH) and tool.has_coverage(GFORTH)


class Pure(unittest.TestCase):
    def test_no_counts_is_a_problem(self):
        self.assertTrue(tool.run_problems(0, 0, None))

    def test_runs_without_counts_are_a_problem(self):
        self.assertEqual(tool.run_problems(9, 0, None), [])
        self.assertTrue(tool.run_problems(8, 2, None))

    def test_fewer_runs_than_the_baseline_is_a_problem(self):
        self.assertEqual(tool.run_problems(100, 0, {"runs": 100}), [])
        self.assertEqual(tool.run_problems(90, 0, {"runs": 100}), [])
        self.assertTrue(tool.run_problems(89, 0, {"runs": 100}))

    def test_ratchet(self):
        base = {"files": {"src/a.fs": {"blocks": 5, "never_run": 2, "reason": "x"}}}
        self.assertEqual(tool.ratchet({"src/a.fs": [5, 2]}, base), [])
        self.assertEqual(tool.ratchet({"src/a.fs": [7, 1]}, base), [])
        self.assertEqual(len(tool.ratchet({"src/a.fs": [5, 3]}, base)), 1)
        self.assertEqual(len(tool.ratchet({"src/b.fs": [5, 1]}, base)), 1)
        self.assertEqual(tool.ratchet({"src/b.fs": [5, 0]}, base), [])

    def test_new_baseline_needs_a_reason_for_new_gaps(self):
        old = {"files": {"src/a.fs": {"blocks": 5, "never_run": 2, "reason": "kept"}}}
        files = {"src/a.fs": [5, 2], "src/b.fs": [4, 0]}
        out = tool.new_baseline(files, 7, old, "")
        self.assertEqual(out["files"]["src/a.fs"]["reason"], "kept")
        self.assertNotIn("reason", out["files"]["src/b.fs"])
        self.assertEqual(out["runs"], 7)
        with self.assertRaises(SystemExit):
            tool.new_baseline({"src/c.fs": [4, 1]}, 7, old, "")
        self.assertEqual(
            tool.new_baseline({"src/c.fs": [4, 1]}, 7, old, "why")["files"]["src/c.fs"]["reason"], "why")

    def test_focused_run_checks_only_its_counts(self):
        # A few targets (make coverage-focus): no share or baseline rule on the run counts.
        self.assertEqual(tool.run_problems(1, 5, {"runs": 100}, focused=True), [])
        self.assertTrue(tool.run_problems(0, 5, {"runs": 100}, focused=True))

    def test_focus_keeps_the_named_files_and_reports_unloaded_ones(self):
        files = {"src/a.fs": [5, 2], "src/b.fs": [4, 4]}
        kept, missing = tool.focus(files, ["src/a.fs", "src/c.fs"])
        self.assertEqual(kept, {"src/a.fs": [5, 2]})
        self.assertEqual(missing, ["src/c.fs: no run of the command loaded it"])

    def test_focus_passes_a_load_list_that_compiles_no_block(self):
        # src/main.fs only requires modules: no run can show it loaded (fix-batch-4).
        kept, missing = tool.focus({}, ["src/main.fs", "src/lib/slab.fs"])
        self.assertEqual((kept, missing), ({}, ["src/lib/slab.fs: no run of the command loaded it"]))
        self.assertFalse(tool.compiles_blocks("src/main.fs"))
        self.assertTrue(tool.compiles_blocks("src/lib/slab.fs"))

    def test_only_needs_check(self):
        for args in (["--only", "src/a.fs"], ["--only", "src/a.fs", "--check", "--update-baseline"]):
            with self.assertRaises(SystemExit):
                tool.main(args + ["--", "true"])


@unittest.skipUnless(HAS_COVERAGE, "needs Gforth 1.0 with coverage.fs")
class EndToEnd(unittest.TestCase):
    def run_tool(self, *args):
        env = {k: v for k, v in os.environ.items() if k != "GFORTH"}
        return subprocess.run([sys.executable, str(SCRIPT), "--gforth", GFORTH, *args],
                              cwd=ROOT, env=env, stdin=subprocess.DEVNULL,
                              capture_output=True, text=True, timeout=300)

    def test_a_command_without_gforth_fails(self):
        result = self.run_tool("--", "true")
        self.assertEqual(result.returncode, 1, result.stdout)
        self.assertIn("no counts were collected", result.stdout)

    def test_a_command_that_bypasses_the_wrapper_fails(self):
        result = self.run_tool("--", GFORTH, "-e", "bye")
        self.assertEqual(result.returncode, 1, result.stdout)

    def test_a_counted_run_succeeds_and_the_ratchet_works(self):
        command = ["sh", "-c", f'"$GFORTH" {ROOT}/src/lib/outcome.fs -e bye </dev/null']
        with tempfile.TemporaryDirectory() as folder:
            baseline = Path(folder) / "baseline.json"
            options = ["--baseline", str(baseline)]
            result = self.run_tool(*options, "--check", "--", *command)
            self.assertEqual(result.returncode, 1, "no baseline: --check must fail")
            result = self.run_tool(*options, "--update-baseline", "--reason", "test",
                                "--", *command)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn("src/lib", result.stdout)
            self.assertIn("1 Gforth runs with counts, 0 without", result.stdout)
            data = json.loads(baseline.read_text())
            self.assertEqual(data["runs"], 1)
            result = self.run_tool(*options, "--check", "--", *command)
            self.assertEqual(result.returncode, 0, result.stdout)
            # A smaller never-run allowance than measured fails; so do fewer runs.
            name = next(iter(data["files"]))
            data["files"][name]["never_run"] = -1
            baseline.write_text(json.dumps(data))
            result = self.run_tool(*options, "--check", "--", *command)
            self.assertEqual(result.returncode, 1, result.stdout)
            self.assertIn(name, result.stdout)
            data["files"][name]["never_run"] = 10 ** 6
            data["runs"] = 50
            baseline.write_text(json.dumps(data))
            result = self.run_tool(*options, "--check", "--", *command)
            self.assertEqual(result.returncode, 1, result.stdout)
            self.assertIn("only 1 Gforth runs", result.stdout)
            # --only: the same run is enough for its file, and a file it never loaded fails.
            result = self.run_tool(*options, "--check", "--only", "src/lib/outcome.fs", "--", *command)
            self.assertEqual(result.returncode, 0, result.stdout)
            self.assertIn("no file of src/lib/outcome.fs has more never-run blocks", result.stdout)
            result = self.run_tool(*options, "--check", "--only", "src/lib/sort.fs", "--", *command)
            self.assertEqual(result.returncode, 1, result.stdout)
            self.assertIn("src/lib/sort.fs: no run of the command loaded it", result.stdout)
            data["files"]["src/lib/outcome.fs"]["never_run"] = -1
            baseline.write_text(json.dumps(data))
            result = self.run_tool(*options, "--check", "--only", "src/lib/outcome.fs", "--", *command)
            self.assertEqual(result.returncode, 1, result.stdout)


if __name__ == "__main__":
    unittest.main()
