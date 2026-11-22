#!/usr/bin/env python3
"""Tests of tests/front/tactics/tactic_check.py's batch arguments (plan row TB2): main's lean=,
lean_wrong= and golden= name the Lean twins, the wrong twins and the golden a batch keeps in its
own directory; the defaults stay goal-layer's. Pinned Lean is a stand-in here (s2.run_many and
s2.lean_binary replaced): no Lean, no Gforth runs."""
import pathlib
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import tactic_check  # noqa: E402

DUMP = "t1 type (pi Nat.{} Nat.{})\nt1 value (lam Nat.{} #0)\n"
WRONG = [("w.lf", 96, "Type mismatch", "  h")]


def done(code, out):
    return subprocess.CompletedProcess([], code, out, "")


class Arguments(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.golden = pathlib.Path(self.tmp.name) / "batch.golden"
        self.runs = []

    def tearDown(self):
        self.tmp.cleanup()

    def fake(self, wrong_out="error: Type mismatch\n  h\n"):
        def run_many(argvs):
            self.runs.append(argvs)
            return iter([done(0, DUMP + "other output\n"), done(1, wrong_out)])
        return [mock.patch.object(tactic_check.s2, "run_many", run_many),
                mock.patch.object(tactic_check.s2, "lean_binary", lambda: "lean")]

    def lean(self, write, **names):
        patches = self.fake()
        for patch in patches:
            patch.start()
        try:
            tactic_check.check_lean(WRONG, write, **names)
        finally:
            for patch in patches:
                patch.stop()

    def test_defaults_are_goal_layers(self):
        self.assertEqual(tactic_check.LEAN_TWINS, "tests/front/tactics/goal-layer.lean")
        self.assertEqual(tactic_check.LEAN_WRONG, "tests/front/tactics/goal-layer-wrong.lean")
        self.assertEqual(tactic_check.GOLDEN.name, "goal-layer.golden")

    def test_the_batch_files_are_run_and_written(self):
        self.lean(True, lean="b.lean", lean_wrong="b-wrong.lean", golden_path=self.golden)
        self.assertEqual(self.runs, [[["lean", "b.lean"], ["lean", "b-wrong.lean"]]])
        self.assertEqual(self.golden.read_text(encoding="utf-8"), DUMP)
        self.assertEqual(tactic_check.golden(self.golden),
                         {"t1 type": DUMP.splitlines()[0], "t1 value": DUMP.splitlines()[1]})

    def test_a_golden_that_differs_is_refused_by_its_name(self):
        self.golden.write_text("t1 type other\n", encoding="utf-8")
        with self.assertRaises(tactic_check.Failure) as caught:
            self.lean(False, lean="b.lean", lean_wrong="b-wrong.lean", golden_path=self.golden)
        self.assertIn("b.lean: pinned Lean's output is not batch.golden", str(caught.exception))

    def test_main_hands_the_names_on(self):
        seen = {}

        def check_lean(wrong, write, lean, lean_wrong, golden):
            seen.update(lean=lean, lean_wrong=lean_wrong, golden=golden, write=write)
        with mock.patch.object(tactic_check, "check_lean", check_lean), \
                mock.patch.object(sys, "argv", ["check.py", "--lean"]):
            tactic_check.main("batch", [], WRONG, [], lean="b.lean", lean_wrong="b-wrong.lean",
                              golden=self.golden)
        self.assertEqual(seen, {"lean": "b.lean", "lean_wrong": "b-wrong.lean", "golden": self.golden,
                                "write": False})

    def test_a_name_may_give_its_axioms(self):
        self.assertEqual(tactic_check.theorem_axioms("t1"), ("t1", "none"))
        self.assertEqual(tactic_check.theorem_axioms("t1=propext, Classical.choice"),
                         ("t1", "propext, Classical.choice"))

    def checked(self, names, out):
        want = {"t1 type": DUMP.splitlines()[0], "t1 value": DUMP.splitlines()[1]}
        with mock.patch.object(tactic_check.s2, "run_many",
                               lambda argvs: iter([done(0, out), done(0, DUMP)])), \
                mock.patch.object(tactic_check.s2, "check_log", lambda path, lines: None):
            return tactic_check.check_files([("f.lf", names)], want)

    def test_the_axioms_are_those_the_name_gives(self):
        self.checked(["t1=propext"], "t1: accepted; axioms: propext\n")
        with self.assertRaises(tactic_check.Failure) as caught:
            self.checked(["t1"], "t1: accepted; axioms: propext\n")
        self.assertIn("t1 not accepted with axioms none", str(caught.exception))

    def test_main_reads_the_batch_golden(self):
        self.golden.write_text(DUMP, encoding="utf-8")
        wanted = {}
        with mock.patch.object(tactic_check, "check_files", lambda files, want, env: wanted.update(want) or []), \
                mock.patch.object(tactic_check, "check_steps", lambda name, logs: None), \
                mock.patch.object(tactic_check, "check_refused", lambda wrong, unsupported, env: None), \
                mock.patch.object(sys, "argv", ["check.py"]):
            tactic_check.main("batch", [], [], [], golden=self.golden)
        self.assertEqual(sorted(wanted), ["t1 type", "t1 value"])


if __name__ == "__main__":
    unittest.main()
