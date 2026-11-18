#!/usr/bin/env python3
"""Tests of the planted-fault runner, scripts/mutants.py (make test-mutants).

Run from the repository root: python3 tests/mutants/test_mutants.py

Each case builds a small tree in a temporary directory (a file and a shell
test that fails when the file loses its first line), writes a fault list
beside it and runs the runner on that tree. It checks the reported verdicts
and the exit status for every result the runner can give (caught, survived
as listed, survived unexpectedly, caught though listed as surviving, stale,
timed out, a failing control, a malformed list, a temporary directory inside
the tree), and after every run that the tree is exactly as before: the same
files with the same bytes and modification times. The last case checks that
the checked-in list, tests/mutants/faults.toml with tests/mutants/faults.d/, is well formed.
The files of a faults.d folder beside a list are read as part of it: their faults run, an id
given in two files and a malformed file refuse the whole list (fail closed), and the history
rule follows a fault across files. Needs only
Python 3.11 and bash; runs no Forth.
"""
import contextlib
import io
import os
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))
import mutants  # noqa: E402

CHECK = "#!/bin/sh\ngrep -qx alpha src/word.txt\n"
SLOW = "#!/bin/sh\ngrep -qx alpha src/word.txt || sleep 30\n"


def entry(ident, old, new, test="sh check.sh", **extra):
    lines = [f"[[fault]]", f'id = "{ident}"', 'file = "src/word.txt"',
             f"old = '''{old}'''", f"new = '''{new}'''", f'test = "{test}"',
             'reason = "planted for the runner test"']
    lines += [f'{key} = "{value}"' if isinstance(value, str) else
              f"{key} = {str(value).lower()}" for key, value in extra.items()]
    return "\n".join(lines) + "\n\n"


CAUGHT = entry("drops-alpha", "alpha", "gamma")
EQUIVALENT = entry("changes-beta", "beta", "delta", equivalent="check.sh reads alpha only")
GAP_CAUGHT = entry("gap-but-caught", "alpha", "gamma", gap="said to be untested")
SURVIVOR = entry("unseen", "beta", "delta")
STALE = entry("gone", "omega", "psi")


def snapshot(root):
    """Every file under root with its bytes and modification time."""
    return {str(path.relative_to(root)): (path.read_bytes(), path.stat().st_mtime_ns)
            for path in sorted(root.rglob("*")) if path.is_file()}


class RunnerTest(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="mutants-test-")
        base = Path(self.temporary.name)
        self.root = base / "tree"
        (self.root / "src").mkdir(parents=True)
        (self.root / "src/word.txt").write_text("alpha\nbeta\n")
        (self.root / "check.sh").write_text(CHECK)
        (self.root / "slow.sh").write_text(SLOW)
        self.list = base / "faults.toml"
        self.before = snapshot(self.root)

    def tearDown(self):
        self.temporary.cleanup()

    def run_list(self, text, *options):
        """(exit status, output) of the runner on the tree with this list."""
        self.list.write_text(text)
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            status = mutants.main(["--root", str(self.root), "--list", str(self.list),
                                   "--gforth", "gforth", "--timeout", "3", *options])
        self.assertEqual(snapshot(self.root), self.before, "the runner changed the tree")
        return status, output.getvalue()

    def test_caught_and_equivalent(self):
        status, output = self.run_list(CAUGHT + EQUIVALENT)
        self.assertEqual(status, 0, output)
        self.assertRegex(output, r"(?m)^caught +drops-alpha")
        self.assertRegex(output, r"(?m)^survived \(known equivalent\) +changes-beta")
        self.assertIn("2 run, 1 caught, 1 survived as listed", output)

    def test_unexpected_survivor_fails(self):
        status, output = self.run_list(CAUGHT + SURVIVOR)
        self.assertEqual(status, 1, output)
        self.assertRegex(output, r"(?m)^SURVIVED +unseen")

    def test_listed_survivor_caught_fails(self):
        status, output = self.run_list(GAP_CAUGHT)
        self.assertEqual(status, 1, output)
        self.assertRegex(output, r"(?m)^CAUGHT, listed as known gap +gap-but-caught")

    def test_stale_entry_fails(self):
        status, output = self.run_list(CAUGHT + STALE)
        self.assertEqual(status, 1, output)
        self.assertRegex(output, r"(?m)^STALE +gone +src/word.txt: old text found 0 times")
        self.assertRegex(output, r"(?m)^caught +drops-alpha")

    def test_check_runs_nothing(self):
        status, output = self.run_list(CAUGHT + STALE, "--check")
        self.assertEqual(status, 1, output)
        self.assertNotIn("caught", output)
        status, output = self.run_list(CAUGHT, "--check")
        self.assertEqual(status, 0, output)

    def test_quick_and_only(self):
        quick = entry("quick-one", "alpha", "gamma", quick=True)
        status, output = self.run_list(quick + SURVIVOR, "--quick")
        self.assertEqual(status, 0, output)
        self.assertIn("1 run, 1 caught", output)
        status, output = self.run_list(CAUGHT + SURVIVOR, "--only", "drops-alpha")
        self.assertEqual(status, 0, output)
        status, output = self.run_list(CAUGHT, "--only", "nonesuch")
        self.assertEqual(status, 2, output)

    def test_timeout_counts_as_caught(self):
        status, output = self.run_list(entry("hangs", "alpha", "gamma", test="sh slow.sh"))
        self.assertEqual(status, 0, output)
        self.assertRegex(output, r"(?m)^caught +hangs +timeout")

    def test_change_that_does_not_load_fails(self):
        (self.root / "src/mod.py").write_text("x = 1\n")
        self.before = snapshot(self.root)
        broken = entry("syntax", "x = 1", "x = = 1", test="python3 src/mod.py")
        broken = broken.replace('file = "src/word.txt"', 'file = "src/mod.py"')
        status, output = self.run_list(broken)
        self.assertEqual(status, 1, output)
        self.assertRegex(output, r"(?m)^BROKEN: the change does not load +syntax")

    def test_failing_control_stops(self):
        status, output = self.run_list(entry("broken", "alpha", "gamma", test="false"))
        self.assertEqual(status, 2, output)
        self.assertIn("control FAILED", output)

    def test_temporary_directory_inside_tree_refused(self):
        status, output = self.run_list(CAUGHT, "--tmpdir", str(self.root / "src"))
        self.assertEqual(status, 2, output)
        self.assertIn("refused", output)

    def test_malformed_lists_refused(self):
        for text in ('[[fault]]\nid = "x"\n',
                     CAUGHT + CAUGHT,
                     CAUGHT.replace('file = "src/word.txt"', 'file = "../word.txt"'),
                     entry("same", "alpha", "alpha"),
                     entry("both", "alpha", "gamma", gap="g", equivalent="e"),
                     CAUGHT.replace("drops-alpha", "Drops Alpha"),
                     "title = 1\n" + CAUGHT):
            status, output = self.run_list(text)
            self.assertEqual(status, 2, (text, output))
            self.assertIn("bad fault list", output)

    def faults_d(self, **files):
        folder = self.list.parent / mutants.FAULTS_DIR
        folder.mkdir(exist_ok=True)
        for name, text in files.items():
            (folder / f"{name}.toml").write_text(text)

    def test_faults_d_files_are_part_of_the_list(self):
        self.faults_d(tactic=EQUIVALENT)
        (self.list.parent / mutants.FAULTS_DIR / "notes.txt").write_text("not a fault file\n")
        status, output = self.run_list(CAUGHT)
        self.assertEqual(status, 0, output)
        self.assertRegex(output, r"(?m)^caught +drops-alpha")
        self.assertRegex(output, r"(?m)^survived \(known equivalent\) +changes-beta")
        self.assertIn("2 run, 1 caught, 1 survived as listed", output)
        status, output = self.run_list(CAUGHT, "--only", "changes-beta")
        self.assertEqual(status, 0, output)
        self.assertEqual([f["id"] for f in mutants.load_list(self.list)], ["drops-alpha", "changes-beta"])

    def test_faults_d_id_given_twice_refused(self):
        self.faults_d(tactic=CAUGHT.replace("gamma", "epsilon"))
        status, output = self.run_list(CAUGHT)
        self.assertEqual(status, 2, output)
        self.assertIn("bad fault list", output)
        self.assertIn("faults.d/tactic.toml: fault drops-alpha: id must be unique", output)
        self.faults_d(tactic=SURVIVOR, other=SURVIVOR.replace("delta", "eta"))
        status, output = self.run_list(CAUGHT)
        self.assertEqual(status, 2, output)
        self.assertIn("other.toml gives it too", output)

    def test_malformed_faults_d_file_refused(self):
        for text in ("[[fault]\nid = broken\n", "title = 1\n" + SURVIVOR, '[[fault]]\nid = "x"\n', ""):
            self.faults_d(tactic=text)
            status, output = self.run_list(CAUGHT)
            self.assertEqual(status, 2, (text, output))
            self.assertIn("bad fault list", output)
            self.assertIn("tactic.toml", output)
            status, output = self.run_list(CAUGHT, "--check")
            self.assertEqual(status, 2, (text, output))

    def test_checked_in_list_keeps_the_history_rule(self):
        status = mutants.main(["--root", str(ROOT), "--history"])
        self.assertEqual(status, 0)

    def test_checked_in_list_is_well_formed(self):
        faults = mutants.load_list(ROOT / mutants.DEFAULT_LIST)
        self.assertGreaterEqual(len(faults), 40)
        for fault in faults:
            self.assertTrue((ROOT / fault["file"]).is_file(), fault["id"])


class HistoryTest(unittest.TestCase):
    """The history rule (plan 9.4.8j) on a throw-away git repository: a commit that changes
    an existing fault's replacement text must name the fault."""

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="mutants-history-")
        self.root = Path(self.temporary.name)
        (self.root / "src").mkdir()
        (self.root / "src/word.txt").write_text("alpha\nbeta\n")
        (self.root / "check.sh").write_text(CHECK)
        self.git("init", "-q", "-b", "main")
        self.git("config", "user.email", "test@example.invalid")
        self.git("config", "user.name", "test")
        self.commit(CAUGHT, "the list")
        self.git("checkout", "-q", "-b", "work")

    def tearDown(self):
        self.temporary.cleanup()

    def git(self, *args):
        mutants.subprocess.run(["git", "-C", str(self.root), *args], check=True,
                               capture_output=True)

    def commit(self, text, message):
        (self.root / "tests").mkdir(exist_ok=True)
        (self.root / mutants.DEFAULT_LIST).parent.mkdir(parents=True, exist_ok=True)
        (self.root / mutants.DEFAULT_LIST).write_text(text)
        self.git("add", "-A")
        self.git("commit", "-q", "-m", message)

    def check(self, *options):
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            status = mutants.main(["--root", str(self.root), *options])
        return status, output.getvalue()

    def test_an_unnamed_replacement_fails(self):
        self.commit(CAUGHT.replace("gamma", "epsilon"), "rewrite a fault quietly")
        for option in ("--history", "--check"):
            status, output = self.check(option)
            self.assertEqual(status, 1, output)
            self.assertRegex(output, r"(?m)^REPLACED UNNAMED +drops-alpha +commit [0-9a-f]+ ")

    def test_a_named_replacement_passes(self):
        self.commit(CAUGHT.replace("gamma", "epsilon"), "Re-target drops-alpha at epsilon")
        self.assertEqual(self.check("--history")[0], 0)
        self.assertEqual(self.check("--check")[0], 0)

    def test_a_name_inside_another_id_does_not_count(self):
        self.commit(CAUGHT.replace("gamma", "epsilon"), "Re-target drops-alpha-two")
        self.assertEqual(self.check("--history")[0], 1)

    def test_reason_and_new_faults_are_free(self):
        changed = CAUGHT.replace("planted for the runner test", "another reason")
        self.commit(changed + entry("new-one", "beta", "delta"), "add a fault, reword one")
        self.assertEqual(self.check("--history")[0], 0)

    def test_an_unnamed_retarget_fails(self):
        # Review reuse-out-2 L2: changing a fault's old text or its file is a change too.
        self.commit(CAUGHT.replace("old = '''alpha'''", "old = '''beta'''"), "retarget quietly")
        self.assertEqual(self.check("--history")[0], 1)
        self.commit(CAUGHT.replace('file = "src/word.txt"', 'file = "src/other.txt"'), "move it")
        status, output = self.check("--history")
        self.assertEqual(status, 1, output)
        self.assertEqual(output.count("REPLACED UNNAMED"), 2, output)

    def test_a_commit_before_the_rule_is_held_to_new_only(self):
        # A commit whose own scripts/mutants.py lacks RETARGET_RULE is judged as it was then.
        (self.root / "scripts").mkdir(exist_ok=True)
        (self.root / "scripts/mutants.py").write_text("# the older rule\n")
        self.commit(CAUGHT.replace("old = '''alpha'''", "old = '''beta'''"), "retarget quietly")
        self.assertEqual(self.check("--history")[0], 0)
        self.commit(CAUGHT.replace("gamma", "epsilon"), "rewrite quietly")
        self.assertEqual(self.check("--history")[0], 1)

    def test_a_named_retarget_passes(self):
        self.commit(CAUGHT.replace("old = '''alpha'''", "old = '''beta'''"), "Re-target drops-alpha")
        self.assertEqual(self.check("--history")[0], 0)

    def test_a_broken_list_hides_nothing(self):
        # Review reuse-out-2 L2: a commit that breaks the list and changes a fault, then one
        # that repairs it, still needs the name; it is compared with the last list that parsed.
        changed = CAUGHT.replace("gamma", "epsilon")
        self.commit(changed + "[[fault]\nid = broken\n", "break the list")
        self.commit(changed, "repair the list")
        status, output = self.check("--history")
        self.assertEqual(status, 1, output)
        self.assertRegex(output, r"(?m)^REPLACED UNNAMED +drops-alpha +commit [0-9a-f]+ ")
        self.commit(CAUGHT.replace("gamma", "zeta"), "Re-target drops-alpha at zeta")
        self.assertEqual(self.check("--history")[0], 1)

    def test_only_the_branch_is_read(self):
        self.commit(CAUGHT.replace("gamma", "epsilon"), "Re-target drops-alpha")
        self.git("checkout", "-q", "main")
        self.commit(CAUGHT.replace("gamma", "zeta"), "a quiet change on main itself")
        self.assertEqual(self.check("--history")[0], 0)
        self.assertEqual(self.check("--history", "--base", "HEAD~1")[0], 1)

    def test_a_merge_counts_only_new_text(self):
        self.commit(CAUGHT.replace("gamma", "epsilon"), "Re-target drops-alpha")
        self.git("checkout", "-q", "main")
        self.commit(CAUGHT + entry("on-main", "beta", "delta"), "add a fault on main")
        self.git("checkout", "-q", "work")
        self.git("merge", "-q", "--no-edit", "main")
        self.assertEqual(self.check("--history")[0], 0)

    def commit_d(self, name, text, message):
        folder = self.root / Path(mutants.DEFAULT_LIST).parent / mutants.FAULTS_DIR
        folder.mkdir(parents=True, exist_ok=True)
        (folder / f"{name}.toml").write_text(text)
        self.git("add", "-A")
        self.git("commit", "-q", "-m", message)

    def test_history_follows_faults_d(self):
        # A fault moved unchanged into faults.d is no change; one changed there needs its name.
        (self.root / mutants.DEFAULT_LIST).write_text(SURVIVOR)
        self.commit_d("tactic", CAUGHT, "move a fault into faults.d")
        self.assertEqual(self.check("--history")[0], 0)
        self.commit_d("tactic", CAUGHT.replace("gamma", "epsilon"), "rewrite it quietly")
        status, output = self.check("--history")
        self.assertEqual(status, 1, output)
        self.assertRegex(output, r"(?m)^REPLACED UNNAMED +drops-alpha +commit [0-9a-f]+ ")

    def test_no_repository_passes(self):
        self.git("checkout", "-q", "main")
        status, output = self.check("--history", "--base", "no-such-branch")
        self.assertEqual(status, 0, output)


if __name__ == "__main__":
    os.chdir(ROOT)
    unittest.main(verbosity=1)
