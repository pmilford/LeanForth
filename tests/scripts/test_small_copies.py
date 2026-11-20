#!/usr/bin/env python3
"""Tests of `scripts/check-duplicates.py --new-words` on a throw-away git repository: a short word added that
copies an old one, a changed body, an excused word, a six-token body left to the ratchet, glue bodies,
data words of two files that only look alike, and a branch with nothing ahead of its base."""
import contextlib
import importlib.util
import io
import pathlib
import subprocess
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("cd", ROOT / "scripts/check-duplicates.py")
cd = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cd)

OLD = ": old-name? ( n -- f ) name-prefix@ s\" Nat\" name-top? ;\n"
LONG = ": long-a ( x -- y ) dup over swap rot nip drop ;\n"           # six tokens: the ratchet's job


class Repo:
    """A repository with src/a.fs on main; branch() starts a branch, write() and commit() change it."""

    def __init__(self, tmp):
        self.root = pathlib.Path(tmp)
        for cmd in (["init", "-q", "-b", "main"], ["config", "user.email", "t@t"], ["config", "user.name", "t"]):
            self.git(*cmd)
        self.write("src/a.fs", OLD + LONG + "variable tab-a\n: look-a ( i -- x ) cells tab-a + @ ;\n")
        self.commit("base")
        self.git("checkout", "-q", "-b", "work")

    def git(self, *args):
        subprocess.run(["git", "-C", str(self.root), *args], check=True, capture_output=True)

    def write(self, rel, text):
        path = self.root / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def commit(self, message="work"):
        self.git("add", "-A")
        self.git("commit", "-q", "-m", message)

    def run(self):
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            code = cd.new_words(self.root, "main")
        return code, out.getvalue()


class NewWords(unittest.TestCase):
    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self._tmp.cleanup)
        self.repo = Repo(self._tmp.name)

    def test_nothing_ahead_of_base_passes(self):
        code, text = self.repo.run()
        self.assertEqual(code, 0, text)
        self.assertIn("none", text)

    def test_added_copy_is_reported_with_both_places(self):
        self.repo.write("src/b.fs", ": new-name? ( n -- f ) name-prefix@ s\" Nat\" name-top? ;\n")
        self.repo.commit()
        code, text = self.repo.run()
        self.assertEqual(code, 1)
        self.assertIn("src/b.fs:1: new-name? ( n -- f ) has the body of src/a.fs:1 old-name?: "
                      "name-prefix@ s\" Nat name-top?", text)

    def test_copy_in_the_same_file_is_reported(self):
        self.repo.write("src/a.fs", OLD + LONG + ": twin? ( n -- f ) name-prefix@ s\" Nat\" name-top? ;\n")
        self.repo.commit()
        code, text = self.repo.run()
        self.assertEqual(code, 1)
        self.assertIn("src/a.fs:3: twin?", text)

    def test_changed_body_counts_as_added(self):
        self.repo.write("src/b.fs", ": mine ( n -- f ) name-prefix@ 0= ;\n")
        self.repo.commit("first")
        self.assertEqual(self.repo.run()[0], 0)
        self.repo.git("checkout", "-q", "main")
        self.repo.git("merge", "-q", "work")
        self.repo.git("checkout", "-q", "-b", "next")
        self.repo.write("src/b.fs", ": mine ( n -- f ) name-prefix@ s\" Nat\" name-top? ;\n")
        self.repo.commit("change")
        code, text = self.repo.run()
        self.assertEqual(code, 1)
        self.assertIn("src/b.fs:1: mine", text)

    def test_old_words_are_not_reported(self):
        self.repo.write("src/b.fs", ": other ( n -- f ) name-prefix@ s\" Nat\" name-top? ;\n")
        self.repo.commit("copy lands")
        self.repo.git("checkout", "-q", "main")
        self.repo.git("merge", "-q", "work")
        self.repo.git("checkout", "-q", "-b", "next")
        self.repo.write("src/c.fs", ": unrelated ( n -- f ) dup 0= ;\n")
        self.repo.commit("next")
        self.assertEqual(self.repo.run()[0], 0)

    def test_excused_word_passes_and_is_counted(self):
        self.repo.write("src/b.fs", ": new-name? ( n -- f ) name-prefix@ s\" Nat\" name-top? ;\n")
        self.repo.write("tests/small-copies-allowed.txt", "# header\nsrc/b.fs:new-name?  a wrapper kept for the layer\n")
        self.repo.commit()
        code, text = self.repo.run()
        self.assertEqual(code, 0, text)
        self.assertIn("1 excused", text)

    def test_excuse_without_reason_fails(self):
        self.repo.write("src/b.fs", ": new-name? ( n -- f ) name-prefix@ s\" Nat\" name-top? ;\n")
        self.repo.write("tests/small-copies-allowed.txt", "src/b.fs:new-name?\n")
        self.repo.commit()
        code, text = self.repo.run()
        self.assertEqual(code, 1)
        self.assertIn("has no reason", text)

    def test_six_token_body_is_left_to_the_ratchet(self):
        self.repo.write("src/b.fs", ": long-b ( x -- y ) dup over swap rot nip drop ;\n")
        self.repo.commit()
        self.assertEqual(self.repo.run()[0], 0)

    def test_single_token_and_glue_bodies_are_not_reported(self):
        self.repo.write("src/b.fs", ": a1 ( x -- y ) 1+ ;\n: a2 ( x -- y ) 8 + ;\n: a3 ( x -- y ) cell+ @ ;\n"
                        ": a4 ( x -- y ) 1+ ;\n: a5 ( x -- y ) swap @ ;\n")
        self.repo.write("src/c.fs", ": c3 ( x -- y ) cell+ @ ;\n: c5 ( x -- y ) swap @ ;\n")
        self.repo.commit()
        self.assertEqual(self.repo.run()[0], 0)

    def test_tables_of_two_files_are_different_words(self):
        self.repo.write("src/b.fs", "variable tab-b\n: look-b ( i -- x ) cells tab-b + @ ;\n")
        self.repo.commit()
        self.assertEqual(self.repo.run()[0], 0)

    def test_calls_of_renamed_helpers_are_the_same_copy(self):
        self.repo.write("src/b.fs", ": h1 ( x -- y ) old-name? 0= ;\n: h2 ( x -- y ) old-name? 0= ;\n")
        self.repo.commit()
        code, text = self.repo.run()
        self.assertEqual(code, 1)
        self.assertIn("src/b.fs:2: h2", text)
        self.assertIn("src/b.fs:1: h1", text)

    def test_head_ref_is_read_from_git_not_the_work_tree(self):
        self.repo.write("src/b.fs", ": new-name? ( n -- f ) name-prefix@ s\" Nat\" name-top? ;\n")
        self.repo.commit()
        self.repo.git("checkout", "-q", "main")
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            code = cd.new_words(self.repo.root, "main", "work")
        self.assertEqual(code, 1, out.getvalue())
        self.assertIn("src/b.fs:1: new-name?", out.getvalue())


class Cli(unittest.TestCase):
    def test_main_runs_the_check_on_this_repository(self):
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            code = cd.main(["--new-words", "--base", "HEAD"])
        self.assertEqual(code, 0, out.getvalue())

    def test_allowed_file_has_a_header_and_every_entry_a_reason(self):
        lines = (ROOT / cd.ALLOWED).read_text().splitlines()
        self.assertTrue(lines[0].startswith("#"))
        for line in lines:
            if line.strip() and not line.startswith("#"):
                self.assertEqual(len(line.split(None, 1)), 2, line)


if __name__ == "__main__":
    unittest.main()
