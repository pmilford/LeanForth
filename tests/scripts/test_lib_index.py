#!/usr/bin/env python3
"""Tests of scripts/lib-index.py on throw-away trees: public words with stack comments and descriptions, private
sections left out, staleness detection and regeneration, and a check that today's index is current."""
import importlib.util
import pathlib
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("li", ROOT / "scripts/lib-index.py")
li = importlib.util.module_from_spec(spec)
spec.loader.exec_module(li)

SOURCE = """\\ header

\\ Adds one.
\\ More text.
: inc ( n -- n+1 ) 1+ ;
: bare 1+ ; \\ trailing note
8 constant limit
lf-lib-private module-open
\\ hidden
: helper ( -- ) ;
lf-lib set-current
: shown ( a -- ) drop ;
lf-lib-private set-current
: hidden-too ( -- ) ;
lf-lib set-current
variable cell-count
  : indented-not-a-definition ;
module-close
: after-close ( -- ) ;
"""


def words(text):
    with tempfile.TemporaryDirectory() as tmp:
        path = pathlib.Path(tmp) / "x.fs"
        path.write_text(text)
        return li.words(path)


class Words(unittest.TestCase):
    def test_public_words_in_order(self):
        names = [w[0] for w in words(SOURCE)]
        self.assertEqual(names, ["inc", "bare", "limit", "shown", "cell-count", "after-close"])

    def test_stack_comment_and_description(self):
        found = {w[0]: w for w in words(SOURCE)}
        self.assertEqual(found["inc"], ("inc", "( n -- n+1 )", "Adds one."))
        self.assertEqual(found["bare"], ("bare", "", "trailing note"))
        self.assertEqual(found["limit"], ("limit", "", ""))

    def test_private_sections_are_left_out(self):
        names = [w[0] for w in words(SOURCE)]
        self.assertNotIn("helper", names)
        self.assertNotIn("hidden-too", names)

    def test_file_without_modules_is_all_public(self):
        self.assertEqual([w[0] for w in words(": a ;\n: b ;\n")], ["a", "b"])

    def test_long_description_is_cut(self):
        self.assertEqual(len(words("\\ " + "x" * 300 + "\n: a ;\n")[0][2]), li.MAX_DESCRIPTION)


class Staleness(unittest.TestCase):
    def test_write_check_edit_check(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            (root / "src/lib").mkdir(parents=True)
            (root / "docs/development").mkdir(parents=True)
            (root / "src/lib/a.fs").write_text(": a ( -- ) ;\n")
            self.assertEqual(li.main([tmp]), 1)           # missing
            self.assertEqual(li.main(["--write", tmp]), 0)
            self.assertEqual(li.main([tmp]), 0)
            (root / "src/lib/a.fs").write_text(": a ( -- ) ;\n: b ( -- ) ;\n")
            self.assertEqual(li.main([tmp]), 1)           # a word added: stale
            self.assertEqual(li.main(["--write", tmp]), 0)
            self.assertEqual(li.main([tmp]), 0)
            self.assertIn("`b`", (root / li.OUTPUT).read_text())


class Tree(unittest.TestCase):
    def test_todays_index_is_current(self):
        self.assertEqual(li.main([]), 0)


if __name__ == "__main__":
    unittest.main()
