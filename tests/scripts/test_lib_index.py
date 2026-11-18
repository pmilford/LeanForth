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

    def test_previous_wordlist_is_public(self):
        # store.fs's form: public words go into the wordlist current at load (dup set-current).
        text = "lf-lib-private module-open\ndup set-current\n: open ( -- ) ;\n" \
               "lf-lib-private set-current\n: inner ( -- ) ;\ndup set-current\n: last ( -- ) ;\n"
        self.assertEqual([w[0] for w in words(text)], ["open", "last"])

    def test_structures_and_their_fields(self):
        # Structure sizes and fields are public words too (review lib-tidy, finding 4), at any
        # indentation, two on a line, and private between lf-lib-private and the next public part.
        text = ("\\ A reader record.\nbegin-structure /reader\n  field: reader-fid  \\ the file\n"
                "  1 cells +field reader-a 8 chars +field reader-b\n  cfield: reader-c\nend-structure\n"
                "lf-lib-private set-current\nbegin-structure /hidden\n  field: hidden-field\n"
                "end-structure\nlf-lib set-current\n")
        found = words(text)
        self.assertEqual([w[0] for w in found],
                         ["/reader", "reader-fid", "reader-a", "reader-b", "reader-c"])
        self.assertEqual(found[0][2], "A reader record.")
        self.assertEqual(found[1][2], "the file")

    def test_words_defined_where_the_host_lacks_them(self):
        # portability.fs's form: the name after [undefined], with the stack comment of its
        # definition on the line; a multi-line block is read from its definition lines; a
        # name defined twice (two branches) is listed once.
        text = ("[undefined] -rot [if] : -rot ( a b c -- c a b ) rot rot ; [then]\n"
                "[undefined] +field [if] : +field ( n1 n2 \"name\" -- n3 ) create over , + does> @ + ; [then]\n"
                "[undefined] begin-structure [if]\n: begin-structure ( \"name\" -- addr 0 ) ;\n[then]\n"
                "[undefined] max-n [if] -1 1 rshift constant max-n [then]\n"
                "[defined] scan [if] : fast ( -- ) ; [else] [then]\n: fast ( -- ) ;\n")
        found = words(text)
        self.assertEqual([w[0] for w in found], ["-rot", "+field", "begin-structure", "max-n", "fast"])
        self.assertEqual(found[0][1], "( a b c -- c a b )")

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

    # Files whose header has no interface list (LIBRARY_WORDS.md lists their words); this set
    # may only shrink.
    NO_LIST = {"lib.fs", "module.fs", "node.fs", "outcome.fs", "portability.fs", "runs.fs",
               "store-columns.fs", "store.fs", "task.fs", "walk.fs"}

    def test_header_interfaces_name_every_public_word(self):
        # Review lib-tidy, note 8: htab.fs's list left out its public fields.
        for path in sorted((ROOT / "src/lib").glob("*.fs")):
            with self.subTest(file=path.name):
                listed = li.interface(path)
                if path.name in self.NO_LIST:
                    self.assertIsNone(listed, "has a list now: take it off NO_LIST")
                    continue
                self.assertIsNotNone(listed, "no `\\ Interface:` list in the header")
                missing = [w[0] for w in li.words(path) if w[0] not in listed]
                self.assertEqual(missing, [], "public words the header's list leaves out")

    def test_interface_reads_the_paragraph(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = pathlib.Path(tmp) / "x.fs"
            path.write_text("\\ Head.\n\\ Interface: a b,\n\\ c. Then prose\n\\\n\\ d\n: a ;\n")
            self.assertTrue({"a", "b", "c", "Then", "prose"} <= li.interface(path))
            self.assertNotIn("d", li.interface(path))
            path.write_text("\\ Head.\n: a ;\n")
            self.assertIsNone(li.interface(path))


if __name__ == "__main__":
    unittest.main()
