#!/usr/bin/env python3
"""Tests of scripts/check-duplicates.py on throw-away source trees: tokenizing, alpha-renaming of file-local
words, the length threshold, cross-file and within-file groups, the ratchet, and a check of today's tree."""
import importlib.util
import json
import pathlib
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("cd", ROOT / "scripts/check-duplicates.py")
cd = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cd)

BODY = "dup over ok? if nip over swap execute else drop then"       # 11 tokens
LONG = ": %s ( x -- x ) \\ comment ( inner ) \n  " + BODY + " ;\n"


def groups(files):
    with tempfile.TemporaryDirectory() as tmp:
        for name, text in files.items():
            path = pathlib.Path(tmp) / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        return cd.groups(pathlib.Path(tmp))


class Tokens(unittest.TestCase):
    def test_comments_and_strings(self):
        toks = [t for t, _ in cd.tokens('a \\ line ( x )\n( b\n c ) d s" x y" e ." p q" .( r ) f')]
        self.assertEqual(toks, ["a", "d", "s\" x y", "e", ".\" p q", ".( r ", "f"])

    def test_string_is_one_token(self):
        toks = [t for t, _ in cd.tokens('x s" a b c" y')]
        self.assertEqual(toks, ["x", "s\" a b c", "y"])

    def test_lines_are_tracked(self):
        self.assertEqual(cd.tokens("a\n\\ c\nb ( x\ny ) c"), [("a", 1), ("b", 3), ("c", 4)])

    def test_case_is_folded(self):
        self.assertEqual([t for t, _ in cd.tokens("DUP Swap")], ["dup", "swap"])


class Normal(unittest.TestCase):
    def test_local_words_become_positional_placeholders(self):
        self.assertEqual(cd.normal_form(["in-a", "dup", "in-b", "in-a"], {"in-a", "in-b"}),
                         ["#0", "dup", "#1", "#0"])

    def test_char_literal_is_kept(self):
        self.assertEqual(cd.normal_form(["[char]", "x", "x"], {"x"}), ["[char]", "x", "#0"])


class Groups(unittest.TestCase):
    def test_renamed_copy_in_another_file_matches(self):
        files = {"src/a.fs": ": in-h swap ;\n" + LONG % "in-x" + "",
                 "src/b.fs": LONG % "ib-x"}
        found = groups(files)
        self.assertEqual(len(found), 1)
        group = next(iter(found.values()))
        self.assertEqual([m[2] for m in group["members"]], ["in-x", "ib-x"])
        self.assertTrue(cd.spans_files(group))

    def test_helper_names_are_alpha_renamed(self):
        body = ": %s %s over %s if nip %s swap execute else drop then ;\n"
        a = ": ha ; : hb ; : ia ; " + body % ("fa", "ha", "hb", "ha")
        b = ": xa ; : xb ; : ib ; " + body % ("fb", "xa", "xb", "xa")
        self.assertEqual(len(groups({"src/a.fs": a, "src/b.fs": b})), 1)

    def test_different_structure_does_not_match(self):
        body = ": %s %s over %s if nip %s swap execute else drop then ;\n"
        a = ": ha ; : hb ; " + body % ("fa", "ha", "hb", "ha")
        b = ": xa ; : xb ; " + body % ("fb", "xa", "xb", "xb")
        self.assertEqual(groups({"src/a.fs": a, "src/b.fs": b}), {})

    def test_short_bodies_are_ignored(self):
        text = ": a ok? ;\n: b ok? ;\n: c 1 2 3 4 5 6 7 ;\n: d 1 2 3 4 5 6 7 ;\n"
        self.assertEqual(groups({"src/a.fs": text}), {})

    def test_threshold_is_eight_tokens(self):
        eight = " ".join(["dup"] * 8)
        seven = " ".join(["dup"] * 7)
        self.assertEqual(len(groups({"src/a.fs": f": a {eight} ;\n: b {eight} ;\n"})), 1)
        self.assertEqual(groups({"src/a.fs": f": a {seven} ;\n: b {seven} ;\n"}), {})

    def test_within_a_file_group(self):
        found = groups({"src/a.fs": LONG % "one" + LONG % "two"})
        group = next(iter(found.values()))
        self.assertFalse(cd.spans_files(group))
        self.assertEqual([m[1] for m in group["members"]], [1, 3])

    def test_lib_words_stay_literal(self):
        lib = ": ok? 0= ;\n: ok-with " + BODY + " ;\n"
        user = ": aux-then " + BODY.replace("ok?", "ok?") + " ;\n"
        self.assertEqual(len(groups({"src/lib/o.fs": lib, "src/b.fs": user})), 1)

    def test_comment_difference_does_not_matter(self):
        a = ": a ( x -- y ) " + BODY + " ;\n"
        b = ": b \\ other\n " + BODY + " ;\n"
        self.assertEqual(len(groups({"src/a.fs": a, "src/b.fs": b})), 1)


class Ratchet(unittest.TestCase):
    def group(self, copies, key="k1"):
        return {key: {"tokens": 9, "members": [("src/f%d.fs" % i, i, "w") for i in range(copies)]}}

    def test_equal_and_smaller_pass(self):
        base = cd.baseline_of(self.group(3))
        self.assertEqual(cd.ratchet(self.group(3), base), [])
        self.assertEqual(cd.ratchet(self.group(2), base), [])
        self.assertEqual(cd.ratchet({}, base), [])

    def test_new_group_fails_with_locations(self):
        problems = cd.ratchet(self.group(2, "new"), cd.baseline_of(self.group(2)))
        self.assertIn("new duplicate group", problems[0])
        self.assertIn("src/f1.fs:1 w", problems[2])

    def test_grown_group_fails(self):
        problems = cd.ratchet(self.group(3), cd.baseline_of(self.group(2)))
        self.assertIn("grew from 2", problems[0])


class Main(unittest.TestCase):
    def test_update_then_check_then_new_copy(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            (root / "src").mkdir()
            (root / "tests").mkdir()
            (root / "src/a.fs").write_text(LONG % "x")
            (root / "src/b.fs").write_text(LONG % "y")
            self.assertEqual(cd.main(["--update-baseline", tmp]), 0)
            self.assertEqual(len(json.loads((root / "tests/duplicates-baseline.json").read_text())), 1)
            self.assertEqual(cd.main([tmp]), 0)
            (root / "src/c.fs").write_text(LONG % "z")
            self.assertEqual(cd.main([tmp]), 1)
            self.assertEqual(cd.main(["--report", "--update-baseline", tmp]), 0)
            self.assertEqual(cd.main([tmp]), 0)

    def test_missing_baseline_fails_on_a_duplicate(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            (root / "src").mkdir()
            (root / "src/a.fs").write_text(LONG % "x" + LONG % "y")
            self.assertEqual(cd.main([tmp]), 1)


class Tree(unittest.TestCase):
    def test_todays_tree_holds_its_baseline(self):
        self.assertEqual(cd.main([]), 0)


if __name__ == "__main__":
    unittest.main()
