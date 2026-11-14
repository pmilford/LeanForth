#!/usr/bin/env python3
"""Tests of scripts/check-duplicates.py on throw-away source trees: tokenizing, alpha-renaming of file-local
words (every defining word), the copy form (calls of another file's helpers, roles, constants by value), the
length threshold, cross-file and within-file groups, the ratchet with its reasons, and a check of today's tree."""
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
        a = ": ha 1 ; : hb 2 ; " + body % ("fa", "ha", "hb", "ha")
        b = ": xa 1 ; : xb 2 ; " + body % ("fb", "xa", "xb", "xb")
        self.assertEqual(groups({"src/a.fs": a, "src/b.fs": b}), {})

    def test_short_bodies_are_ignored(self):
        text = ": a ok? ;\n: b ok? ;\n: c 1 2 3 4 5 ;\n: d 1 2 3 4 5 ;\n"
        self.assertEqual(groups({"src/a.fs": text}), {})

    def test_threshold_is_six_tokens(self):
        six = " ".join(["dup"] * 6)
        five = " ".join(["dup"] * 5)
        self.assertEqual(cd.MIN_TOKENS, 6)
        self.assertEqual(len(groups({"src/a.fs": f": a {six} ;\n: b {six} ;\n"})), 1)
        self.assertEqual(groups({"src/a.fs": f": a {five} ;\n: b {five} ;\n"}), {})

    def test_every_defining_word_names_a_local(self):
        for definer in ("+field", "field:", "context-slab:", "begin-structure", "store:"):
            a = f"1 {definer} in-s\n: in-x in-s @ over + swap execute drop ;\n"
            b = f"1 {definer} ib-s\n: ib-x ib-s @ over + swap execute drop ;\n"
            with self.subTest(definer=definer):
                self.assertEqual(len(groups({"src/a.fs": a, "src/b.fs": b})), 1)

    def test_locals_and_quotations_define_nothing(self):
        self.assertFalse(cd.definer("{:"))
        self.assertFalse(cd.definer("[:"))
        self.assertFalse(cd.definer(":"))
        self.assertTrue(cd.definer("walk2:"))

    def test_a_string_ending_in_a_colon_defines_nothing(self):
        """Review reuse-out-2 M2: `." fuel:"` is one token ending in `:`; the word after it is no definition."""
        for text in ('." fuel:"', 's" key:"', 'c" x:"', 'abort" bad:"', '.( note:)'):
            with self.subTest(text=text):
                token = cd.tokens(text)[0][0]
                self.assertFalse(cd.definer(token), token)
        a = ': in-x ." fuel:" cr over + swap execute drop ;\n'
        b = ': ib-y cr over + swap execute drop ;\n'
        _, names = cd.definitions_of_text(a)
        self.assertEqual(names, {"in-x"})
        found = groups({"src/a.fs": a + ": in-z cr over + swap execute drop ;\n", "src/b.fs": b})
        self.assertEqual([sorted(m[2] for m in g["members"]) for g in found.values()], [["ib-y", "in-z"]])

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


class Copies(unittest.TestCase):
    """The copy form: a call of a colon word defined outside lib/ is replaced by that word's role."""
    HELPERS = ": in-h ( x -- y ) dup 1+ * ;\n: in-g ( x -- y ) 2 lshift ;\n"
    USER = ": %s ( x -- y ) dup in-h swap in-g + over - abs ;\n"

    def test_a_copy_calling_the_other_files_helpers(self):
        found = groups({"src/a.fs": self.HELPERS + self.USER % "in-x", "src/b.fs": self.USER % "ib-x"})
        self.assertEqual(len(found), 1)
        group = next(iter(found.values()))
        self.assertEqual(group["kind"], "copy")
        self.assertEqual([m[2] for m in group["members"]], ["in-x", "ib-x"])

    def test_a_copy_with_renamed_copies_of_the_helpers(self):
        b = self.HELPERS.replace("in-", "ib-") + (self.USER % "ib-x").replace("in-", "ib-")
        found = groups({"src/a.fs": self.HELPERS + self.USER % "in-x", "src/b.fs": b})
        self.assertEqual(len(found), 1)
        self.assertEqual(next(iter(found.values()))["kind"], "shape")

    def test_helpers_that_differ_do_not_match(self):
        b = ": ib-h ( x -- y ) dup 1- * ;\n" + (self.USER % "ib-x").replace("in-h", "ib-h")
        self.assertEqual(groups({"src/a.fs": self.HELPERS + self.USER % "in-x", "src/b.fs": b}), {})

    def test_constants_keep_their_value(self):
        a = "1 constant in-k\n: in-make in-k + ;\n: in-x in-make dup * over + swap ;\n"
        b = "2 constant ib-k\n: ib-make ib-k + ;\n: ib-x ib-make dup * over + swap ;\n"
        c = "1 constant ic-k\n: ic-make ic-k + ;\n: ic-x ic-make dup * over + swap ;\n"
        found = groups({"src/a.fs": a, "src/b.fs": b, "src/c.fs": c})
        kinds = sorted((g["kind"], sorted(m[2] for m in g["members"])) for g in found.values())
        self.assertEqual(kinds, [("shape", ["ib-x", "ic-x", "in-x"])])
        with tempfile.TemporaryDirectory() as tmp:
            for name, text in (("a", a), ("b", b), ("c", c)):
                (pathlib.Path(tmp) / "src").mkdir(exist_ok=True)
                (pathlib.Path(tmp) / "src" / (name + ".fs")).write_text(text)
            copy = {m[2]: cform for m, _, cform in cd.Tree(pathlib.Path(tmp)).forms()}
        self.assertEqual(copy["in-x"], copy["ic-x"])
        self.assertNotEqual(copy["in-x"], copy["ib-x"])
        self.assertEqual(copy["in-make"], ["=1", "+"])

    def test_lib_words_have_no_role(self):
        lib = ": in-h dup 1+ * ;\n"
        a = ": in-h dup 1+ * ;\n: in-x in-h over + swap execute drop ;\n"
        b = ": ib-x in-h over + swap execute drop ;\n"
        found = groups({"src/lib/l.fs": lib, "src/a.fs": a, "src/b.fs": b})
        self.assertEqual([g["kind"] for g in found.values()], ["shape"])

    def test_an_ambiguous_name_stays_literal(self):
        a = ": h 1 ;\n"
        b = ": h 2 ;\n"
        c = ": x h over + swap execute drop ;\n: y h over + swap execute drop ;\n"
        found = groups({"src/a.fs": a, "src/b.fs": b, "src/c.fs": c})
        self.assertEqual(len(found), 1)


class Ratchet(unittest.TestCase):
    def group(self, copies, key="k1"):
        return {key: {"tokens": 9, "kind": "shape",
                      "members": [("src/f%d.fs" % i, i, "w") for i in range(copies)]}}

    def based(self, copies, reason="accepted: test"):
        base = cd.baseline_of(self.group(copies))
        for entry in base.values():
            entry["reason"] = reason
        return base

    def test_equal_and_smaller_pass(self):
        base = self.based(3)
        self.assertEqual(cd.ratchet(self.group(3), base), [])
        self.assertEqual(cd.ratchet(self.group(2), base), [])
        self.assertEqual(cd.ratchet({}, base), [])

    def test_new_group_fails_with_locations(self):
        problems = cd.ratchet(self.group(2, "new"), self.based(2))
        self.assertIn("new duplicate group", problems[0])
        self.assertIn("src/f1.fs:1 w", problems[2])

    def test_grown_group_fails(self):
        problems = cd.ratchet(self.group(3), self.based(2))
        self.assertIn("members its record does not list", problems[0])
        self.assertEqual(problems[1:], ["    src/f2.fs:2 w"])

    def test_a_copy_moved_elsewhere_fails(self):
        """Review reuse-out-2 L1: one copy removed and another added keeps the count but not the members."""
        moved = {"k1": {"tokens": 9, "kind": "shape",
                        "members": [("src/f0.fs", 0, "w"), ("src/g.fs", 7, "w")]}}
        problems = cd.ratchet(moved, self.based(2))
        self.assertIn("members its record does not list", problems[0])
        self.assertEqual(problems[1:], ["    src/g.fs:7 w"])
        renamed = {"k1": {"tokens": 9, "kind": "shape",
                          "members": [("src/f0.fs", 0, "w"), ("src/f1.fs", 1, "v")]}}
        self.assertEqual(len(cd.ratchet(renamed, self.based(2))), 2)

    def test_a_group_without_a_reason_fails(self):
        problems = cd.ratchet(self.group(2), cd.baseline_of(self.group(2)))
        self.assertIn("group without a reason", problems[0])

    def test_every_reason_kind_passes_and_others_fail(self):
        for reason in ("false positive: x", "family, table-driven later: 9.4.8k follow-up 8, x", "accepted: x",
                       "planned: 9.4.8k", "planned: FE1i-4 the instance root", "planned: S2 slice"):
            with self.subTest(reason=reason):
                self.assertEqual(cd.ratchet(self.group(2), self.based(2, reason)), [])
        for reason in ("", "fine", "todo: later"):
            with self.subTest(reason=reason):
                problems = cd.ratchet(self.group(2), self.based(2, reason))
                self.assertEqual(len(problems), 1)
                self.assertIn("group without a reason", problems[0])

    def test_a_planned_reason_names_a_plan_row(self):
        """Review reuse-out-2 B2: `planned:` and `family…:` reasons carry a plan row id, as PLAN_ID reads one."""
        for reason in ("family, table-driven later: x", "planned: a later pass", "planned: version 9"):
            with self.subTest(reason=reason):
                problems = cd.ratchet(self.group(2), self.based(2, reason))
                self.assertEqual(len(problems), 1)
                self.assertIn("without a plan row id", problems[0])
        self.assertEqual(cd.PLAN_ID.pattern, cd.plan_id().pattern)

    def test_update_keeps_reasons_by_key_and_by_members(self):
        old = self.based(2, "accepted: kept")
        self.assertEqual(cd.baseline_of(self.group(2), old)["k1"]["reason"], "accepted: kept")
        moved = cd.baseline_of(self.group(2, "k2"), old)
        self.assertEqual(moved["k2"]["reason"], "accepted: kept")
        self.assertNotIn("reason", cd.baseline_of(self.group(3, "k3"), old)["k3"])


class Main(unittest.TestCase):
    def test_update_then_check_then_new_copy(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            (root / "src").mkdir()
            (root / "tests").mkdir()
            (root / "src/a.fs").write_text(LONG % "x")
            (root / "src/b.fs").write_text(LONG % "y")
            path = root / "tests/duplicates-baseline.json"
            self.assertEqual(cd.main(["--update-baseline", tmp]), 0)
            self.assertEqual(len(json.loads(path.read_text())), 1)
            self.assertEqual(cd.main([tmp]), 1)                 # no reason yet
            self.give_reason(path, "accepted: a test")
            self.assertEqual(cd.main([tmp]), 0)
            (root / "src/c.fs").write_text(LONG % "z")
            self.assertEqual(cd.main([tmp]), 1)
            self.assertEqual(cd.main(["--report", "--counts", "--update-baseline", tmp]), 0)
            self.assertEqual(cd.main(["--report", "--counts", tmp]), 0)     # the same key keeps its reason
            other = LONG.replace("drop then", "nip then")
            (root / "src/c.fs").write_text(other % "z1" + other % "z2" + LONG % "z")
            self.assertEqual(cd.main(["--update-baseline", tmp]), 0)
            self.assertEqual(cd.main([tmp]), 1)                 # the new pair has no reason
            reasons = [v.get("reason") for v in json.loads(path.read_text()).values()]
            self.assertEqual(sorted(map(str, reasons)), ["None", "accepted: a test"])

    def give_reason(self, path, reason):
        base = json.loads(path.read_text())
        next(iter(base.values()))["reason"] = reason
        path.write_text(json.dumps(base))

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
