#!/usr/bin/env python3
"""Tests of scripts/check-outcome-steps.py on throw-away source trees: steps of the right and wrong shape for each
chain, alternatives, defer, names without case, sites in comments and strings, what it cannot check, the exit
code, and a check of today's tree."""
import contextlib
import importlib.util
import io
import pathlib
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("cos", ROOT / "scripts/check-outcome-steps.py")
cos = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cos)


def run(files):
    """check() on a tree of src/ files: (wrong, unchecked, count)."""
    with tempfile.TemporaryDirectory() as tmp:
        for name, text in files.items():
            path = pathlib.Path(tmp) / "src" / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        return cos.check(pathlib.Path(tmp))


def one(defs, use):
    return run({"a.fs": defs + "\n: user ( -- r outcome )\n  " + use + " ;\n"})


class Shapes(unittest.TestCase):
    def test_right_steps_of_one_two_and_three_values_pass(self):
        defs = (": s1 ( x -- r outcome ) 0 ;\n: s2 ( x y -- r outcome ) 0 ;\n"
                ": s3 ( x y z -- r status ) 0 ;")
        uses = "1 0 ['] s1 ok-apply 1 2 0 ['] s2 ok-apply2 1 2 3 0 ['] s3 ok-apply3"
        self.assertEqual(one(defs, uses), ([], [], 3))

    def test_a_step_leaving_three_cells_is_wrong(self):
        wrong, unchecked, count = one(": ac-abstract ( e i type -- type body outcome ) 0 ;",
                                      "['] ac-abstract ok-apply3")
        self.assertEqual((len(wrong), unchecked, count), (1, [], 1))
        self.assertIn("a.fs:3: ac-abstract via ok-apply3", wrong[0])
        self.assertIn("leaves 3 cells", wrong[0])

    def test_a_step_taking_the_wrong_number_of_cells_is_wrong(self):
        wrong = one(": s ( x y -- r outcome ) 0 ;", "['] s ok-apply")[0]
        self.assertEqual(len(wrong), 1)
        self.assertIn("takes 2 cells, the chain passes 1", wrong[0])
        self.assertEqual(len(one(": s ( x -- r outcome ) 0 ;", "['] s ok-apply3")[0]), 1)

    def test_a_second_cell_that_is_no_outcome_is_wrong(self):
        wrong = one(": s ( x -- r flag ) 0 ;", "['] s ok-apply")[0]
        self.assertEqual(len(wrong), 1)
        self.assertIn("not an outcome", wrong[0])

    def test_each_alternative_is_counted(self):
        self.assertEqual(one(": s ( x -- r outcome | -1 outcome ) 0 ;", "['] s ok-apply")[0], [])
        self.assertEqual(len(one(": s ( x -- r outcome | outcome ) 0 ;", "['] s ok-apply")[0]), 1)

    def test_defer_names_and_case(self):
        self.assertEqual(one("defer Walk ( node -- type status )", "['] wALK ok-apply"), ([], [], 1))
        self.assertEqual(len(one("defer s ( node -- a b status )", "['] s ok-apply")[0]), 1)

    def test_a_site_across_lines_and_with_a_plain_tick(self):
        self.assertEqual(len(one(": s ( x y -- a b c ) 0 ;", "['] s\n  ok-apply2")[0]), 1)
        self.assertEqual(len(one(": s ( x y -- a b c ) 0 ;", "' s ok-apply2")[0]), 1)


class Text(unittest.TestCase):
    BAD = ": s ( x y z -- a b c ) 0 ;\n"

    def test_sites_in_comments_and_strings_are_not_counted(self):
        for use in ("\\ ['] s ok-apply3", "( ['] s ok-apply3 )", '.( [\'] s ok-apply3 )',
                    's" [\'] s ok-apply3"', 's\\" a\\" [\'] s ok-apply3 \\" b"', 'abort" [\'] s ok-apply3"'):
            with self.subTest(use=use):
                self.assertEqual(one(self.BAD, use), ([], [], 0))

    def test_a_char_paren_opens_no_comment(self):
        wrong, _, count = one(self.BAD, "[char] ( ['] s ok-apply3 [char] ) drop")
        self.assertEqual((len(wrong), count), (1, 1))

    def test_a_backslash_inside_a_word_is_no_comment(self):
        self.assertEqual(len(one(self.BAD, "a\\b ['] s ok-apply3")[0]), 1)


class NotChecked(unittest.TestCase):
    def test_no_definition_is_reported_not_failed(self):
        wrong, unchecked, count = one("", "['] elsewhere ok-apply")
        self.assertEqual((wrong, count), ([], 1))
        self.assertIn("not checked (no definition in src/)", unchecked[0])

    def test_uncountable_comments(self):
        for comment in ("( x ... -- r outcome )", "( x .. y -- r outcome )", "( x | y -- r outcome )",
                        "( [x] -- r outcome )", "( x r outcome )", ""):
            with self.subTest(comment=comment):
                wrong, unchecked, _ = one(": s " + comment + " 0 ;", "['] s ok-apply")
                self.assertEqual((wrong, len(unchecked)), ([], 1))
                self.assertIn("not checked", unchecked[0])

    def test_definitions_that_disagree_or_agree(self):
        files = {"a.fs": ": s ( x -- r outcome ) ;\n", "b.fs": ": s ( x -- a b c ) ;\n: u ['] s ok-apply ;\n"}
        wrong, unchecked, _ = run(files)
        self.assertEqual((wrong, len(unchecked)), ([], 1))
        self.assertIn("2 definitions disagree", unchecked[0])
        files["a.fs"] = ": s ( x -- a b ) ;\n"
        self.assertEqual(len(run(files)[0]), 1)


class Command(unittest.TestCase):
    def main(self, files):
        with tempfile.TemporaryDirectory() as tmp:
            for name, text in files.items():
                (pathlib.Path(tmp) / "src").mkdir(exist_ok=True)
                (pathlib.Path(tmp) / "src" / name).write_text(text)
            out = io.StringIO()
            with contextlib.redirect_stdout(out):
                code = cos.main(["check-outcome-steps.py", tmp])
            return code, out.getvalue()

    def test_exit_code_and_summary(self):
        code, out = self.main({"a.fs": ": s ( x -- a b c ) ;\n: u ['] s ok-apply ['] t ok-apply ;\n"})
        self.assertEqual(code, 1)
        self.assertIn("outcome steps: 2 sites, 0 right, 1 wrong, 1 not checked", out)
        code, out = self.main({"a.fs": ": u ['] t ok-apply ;\n"})
        self.assertEqual(code, 0)

    def test_todays_tree_has_no_wrong_step(self):
        wrong, _, count = cos.check(ROOT)
        self.assertEqual(wrong, [])
        self.assertGreater(count, 100)


if __name__ == "__main__":
    unittest.main()
