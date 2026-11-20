#!/usr/bin/env python3
"""Tests of scripts/check-duplicates.py's tools for removing a group (owner, 2026-11-19): --explain, --plan,
--extract and --extract-table, on small throw-away Forth trees (never the real src/, which only --plan reads).

Covered: an exact group extracted with every member rewritten and the baseline's group dropped; a shape
group and a same-text group whose words differ refused; a member's file that does not load the home refused
with the missing require named, and accepted with --add-require; a member in a private wordlist and a home
whose place is private (the new word compiled public); a phrase twice in one body; a name that exists with
another body refused, a member in the home used as the word; the dry run writes nothing; an extraction that
would make a new group is refused with nothing written, and a written tree that differs from the checked
copy is restored; the table form, all or nothing; the layering and the plan's ranking.
--rewrite: a phrase replaced across line breaks but never in comments or strings; wildcards (one name, the
same wherever it recurs, never a control or frame word, a number or a string); a comment inside the phrase
and the definition of a word the new phrase calls left; a missing require refused or added; planted faults
re-targeted or named; --paths; the dry run; a rewrite that would make a duplicate group refused, a group it
removes dropped from the baseline."""
import contextlib
import importlib.util
import io
import json
import pathlib
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("cd", ROOT / "scripts/check-duplicates.py")
cd = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cd)

BODY = "dup over ok? if nip over swap execute else drop then"       # 11 tokens, Gforth words only
OTHER = "2dup + over * swap - abs negate"                            # 8 tokens
HOME = ": helper-x ( n -- n ) 1 + ;\n"


class Tree:
    """A throw-away tree: src/ files and a baseline giving every group a reason."""

    def __init__(self, files, reason="planned: 9.4.8k test"):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = pathlib.Path(self.tmp.name)
        for name, text in files.items():
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        (self.root / "tests").mkdir(exist_ok=True)
        base = cd.baseline_of(cd.groups(self.root))
        for entry in base.values():
            entry["reason"] = reason
        self.baseline().write_text(json.dumps(base, indent=1, sort_keys=True) + "\n")

    def baseline(self):
        return self.root / "tests/duplicates-baseline.json"

    def text(self, name):
        return (self.root / name).read_text()

    def snapshot(self):
        return {str(p.relative_to(self.root)): p.read_text() for p in self.root.rglob("*") if p.is_file()}

    def key(self, member):
        return next(k for k, g in cd.groups(self.root).items() if member in [m[2] for m in g["members"]])

    def run(self, *args):
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            status = cd.main([*args, str(self.root)])
        return status, out.getvalue()

    def extract(self, member, word, home, *more):
        return self.run("--extract", self.key(member), "--word", word, "--stack", "( x -- x )", "--home", home,
                        *more)

    def close(self):
        self.tmp.cleanup()


def three_members():
    return {"src/core/home.fs": HOME,
            "src/core/a.fs": "require ./home.fs\n: a-one ( x -- x ) " + BODY + " ;  \\ kept\n: a-two 1 ;\n",
            "src/core/b.fs": "require ./home.fs\n: b-one ( x -- x ) \\ note\n  " + BODY + " ;\n",
            "src/kernel/k.fs": "require ../core/home.fs\n: k-one ( x -- x )\n  " + BODY.replace(" if", "\n  IF")
            + " ;\n"}


class Extract(unittest.TestCase):
    def setUp(self):
        self.tree = Tree(three_members())

    def tearDown(self):
        self.tree.close()

    def test_an_exact_group_is_extracted_and_every_member_rewritten(self):
        key = self.tree.key("a-one")
        status, out = self.tree.extract("a-one", "shared-step", "src/core/home.fs", "--comment", "the step")
        self.assertEqual(status, 0, out)
        self.assertEqual(self.tree.text("src/core/home.fs"),
                         HOME + "\\ the step\n: shared-step ( x -- x ) " + BODY + " ;\n")
        self.assertEqual(self.tree.text("src/core/a.fs"),
                         "require ./home.fs\n: a-one ( x -- x ) shared-step ;  \\ kept\n: a-two 1 ;\n")
        self.assertEqual(self.tree.text("src/core/b.fs"),
                         "require ./home.fs\n: b-one ( x -- x ) \\ note\n  shared-step ;\n")
        self.assertEqual(self.tree.text("src/kernel/k.fs"), "require ../core/home.fs\n: k-one ( x -- x )\n"
                                                             "  shared-step ;\n")
        self.assertNotIn(key, json.loads(self.tree.baseline().read_text()))
        self.assertEqual(self.tree.run()[0], 0)
        self.assertIn("changed 4 file(s)", out)
        self.assertIn("EXACT EXTRACTION BY SCRIPT", out)
        self.assertIn("- src/core/a.fs:2 a-one -> shared-step", out)
        self.assertIn("- src/kernel/k.fs:2 k-one -> shared-step", out)

    def test_the_dry_run_writes_nothing(self):
        before = self.tree.snapshot()
        status, out = self.tree.extract("a-one", "shared-step", "src/core/home.fs", "--dry-run")
        self.assertEqual(status, 0, out)
        self.assertEqual(self.tree.snapshot(), before)
        self.assertIn("+: shared-step ( x -- x ) " + BODY + " ;", out)
        self.assertIn("-: a-one ( x -- x ) " + BODY + " ;  \\ kept", out)
        self.assertIn("would change 4 file(s)", out)

    def test_a_name_that_exists_with_another_body_is_refused(self):
        before = self.tree.snapshot()
        for name in ("helper-x", "a-two"):
            with self.subTest(name=name):
                status, out = self.tree.extract("a-one", name, "src/core/home.fs")
                self.assertEqual(status, 1)
                self.assertIn(f"{name} already exists with another body", out)
        self.assertEqual(self.tree.snapshot(), before)

    def test_a_member_named_by_word_is_used_as_it_is(self):
        status, out = self.tree.extract("a-one", "a-one", "src/core/a.fs", "--add-require")
        self.assertEqual(status, 0, out)
        self.assertIn("used the existing word a-one", out)
        self.assertIn(": a-one ( x -- x ) " + BODY, self.tree.text("src/core/a.fs"))
        self.assertIn("require ./a.fs\n", self.tree.text("src/core/b.fs"))
        self.assertIn("  a-one ;", self.tree.text("src/core/b.fs"))

    def test_a_home_that_cannot_see_a_word_is_refused(self):
        tree = Tree({"src/core/h.fs": ": h-step 1 + ;\n", "src/core/other.fs": ": unrelated 2 ;\n",
                     "src/core/a.fs": "require ./h.fs\n: a-x h-step over + swap execute drop ;\n",
                     "src/core/b.fs": "require ./h.fs\n: b-x h-step over + swap execute drop ;\n"})
        try:
            status, out = tree.extract("a-x", "step-run", "src/core/other.fs", "--add-require")
            self.assertEqual(status, 1)
            self.assertIn("cannot see `h-step` (defined in src/core/h.fs)", out)
        finally:
            tree.close()


class Refusals(unittest.TestCase):
    def test_a_shape_group_is_refused(self):
        tree = Tree({"src/core/a.fs": ": in-h 1 ;\n: in-x ( x -- x ) in-h over + swap execute drop ;\n",
                     "src/core/b.fs": ": ib-h 2 ;\n: ib-x ( x -- x ) ib-h over + swap execute drop ;\n"})
        try:
            before = tree.snapshot()
            status, out = tree.extract("in-x", "shared", "src/core/a.fs")
            self.assertEqual(status, 1)
            self.assertIn("is a shape group, not an exact one (token 1 differs (in-x: in-h, ib-x: ib-h))", out)
            self.assertEqual(tree.snapshot(), before)
        finally:
            tree.close()

    def test_the_same_text_naming_different_words_is_a_shape(self):
        tree = Tree({"src/core/a.fs": ": h 1 ;\n: a-x ( x -- x ) h over + swap execute drop ;\n",
                     "src/core/b.fs": ": h 2 ;\n: b-x ( x -- x ) h over + swap execute drop ;\n"})
        try:
            ws = cd.Workspace(tree.root)
            exact, why = cd.exactness(ws, [ws.definition("src/core/a.fs", "a-x"), ws.definition("src/core/b.fs", "b-x")])
            self.assertFalse(exact)
            self.assertIn("`h` names src/core/a.fs in src/core/a.fs; src/core/b.fs in src/core/b.fs", why)
            status, out = tree.extract("a-x", "shared", "src/core/a.fs")
            self.assertEqual(status, 1)
            self.assertIn("shape group", out)
        finally:
            tree.close()

    def test_a_missing_require_is_named_and_added_on_request(self):
        files = three_members()
        files["src/core/b.fs"] = files["src/core/b.fs"].replace("require ./home.fs\n", "")
        tree = Tree(files)
        try:
            before = tree.snapshot()
            status, out = tree.extract("a-one", "shared-step", "src/core/home.fs")
            self.assertEqual(status, 1)
            self.assertIn("src/core/b.fs does not load src/core/home.fs, directly or not: it needs "
                          "`require ./home.fs`", out)
            self.assertEqual(tree.snapshot(), before)
            status, out = tree.extract("a-one", "shared-step", "src/core/home.fs", "--add-require")
            self.assertEqual(status, 0, out)
            self.assertTrue(tree.text("src/core/b.fs").startswith("require ./home.fs\n: b-one"))
            self.assertIn("added `require ./home.fs` to src/core/b.fs", out)
        finally:
            tree.close()

    def test_a_home_that_loads_a_member_is_refused(self):
        files = {"src/core/a.fs": ": a-x ( x -- x ) " + BODY + " ;\n",
                 "src/core/b.fs": "require ./a.fs\n: b-x ( x -- x ) " + BODY + " ;\n: b-y 1 ;\n"}
        tree = Tree(files)
        try:
            status, out = tree.extract("a-x", "shared", "src/core/b.fs", "--add-require")
            self.assertEqual(status, 1)
            self.assertIn("src/core/b.fs loads src/core/a.fs, so src/core/a.fs cannot load src/core/b.fs", out)
        finally:
            tree.close()


PRIVATE_HOME = ("lf-lib-private module-open\n: h-helper 1 ;\nlf-lib set-current\n: h-public 2 ;\n"
                "lf-lib-private set-current\n: h-private 3 ;\nmodule-close\n")


class Wordlists(unittest.TestCase):
    def setUp(self):
        self.tree = Tree({
            "src/lib/h.fs": PRIVATE_HOME,
            "src/lib/m.fs": "require ./h.fs\nlf-lib-private module-open\n: m-copy ( x -- x ) " + BODY
                            + " ;\nlf-lib set-current\n: m-pub m-copy ;\nmodule-close\n",
            "src/lib/n.fs": "require ./h.fs\n: n-copy ( x -- x ) " + BODY + " ;\n"})

    def tearDown(self):
        self.tree.close()

    def test_explain_names_each_members_wordlist(self):
        status, out = self.tree.run("--explain", self.tree.key("m-copy")[:6])
        self.assertEqual(status, 0)
        self.assertIn("EXACT: identical tokens", out)
        self.assertIn("phrase: " + BODY, out)
        self.assertIn("src/lib/m.fs:3 m-copy ( x -- x )  [lib; wordlist: lf-lib-private (private: module-open at "
                      "line 2)]", out)
        self.assertIn("src/lib/n.fs:2 n-copy ( x -- x )  [lib; wordlist: default]", out)
        self.assertIn("      | : n-copy ( x -- x ) " + BODY + " ;", out)

    def test_a_private_place_gets_the_word_compiled_public(self):
        status, out = self.tree.extract("m-copy", "shared-run", "src/lib/h.fs")
        self.assertEqual(status, 0, out)
        self.assertEqual(self.tree.text("src/lib/h.fs"), PRIVATE_HOME.replace(
            "module-close\n", "lf-lib set-current\n"
            "\\ shared-run: shared by m-copy, n-copy (check-duplicates.py --extract)\n: shared-run ( x -- x ) " + BODY + " ;\nlf-lib-private set-current\n"
            "module-close\n"))
        self.assertIn(": m-copy ( x -- x ) shared-run ;\nlf-lib set-current", self.tree.text("src/lib/m.fs"))
        self.assertIn("compiled into lf-lib (public)", out)

    def test_after_a_public_word_needs_no_wrapping(self):
        status, out = self.tree.extract("m-copy", "shared-run", "src/lib/h.fs", "--after", "h-public")
        self.assertEqual(status, 0, out)
        self.assertIn(": h-public 2 ;\n\\ shared-run: shared by m-copy, n-copy (check-duplicates.py --extract)\n"
                      ": shared-run ( x -- x ) " + BODY + " ;\nlf-lib-private set-current\n",
                      self.tree.text("src/lib/h.fs"))


class Phrases(unittest.TestCase):
    def test_a_phrase_twice_in_one_body_is_replaced_twice(self):
        ws_text = ": twice ( x -- y ) " + OTHER + " 1+ " + OTHER + " ;\n"
        src = cd.Source(pathlib.Path("."), "src/x.fs", ws_text)
        edits = cd.replace_phrase(src.defs[0], OTHER.split(), "step")
        self.assertEqual(len(edits), 2)
        self.assertEqual(cd.apply_edits(ws_text, edits), ": twice ( x -- y ) step 1+ step ;\n")

    def test_a_cut_phrase_may_not_reach_the_callers_frame(self):
        text = ": w ( -- ) 1 >r drop r> drop dup ;\n"
        src = cd.Source(pathlib.Path("."), "src/x.fs", text)
        with self.assertRaises(cd.Refusal):
            cd.replace_phrase(src.defs[0], ">r drop r>".split(), "step")

    def test_a_long_phrase_is_wrapped_below_the_line_limit(self):
        phrase = " ".join(["over"] * 40)
        lines = cd.new_definition("w", "( a b -- a b )", phrase, "note")
        self.assertEqual(lines[:2], ["\\ note", ": w ( a b -- a b )"])
        self.assertTrue(all(len(line) <= cd.LINE_LIMIT for line in lines))
        self.assertEqual(" ".join(" ".join(lines[2:]).split()), phrase + " ;")

    def test_spans_agree_with_tokens(self):
        text = (ROOT / "src/lib/outcome.fs").read_text()
        self.assertEqual(cd.tokens(text), [(t, line) for t, line, _, _ in cd.spans(text)])
        for tok, _, start, end in cd.spans(text):
            self.assertEqual(text[start:end].lower().split()[0], tok.split()[0])


class Failures(unittest.TestCase):
    def test_an_extraction_that_makes_a_new_group_writes_nothing(self):
        body = "dup helper-x over ok? if nip over swap execute else drop then"
        tree = Tree({"src/core/home.fs": HOME,
                     "src/core/a.fs": "require ./home.fs\n: a-x ( x -- x ) " + body + " ;\n",
                     "src/core/b.fs": "require ./home.fs\n: b-x ( x -- x ) " + body + " ;\n",
                     "src/core/d.fs": ": d-local 2 + ;\n: d-x ( x -- x ) "
                                      + body.replace("helper-x", "d-local") + " ;\n"})
        try:
            before = tree.snapshot()
            status, out = tree.extract("a-x", "shared", "src/core/home.fs")
            self.assertEqual(status, 1)
            self.assertIn("would change other groups (nothing written)", out)
            self.assertIn("new group", out)
            self.assertEqual(tree.snapshot(), before)
        finally:
            tree.close()

    def test_a_written_tree_that_differs_from_the_checked_copy_is_restored(self):
        tree = Tree(three_members())
        real, calls = cd.groups, []

        def groups(root, *args):
            found = real(root, *args)
            calls.append(root)
            if pathlib.Path(root) == tree.root and len([c for c in calls if pathlib.Path(c) == tree.root]) > 1:
                found["000000000000"] = {"tokens": 9, "kind": "shape", "members": [("src/core/a.fs", 1, "zz")]}
            return found
        try:
            key = tree.key("a-one")
            before = tree.snapshot()
            cd.groups = groups
            status, out = tree.run("--extract", key, "--word", "shared-step", "--home", "src/core/home.fs")
            self.assertEqual(status, 1)
            self.assertIn("every file restored", out)
            self.assertEqual(tree.snapshot(), before)
        finally:
            cd.groups = real
            tree.close()


class Table(unittest.TestCase):
    def setUp(self):
        files = three_members()
        files["src/core/a.fs"] += ": a-other ( a b -- c ) " + OTHER + " ;\n"
        files["src/core/b.fs"] += ": b-other ( a b -- c ) " + OTHER + " ;\n"
        files["src/core/s1.fs"] = ": in-h 1 ;\n: in-x ( x -- x ) in-h over + swap execute drop ;\n"
        files["src/core/s2.fs"] = ": ib-h 2 ;\n: ib-x ( x -- x ) ib-h over + swap execute drop ;\n"
        self.tree = Tree(files)
        self.table = self.tree.root / "table.txt"

    def tearDown(self):
        self.tree.close()

    def test_every_line_is_applied(self):
        self.table.write_text(f"# group word stack home after comment\n{self.tree.key('a-one')} shared-step "
                              f"\"( x -- x )\" src/core/home.fs - \"the step\"\n\n"
                              f"{self.tree.key('a-other')} other-step \"( a b -- c )\" src/core/home.fs "
                              "helper-x\n")
        status, out = self.tree.run("--extract-table", str(self.table))
        self.assertEqual(status, 0, out)
        home = self.tree.text("src/core/home.fs")
        self.assertIn(HOME + "\\ other-step: shared by a-other, b-other", home)
        self.assertIn("\\ the step\n: shared-step ( x -- x ) " + BODY + " ;\n", home)
        self.assertIn(": b-other ( a b -- c ) other-step ;", self.tree.text("src/core/b.fs"))
        self.assertEqual(self.tree.run()[0], 0)

    def test_one_refused_line_writes_nothing(self):
        before = self.tree.snapshot()
        self.table.write_text(f"{self.tree.key('a-one')} shared-step \"( x -- x )\" src/core/home.fs\n"
                              f"{self.tree.key('in-x')} shared-h \"( x -- x )\" src/core/s1.fs\n")
        status, out = self.tree.run("--extract-table", str(self.table))
        self.assertEqual(status, 1)
        self.assertIn("shape group", out)
        self.assertEqual({k: v for k, v in self.tree.snapshot().items() if k != "table.txt"},
                         {k: v for k, v in before.items() if k != "table.txt"})

    def test_a_malformed_line_is_named(self):
        self.table.write_text("abc only-two\n")
        with self.assertRaises(SystemExit) as caught:
            cd.table_specs(self.table)
        self.assertIn("table.txt:1", str(caught.exception))


GUARD = "ok-then? 0= if nip no-result exit then"
STEP_LIB = (": ok-then? ( x o -- x t | o f ) dup 0= if drop true else nip false then ;\n"
            ": no-result ( o -- -1 o ) -1 swap ;\n"
            ": ok-apply2 ( a b o xt -- r o ) over 0= if nip execute else drop nip nip no-result then ;\n")


def rewrite_tree(**more):
    """A tree for --rewrite: the step words in src/lib/o.fs, two callers of the guard (one across a line
    break), the phrase in a comment and a string, and two faults quoting the callers' lines."""
    files = {"src/lib/o.fs": STEP_LIB,
             "src/core/a.fs": "require ../lib/o.fs\n: a-step ( x -- y ) 1+ 0 ;\n"
                              ": a-run ( a x o -- y o ) " + GUARD + " a-step ;  \\ kept\n",
             "src/core/b.fs": "require ../lib/o.fs\n: b-step ( x -- y ) 2* 0 ;\n"
                              ": b-run ( a x o -- y o ) \\ " + GUARD + " b-step ;\n"
                              "  ok-then? 0= if nip\n  no-result exit then b-step ;\n"
                              ": b-note ( -- ) .\" ok-then? 0= if nip no-result exit then b-step ;\" ;\n"}
    files.update(more)
    tree = Tree(files)
    (tree.root / "tests/mutants").mkdir(parents=True)
    (tree.root / "tests/mutants/faults.toml").write_text(
        "[[fault]]\nid = \"a-run-drops-first\"\nfile = \"src/core/a.fs\"\n"
        "old = ''': a-run ( a x o -- y o ) " + GUARD + " a-step ;'''\n"
        "new = ''': a-run ( a x o -- y o ) drop " + GUARD + " a-step ;'''\n"
        "test = \"true\"\nreason = \"r\"\n\n"
        "[[fault]]\nid = \"a-step-off\"\nfile = \"src/core/a.fs\"\n"
        "old = ''': a-step ( x -- y ) 1+ 0 ;'''\nnew = ''': a-step ( x -- y ) 1- 0 ;'''\n"
        "test = \"true\"\nreason = \"r\"\n\n"
        "[[fault]]\nid = \"b-run-no-drop\"\nfile = \"src/core/b.fs\"\n"
        "old = '''  no-result exit then b-step ;'''\n"
        "new = '''  -1 exit then b-step ;'''\n"
        "test = \"true\"\nreason = \"r\"\n")
    return tree


class Rewrite(unittest.TestCase):
    """--rewrite: a phrase replaced token for token in every file, wildcards, requires, faults."""

    def setUp(self):
        self.tree = rewrite_tree()

    def tearDown(self):
        self.tree.close()

    def rewrite(self, frm, to, *more):
        return self.tree.run("--rewrite", "--from", frm, "--to", to, *more)

    def test_every_site_is_rewritten_across_line_breaks_but_not_in_comments_or_strings(self):
        status, out = self.rewrite(GUARD + " $X ;", "['] $X ok-apply2 ;")
        self.assertEqual(status, 0, out)
        self.assertEqual(self.tree.text("src/core/a.fs"), "require ../lib/o.fs\n: a-step ( x -- y ) 1+ 0 ;\n"
                         ": a-run ( a x o -- y o ) ['] a-step ok-apply2 ;  \\ kept\n")
        b = self.tree.text("src/core/b.fs")
        self.assertIn(": b-run ( a x o -- y o ) \\ " + GUARD + " b-step ;\n  ['] b-step ok-apply2 ;\n", b)
        self.assertIn(".\" ok-then? 0= if nip no-result exit then b-step ;\"", b)
        self.assertIn("rewrote 2 site(s) in 2 file(s)", out)
        self.assertIn("src/core/a.fs:3 a-run", out)
        self.assertIn("src/core/b.fs:4 b-run", out)
        self.assertIn("- src/core/a.fs:3 a-run", out.split("REWRITE BY SCRIPT")[1])

    def test_planted_faults_on_the_phrase_follow_it_or_are_named(self):
        status, out = self.rewrite(GUARD + " $X ;", "['] $X ok-apply2 ;")
        self.assertEqual(status, 0, out)
        faults = self.tree.text("tests/mutants/faults.toml")
        self.assertIn("old = ''': a-run ( a x o -- y o ) ['] a-step ok-apply2 ;'''", faults)
        self.assertIn("new = ''': a-run ( a x o -- y o ) drop ['] a-step ok-apply2 ;'''", faults)
        self.assertIn("planted faults re-targeted: a-run-drops-first (new text changed)\n", out)
        self.assertIn("old = ''': a-step ( x -- y ) 1+ 0 ;'''", faults)
        self.assertIn("fault b-run-no-drop (src/core/b.fs): its old text no longer occurs once", out)
        self.assertIn("old = '''  no-result exit then b-step ;'''", faults)

    def test_paths_limit_the_rewrite_and_the_dry_run_writes_nothing(self):
        before = self.tree.snapshot()
        status, out = self.rewrite(GUARD + " $X ;", "['] $X ok-apply2 ;", "--paths", "src/core/b.fs",
                                   "--dry-run")
        self.assertEqual(status, 0, out)
        self.assertEqual(self.tree.snapshot(), before)
        self.assertIn("would rewrite 1 site(s) in 1 file(s)", out)
        self.assertNotIn("a-run", out.split("REWRITE BY SCRIPT")[0].split("would rewrite")[1])
        self.assertIn("+  ['] b-step ok-apply2 ;", out)

    def test_a_wildcard_binds_one_name_the_same_wherever_it_recurs(self):
        pattern = cd.Pattern("$X $X +", "$X 2*")
        self.assertEqual(pattern.apply(": w dup DUP + ;")[0], ": w dup 2* ;")
        self.assertEqual(pattern.apply(": w dup drop + ;"), (": w dup drop + ;", 0))
        for text in (": w exit exit + ;", ": w 7 7 + ;", ": w r> r> + ;", ": w ['] ['] + ;",
                     ": w s\" a\" s\" a\" + ;"):
            with self.subTest(text=text):
                self.assertEqual(pattern.apply(text)[1], 0)
        two = cd.Pattern("ok-then? if $X else $Y then", "$Y $X")
        self.assertEqual(two.apply(": w ok-then? IF a-b else C-D then ;")[0], ": w C-D a-b ;")

    def test_a_comment_inside_the_phrase_leaves_the_site(self):
        tree = rewrite_tree(**{"src/core/c.fs": "require ../lib/o.fs\n: c-step 0 ;\n"
                                                ": c-run ok-then? 0= ( why ) if nip no-result exit then c-step ;\n"})
        try:
            status, out = tree.run("--rewrite", "--from", GUARD + " $X ;", "--to", "['] $X ok-apply2 ;")
            self.assertEqual(status, 0, out)
            self.assertIn("left: src/core/c.fs:3 c-run: a comment inside the phrase", out)
            self.assertIn("( why )", tree.text("src/core/c.fs"))
        finally:
            tree.close()

    def test_the_definition_of_a_new_word_is_left_alone(self):
        status, out = self.rewrite("over 0= if nip execute else drop nip nip no-result then",
                                   "['] execute ok-apply2")
        self.assertIn("left: src/lib/o.fs:3 ok-apply2: inside the definition of ok-apply2", out)
        self.assertEqual(self.tree.text("src/lib/o.fs"), STEP_LIB)

    def test_a_file_that_cannot_see_a_new_word_is_refused_or_given_the_require(self):
        tree = rewrite_tree(**{"src/core/d.fs": ": d-step 0 ;\n: d-run " + GUARD + " d-step ;\n"})
        try:
            before = tree.snapshot()
            status, out = tree.run("--rewrite", "--from", GUARD + " $X ;", "--to", "['] $X ok-apply2 ;")
            self.assertEqual(status, 1)
            self.assertIn("src/core/d.fs does not load the definition of `ok-apply2`: it needs "
                          "`require ../lib/o.fs`", out)
            self.assertEqual(tree.snapshot(), before)
            status, out = tree.run("--rewrite", "--from", GUARD + " $X ;", "--to", "['] $X ok-apply2 ;",
                                   "--add-require")
            self.assertEqual(status, 0, out)
            self.assertEqual(tree.text("src/core/d.fs"), "require ../lib/o.fs\n: d-step 0 ;\n"
                                                         ": d-run ['] d-step ok-apply2 ;\n")
            self.assertIn("added `require ../lib/o.fs` to src/core/d.fs", out)
        finally:
            tree.close()

    def test_add_require_names_the_file_to_load(self):
        tree = rewrite_tree(**{"src/core/d.fs": ": d-step 0 ;\n: d-run " + GUARD + " d-step ;\n",
                               "src/core/e.fs": "require ../lib/o.fs\n"})
        try:
            status, out = tree.run("--rewrite", "--from", GUARD + " $X ;", "--to", "['] $X ok-apply2 ;",
                                   "--add-require", "src/core/e.fs", "--paths", "src/core/d.fs")
            self.assertEqual(status, 0, out)
            self.assertTrue(tree.text("src/core/d.fs").startswith("require ./e.fs\n"))
        finally:
            tree.close()

    def test_a_rewrite_that_makes_a_duplicate_group_writes_nothing(self):
        tree = rewrite_tree(**{"src/core/f.fs": "require ../lib/o.fs\n: f-step 0 ;\n"
                                                ": f-one 1 2 3 4 5 swap-it f-step ;\n"
                                                ": f-two 1 2 3 4 5 other f-step ;\n"})
        try:
            before = tree.snapshot()
            status, out = tree.run("--rewrite", "--from", "other", "--to", "swap-it")
            self.assertEqual(status, 1)
            self.assertIn("would make a duplicate group", out)
            self.assertEqual(tree.snapshot(), before)
        finally:
            tree.close()

    def test_a_group_the_rewrite_removes_leaves_the_baseline(self):
        tree = rewrite_tree(**{"src/core/g.fs": ": old-a 0 ;\n: old-b 1 ;\n"
                                                ": g-one 1 2 3 4 5 6 old-a ;\n: g-two 1 2 3 4 5 6 old-b ;\n"})
        try:
            key = tree.key("g-one")
            status, out = tree.run("--rewrite", "--from", "4 5 6 old-a", "--to", "old-a")
            self.assertEqual(status, 0, out)
            self.assertNotIn(key, json.loads(tree.baseline().read_text()))
            self.assertIn("duplicate groups gone:", out)
            self.assertEqual(tree.run()[0], 0)
        finally:
            tree.close()

    def test_a_malformed_pattern_is_refused(self):
        for frm, to in (("", "x"), ("a $X", "$Y")):
            with self.subTest(frm=frm, to=to):
                status, out = self.rewrite(frm, to)
                self.assertEqual(status, 1)
                self.assertIn("refused:", out)


class Plan(unittest.TestCase):
    def test_layers_follow_src_readme(self):
        self.assertEqual(cd.MAY_REQUIRE["core"], {"lib", "core"})
        self.assertNotIn("kernel", cd.MAY_REQUIRE["front"])
        tree = Tree({"src/core/w.fs": ": core-step 1 + ;\n",
                     "src/kernel/k.fs": "require ../core/w.fs\n: k-x ( x -- x ) core-step " + BODY + " ;\n",
                     "src/front/f.fs": "require ../core/w.fs\n: f-x ( x -- x ) core-step " + BODY + " ;\n",
                     "src/present/p.fs": ": p-x ( x -- x ) " + OTHER + " ;\n",
                     "src/kernel/q.fs": ": q-x ( x -- x ) " + OTHER + " ;\n"})
        try:
            ws = cd.Workspace(tree.root)
            core = [ws.definition("src/kernel/k.fs", "k-x"), ws.definition("src/front/f.fs", "f-x")]
            self.assertEqual(cd.suggested_layer(ws, core), "core")
            plain = [ws.definition("src/present/p.fs", "p-x"), ws.definition("src/kernel/q.fs", "q-x")]
            self.assertEqual(cd.suggested_layer(ws, plain), "lib")
            self.assertEqual(cd.home_files(ws, core), ["src/core/w.fs"])
        finally:
            tree.close()

    def test_the_plan_ranks_groups_and_counts_them(self):
        files = three_members()
        files["src/core/s1.fs"] = ": in-h 1 ;\n: in-x ( x -- x ) in-h over + swap execute drop ;\n"
        files["src/core/s2.fs"] = ": ib-h 2 ;\n: ib-x ( x -- x ) ib-h over + swap execute drop ;\n"
        files["src/lib/o.fs"] = ": ok-step ( x -- x ) " + OTHER + " ;\n"
        files["src/core/c.fs"] = "require ../lib/o.fs\n: c-step ( x -- x ) " + OTHER + " ;\n"
        tree = Tree(files)
        try:
            status, out = tree.run("--plan")
            self.assertEqual(status, 0)
            lines = out.splitlines()
            self.assertIn("   33 ", lines[1])                     # 3 copies x 11 tokens first
            self.assertIn("exact", lines[1])
            self.assertIn("home src/core/home.fs", lines[1])
            self.assertIn("existing src/lib/o.fs:ok-step", out)
            self.assertIn("src/core/s1.fs (core), src/core/s2.fs (core)", out)
            self.assertEqual(lines[-1], "3 groups not false positive: 2 exact (1 with an existing word every "
                                        "member can call), 1 shape")
        finally:
            tree.close()

    def test_false_positives_are_left_out(self):
        tree = Tree(three_members(), reason="false positive: a test")
        try:
            self.assertIn("0 groups not false positive", tree.run("--plan")[1])
        finally:
            tree.close()

    def test_the_real_tree_plans(self):
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            self.assertEqual(cd.main(["--plan"]), 0)
        self.assertRegex(out.getvalue(), r"\d+ groups not false positive: \d+ exact")


if __name__ == "__main__":
    unittest.main()
