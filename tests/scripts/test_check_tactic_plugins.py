#!/usr/bin/env python3
"""Tests of scripts/check-tactic-plugins.py and the tactic change tier (tactic plug-in design,
slice (a1); owner's decision 2 of 2026-11-17): the Forth tokens without comments and strings;
each rule (a hook written with is or defer!, a data word of another file written, a row setter
called for another file's kind) caught and its clean twin passed; on throw-away repositories
(tests/scripts/tier_fixture.py) a confined tactic branch gets the tactic tier (the front end's
unit tests, the S1/S2 pinned-Lean comparisons, no kernel test, no make check-rest), and a branch
that also edits the runner, a file outside the tactic's own, or breaks a rule never does."""
import importlib.util
import json
import pathlib
import sys
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import tier_fixture  # noqa: E402

ROOT = tier_fixture.ROOT
spec = importlib.util.spec_from_file_location("tactic_plugins", ROOT / "scripts/check-tactic-plugins.py")
tp = importlib.util.module_from_spec(spec)
spec.loader.exec_module(tp)

CLEAN = """\\ src/front/tactics/decide.fs: by-decide (a stand-in)
wordlist constant decide-private
variable decide-count            \\ its own state
tac-shape-plain lf-tactic: by-decide constant tac-k-decide
s" decide" tac-k-decide lf-tactic-lean!
: lfd-run ( i -- ) drop 1 decide-count +! ;
' lfd-run tac-k-decide lf-tactic-action!
( a comment that names is and defer! )
: lfd-text ( -- a u ) s" is defer! lf-run-hook !" ;
"""


class Tokens(unittest.TestCase):
    def test_comments_and_strings_left_out(self):
        text = ': a ( x -- ) s" is it" type \\ is here\n  x ! ; ( multi\nline is ) defer! ." q is"'
        self.assertEqual(tp.tokens(text), [":", "a", "type", "x", "!", ";", "defer!"])

    def test_clean_file_passes(self):
        self.assertEqual(tp.rule_problems("t.fs", CLEAN, {"lf-run-hook", "decide-count"}), [])

    def test_each_rule(self):
        foreign = {"lf-run-hook", "lf-max-goals"}
        cases = {
            "' lfd-run is lf-step-hook": "writes a hook (is)",
            "' lfd-run ['] lf-step-hook defer!": "writes a hook (defer!)",
            "5 lf-run-hook !": "writes lf-run-hook (lf-run-hook !)",
            "1 lf-max-goals +!": "writes lf-max-goals (lf-max-goals +!)",
            "7 to lf-max-goals": "writes lf-max-goals (to lf-max-goals)",
            "' lfd-run tac-k-rfl lf-tactic-action!": "calls lf-tactic-action! for tac-k-rfl",
        }
        for line, wanted in cases.items():
            with self.subTest(line=line):
                problems = tp.rule_problems("t.fs", CLEAN + line + "\n", foreign)
                self.assertEqual(len(problems), 1, problems)
                self.assertIn(wanted, problems[0])

    def test_fixed_kinds_belong_to_their_files(self):
        line = "' trf-run tac-k-rfl lf-tactic-action!\n"
        self.assertEqual(tp.rule_problems("src/front/tactics/rfl.fs", line, set()), [])
        for path, kind in (("src/front/tactics/intro.fs", "tac-k-rfl"), ("t.fs", "tac-k-rfl"),
                           ("src/front/tactics/rfl.fs", "tac-k-sorry"), ("src/front/rfl.fs", "tac-k-rfl"),
                           ("src/front/tactics/sub/rfl.fs", "tac-k-rfl")):
            with self.subTest(path=path, kind=kind):
                problems = tp.rule_problems(path, f"' trf-run {kind} lf-tactic-action!\n", set())
                self.assertEqual(len(problems), 1, problems)
                self.assertIn(f"calls lf-tactic-action! for {kind}", problems[0])
        self.assertEqual({tp.FIXED_KINDS[k] for k in ("tac-k-induction", "tac-k-with")}, {"induction"})
        self.assertEqual(len(tp.FIXED_KINDS), 11)
        # The alternative's row is the runner's (lf-tactic-alt!, plan 9.4.8l-I C4): induction.fs
        # sets it through its own tac-k-with, never by naming tac-k-alt.
        self.assertIsNone(tp.FIXED_KINDS["tac-k-alt"])
        self.assertEqual(tp.rule_problems("src/front/tactics/induction.fs",
                                          "' lf-alt-run tac-k-with lf-tactic-alt!\n", set()), [])
        problems = tp.rule_problems("src/front/tactics/induction.fs", "' run tac-k-alt lf-tactic-action!\n", set())
        self.assertEqual(len(problems), 1, problems)

    def test_an_alias_of_another_kind_is_not_own(self):
        # Review tactic-move L1: a constant, value or colon definition made from a fixed kind or
        # another file's kind is that kind under a new name, so this file may not set its rows.
        for alias in ("tac-k-rfl constant my-k", "tac-k-exact value my-k", ": my-k ( -- k ) tac-k-intro ;",
                      "tac-k-decide constant my-k"):
            with self.subTest(alias=alias):
                problems = tp.rule_problems("src/front/tactics/mine.fs",
                                            f"{alias}\n' run my-k lf-tactic-action!\n", set())
                self.assertEqual(len(problems), 1, problems)
                self.assertIn("calls lf-tactic-action! for my-k", problems[0])
        own = "tac-shape-plain lf-tactic: by-mine constant tac-k-mine\n' run tac-k-mine lf-tactic-action!\n"
        self.assertEqual(tp.rule_problems("src/front/tactics/mine.fs", own, set()), [])

    def test_own_data_words_may_be_written(self):
        text = "variable lf-max-goals\n3 lf-max-goals !\n"
        self.assertEqual(tp.rule_problems("t.fs", text, {"lf-max-goals"}), [])

    def test_create_inside_a_colon_definition_defines_no_data_word(self):
        # portability.fs's +field: create over , inside a defining word (plan row TB2).
        toks = tp.tokens(": +field ( n1 n2 -- n3 ) create over , + does> @ + ;\ncreate table 8 ,\n")
        self.assertEqual(tp.outside_colons(toks), ["create", "table", "8", ","])
        self.assertEqual(tp.DATA_WORD.findall(" ".join(tp.outside_colons(toks))), ["table"])


META_NEW = "\\ a goal operation\n: mgo-step ( goal -- goal' ) ;\n: lf-goal-new-op ( goal -- goal' ) mgo-step ;\n"
TACTIC_NEW = "tac-shape-plain lf-tactic: by-new constant tac-k-new\n"


class Batches(unittest.TestCase):
    """Plan row TB2: a batch's tests and faults, and goal operations that only gain lines."""

    def run_check(self, changed, texts, deleted=None, elsewhere=frozenset()):
        return tp.check(changed, read=lambda p: texts.get(p), deleted=deleted,
                        elsewhere=lambda path: set(elsewhere))

    def test_batch_files_with_a_tactic_added(self):
        changed = [("A", "src/front/tactics/new.fs"), ("A", "tests/front/tactics/batch-a/check.py"),
                   ("A", "tests/front/tactics/batch-a/x.lf"), ("A", "tests/mutants/faults.d/batch-a.toml")]
        result = self.run_check(changed, {"src/front/tactics/new.fs": TACTIC_NEW})
        self.assertEqual(result["reasons"], [])
        self.assertTrue(result["confined"])

    def test_batch_files_without_a_tactic_added(self):
        result = self.run_check([("M", "tests/front/tactics/batch-a/check.py")], {})
        self.assertFalse(result["confined"])
        self.assertIn("no tactic file is added (src/front/tactics/NAME.fs)", result["reasons"])
        for path in ("tests/front/tactics/batchy/check.py", "tests/mutants/faults.d/batch.toml"):
            with self.subTest(path=path):
                changed = [("A", "src/front/tactics/new.fs"), ("A", path)]
                result = self.run_check(changed, {"src/front/tactics/new.fs": TACTIC_NEW})
                self.assertIn(f"{path} lies outside the tactic's own files", result["reasons"])

    def test_goal_operations_new_or_gaining_lines(self):
        tactic = [("A", "src/front/tactics/new.fs")]
        texts = {"src/front/tactics/new.fs": TACTIC_NEW, "src/front/meta-tactic/new.fs": META_NEW,
                 "src/front/meta-tactic/goal.fs": META_NEW}
        for changed, deleted in (([("A", "src/front/meta-tactic/new.fs")], None),
                                 ([("M", "src/front/meta-tactic/goal.fs")], {"src/front/meta-tactic/goal.fs": 0})):
            with self.subTest(changed=changed):
                self.assertTrue(self.run_check(tactic + changed, texts, deleted)["confined"])

    def test_goal_operations_losing_lines_or_shadowing(self):
        tactic = [("A", "src/front/tactics/new.fs")]
        texts = {"src/front/tactics/new.fs": TACTIC_NEW, "src/front/meta-tactic/goal.fs": META_NEW,
                 "src/front/meta-tactic/twice.fs": META_NEW + ": mgo-step ( goal -- goal ) ;\n",
                 "src/front/meta-tactic/hook.fs": META_NEW + "' mgo-step is lf-run-hook\n"}
        cases = [
            ([("M", "src/front/meta-tactic/goal.fs")], {"src/front/meta-tactic/goal.fs": 2}, set(),
             "changes or removes lines of a goal operation"),
            ([("M", "src/front/meta-tactic/goal.fs")], None, set(), "changes or removes lines"),
            ([("A", "src/front/meta-tactic/goal.fs")], None, {"lf-goal-new-op"},
             "defines lf-goal-new-op again"),
            ([("A", "src/front/meta-tactic/twice.fs")], None, set(), "defines mgo-step again"),
        ]
        for changed, deleted, elsewhere, wanted in cases:
            with self.subTest(wanted=wanted):
                result = self.run_check(tactic + changed, texts, deleted, elsewhere)
                self.assertFalse(result["confined"])
                self.assertTrue(any(wanted in r for r in result["reasons"]), result["reasons"])
        result = self.run_check(tactic + [("A", "src/front/meta-tactic/hook.fs")], texts)
        self.assertFalse(result["confined"])
        self.assertTrue(any("writes a hook (is)" in p for p in result["problems"]), result["problems"])


FILES = dict(tier_fixture.FILES)
FILES["src/main.fs"] = "require ./core/c.fs\nrequire ./front/loaded.fs\nrequire ./front/tactics/all.fs\n"
FILES["src/front/tactics/all.fs"] = "require ./rfl.fs\n"
FILES["src/front/tactics/rfl.fs"] = "tac-shape-plain lf-tactic: by-rfl constant tac-k-rfl\n"
FILES["src/front/runner.fs"] = "variable lf-run-hook\n: lf-run ;\n"
FILES["src/front/meta-tactic/goal.fs"] = ": lf-goal-op ( -- ) ;\n"
FILES["tests/front/f.fs"] = "require ../../src/front/alone.fs\nrequire ../../src/main.fs\n"


class Tier(unittest.TestCase):
    """The tactic tier on a throw-away repository whose src/main.fs loads the tactics' list."""

    def setUp(self):
        self.repo = tier_fixture.Repo(FILES)

    def tearDown(self):
        self.repo.close()

    def tactic_branch(self, extra=None, text=CLEAN):
        files = {"src/front/tactics/decide.fs": text,
                 "src/front/tactics/all.fs": "require ./decide.fs\nrequire ./rfl.fs\n",
                 "tests/front/tactics/decide/test.fs": "require ../../../../src/main.fs\n",
                 "tests/mutants/faults.d/decide.toml": "",
                 "TACTICS.md": "# by-decide\n"}
        files.update(extra or {})
        for name, body in files.items():
            self.repo.write(name, body)
        self.repo.commit("a tactic")

    def plan(self):
        run = self.repo.script("test-tier.py", "--base", "base", "--json")
        self.assertEqual(run.returncode, 0, run.stderr)
        return json.loads(run.stdout)

    def check(self):
        return self.repo.script("check-tactic-plugins.py", "--base", "base")

    def test_confined_branch_gets_the_tactic_tier(self):
        self.tactic_branch()
        run = self.check()
        self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
        self.assertIn("confined: the tactic tier applies (decide)", run.stdout)
        result = self.plan()
        self.assertEqual(result["tier"], "tactic")
        self.assertIn("test-front", result["targets"])
        self.assertIn("reference-front", result["targets"])
        self.assertIn("check-docs", result["targets"])
        self.assertNotIn("reference-core", result["targets"], "no kernel comparison in the tactic tier")
        labels = [s["label"] for s in result["suites"]]
        self.assertNotIn("check-rest", labels)
        self.assertNotIn("test", labels)
        self.assertEqual(result["coverage"]["files"], ["src/front/tactics/all.fs", "src/front/tactics/decide.fs"])

    def test_runner_edit_refuses_the_tier(self):
        self.tactic_branch({"src/front/runner.fs": "variable lf-run-hook\n: lf-run 1 ;\n"})
        run = self.check()
        self.assertEqual(run.returncode, 3, run.stdout + run.stderr)
        self.assertIn("src/front/runner.fs lies outside the tactic's own files", run.stdout)
        result = self.plan()
        self.assertEqual(result["tier"], "full")
        self.assertIn("check-rest", [s["label"] for s in result["suites"]])

    def test_other_tests_or_fault_files_refuse_the_tier(self):
        for extra in ({"tests/front/tactics/rfl/test.fs": "\\ another tactic's tests\n"},
                      {"tests/mutants/faults.d/other.toml": ""}, {"tests/mutants/faults.toml": tier_fixture.FAULTS
                                                                  + "\n"},
                      {"Makefile": tier_fixture.MAKEFILE + "\n"}):
            with self.subTest(extra=sorted(extra)):
                base = self.repo.git("rev-parse", "HEAD")
                self.tactic_branch(extra)
                self.assertEqual(self.check().returncode, 3)
                self.assertEqual(self.plan()["tier"], "full")
                self.repo.git("reset", "-q", "--hard", base)

    def test_rule_break_refuses_the_tier_and_fails_the_check(self):
        self.tactic_branch(text=CLEAN + "1 lf-run-hook !\n")
        run = self.check()
        self.assertEqual(run.returncode, 1, run.stdout + run.stderr)
        self.assertIn("writes lf-run-hook", run.stderr)
        result = self.plan()
        self.assertEqual(result["tier"], "full")
        self.assertIn("writes lf-run-hook", self.repo.script("test-tier.py", "--base", "base").stdout)
        tier = self.repo.script("tested-tree.py", "tier", "--base", "base", "--no-progress", "--dry-run")
        self.assertEqual(tier.returncode, 1, tier.stdout + tier.stderr)
        self.assertIn("tactic plug-in check failed", tier.stdout)

    def test_goal_operation_gaining_lines_keeps_the_tactic_tier(self):
        # Plan row TB2: lines added to a goal operation and a batch's own tests and faults.
        self.tactic_branch({"src/front/meta-tactic/goal.fs": ": lf-goal-op ( -- ) ;\n: lf-goal-more ( -- ) ;\n",
                            "tests/front/tactics/batch-a/check.py": "", "tests/mutants/faults.d/batch-a.toml": ""})
        run = self.check()
        self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
        self.assertEqual(self.plan()["tier"], "tactic")

    def test_goal_operation_losing_lines_gets_the_full_tier(self):
        self.tactic_branch({"src/front/meta-tactic/goal.fs": ": lf-goal-op ( -- ) 1 ;\n"})
        run = self.check()
        self.assertEqual(run.returncode, 3, run.stdout + run.stderr)
        self.assertIn("changes or removes lines of a goal operation", run.stdout)
        self.assertEqual(self.plan()["tier"], "full")

    def test_no_tactic_added_is_no_tactic_branch(self):
        self.repo.write("src/front/tactics/rfl.fs", "tac-shape-plain lf-tactic: by-rfl constant tac-k-rfl \\ x\n")
        self.repo.commit("an existing tactic changed")
        run = self.check()
        self.assertEqual(run.returncode, 3)
        self.assertIn("no tactic file is added", run.stdout)
        self.assertEqual(self.plan()["tier"], "full")


if __name__ == "__main__":
    unittest.main()
