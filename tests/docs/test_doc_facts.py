#!/usr/bin/env python3
"""Facts the documentation restates, checked against what they restate.

These checks read frequently edited pages (the progress page, the user manuals, the
roadmap). They were part of the command line's tests (tests/cli/test_leanforth.py) and
the program receipts' tests (tests/program/test_receipts.py) until 2026-11-18, which
made every status update re-run those slow targets under per-target reuse (a target
runs again when any file its test programs read changes). Here they form one small
target, make test-doc-facts, with exactly the same assertions:

1. The progress page records the full-Mathlib run the capabilities text states:
   729,263 of 729,263 accepted on build b74a04d (the command line's tests check that
   `leanforth capabilities` says the same).
2. The command line's manual gives help's exit codes in tally.fs's order of severity
   (FRP review C2: user text that restates the codes must not go stale).
3. The AI guide names the current program-receipt schema, and no page of the current
   state names the superseded schema 0.1 (re-review D of the receipts).
Each check also refuses a planted wrong copy of its page, so it cannot pass vacuously.
Python standard library only; runs no Forth and no Lean.

Usage (from the repository root): python3 tests/docs/test_doc_facts.py
"""
import re
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
PROGRESS = ROOT / "docs/project/PROJECT_PROGRESS.md"
MANUAL = ROOT / "docs/user/COMMAND_LINE.md"
TALLY = ROOT / "src/cli/tally.fs"
# tests/program/test_receipts.py's SCHEMA: the program-receipt schema the reader writes.
SCHEMA = Path("schemas/program-receipt-0.3.schema.json")
AI_DOC = ROOT / "docs/user/AI_TOOLS.md"
CURRENT_STATE = ("docs/user/AI_TOOLS.md", "docs/README.md", "docs/user/WORKFLOWS.md",
                 "docs/programming/INTERFACE_CONTRACTS.md", "docs/programming/PROGRAM_VC.md",
                 "docs/development/MINIFORTH_REVIEW.md", "docs/project/DEVELOPMENT_ROADMAP.md",
                 "docs/project/PROJECT_PROGRESS.md")


def severity_order():
    """The exit codes, most severe first, from tally.fs's cli-severity table."""
    tally = TALLY.read_text()
    table = re.search(r"^create cli-severity((?:\s+\d+ ,)+)", tally, re.M).group(1)
    ranks = [int(rank) for rank in table.replace(",", " ").split()]
    return sorted(range(len(ranks)), key=lambda code: -ranks[code])


class ProgressPage(unittest.TestCase):
    def mathlib_recorded(self, progress):
        self.assertRegex(progress, r"729,263 of\s+729,263 accepted\*\* on build `b74a04d`")

    def test_mathlib_count_and_build(self):
        self.mathlib_recorded(PROGRESS.read_text())

    def test_a_wrong_count_is_refused(self):
        wrong = PROGRESS.read_text().replace("729,263 of", "729,262 of")
        with self.assertRaises(AssertionError):
            self.mathlib_recorded(wrong)


class CommandLineManual(unittest.TestCase):
    def order_given(self, manual):
        manual = " ".join(manual.split())
        self.assertIn(f"the order {', '.join(str(code) for code in severity_order())}:", manual)

    def test_exit_codes_in_tally_order(self):
        self.order_given(MANUAL.read_text())

    def test_a_wrong_order_is_refused(self):
        order = ", ".join(str(code) for code in severity_order())
        swapped = ", ".join(str(code) for code in reversed(severity_order()))
        with self.assertRaises(AssertionError):
            self.order_given(MANUAL.read_text().replace(f"the order {order}:", f"the order {swapped}:"))


class ReceiptPages(unittest.TestCase):
    """Finding 2 of the receipts' review: the documents an AI reads describe the current
    receipt."""
    stale = re.compile(r"schema,? 0\.1\b|0\.1 kept readable")

    def names_current_schema(self, text):
        self.assertIn(str(SCHEMA), text)
        self.assertNotIn("no receipt is generated yet", text)

    def test_ai_guide_names_the_current_schema(self):
        self.names_current_schema(AI_DOC.read_text(encoding="utf-8"))

    def test_current_state_documents_do_not_name_the_superseded_schema(self):
        """Re-review D: documents of the current state say 0.2 (the decision log keeps history)."""
        for path in CURRENT_STATE:
            with self.subTest(path=path):
                self.assertEqual(self.stale.findall((ROOT / path).read_text(encoding="utf-8")), [])

    def test_wrong_copies_are_refused(self):
        with self.assertRaises(AssertionError):
            self.names_current_schema(AI_DOC.read_text(encoding="utf-8").replace(str(SCHEMA), "x"))
        self.assertTrue(self.stale.findall("the receipt schema 0.1 is current"))


if __name__ == "__main__":
    unittest.main()
