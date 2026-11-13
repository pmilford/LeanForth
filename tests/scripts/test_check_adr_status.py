#!/usr/bin/env python3
"""Tests of scripts/check-adr-status.py: every ADR and amendment needs a well-formed approval-status line."""
import importlib.util
import pathlib
import subprocess
import sys
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("cas", ROOT / "scripts/check-adr-status.py")
cas = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cas)

OK_ACCEPTED = ("Approval status: accepted 2026-11-03, gate: kernel, "
               "[OWNER_DECISIONS.md](../project/OWNER_DECISIONS.md) section \"X\"")
UNCLEAR = "Approval status: status unclear (no owner decision found)"


def adr(*parts):
    return "\n".join(["# ADR 9999: t", "", "Status: x", ""] + list(parts))


class Values(unittest.TestCase):
    def test_allowed_values(self):
        for v in ("proposed", "proposed (note)", "superseded by ADR 0099",
                  "status unclear (no owner decision found); more", OK_ACCEPTED[len("Approval status: "):]):
            self.assertIsNone(cas.value_problem(v), v)

    def test_refused_values(self):
        for v in ("approved", "accepted", "accepted 2026-11-03", "accepted 2026-11-03, gate: kernel",
                  "accepted by the owner, gate: kernel, OWNER_DECISIONS.md",
                  "accepted 2026-11-03, OWNER_DECISIONS.md", "status unclear", "draft", ""):
            self.assertIsNotNone(cas.value_problem(v), v)


class Documents(unittest.TestCase):
    def test_plain_adr_ok(self):
        self.assertEqual(cas.problems_in("a.md", adr(UNCLEAR, "", "## Goal", "text")), [])

    def test_missing_adr_line(self):
        self.assertEqual(len(cas.problems_in("a.md", adr("## Goal", "text"))), 1)

    def test_amendment_needs_its_own_line(self):
        text = adr(UNCLEAR, "", "## Amendment 1: x", "", "text")
        self.assertEqual(len(cas.problems_in("a.md", text)), 1)
        text = adr(UNCLEAR, "", "## Amendment 1: x", "", OK_ACCEPTED, "", "text")
        self.assertEqual(cas.problems_in("a.md", text), [])

    def test_amendment_line_of_a_neighbour_does_not_count(self):
        text = adr(UNCLEAR, "", "## Amendment 1: x", "", OK_ACCEPTED, "", "## Amendment 2: y", "", "text")
        problems = cas.problems_in("a.md", text)
        self.assertEqual(len(problems), 1)
        self.assertIn("Amendment 2", problems[0])

    def test_sub_heading_amendment_is_found(self):
        self.assertEqual(len(cas.problems_in("a.md", adr(UNCLEAR, "", "### Amendment (x)", "text"))), 1)

    def test_malformed_line_reported(self):
        self.assertEqual(len(cas.problems_in("a.md", adr("Approval status: approved", ""))), 1)

    def test_line_in_code_fence_ignored(self):
        text = adr("```", UNCLEAR, "```", "## Goal")
        self.assertEqual(len(cas.problems_in("a.md", text)), 1)


class Repository(unittest.TestCase):
    def test_every_real_adr_passes(self):
        done = subprocess.run([sys.executable, str(ROOT / "scripts/check-adr-status.py")],
                              capture_output=True, text=True)
        self.assertEqual(done.returncode, 0, done.stdout)


if __name__ == "__main__":
    unittest.main()
