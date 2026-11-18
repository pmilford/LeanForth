#!/usr/bin/env python3
"""Tests of scripts/check-agent-sync.py: Claude Code and Codex agent definitions stay equivalent."""
import importlib.util
import pathlib
import subprocess
import sys
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("cas", ROOT / "scripts/check-agent-sync.py")
cas = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cas)

REAL = (cas.claude_agents(ROOT / ".claude/agents"), cas.codex_agents(ROOT / ".codex/agents"))


def pair():
    return dict(REAL[0]), dict(REAL[1])


class Sync(unittest.TestCase):
    def test_real_definitions_agree(self):
        self.assertEqual(cas.sync_problems(*REAL), [])

    def test_both_agents_found_with_either_spelling(self):
        self.assertEqual(sorted(REAL[0]), ["architect", "done-checker", "forth-reviewer"])
        self.assertEqual(sorted(REAL[1]), ["architect", "done_checker", "forth_reviewer"])

    def test_agent_only_on_one_side(self):
        claude, codex = pair()
        del codex["done_checker"]
        self.assertEqual(len(cas.sync_problems(claude, codex)), 1)
        claude, codex = pair()
        codex["extra"] = "x"
        self.assertEqual(len(cas.sync_problems(claude, codex)), 1)

    def test_dropped_key_sentence_is_found_on_either_side(self):
        claude, codex = pair()
        claude["forth-reviewer"] = claude["forth-reviewer"].replace("emulated locals", "something else")
        self.assertTrue(any("Claude Code" in p and "emulated locals" in p for p in cas.sync_problems(claude, codex)))
        claude, codex = pair()
        codex["forth_reviewer"] = codex["forth_reviewer"].replace("emulated locals", "something else")
        self.assertTrue(any("Codex" in p and "emulated locals" in p for p in cas.sync_problems(claude, codex)))

    def test_rewritten_instructions_drift(self):
        claude, codex = pair()
        codex["done_checker"] = " ".join(cas.KEY_PHRASES["done-checker"]) + " unrelated words " * 80
        self.assertTrue(any("alike" in p for p in cas.sync_problems(claude, codex)))

    def test_unlisted_agent_fails(self):
        claude, codex = pair()
        claude["new-agent"], codex["new_agent"] = "same text", "same text"
        self.assertEqual(len(cas.sync_problems(claude, codex)), 1)

    def test_empty_instructions(self):
        claude, codex = pair()
        codex["done_checker"] = ""
        self.assertTrue(any("empty" in p for p in cas.sync_problems(claude, codex)))

    def test_command_passes(self):
        done = subprocess.run([sys.executable, str(ROOT / "scripts/check-agent-sync.py")], capture_output=True, text=True)
        self.assertEqual(done.returncode, 0, done.stdout)


if __name__ == "__main__":
    unittest.main()
