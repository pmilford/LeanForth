#!/usr/bin/env python3
"""Fail unless the Claude Code and Codex agent definitions agree (AGENTS.md: keep equivalent definitions in sync).

Usage: python3 scripts/check-agent-sync.py   (run from the repository root)

Compares each .claude/agents/NAME.md with .codex/agents/NAME.toml (a hyphen in one is an underscore in the other):

1. the same set of agent names in both folders;
2. each agent's instructions (the Markdown body, the TOML developer_instructions) contain every key phrase listed
   for it in KEY_PHRASES below, after collapsing white space and dropping backticks and case;
3. the two texts are at least MIN_SIMILARITY alike, so a rewritten instruction cannot drift unnoticed.

An agent with no entry in KEY_PHRASES fails: add its key sections there when adding the agent.
"""
import difflib
import pathlib
import re
import sys
import tomllib

ROOT = pathlib.Path(__file__).resolve().parent.parent
MIN_SIMILARITY = 0.8
KEY_PHRASES = {
    "done-checker": (
        "never modify tracked files", "docs/development/DONE_CHECKER.md", "A user can", "real input the claim implies",
        "placeholders", "CPU mode", "Do not spawn agents", "at most 60 lines", "stage reached",
    ),
    "forth-reviewer": (
        "do not modify files", "TEST_COVERAGE_REVIEW.md", "docs/development/FORTH_STYLE.md",
        "forth-metrics.py --words 10", "words longer than five lines", "VARIABLEs used as registers",
        "emulated locals", "BEGIN-STRUCTURE", "PICK/ROLL", "Trace all success and failure paths",
        "Forth-2012 portability", "human review of trusted semantics",
    ),
    "architect": (
        "You do not review a diff", "change no file except the report", "docs/development/FORTH_LIBRARY.md",
        "private words inside feature files", "What the next five slices need in common", "Density",
        "Collisions", "Interfaces", "Estimates", "at most ten recommendations", "only the kernel accepts a proof",
    ),
}


def normal(text):
    return re.sub(r"\s+", " ", text.replace("`", "")).strip().lower()


def claude_agents(folder):
    """Return {name: instructions} from Markdown files with a front-matter block."""
    found = {}
    for path in sorted(folder.glob("*.md")):
        parts = path.read_text(encoding="utf-8").split("---", 2)
        meta = re.search(r"^name:\s*(\S+)", parts[1], re.M) if len(parts) == 3 else None
        found[meta.group(1) if meta else path.stem] = parts[2] if len(parts) == 3 else ""
    return found


def codex_agents(folder):
    found = {}
    for path in sorted(folder.glob("*.toml")):
        data = tomllib.loads(path.read_text(encoding="utf-8"))
        found[data.get("name", path.stem)] = data.get("developer_instructions", "")
    return found


def sync_problems(claude, codex):
    """Compare two {name: instructions} dictionaries; return a list of problems."""
    claude = {k.replace("_", "-"): v for k, v in claude.items()}
    codex = {k.replace("_", "-"): v for k, v in codex.items()}
    problems = [f"agent {n} exists only for Codex" for n in sorted(set(codex) - set(claude))]
    problems += [f"agent {n} exists only for Claude Code" for n in sorted(set(claude) - set(codex))]
    for name in sorted(set(claude) & set(codex)):
        a, b = normal(claude[name]), normal(codex[name])
        if name not in KEY_PHRASES:
            problems.append(f"agent {name}: no entry in KEY_PHRASES of check-agent-sync.py")
        for phrase in KEY_PHRASES.get(name, ()):
            for side, text in (("Claude Code", a), ("Codex", b)):
                if normal(phrase) not in text:
                    problems.append(f"agent {name}: {side} instructions lack the key phrase '{phrase}'")
        if not a or not b:
            problems.append(f"agent {name}: empty instructions")
        else:
            ratio = difflib.SequenceMatcher(None, a, b).ratio()
            if ratio < MIN_SIMILARITY:
                problems.append(f"agent {name}: instructions only {ratio:.2f} alike (needs {MIN_SIMILARITY})")
    return problems


def main():
    claude = claude_agents(ROOT / ".claude/agents")
    codex = codex_agents(ROOT / ".codex/agents")
    problems = sync_problems(claude, codex)
    for p in problems:
        print("agent sync: " + p)
    if not problems:
        print(f"agent sync: {len(claude)} agents defined alike for Claude Code and Codex")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
