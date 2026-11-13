#!/usr/bin/env python3
"""Fail if Lean reference checks could pass without a real proof.

Usage: python3 scripts/check-lean-sources.py   (run from the repository root)

Two static guards, both needing no Lean installation:

1. No Lean file under tests/ may use `sorry`, `admit`, `native_decide`,
   `axiom` declarations or a `warningAsError` override, except the entries
   in ALLOWED below. `native_decide` trusts Lean's compiler, and the owner's
   axiom policy (docs/project/OWNER_DECISIONS.md) never allows that.
2. Every Lean invocation that elaborates a file in a test script must pass
   `-DwarningAsError=true`, so that `sorry` and other warnings fail the run.
   tests/reference/sorry-must-fail.lean checks that this flag works.

Exits 1 and lists each problem, or prints a summary and exits 0.
"""
import pathlib
import re
import subprocess
import sys

FORBIDDEN = re.compile(r"\b(sorry|admit|native_decide|axiom|warningAsError)\b")
# (file, forbidden word, declared name or None) -> reason.
ALLOWED = {
    ("tests/reference/sorry-must-fail.lean", "sorry", None):
        "negative fixture that must be rejected",
    ("tests/front/tactic-run.lean", "sorry", None):
        "Lean twins of LeanForth's by-sorry (plan FE1g-3): check_tactics.py --lean expects "
        "Lean's sorry message, an error under -DwarningAsError=true, and sorryAx",
    **{("tests/reference/mixed-beta-table.lean", "axiom", name):
       "opaque test constant in a Lean-only comparison table"
       for name in ("mixedBetaC", "mixedBetaD", "mixedBetaF")},
    **{("tests/reference/mixed-convert-table.lean", "axiom", name):
       "opaque test constant in a Lean-only comparison table"
       for name in ("mixedConvertC", "mixedConvertD", "mixedConvertF")},
}
FLAG = "-DwarningAsError=true"
# A call is the Lean executable followed directly by its first argument.
# `LEAN="$lean" bash other.sh` passes the path on and is not a call.
SHELL_CALL = re.compile(r'"\$lean" +(?P<first>\S+)')
PYTHON_CALL = re.compile(r"\[(?:LEAN|lean|lean_path|LEAN_PATH), *(?P<first>[^,\]]+)")


def candidate_files(pattern):
    listing = subprocess.check_output(
        ["git", "ls-files", "--cached", "--others", "--exclude-standard", pattern],
        text=True)
    return [p for p in sorted(set(listing.splitlines())) if pathlib.Path(p).exists()]


def strip_comments(text):
    """Blank out Lean comments, keeping line numbers. Block comments may nest."""
    out, depth, i = [], 0, 0
    while i < len(text):
        two = text[i:i + 2]
        if two == "/-":
            depth, i = depth + 1, i + 2
            out.append("  ")
        elif two == "-/" and depth:
            depth, i = depth - 1, i + 2
            out.append("  ")
        elif two == "--" and not depth:
            end = text.find("\n", i)
            end = len(text) if end < 0 else end
            out.append(" " * (end - i))
            i = end
        else:
            out.append(text[i] if not depth or text[i] == "\n" else " ")
            i += 1
    return "".join(out)


def lean_problems(path):
    code = strip_comments(pathlib.Path(path).read_text(encoding="utf-8"))
    for number, line in enumerate(code.splitlines(), 1):
        for match in FORBIDDEN.finditer(line):
            word = match.group(1)
            name = None
            if word == "axiom":
                declared = re.match(r"\s*(\S+)", line[match.end():])
                name = declared.group(1) if declared else None
            if (path, word, name) not in ALLOWED:
                yield f"{path}:{number}: forbidden `{word}`" + (f" {name}" if name else "")


def invocation_problems(path):
    text = pathlib.Path(path).read_text(encoding="utf-8")
    pattern = PYTHON_CALL if path.endswith(".py") else SHELL_CALL
    for match in pattern.finditer(text):
        first = match.group("first").strip("\"'();")
        elaborates = (first in ("-o", "--run") or first.startswith("tests/")
                      or first.endswith(".lean"))
        if elaborates:
            number = text.count("\n", 0, match.start()) + 1
            yield f"{path}:{number}: Lean invocation without {FLAG}"


def main():
    lean_files = candidate_files("tests/*.lean")
    scripts = candidate_files("tests/*.sh") + candidate_files("tests/*.py") \
        + candidate_files("scripts/*.sh")
    problems = [p for f in lean_files for p in lean_problems(f)]
    problems += [p for f in scripts for p in invocation_problems(f)]
    for problem in problems:
        print(problem, file=sys.stderr)
    if problems:
        print(f"{len(problems)} Lean source or invocation problem(s).", file=sys.stderr)
        return 1
    print(f"Lean sources clean ({len(lean_files)} files); "
          f"all Lean invocations in {len(scripts)} scripts use {FLAG}.")
    return 0


sys.exit(main())
