#!/usr/bin/env python3
"""Fail unless every ADR and every ADR amendment carries an approval-status line (owner process audit, 2026-11-12).

Usage: python3 scripts/check-adr-status.py   (run from the repository root)

An ADR (a file of the docs/adr folder) has a line "Approval status: ..." before its first "## " heading; each heading that
contains "Amendment" has one before the next heading. The line begins with one of:

  proposed
  accepted DATE, gate: GATES, ... OWNER_DECISIONS.md ...   (DATE is YYYY-MM-DD; GATES names the gate approved, or
                                                          "not stated" when the owner's entry names none)
  superseded by ...
  status unclear (no owner decision found)

An "accepted" line names the date and the gate and cites OWNER_DECISIONS.md. Facts come only from that file and
the ADRs; where approval is unclear the line says so rather than guessing.
"""
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
LINE = re.compile(r"^Approval status: (.*)$")
ACCEPTED = re.compile(r"^accepted \d{4}-\d{2}-\d{2}\b.*\bgate: \S.*OWNER_DECISIONS\.md")
OTHER = ("proposed", "superseded by ", "status unclear (no owner decision found)")
HEADING = re.compile(r"^(#+) (.*)$")


def value_problem(value):
    """Return why an approval-status value is not allowed, or None."""
    if value.startswith("accepted"):
        return None if ACCEPTED.match(value) else "accepted needs a date, 'gate: ...' and OWNER_DECISIONS.md"
    if value.startswith(OTHER):
        return None
    return "must start with proposed, accepted, superseded by, or status unclear (no owner decision found)"


def sections(text):
    """Yield (label, [approval-status values]) for the ADR itself and each Amendment heading."""
    label, values, in_fence = "the ADR itself", [], False
    for line in text.splitlines():
        if line.startswith("```"):
            in_fence = not in_fence
        if in_fence:
            continue
        head = HEADING.match(line)
        if head and (len(head.group(1)) == 2 or "Amendment" in head.group(2)):
            yield label, values
            label, values = (head.group(2) if "Amendment" in head.group(2) else None), []
            if label is None:
                label = "(other section)"
            continue
        found = LINE.match(line)
        if found:
            values.append(found.group(1))
    yield label, values


def problems_in(name, text):
    problems = []
    for label, values in sections(text):
        if label == "(other section)":
            continue
        if not values:
            problems.append(f"{name}: {label}: no 'Approval status:' line")
        for value in values:
            why = value_problem(value)
            if why:
                problems.append(f"{name}: {label}: {why}")
    return problems


def main():
    problems, count = [], 0
    for path in sorted((ROOT / "docs/adr").glob("[0-9][0-9][0-9][0-9]-*.md")):
        problems += problems_in(path.name, path.read_text(encoding="utf-8"))
        count += 1
    for p in problems:
        print("adr status: " + p)
    if not problems:
        print(f"adr status: {count} ADRs and their amendments all carry an approval-status line")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
