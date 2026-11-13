#!/usr/bin/env python3
"""Check that status reporting follows the owner's rules (2026-11-12). Run by scripts/push.sh before every push.

Usage: python3 scripts/check-progress.py [BASE]      (BASE defaults to origin/main; the range checked is BASE..HEAD)

1. Stage words. A plan row (docs/project/PLAN_DRAFT.md) whose status is dated 2026-11-13 or later uses one of the
   stages of docs/development/DONE_CHECKER.md: not started, designed, written, tested alone, integrated, works end to
   end, done; and a row that says done links a done-checker report (docs/development/done-checks/).
2. Progress kept with the plan. When BASE..HEAD changes any plan row's status, it also changes
   docs/project/PROJECT_PROGRESS.md.
3. Now, next, later. PROJECT_PROGRESS.md has a section "## Now, next, later (updated YYYY-MM-DD)" whose date is not
   older than the newest commit in BASE..HEAD that changed a plan row's status.
4. Kernel changes with their decision. When BASE..HEAD changes src/kernel/*.fs, it also changes an ADR (docs/adr/) or
   docs/project/OWNER_DECISIONS.md, so a kernel change never lands without its written rule or decision.
5. The Mathlib line. PROJECT_PROGRESS.md has a paragraph starting "**Mathlib checked:**" that gives "N of M" (the
   denominator) and cites the run it comes from: the words "run record" or "run log" and a path in .claude/work/,
   done-checks/, measurements/ or a .log file.
"""
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
PLAN = "docs/project/PLAN_DRAFT.md"
PROGRESS = "docs/project/PROJECT_PROGRESS.md"
STAGES = ("not started", "designed", "written", "tested alone", "integrated", "works end to end", "done")
STATUS = re.compile(r"\*\*Status \((\d{4}-\d{2}-\d{2})\): ([^.*;(]*)")
NNL = re.compile(r"^## Now, next, later \(updated (\d{4}-\d{2}-\d{2})\)", re.M)
RULE_START = "2026-11-13"
MATHLIB = re.compile(r"^\*\*Mathlib checked:\*\*(.*)$", re.M)
FRACTION = re.compile(r"\d[\d,]* of \d[\d,]*")
RUN_CITATION = re.compile(r"run (record|log)", re.I)
RUN_PATH = re.compile(r"(\.claude/work/|done-checks/|measurements/|\.log\b)")


def git(*args):
    return subprocess.run(["git", *args], cwd=ROOT, capture_output=True, text=True, check=True).stdout


def stage_problems(text):
    problems = []
    for line in text.splitlines():
        if not line.startswith("| "):
            continue
        for date, words in STATUS.findall(line):
            if date < RULE_START:
                continue
            row = line.split("|")[1].strip()
            stage = words.strip().lower()
            if not stage.startswith(STAGES):
                problems.append(f"plan row {row}: status '{words.strip()}' is not one of the stages {STAGES}")
            elif stage.startswith("done") and "done-checks/" not in line:
                problems.append(f"plan row {row}: says done without a done-checker report (done-checks/)")
    return problems


def mathlib_problems(text):
    """The progress report's Mathlib line names its denominator and the run it comes from."""
    found = MATHLIB.search(text)
    if not found:
        return ['PROJECT_PROGRESS.md has no paragraph starting "**Mathlib checked:**"']
    line, problems = found.group(1), []
    if not FRACTION.search(line):
        problems.append('the "Mathlib checked" line gives no "N of M" with its denominator')
    if not (RUN_CITATION.search(line) and RUN_PATH.search(line)):
        problems.append('the "Mathlib checked" line cites no run record or log (words "run record" and a path)')
    return problems


def status_commits(base):
    commits = []
    for c in git("rev-list", f"{base}..HEAD", "--", PLAN).split():
        diff = git("show", "--format=", "-U0", c, "--", PLAN)
        if any(l.startswith(("+", "-")) and "**Status (" in l for l in diff.splitlines()):
            commits.append(c)
    return commits


def main(argv):
    base = argv[0] if argv else "origin/main"
    problems = stage_problems((ROOT / PLAN).read_text(encoding="utf-8"))
    problems += mathlib_problems((ROOT / PROGRESS).read_text(encoding="utf-8"))
    changed = status_commits(base)
    if changed:
        if PROGRESS not in git("diff", "--name-only", f"{base}..HEAD").split():
            problems.append(f"{base}..HEAD changes plan statuses but not {PROGRESS}")
        found = NNL.search((ROOT / PROGRESS).read_text(encoding="utf-8"))
        newest = max(git("log", "-1", "--format=%cs", c).strip() for c in changed)
        if not found:
            problems.append(f"{PROGRESS} has no '## Now, next, later (updated YYYY-MM-DD)' section")
        elif found.group(1) < newest:
            problems.append(f"Now, next, later dated {found.group(1)}, older than plan changes of {newest}")
    changed_files = git("diff", "--name-only", f"{base}..HEAD").split()
    if any(f.startswith("src/kernel/") and f.endswith(".fs") for f in changed_files) and not any(
            f.startswith("docs/adr/") or f == "docs/project/OWNER_DECISIONS.md" for f in changed_files):
        problems.append(f"{base}..HEAD changes src/kernel without an ADR or OWNER_DECISIONS.md change")
    for p in problems:
        print("progress check: " + p)
    if not problems:
        print(f"progress check: plan stages, progress report and Now/next/later agree ({base}..HEAD)")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
