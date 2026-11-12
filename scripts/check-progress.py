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
    for p in problems:
        print("progress check: " + p)
    if not problems:
        print(f"progress check: plan stages, progress report and Now/next/later agree ({base}..HEAD)")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
