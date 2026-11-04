#!/usr/bin/env python3
"""Planted faults for the failure-path suite (plan tasks 2.2.4, 1.4.6; make check).

Usage, from the repository root (GFORTH names Gforth, as in the Makefile):
  python3 tests/core/failure_path_faults.py

The suite tests/core/failure-paths.fs runs first on the tree as it is and
must pass. Then each fault below is planted, one at a time, in a copy of
src/ and of the files the suite reads, in a temporary directory (the
working tree is never changed), and the suite must fail on it. Each fault
is a bug the suite exists to catch: a slot published before its
publication's last step, a full outcome turned into ok, a rollback
forgotten, an acceptance after an injected failure, a stale "axioms: none",
and the injection itself switched off or a THROW that no longer spends its
context. Finite evidence about the suite; it never accepts a theorem.
"""
import os
import pathlib
import shutil
import subprocess
import sys
import tempfile

GFORTH = os.environ.get("GFORTH", "gforth")
if "/" in GFORTH:  # the suite runs in a copy of the tree
    GFORTH = os.path.abspath(GFORTH)
SUITE = "tests/core/failure-paths.fs"
COPIED = ["src", "tests/support", "tests/reference"]

# (name, file, old text, new text): one deliberate bug each.
FAULTS = [
    ("publish before the final step: the slot marked final before its record",
     "src/kernel/env-publish.fs",
     "lf-env-may-write lf-env-verdict dup lf-env-recorded? if lf-env-recorded then",
     "lf-env-may-write lf-env-verdict 2dup lf-env-final drop dup lf-env-recorded?"
     " if lf-env-recorded then"),
    ("publish before the final step: accepted before the comparison (step 8)",
     "src/kernel/check-declaration.fs",
     "  lf-check-steps# 0 ?do i lf-check-do",
     "  lf-check-steps# 1- 0 ?do i lf-check-do"),
    ("map full to ok: a step that runs out of room lets the check go on",
     "src/kernel/check-declaration.fs",
     "lf-check-step! cells lf-check-steps + @ execute ;",
     "lf-check-step! cells lf-check-steps + @ execute\n"
     "  dup outcome-full = if drop outcome-ok then ;"),
    ("forget one store's rollback: the level store after each check",
     "src/core/input.fs",
     ": lf-mark-back ( mark store -- flag ) store-rollback ok? ;",
     ": lf-mark-back ( mark store -- flag )\n"
     "  dup lf-levels = if 2drop true exit then store-rollback ok? ;"),
    ("forget one store's rollback: the dependency pool after a failed publication",
     "src/kernel/env-publish.fs",
     "  dup lf-span-all-open? if lf-env-pub-mark store-rollback drop then lf-span-clear ;",
     "  lf-span-clear ;"),
    ("accept after an injected failure: a check that ends full is finished ok",
     "src/kernel/environment.fs",
     ": lf-env-finish ( outcome -- ) outcome-sane lf-env-cand lf-cand-outcome ! ;",
     ": lf-env-finish ( outcome -- )\n"
     "  outcome-sane dup outcome-full = if drop outcome-ok then\n"
     "  lf-env-cand lf-cand-outcome ! ;"),
    ("a stale \"axioms: none\": printed without reading the slot's axiom set",
     "src/kernel/check-declaration.fs",
     "  lf-env-axioms ok? if lf-check-axioms. else drop .\" axioms: ?\" then ;",
     "  lf-env-axioms ok? if drop .\" axioms: none\" else drop .\" axioms: ?\" then ;"),
    ("the injection switched off: the hook never refuses",
     "src/lib/store.fs",
     "  if store-refuse? 0= else drop false then ;",
     "  if drop true else drop false then ;"),
    ("a THROW in a check no longer spends its context",
     "src/kernel/env-publish.fs",
     "  outcome-invalid lf-env-finish lf-env-spend ;",
     "  outcome-invalid lf-env-finish ;"),
]


class Failure(Exception):
    pass


def run_suite(root):
    """The suite's exit status and its last line of output, run in root."""
    done = subprocess.run([GFORTH, SUITE], cwd=root, stdin=subprocess.DEVNULL,
                          capture_output=True, text=True, timeout=300)
    lines = (done.stdout + done.stderr).strip().splitlines()
    failed = [line for line in lines if ": " in line and "slot" in line]
    return done.returncode, (failed or lines or ["(no output)"])[-1]


def plant(root, fault):
    name, path, old, new = fault
    target = root / path
    text = target.read_text(encoding="utf-8")
    if text.count(old) != 1:
        raise Failure(f"fault {name}: the text to replace is not in {path} exactly once")
    target.write_text(text.replace(old, new), encoding="utf-8")
    return target, text


def main():
    with tempfile.TemporaryDirectory(prefix="failure-path-faults-") as workdir:
        root = pathlib.Path(workdir)
        for part in COPIED:
            shutil.copytree(part, root / part)
        (root / "tests/core").mkdir()
        shutil.copy(SUITE, root / SUITE)
        status, last = run_suite(root)
        if status != 0:
            raise Failure(f"the suite fails without a fault: {last}")
        caught = 0
        for fault in FAULTS:
            target, original = plant(root, fault)
            status, last = run_suite(root)
            target.write_text(original, encoding="utf-8")
            print(f"{'caught' if status else 'SURVIVED'}: {fault[0]}\n    {last}")
            caught += status != 0
    print(f"planted faults: {caught} of {len(FAULTS)} caught")
    if caught != len(FAULTS):
        raise Failure("a planted fault was not caught")


if __name__ == "__main__":
    try:
        main()
    except (Failure, subprocess.TimeoutExpired) as error:
        print(f"failure_path_faults.py: {error}", file=sys.stderr)
        sys.exit(1)
