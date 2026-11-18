#!/usr/bin/env python3
"""Fuel independent of the tier's numbering (review rvSN4 B1, probe p2; ADR
0014 Amendment 7, ADR 0020 I2 and D5).

Usage: cross_snapshot.py [GFORTH]
  For each of the nine fixtures B, a snapshot of B is saved; then every
  fixture E is checked fresh and against the snapshot of each other fixture
  (check --snapshot B E: B's records first in one tier, so the records E
  shares with B get B's numbers and E's == binders may meet B's first).
  Every declaration of E must have the same verdict and the same fuel in
  both runs, and the exit status must agree. Before agent PF's fix the
  binder table gave a binder a check made the first record of its ==
  class in the whole tier, which can be B's: unfold's Implies took 34
  fuel fresh and 38 against B. Then the let pair (review rvRS F2), each
  of let-b and let-zd checked fresh and against the other's snapshot:
  let-b's B makes a let equal to let-zd's but for its name, which Lean's
  == ignores; before each == class of input lets was one node, B took 295
  fuel fresh and 302 against let-zd. Prints one line per differing
  declaration and exits 1 when any differs.
"""
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tests" / "support"))
import toolchain  # noqa: E402  (the Gforth as every test script finds it)
FIXTURES = ["tests/reference/composition.ndjson", "tests/reference/constant-fixture.ndjson",
            "tests/cli/inductive.ndjson", "tests/cli/chain.ndjson", "tests/cli/dependent.ndjson",
            "tests/cli/sibling.ndjson", "tests/cli/unfold.ndjson", "tests/cli/nested.ndjson",
            "tests/cli/sharing.ndjson"]
LETS = ["tests/cli/let-b.ndjson", "tests/cli/let-zd.ndjson"]
PAIRS = [(e, b) for e in FIXTURES for b in FIXTURES if e != b] + \
    [(e, b) for e in LETS for b in LETS if e != b]


def run(gforth, *args):
    """bin/leanforth's exit status and standard output, on the fast engine."""
    command = [str(ROOT / "bin" / "leanforth"), args[0], "--fast", *args[1:]]
    result = subprocess.run(command, cwd=ROOT, stdin=subprocess.DEVNULL, capture_output=True,
                            text=True, timeout=600, env=dict(os.environ, GFORTH=gforth))
    return result.returncode, result.stdout


def main():
    # The environment's, else this checkout's .tools, else the PATH's (a worktree has no
    # .tools: make tier's run of reference-cli exited 5 there, fix-batch-4).
    gforth = sys.argv[1] if len(sys.argv) > 1 else toolchain.gforth()
    if os.sep in gforth:
        gforth = str(Path(gforth).resolve())
    differences = pairs = 0
    with tempfile.TemporaryDirectory() as folder:
        snaps = {}
        for b in FIXTURES + LETS:
            snaps[b] = Path(folder) / (Path(b).stem + ".lfsnap")
            status, _ = run(gforth, "check", "--no-manifest", "--save-snapshot", str(snaps[b]), b)
            if status != 0 or not snaps[b].exists():
                sys.exit(f"cannot save a snapshot of {b} (exit {status})")
        fresh = {}
        for e, b in PAIRS:
            if e not in fresh:
                fresh_status, out = run(gforth, "check", "--json", "--no-manifest", e)
                fresh[e] = fresh_status, json.loads(out)["declarations"]
            fresh_status, first = fresh[e]
            pairs += 1
            status, out = run(gforth, "check", "--json", "--snapshot", str(snaps[b]),
                              "--no-manifest", e)
            got = json.loads(out)["declarations"]
            if status != fresh_status or len(got) != len(first):
                differences += 1
                print(f"{Path(e).stem} against {Path(b).stem}: exit {fresh_status} -> "
                      f"{status}, {len(first)} -> {len(got)} declarations")
                continue
            for x, y in zip(first, got):
                if (x["name"], x["verdict"], x.get("fuel")) != \
                        (y["name"], y["verdict"], y.get("fuel")):
                    differences += 1
                    print(f"{Path(e).stem} against {Path(b).stem}: {x['name']} "
                          f"{x['verdict']} {x.get('fuel')} -> {y['verdict']} "
                          f"{y.get('fuel')} ({y.get('provenance')})")
    if differences:
        sys.exit(f"{differences} difference(s) in {pairs} pairs")
    print(f"cross-snapshot: {len(FIXTURES)} fixtures and the let pair, {pairs} pairs, every "
          "declaration's verdict and fuel the same fresh and against another fixture's snapshot")


main()
