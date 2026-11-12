#!/usr/bin/env python3
"""Pinned Lean against LeanForth on tests/cli/shared-depths.lean (review rvS36
probes P1 and P2; plan task 4.2.7, ADR 0014 Amendments 3 and 4; P3, three
perf ladders of the Lean Kernel Arena at n = 48, agent PF, Amendment 6; P4,
proof irrelevance typing 48-argument spines aside, agent R5, Amendment 8).

Usage: shared_depths.py LEAN [GFORTH]
  Runs LEAN (the pinned 4.35.0 binary) on shared-depths.lean, which prints a
  `row<TAB>id<TAB>verdict` line per case and then the case's export between
  `ndjson-begin<TAB>id` and `ndjson-end`. Each export is checked by
  bin/leanforth two ways: as it is, and with the audit memo off (the memo is an
  optimisation: tests/cli/audit-memo-off.fs), and the exit status must be 0
  where Lean accepts and, where Lean rejects, 1 (rejected) or 4 (invalid: a
  loose bound variable, which the checker finds in its entry audit before
  Lean's kernel would), never 0 or anything else.
P3's and P4's good rows must also stay below their fuel bounds (FUEL_BOUNDS).
Prints one line per case and exits 1 when any case differs.
"""
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "tests" / "cli" / "shared-depths.lean"
MEMO_OFF = ROOT / "tests" / "cli" / "audit-memo-off.fs"
EXPECTED_ROWS = 27   # P1 has 12, P2 has 7, P3 has 6, P4 has 2
# P3's good rows (agent PF): the fuel `check --json` reports for the row's
# declaration stays below these bounds, about 10% above what it was on
# 2026-11-11 (13,250, 18,060 and 13,157): a guard against a pass whose work
# grows with the paths or the depth instead of the nodes (ADR 0014,
# Amendment 6). Lean's own work on these ladders grows as n squared.
# P4's good row (agent R5): 15,749 on 2026-11-11, 25,063 before an
# application aside was typed from its spine's head (ADR 0014, Amendment 8).
FUEL_BOUNDS = {"letgood": ("PF_letgood", 14600), "betagood": ("PF_betagood", 19900),
               "appgood": ("PF_appgood", 14500), "spinegood": ("Spine.good", 17300)}


def lean_cases(lean):
    """The (id, verdict, export text) of every case Lean prints."""
    toolchain = Path(subprocess.run([lean, "--print-prefix"], capture_output=True, text=True,
                                    check=True).stdout.strip())
    env = dict(os.environ, LEAN_PATH=str(toolchain / "lib" / "lean"))
    run = subprocess.run([lean, "-DwarningAsError=true", str(SOURCE)], env=env,
                         stdin=subprocess.DEVNULL, capture_output=True, text=True, timeout=600)
    if run.returncode != 0:
        sys.exit(f"Lean failed on {SOURCE}:\n{run.stdout[-2000:]}{run.stderr[-2000:]}")
    rows, exports, current, body = {}, {}, None, []
    for line in run.stdout.splitlines(keepends=True):
        if line.startswith("row\t"):
            _, case, verdict = line.rstrip("\n").split("\t", 2)
            rows[case] = verdict
        elif line.startswith("ndjson-begin\t"):
            current, body = line.rstrip("\n").split("\t")[1], []
        elif line.startswith("ndjson-end"):
            exports[current], current = "".join(body), None
        elif current is not None:
            body.append(line)
    if len(rows) != EXPECTED_ROWS or sorted(rows) != sorted(exports):
        sys.exit(f"expected {EXPECTED_ROWS} cases with exports, got rows {sorted(rows)}")
    return [(case, rows[case], exports[case]) for case in rows]


def leanforth(gforth, path, memo_off):
    """The exit status of `leanforth check --no-manifest --fast path`, and its text."""
    if memo_off:
        command = [gforth, str(ROOT / "src" / "main.fs"), str(MEMO_OFF), "-e", "cli-main",
                   "check", "--no-manifest", str(path)]
    else:
        command = [str(ROOT / "bin" / "leanforth"), "check", "--no-manifest", "--fast", str(path)]
    run = subprocess.run(command, stdin=subprocess.DEVNULL, capture_output=True, text=True,
                         timeout=600, env=dict(os.environ, GFORTH=gforth))
    status = run.returncode - 100 if memo_off else run.returncode
    return status, run.stdout + run.stderr


def fuel_of(path, name):
    """The fuel `leanforth check --json` reports for declaration name."""
    run = subprocess.run([str(ROOT / "bin" / "leanforth"), "check", "--no-manifest", "--fast",
                          "--json", str(path)], stdin=subprocess.DEVNULL, capture_output=True,
                         text=True, timeout=600)
    fuel = {d["name"]: d["fuel"] for d in json.loads(run.stdout)["declarations"]}
    return fuel[name]


def main():
    lean = sys.argv[1]
    gforth = sys.argv[2] if len(sys.argv) > 2 else os.environ.get(
        "GFORTH", str(ROOT / ".tools" / "gforth" / "bin" / "gforth-fast"))
    if os.sep in gforth:
        gforth = str(Path(gforth).resolve())
    failures = 0
    with tempfile.TemporaryDirectory() as folder:
        for case, verdict, export in lean_cases(lean):
            path = Path(folder) / f"{case}.ndjson"
            path.write_text(export, encoding="utf-8")
            want = {0} if verdict == "accepted" else {1, 4}
            results = [leanforth(gforth, path, off)[0] for off in (False, True)]
            ok = all(status in want for status in results)
            failures += not ok
            print(f"{case}: Lean {verdict.split(':')[0]}; LeanForth exit {results[0]}, "
                  f"audit memo off {results[1]}" + ("" if ok else f"  DIFFERENT (want {sorted(want)})"))
            if case in FUEL_BOUNDS:
                name, bound = FUEL_BOUNDS[case]
                fuel = fuel_of(path, name)
                failures += fuel >= bound
                print(f"{case}: fuel {fuel}" + ("" if fuel < bound else f"  NOT BELOW {bound}"))
    if failures:
        sys.exit(f"{failures} case(s) differ from pinned Lean")
    print(f"shared-depths: {EXPECTED_ROWS} cases agree with pinned Lean, memo on and off")


main()
