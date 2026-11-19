#!/usr/bin/env python3
"""parallel-init: all of Lean's Init checked at --jobs 8 and at --jobs 1 (plan 9.4.8p (1);
make parallel-init, part of make daily, never of make check or a tier).

Usage (from anywhere in the checkout):
  python3 scripts/parallel-init.py [--init EXPORT] [--jobs N] [--gforth-fast GFORTH]
                                   [--out DIR] [--record-dir DIR] [--timeout SECONDS]

  --init EXPORT        Lean's Init as a lean4export NDJSON file (default, as
                       scripts/engine-gate.sh: .claude/work/IM/init.ndjson of the
                       main checkout); machine-local and not in the repository.
  --jobs N             the parallel run's workers (default 8).
  --gforth-fast PATH   the engine (default: GFORTH_FAST, else the gforth-fast of
                       this checkout's .tools, else on PATH): users' default engine.
  --out DIR            where the runs' outputs and snapshots go, overwritten each
                       time (default: .claude/work/parallel-init of the main checkout).
  --record-dir DIR     where the record of the run is written (default:
                       .claude/work/ci/parallel-init of the main checkout, beside
                       scripts/tested-tree.py's records).
  --timeout SECONDS    per run (default 7200).

bin/leanforth check runs four times on the same export with the same engine: text
with --resources and --save-snapshot, and --json, each at --jobs N and at --jobs 1.
It requires, between --jobs N and --jobs 1:
  - the same exit code of each pair;
  - the same text up to the resource report (the snapshot line's file name aside);
  - the same JSON report but for "measured" (times, memory, workers);
  - the same snapshot but for its information section (kind 17: LeanForth's
    version, commit, host and engine), section by section: kind, unit size,
    count and SHA-256 from the table, and the caller's header fields;
  - in the parallel run's resource report: not ready 0, forced 0, workers
    replaced 0 (the plan held and no check threw).
It prints both wall times and the speed-up and records them, with the result, in a
JSON file named by date and commit under the record folder.

Exit status: 0 everything identical; 1 a difference; 4 the Init export or the engine
is missing (skipped: said so, never a pass) or bad usage; 5 a run that timed out,
crashed or left no output.
"""

import argparse
import datetime
import json
import os
import re
import shutil
import struct
import subprocess
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
INFO_KIND = 17  # src/kernel/env-snapshot.fs: the information section (position 16, kind 17)
SCHED = re.compile(r"checks handed out (\d+), run again (\d+), not ready (\d+), "
                   r"forced (\d+), workers replaced (\d+)")
SNAPSHOT_LINE = re.compile(r"^snapshot: written to .*$", re.MULTILINE)


def main_checkout():
    """The main checkout of this repository (a worktree's common git folder's parent)."""
    try:
        common = subprocess.run(["git", "-C", ROOT, "rev-parse", "--path-format=absolute",
                                 "--git-common-dir"], capture_output=True, text=True,
                                check=True).stdout.strip()
        return os.path.dirname(common) if common.endswith("/.git") else ROOT
    except (OSError, subprocess.CalledProcessError):
        return ROOT


def git(*args):
    result = subprocess.run(["git", "-C", ROOT, *args], capture_output=True, text=True)
    return result.stdout.strip() if result.returncode == 0 else ""


def default_fast():
    named = os.environ.get("GFORTH_FAST")
    if named:
        return named
    local = os.path.join(ROOT, ".tools/gforth/bin/gforth-fast")
    return local if os.access(local, os.X_OK) else (shutil.which("gforth-fast") or "")


def run(args, gforth, out, timeout):
    """bin/leanforth check ARGS: (exit status, stdout, wall seconds); status None when it
    timed out."""
    env = dict(os.environ, GFORTH=gforth)
    started = time.monotonic()
    with open(out, "wb") as stream:
        try:
            status = subprocess.run([os.path.join(ROOT, "bin/leanforth"), "check", *args],
                                    stdin=subprocess.DEVNULL, stdout=stream,
                                    stderr=subprocess.DEVNULL, env=env,
                                    timeout=timeout).returncode
        except subprocess.TimeoutExpired:
            status = None
    seconds = time.monotonic() - started
    with open(out, encoding="utf-8", errors="replace") as stream:
        return status, stream.read(), seconds


def verdict_text(text):
    """The text report up to its resource report, the snapshot's file name left out."""
    head = text.split("\nresources:\n", 1)[0]
    return SNAPSHOT_LINE.sub("snapshot: written", head)


def sched_counts(text):
    found = SCHED.search(text)
    return None if found is None else dict(zip(
        ("handed", "reruns", "unready", "forced", "renewed"), map(int, found.groups())))


def without_measured(text):
    try:
        report = json.loads(text)
    except ValueError:
        return None
    report.pop("measured", None)
    return report


def sections(path):
    """(caller's header fields, {kind: (unit, count, sha256)}) of a sectioned file
    (docs/programming/SECTIONED_FILES.md), or None when it cannot be read."""
    try:
        with open(path, "rb") as stream:
            header = stream.read(4096)
    except OSError:
        return None
    if len(header) < 4096 or header[:8] != b"SECTFILE":
        return None
    n = struct.unpack_from("<I", header, 16)[0]
    fields = struct.unpack_from("<16I", header, 24)
    table = {}
    for i in range(min(n, 62)):
        kind, unit, count = struct.unpack_from("<IIQ", header, 96 + 64 * i)
        table[kind] = (unit, count, header[96 + 64 * i + 32:96 + 64 * i + 64].hex())
    return fields, table


def snapshot_same(one, other):
    """None when the two snapshots hold the same content but the information section,
    else what differs."""
    a, b = sections(one), sections(other)
    if a is None or b is None:
        return "a snapshot is missing or not a sectioned file"
    if a[0] != b[0]:
        return "the header's caller fields differ"
    kinds = sorted(set(a[1]) | set(b[1]))
    differ = [k for k in kinds if k != INFO_KIND and a[1].get(k) != b[1].get(k)]
    return f"sections {differ} differ" if differ else None


def record(folder, entry):
    try:
        os.makedirs(folder, exist_ok=True)
        name = f"{entry['date'][:10]}-{entry['commit'][:10] or 'nocommit'}.json"
        path = os.path.join(folder, name)
        with open(path, "w", encoding="utf-8") as stream:
            json.dump(entry, stream, indent=2, sort_keys=True)
            stream.write("\n")
        return path
    except OSError as error:
        print(f"parallel-init: the record could not be written: {error}", file=sys.stderr)
        return None


def parse():
    main = main_checkout()
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--init", default=os.path.join(main, ".claude/work/IM/init.ndjson"))
    parser.add_argument("--jobs", type=int, default=8)
    parser.add_argument("--gforth-fast", default=default_fast())
    parser.add_argument("--out", default=os.path.join(main, ".claude/work/parallel-init"))
    parser.add_argument("--record-dir", default=os.path.join(main, ".claude/work/ci/parallel-init"))
    parser.add_argument("--timeout", type=int, default=7200)
    args = parser.parse_args()
    if args.jobs < 2:
        parser.error("--jobs must be at least 2")
    return args


def runs(args):
    """The four runs: {(form, jobs): (status, text, seconds)}."""
    found = {}
    for jobs in (args.jobs, 1):
        snap = os.path.join(args.out, f"init-{jobs}.lfsn")
        for form, extra in (("text", ["--resources", "--save-snapshot", snap]), ("json", ["--json"])):
            out = os.path.join(args.out, f"init-{jobs}.{form}")
            print(f"parallel-init: --jobs {jobs}, {form} ...", flush=True)
            found[form, jobs] = run(["--jobs", str(jobs), *extra, args.init], args.gforth_fast,
                                    out, args.timeout)
            print(f"parallel-init: --jobs {jobs}, {form}: exit {found[form, jobs][0]}, "
                  f"{found[form, jobs][2]:.1f} s", flush=True)
    return found


def compare(args, found):
    """The differences found (empty when all hold), and the parallel run's counts."""
    n, problems = args.jobs, []
    for form in ("text", "json"):
        if found[form, n][0] != found[form, 1][0]:
            problems.append(f"{form}: exit {found[form, n][0]} at --jobs {n}, {found[form, 1][0]} at 1")
    if verdict_text(found["text", n][1]) != verdict_text(found["text", 1][1]):
        problems.append("the verdict lines differ")
    one, other = without_measured(found["json", n][1]), without_measured(found["json", 1][1])
    if one is None or other is None or one != other:
        problems.append("the JSON reports differ (or one is not JSON), \"measured\" aside")
    differ = snapshot_same(os.path.join(args.out, f"init-{n}.lfsn"),
                           os.path.join(args.out, "init-1.lfsn"))
    if differ:
        problems.append(f"the snapshots differ: {differ}")
    counts = sched_counts(found["text", n][1])
    if counts is None:
        problems.append(f"no scheduler line in the --jobs {n} resource report (no workers ran?)")
    elif counts["unready"] or counts["forced"] or counts["renewed"]:
        problems.append(f"the scheduler's counts are not 0: {counts}")
    return problems, counts


def main():
    args = parse()
    if not os.path.isfile(args.init):
        print(f"parallel-init: SKIPPED, not a pass: no Init export at {args.init} "
              "(machine-local; see scripts/engine-gate.sh)")
        return 4
    if not args.gforth_fast or not shutil.which(args.gforth_fast):
        print(f"parallel-init: SKIPPED, not a pass: no gforth-fast ({args.gforth_fast or 'none found'})")
        return 4
    os.makedirs(args.out, exist_ok=True)
    found = runs(args)
    if any(status is None or not text.strip() for status, text, _ in found.values()):
        print("parallel-init: FAILED (5): a run timed out or wrote nothing")
        return 5
    problems, counts = compare(args, found)
    wall_n, wall_1 = found["text", args.jobs][2], found["text", 1][2]
    speedup = wall_1 / wall_n if wall_n > 0 else 0.0
    print(f"parallel-init: wall time --jobs {args.jobs} {wall_n:.1f} s, --jobs 1 {wall_1:.1f} s, "
          f"speed-up {speedup:.2f}")
    status = 1 if problems else 0
    entry = {"date": datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
             "commit": git("rev-parse", "HEAD"), "tree": git("rev-parse", "HEAD^{tree}"),
             "modified": bool(git("status", "--porcelain", "--untracked-files=no")),
             "init": args.init, "init_bytes": os.path.getsize(args.init),
             "engine": args.gforth_fast, "jobs": args.jobs, "wall_jobs": round(wall_n, 1),
             "wall_1": round(wall_1, 1), "speedup": round(speedup, 2),
             "json_wall_jobs": round(found["json", args.jobs][2], 1),
             "json_wall_1": round(found["json", 1][2], 1), "exit": found["text", 1][0],
             "scheduler": counts, "problems": problems, "status": status}
    path = record(args.record_dir, entry)
    if path:
        print(f"parallel-init: recorded in {path}")
    for problem in problems:
        print(f"parallel-init: DIFFERS: {problem}")
    print("parallel-init: PASSED" if status == 0 else "parallel-init: FAILED (1)")
    return status


if __name__ == "__main__":
    sys.exit(main())
