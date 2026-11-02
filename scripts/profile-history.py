#!/usr/bin/env python3
"""Record opt-in process profiles; this is not checker benchmarking."""
import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import re
import statistics
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
ROW = re.compile(r"^(\d+) (Lean|Forth) ([0-9.]+) ([0-9]+|unavailable)$")
# The workload names a timing series; only records of the same series are
# compared. Until 2026-11-02 the series was "term-level-substitution-48",
# timed on the retired legacy Forth table; its timings are not comparable.
WORKLOAD = "mixed-level-substitution-48"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repetitions", type=int, default=3, choices=range(1, 100), metavar="1..99")
    parser.add_argument("--history", type=Path, default=ROOT / ".profiling/history.jsonl")
    args = parser.parse_args()
    result = subprocess.run(["bash", str(ROOT / "scripts/profile-existing.sh"),
                             str(args.repetitions)], cwd=ROOT, capture_output=True, text=True)
    if result.returncode:
        sys.stderr.write(result.stderr + result.stdout)
        return result.returncode
    samples = {"Lean": [], "Forth": []}
    for line in result.stdout.splitlines():
        match = ROW.fullmatch(line)
        if match:
            iteration, label, elapsed, rss = match.groups()
            samples[label].append({"run": int(iteration), "seconds": float(elapsed),
                                   "peak_rss_kib": None if rss == "unavailable" else int(rss)})
    if any(len(rows) != args.repetitions for rows in samples.values()):
        raise ValueError("profile output has an unexpected number of samples")
    previous = None
    if args.history.exists():
        with args.history.open(encoding="utf-8") as stream:
            for line in stream:
                entry = json.loads(line)
                if entry.get("schema") == 1 and entry.get("workload") == WORKLOAD:
                    previous = entry
    record = {"schema": 1, "workload": WORKLOAD,
              "recorded_utc": datetime.now(timezone.utc).isoformat(),
              "samples": samples, "raw_report": result.stdout}
    args.history.parent.mkdir(parents=True, exist_ok=True)
    with args.history.open("a", encoding="utf-8") as stream:
        stream.write(json.dumps(record, sort_keys=True) + "\n")
    print(f"Saved {args.repetitions} samples per implementation to {args.history}")
    for label, rows in samples.items():
        seconds = statistics.median(row["seconds"] for row in rows)
        rss = [row["peak_rss_kib"] for row in rows if row["peak_rss_kib"] is not None]
        memory = f"{statistics.median(rss):,.0f} KiB" if rss else "unavailable"
        print(f"{label}: median {seconds:g} s; peak RSS median {memory}")
        if previous:
            old = previous.get("samples", {}).get(label, [])
            if old:
                old_time = statistics.median(row["seconds"] for row in old)
                print(f"  Previous median: {old_time:g} s; difference {seconds - old_time:+g} s")
                old_rss = [row["peak_rss_kib"] for row in old if row["peak_rss_kib"] is not None]
                if old_rss and rss:
                    old_memory = statistics.median(old_rss)
                    print(f"  Previous peak RSS median: {old_memory:,.0f} KiB; "
                          f"difference {statistics.median(rss) - old_memory:+,.0f} KiB")
    print("Whole-process observations include startup; compare environments and input hashes in the saved reports.")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        print(f"Profiling history error: {exc}", file=sys.stderr)
        raise SystemExit(1)
