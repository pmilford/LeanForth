#!/usr/bin/env python3
"""List the slowest declarations of a `check --json --resources` report.

The report's measured member gives, with --resources, the wall microseconds
each declaration's own check took ("declarationMicroseconds", in file order;
docs/user/COMMAND_LINE.md, "JSON output"). This prints the N that took the
longest, slowest first, one tab-separated row each after a header: rank,
index, microseconds, fuel, nanoseconds per fuel unit, verdict and name.
A declaration with no fuel known, or none, shows "-" for the rate. A report
without the member (no --resources, or a host without clocks) is refused
with status 2. Ties keep file order. A report of the run, never a verdict.

usage: slowest-declarations.py [-n N] [--sum] REPORT.json   (- reads stdin)
  --sum  also print, after the rows, the total and the share of the N.
"""
import argparse
import json
import sys


def load(path):
    text = sys.stdin.read() if path == "-" else open(path, encoding="utf-8").read()
    return json.loads(text)


def rate(us, fuel):
    """Nanoseconds per fuel unit, or "-" when the fuel is not known or 0."""
    return "-" if not fuel else "%.0f" % (1000.0 * us / fuel)


def rows(report, count):
    took = (report.get("measured") or {}).get("declarationMicroseconds")
    if took is None:
        return None
    decls = report["declarations"]
    order = sorted(range(len(took)), key=lambda i: (-took[i], i))[:count]
    return [(rank + 1, i, took[i], decls[i].get("fuel"), decls[i]["verdict"], decls[i]["name"])
            for rank, i in enumerate(order)]


def main(argv):
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("-n", type=int, default=30, help="how many (default 30)")
    parser.add_argument("--sum", action="store_true", help="print the total and the share")
    parser.add_argument("report")
    args = parser.parse_args(argv)
    report = load(args.report)
    listed = rows(report, args.n)
    if listed is None:
        print("no declarationMicroseconds: run check --json --resources", file=sys.stderr)
        return 2
    print("rank\tindex\tmicroseconds\tfuel\tns/fuel\tverdict\tname")
    for rank, index, us, fuel, verdict, name in listed:
        shown = "null" if fuel is None else fuel
        print(f"{rank}\t{index}\t{us}\t{shown}\t{rate(us, fuel)}\t{verdict}\t{name}")
    if args.sum:
        total = sum(report["measured"]["declarationMicroseconds"])
        top = sum(r[2] for r in listed)
        share = 100.0 * top / total if total else 0.0
        print(f"total {total} us; the {len(listed)} listed {top} us ({share:.1f}%)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
