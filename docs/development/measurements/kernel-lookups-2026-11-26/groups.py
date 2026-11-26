#!/usr/bin/env python3
"""Group the exclusive word shares of a profile-summary.py table (--top 3000) by kind.
usage: groups.py FULL.txt"""
import sys
lines = open(sys.argv[1]).read().split("-- words, exclusive")[1].split("-- words, inclusive")[0].splitlines()
rows = [l.split() for l in lines if "%" in l]
def s(pred): return sum(float(r[0].rstrip("%")) for r in rows if pred(r[1]))
groups = {
 "input-tier decode (lf-tin-*, quad-*, head-*)": lambda w: w.startswith(("lf-tin", "quad-", "head-")) or w in ("lf-term-input-identity", "lf-term-input?"),
 "base fetch (lf-term-base, lf-terms, lf-term-view)": lambda w: w in ("lf-term-base", "lf-terms", "lf-term-view"),
 "store reads (lf-term-at, slab-*, store-*)": lambda w: w in ("lf-term-at", "lf-term-id-at") or w.startswith(("slab-", "store-")),
 "field words (lf-term-*@, data, tag)": lambda w: w.startswith("lf-term-") and (w.endswith("@") or "data" in w or "fields" in w),
 "validity (valid?, between?, identity)": lambda w: w in ("lf-term-valid?", "between?", "lf-term-identity", "lf-term-store-identity", "lf-term-root?", "lf-term-count-valid?"),
 "htab and hashing": lambda w: w.startswith(("htab", "hash-")),
 "memo.fs": lambda w: w.startswith("memo-"),
 "frame.fs": lambda w: w.startswith("frame-"),
 "sort.fs and lower-bound": lambda w: w.startswith("sort-") or w == "lower-bound",
 "outcome.fs": lambda w: w in ("ok?", "ok-then?", "ok-and", "ok-each"),
 "Gforth depth": lambda w: w == "depth",
}
for k, f in groups.items(): print(f"{s(f):6.2f}%  {k}")
print(f"{sum(float(r[0].rstrip('%')) for r in rows):6.2f}%  all words listed")
