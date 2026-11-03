#!/usr/bin/env python3
"""Kernel time by declaration size (distinct nodes), and a parallel-schedule bound.

Usage: sizestats.py DECLS.tsv
"""
import collections, sys

rows = []
with open(sys.argv[1]) as f:
    hdr = f.readline().rstrip('\n').split('\t')
    for line in f:
        r = dict(zip(hdr, line.rstrip('\n').split('\t')))
        rows.append((int(r['ns']), int(r['dag']), r['kind'], int(r['unfolds'])))
tot = sum(r[0] for r in rows)
edges = [0, 100, 1000, 10000, 100000, 10 ** 9]
b = collections.defaultdict(lambda: [0, 0, 0])
for ns, dag, kind, unf in rows:
    for lo, hi in zip(edges, edges[1:]):
        if lo <= dag < hi:
            b[(lo, hi)][0] += 1
            b[(lo, hi)][1] += ns
            b[(lo, hi)][2] += dag
print('distinct nodes   decls   share of decls   share of time   ns per node')
for lo, hi in zip(edges, edges[1:]):
    c, t, d = b[(lo, hi)]
    if c:
        print(f'{lo:>7}-{hi:<9} {c:7d} {100 * c / len(rows):8.1f}% {100 * t / tot:12.1f}% {t / max(d, 1):12.0f}')
thm = sum(r[0] for r in rows if r[2] == 'thm')
mx = max(r[0] for r in rows)
print(f'theorems {100 * thm / tot:.1f}% of kernel time; largest single declaration {mx / 1e9:.2f} s')
for w in (6, 12):
    print(f'lower bound on wall time with {w} workers (no dependencies): '
          f'{max(tot / w, mx) / 1e9:.1f} s (serial {tot / 1e9:.1f} s)')
unf = sum(r[3] for r in rows)
print(f'delta/iota unfolds recorded {unf}; per declaration mean {unf / len(rows):.0f}; '
      f'declarations with zero unfolds {sum(1 for r in rows if r[3] == 0)}')
