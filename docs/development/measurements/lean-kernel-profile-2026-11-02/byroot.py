#!/usr/bin/env python3
"""Kernel time by package (first component of the module name), with tag shares.

Usage: byroot.py DECLS.tsv
"""
import collections, sys

agg = collections.defaultdict(lambda: [0, 0, collections.Counter()])
tot = 0
with open(sys.argv[1]) as f:
    hdr = f.readline().rstrip('\n').split('\t')
    for line in f:
        r = dict(zip(hdr, line.rstrip('\n').split('\t')))
        root = r['module'].split('.')[0]
        ns = int(r['ns'])
        tot += ns
        a = agg[root]
        a[0] += 1
        a[1] += ns
        for t in (r.get('tags') or '(none)').split(','):
            a[2][t] += ns
for root, (c, t, tags) in sorted(agg.items(), key=lambda kv: -kv[1][1]):
    top = ', '.join(f'{k} {100 * v / t:.0f}%' for k, v in tags.most_common(4))
    print(f'{root:12} {c:7d} decls {t / 1e9:7.2f} s {100 * t / tot:5.1f}%  mean {t / c / 1e3:7.1f} us  [{top}]')
