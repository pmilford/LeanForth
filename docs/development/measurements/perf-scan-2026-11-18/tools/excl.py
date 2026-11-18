#!/usr/bin/env python3
"""samples under WORD without any of the words EXCL...; usage: excl.py FILE.prof WORD EXCL..."""
import sys
rows = []
for l in open(sys.argv[1]):
    if l.startswith('#'):
        continue
    c, s = l.rstrip('\n').split('\t', 1)
    rows.append((int(c), set(s.split(';'))))
N = sum(c for c, _ in rows)
w = sys.argv[2]
ex = set(sys.argv[3:])
a = sum(c for c, r in rows if w in r)
b = sum(c for c, r in rows if w in r and not (r & ex))
print('%s: %.2f%% (%d), without %s: %.2f%% (%d) of %d' % (w, 100 * a / N, a, ' '.join(sorted(ex)), 100 * b / N, b, N))
