#!/usr/bin/env python3
"""PERF1: callers of words in a sample.py profile.
usage: callers.py FILE.prof WORD[,WORD...] [DEPTH]"""
import collections, sys
rows = []
for l in open(sys.argv[1]):
    if l.startswith('#'):
        continue
    c, s = l.rstrip('\n').split('\t', 1)
    rows.append((int(c), s.split(';')))
N = sum(c for c, _ in rows)
depth = int(sys.argv[3]) if len(sys.argv) > 3 else 2
for word in sys.argv[2].split(','):
    cnt = collections.Counter(); tot = 0
    for c, r in rows:
        if word in r:
            i = r.index(word); tot += c
            cnt[' < '.join(r[i + 1:i + 1 + depth])] += c
    print('== %s %.2f%%' % (word, 100 * tot / N))
    for k, v in cnt.most_common(8):
        print('%6.2f%%  %s' % (100 * v / N, k))
