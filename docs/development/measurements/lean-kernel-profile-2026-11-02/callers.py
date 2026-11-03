#!/usr/bin/env python3
"""For samples whose chain contains a frame matching TARGET (regex on the stripped
name), count the outermost such frame's caller (the next frame outwards that
does not match SKIP). Gives "who pays for TARGET" as shares of all samples.

Usage: callers.py STACKS TARGET [SKIP]
"""
import collections, re, sys

path, target = sys.argv[1], re.compile(sys.argv[2])
skip = re.compile(sys.argv[3]) if len(sys.argv) > 3 else re.compile(r'^std::|__func<')
strip = lambda f: re.sub(r'\(.*', '', f)
total = hit = 0
by = collections.Counter()
for line in open(path):
    frames = [strip(f) for f in line.rstrip('\n').split('\t')[2].split(';')]
    total += 1
    idx = [i for i, f in enumerate(frames) if target.search(f)]
    if not idx:
        continue
    hit += 1
    j = idx[-1] + 1
    while j < len(frames) and (skip.search(frames[j]) or target.search(frames[j])):
        j += 1
    by[(frames[idx[-1]][:60], frames[j][:70] if j < len(frames) else '?')] += 1
print(f'{hit}/{total} samples ({100 * hit / total:.1f}%) contain {sys.argv[2]}')
for (t, c), n in by.most_common(25):
    print(f'{100 * n / total:5.1f}%  {t}  <-  {c}')
