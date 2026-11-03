#!/usr/bin/env python3
"""Top exclusive (leaf) and inclusive (anywhere in the chain, once per sample) symbols.

Usage: topsyms.py STACKS [N] [--only REGEX]
"""
import collections, re, sys

path = sys.argv[1]
n = int(sys.argv[2]) if len(sys.argv) > 2 and not sys.argv[2].startswith('--') else 60
only = None
if '--only' in sys.argv:
    only = re.compile(sys.argv[sys.argv.index('--only') + 1])


def short(s):
    s = re.sub(r'\(.*', '', s)  # drop argument lists
    return s


excl, incl = collections.Counter(), collections.Counter()
total = 0
for line in open(path):
    pid, trunc, chain = line.rstrip('\n').split('\t')
    frames = [short(f) for f in chain.split(';')]
    if only and not any(only.search(f) for f in frames):
        continue
    total += 1
    excl[frames[0]] += 1
    for f in set(frames):
        incl[f] += 1
print(f'samples {total}')
print('--- exclusive (leaf) ---')
for s, c in excl.most_common(n):
    print(f'{100 * c / total:6.2f}%  {c:6d}  {s}')
print('--- inclusive ---')
for s, c in incl.most_common(n):
    print(f'{100 * c / total:6.2f}%  {c:6d}  {s}')
