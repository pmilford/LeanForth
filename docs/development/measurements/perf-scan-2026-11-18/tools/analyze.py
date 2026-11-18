#!/usr/bin/env python3
"""PERF1: summarise sample.py's stacks. usage: analyze.py FILE.prof [N] [--under WORD]
Prints exclusive (leaf Forth word; '<libc>' when the CPU was in libc) and inclusive
(word anywhere on the stack, once per sample) shares, and a phase split."""
import sys, collections
path = sys.argv[1]
top = int(sys.argv[2]) if len(sys.argv) > 2 and sys.argv[2].isdigit() else 40
under = sys.argv[sys.argv.index('--under') + 1] if '--under' in sys.argv else None
rows = []
for l in open(path):
    if l.startswith('#') or not l.strip(): continue
    c, st = l.rstrip('\n').split('\t', 1) if '\t' in l else (1, l.rstrip('\n'))
    rows.append((int(c), st.split(';')))
if under:
    rows = [r for r in rows if under in r[1]]
n = sum(c for c, _ in rows)
excl, incl, libc = collections.Counter(), collections.Counter(), collections.Counter()
for c, r in rows:
    if r[0] == '<libc>':
        libc[r[1] if len(r) > 1 else '?'] += c
        r = r[1:]
    excl[r[0]] += c
    for w in set(r):
        incl[w] += c
PHASES = [('stage (read export)', 'ck-stage-phase'), ('snapshot load', 'ck-snapshot-load'),
          ('feed', 'ck-feed-phase'), ('check: declaration', 'lf-check-declaration'),
          ('check: block', 'lf-check-block'), ('check: publish (lf-env-logged-publish)', 'lf-env-logged-publish'),
          ('check (other)', 'ck-check'), ('loading main.fs', 'included')]
ph = collections.Counter()
for c, r in rows:
    s = set(r)
    for name, w in PHASES:
        if w in s:
            ph[name] += c; break
    else:
        ph['other'] += c
print('samples', n, ('under ' + under) if under else '')
print('-- phases (first match in this order)')
for name, _ in PHASES + [('other', '')]:
    if ph[name]:
        print('%6.2f%%  %s' % (100.0 * ph[name] / n, name))
print('-- libc (by calling word): %.2f%%' % (100.0 * sum(libc.values()) / n))
for w, c in libc.most_common(8):
    print('%6.2f%%  %s' % (100.0 * c / n, w))
print('-- exclusive')
for w, c in excl.most_common(top):
    print('%6.2f%%  %s' % (100.0 * c / n, w))
print('-- inclusive')
for w, c in incl.most_common(top * 2):
    print('%6.2f%%  %s' % (100.0 * c / n, w))
