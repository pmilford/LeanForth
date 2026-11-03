#!/usr/bin/env python3
"""Summarise per-declaration kernel times written by TimedReplay.lean.

Usage: declstats.py DECLS.tsv [TOP] [--modules]
"""
import collections, sys

path = sys.argv[1]
top = int(sys.argv[2]) if len(sys.argv) > 2 and sys.argv[2].isdigit() else 40
rows = []
with open(path) as f:
    hdr = f.readline().rstrip('\n').split('\t')
    for line in f:
        r = dict(zip(hdr, line.rstrip('\n').split('\t')))
        for k in ('ns', 'unfolds', 'distinct_unfolded', 'top_count', 'dag'):
            r[k] = int(r[k])
        rows.append(r)
rows.sort(key=lambda r: -r['ns'])
tot = sum(r['ns'] for r in rows)
n = len(rows)
print(f'declarations {n}; kernel time {tot / 1e9:.2f} s; mean {tot / n / 1e3:.1f} us; '
      f'median {rows[n // 2]["ns"] / 1e3:.1f} us')
acc = 0
marks = {1, 10, 100, 1000, n // 100, n // 10, n // 2}
for i, r in enumerate(rows, 1):
    acc += r['ns']
    if i in marks:
        print(f'  slowest {i:6d} ({100 * i / n:5.2f}% of declarations): {100 * acc / tot:5.1f}% of kernel time')
bucket = collections.Counter()
for r in rows:
    us = r['ns'] / 1e3
    b = '<10us' if us < 10 else '<100us' if us < 100 else '<1ms' if us < 1000 else '<10ms' if us < 1e4 else '<100ms' if us < 1e5 else '<1s' if us < 1e6 else '>=1s'
    bucket[b] += 1
for b in ('<10us', '<100us', '<1ms', '<10ms', '<100ms', '<1s', '>=1s'):
    print(f'  {b:>7}: {bucket[b]:6d}')
kind = collections.defaultdict(lambda: [0, 0])
for r in rows:
    kind[r['kind']][0] += 1
    kind[r['kind']][1] += r['ns']
print('by kind: ' + '; '.join(f'{k} {c} decls {t / 1e9:.2f} s ({100 * t / tot:.1f}%)'
                             for k, (c, t) in sorted(kind.items(), key=lambda kv: -kv[1][1])))
if rows[0]['dag']:
    # time per DAG node, and correlation
    import math
    xs = [math.log(max(r['dag'], 1)) for r in rows]
    ys = [math.log(max(r['ns'], 1)) for r in rows]
    mx, my = sum(xs) / n, sum(ys) / n
    cov = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
    vx = sum((x - mx) ** 2 for x in xs); vy = sum((y - my) ** 2 for y in ys)
    print(f'log-log correlation of time with distinct nodes: {cov / math.sqrt(vx * vy):.2f}')
    dsum = sum(r['dag'] for r in rows)
    print(f'distinct nodes summed over declarations {dsum}; {tot / dsum:.0f} ns per node overall')
if rows[0]['unfolds'] or any(r['unfolds'] for r in rows[:50]):
    us = sum(r['unfolds'] for r in rows)
    print(f'delta unfolds total {us}')
if any(r.get('tags') for r in rows[:2000]):
    slow = set(id(r) for r in rows[: max(n // 100, 1)])
    tag = collections.defaultdict(lambda: [0, 0, 0])
    for r in rows:
        ts = [t for t in r.get('tags', '').split(',') if t] or ['(none)']
        for t in ts:
            tag[t][0] += 1
            tag[t][1] += r['ns']
            tag[t][2] += id(r) in slow
    print('by proof-style tag (tags overlap): tag, decls, kernel time, share of time, '
          'decls among the slowest 1%')
    for t, (c, tt, s) in sorted(tag.items(), key=lambda kv: -kv[1][1]):
        print(f'  {t:13} {c:7d} {tt / 1e9:8.2f} s {100 * tt / tot:5.1f}%  {s:5d}  '
              f'mean {tt / c / 1e3:8.1f} us')
if '--modules' in sys.argv:
    mod = collections.defaultdict(lambda: [0, 0])
    for r in rows:
        mod[r['module']][0] += 1
        mod[r['module']][1] += r['ns']
    print('slowest modules:')
    for m, (c, t) in sorted(mod.items(), key=lambda kv: -kv[1][1])[:25]:
        print(f'  {t / 1e9:7.2f} s  {100 * t / tot:5.1f}%  {c:6d} decls  {m}')
print(f'top {top}:')
print('  ms      kind    unfolds distinct top_unfolded(count)  dag  tags  name  [module]')
for r in rows[:top]:
    print(f'  {r["ns"] / 1e6:8.1f} {r["kind"]:6} {r["unfolds"]:8d} {r["distinct_unfolded"]:6d} '
          f'{r["top_unfolded"]}({r["top_count"]}) {r["dag"]}  {r.get("tags", "")}  {r["name"]}  [{r["module"]}]')
