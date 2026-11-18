#!/usr/bin/env python3
"""perf-scan: Init fuel distribution, test-cli-4's Gforth runs, the last push's slowest targets."""
import collections, json, os
os.chdir(os.path.join(os.path.dirname(__file__), '..', '..'))
M = 'docs/development/measurements/perf-scan-2026-11-18'
P = 'build/perf'
out = []
d = json.load(open(P + '/init-j2.json'))
out.append('# all of Init (S1DONE/init.ndjson), check --json --jobs 2, gforth-fast, nice 5, load 9-12 on 10 cores')
out.append('# /usr/bin/time: ' + open(P + '/init-j2.time').read().strip())
out.append('# measured (microseconds): ' + json.dumps(d['measured']['microseconds']))
out.append('# peak resident bytes %d' % d['measured']['peakResidentBytes'])
ds = d['declarations']
f = sorted((x['fuel'], x['name']) for x in ds)
tot = sum(x[0] for x in f)
out.append('declarations %d, fuel %d, verdicts %s' % (len(f), tot, dict(collections.Counter(x['verdict'] for x in ds))))
for q in (0.5, 0.9, 0.99, 0.999):
    out.append('fuel quantile %s: %d' % (q, f[int(q * len(f))][0]))
for k in (10, 20, 100, 1000, 5900):
    out.append('top %d declarations: %.1f%% of all fuel' % (k, 100 * sum(x[0] for x in f[-k:]) / tot))
bins = collections.Counter()
for x in f:
    bins[len(str(x[0]))] += x[0]
out.append('fuel share by declaration fuel 10^k: ' +
           ', '.join('10^%d: %.1f%%' % (k - 1, 100 * v / tot) for k, v in sorted(bins.items())))
out.append('the 20 declarations using most fuel:')
for x in f[-20:][::-1]:
    out.append('  %9d %s' % x)
open(M + '/init-fuel.txt', 'w').write('\n'.join(out) + '\n')

rows = []
for l in open(P + '/cli4.log', errors='replace'):
    p = l.split(None, 2)
    try:
        rows.append((float(p[0]), float(p[1]), p[2].strip() if len(p) > 2 else ''))
    except (ValueError, IndexError):
        pass
o = ['# tests/cli/run_group.py 4 (test-cli-4) with GFORTH=tools/gtime.sh around gforth 1.0.0 (the checking engine),',
     '# load 10-13 on 10 cores: every Gforth run logged with its wall and user seconds',
     'runs %d, wall sum %.1f s, user sum %.1f s' % (len(rows), sum(r[0] for r in rows), sum(r[1] for r in rows)),
     'runs under 0.6 s: %d, their wall sum %.1f s' % (len([r for r in rows if r[0] < 0.6]),
                                                     sum(r[0] for r in rows if r[0] < 0.6)),
     'median run %.2f s' % sorted(r[0] for r in rows)[len(rows) // 2]]
open(M + '/test-cli-4-runs.txt', 'w').write('\n'.join(o) + '\n')

t = collections.defaultdict(float)
n = collections.Counter()
src = '/home/peter/code/LeanForth/.claude/work/ci/dfa21ac6-timing.txt'
for l in open(src):
    p = l.split()
    try:
        t[p[0]] += float(p[1]); n[p[0]] += 1
    except (ValueError, IndexError):
        pass
o = ['# the last push (dfa21ac6, 2026-11-17): scripts/timed.sh per command (LF_TIMING_LOG), summed by target;',
     '# both Gforths and the coverage run together; JOBS=2, Lean cache on',
     'commands %d, targets %d, sum %.0f s' % (sum(n.values()), len(t), sum(t.values()))]
for k, v in sorted(t.items(), key=lambda x: -x[1])[:15]:
    o.append('%7.1f s %4d commands  %s' % (v, n[k], k))
open(M + '/push-targets.txt', 'w').write('\n'.join(o) + '\n')
print('ok')
