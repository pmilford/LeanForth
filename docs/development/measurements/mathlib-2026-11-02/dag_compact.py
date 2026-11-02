# Memory-compact variant of docs/development/measurements/scale-2026-11-02/dag.py
# for exports with ~10^8 expression nodes. Same statistics and output lines as
# dag.py, plus the ten heaviest declarations by name. Differences:
#  - children, depth and marks are 32-bit arrays (dag.py: 64-bit and lists);
#  - tree sizes are float64 (exact up to 2^53, approximate beyond), because
#    exact Python ints for 10^8 nodes would cost several GB;
#  - declaration roots are kept in one flat array with offsets.
# Usage: python3 -I dag_compact.py export.ndjson
# Verified to match dag.py line for line on an Init.Prelude export.
import sys, json, heapq
from array import array as A

ch1 = A('i'); ch2 = A('i'); ch3 = A('i')
N = 0
name_pre = A('i', [-1]); name_comp = ['']          # index 0 is anonymous
decl_kind = []; decl_name = A('i'); root_off = A('q', [0]); roots = A('i')

def need(i):
    if i != N:
        raise SystemExit("expression index %d out of order (expected %d)" % (i, N))

with open(sys.argv[1], 'rb') as f:
    for line in f:
        if line.startswith(b'{"il"') or line.startswith(b'{"meta"'):
            continue
        o = json.loads(line)
        if 'ie' in o:
            i = o['ie']; need(i)
            if 'app' in o: d = o['app']; a, b, c = d['fn'], d['arg'], -1
            elif 'lam' in o: d = o['lam']; a, b, c = d['type'], d['body'], -1
            elif 'forallE' in o: d = o['forallE']; a, b, c = d['type'], d['body'], -1
            elif 'letE' in o: d = o['letE']; a, b, c = d['type'], d['value'], d['body']
            elif 'proj' in o: a, b, c = o['proj']['struct'], -1, -1
            elif 'mdata' in o: a, b, c = o['mdata']['expr'], -1, -1
            else: a, b, c = -1, -1, -1
            ch1.append(a); ch2.append(b); ch3.append(c); N += 1
        elif 'in' in o:
            i = o['in']
            if i != len(name_pre):
                raise SystemExit("name index %d out of order" % i)
            if 'str' in o: d = o['str']; name_pre.append(d['pre']); name_comp.append(d['str'])
            else: d = o['num']; name_pre.append(d['pre']); name_comp.append(str(d['i']))
        else:
            k = next(iter(o)); d = o[k]
            if k == 'inductive':
                nm = d['types'][0]['name'] if d['types'] else 0
                for t in d['types']: roots.append(t['type'])
                for c in d['ctors']: roots.append(c['type'])
                for r in d['recs']:
                    roots.append(r['type'])
                    for ru in r['rules']: roots.append(ru['rhs'])
            else:
                nm = d.get('name', 0)
                if 'type' in d: roots.append(d['type'])
                if 'value' in d: roots.append(d['value'])
            decl_kind.append(k); decl_name.append(nm); root_off.append(len(roots))

def name_str(i):
    parts = []
    while i > 0:
        parts.append(name_comp[i]); i = name_pre[i]
    return '.'.join(reversed(parts)) or '[anonymous]'

# tree size and depth; children precede parents
tree = A('d', [0.0]) * N
depth = A('i', [0]) * N
maxdepth = 0
for i in range(N):
    s = 1.0; dp = 0
    c = ch1[i]
    if c >= 0:
        s += tree[c]; dp = depth[c]
        c = ch2[i]
        if c >= 0:
            s += tree[c]
            if depth[c] > dp: dp = depth[c]
            c = ch3[i]
            if c >= 0:
                s += tree[c]
                if depth[c] > dp: dp = depth[c]
    tree[i] = s; dp += 1; depth[i] = dp
    if dp > maxdepth: maxdepth = dp
print("exprs", N, "max depth", maxdepth)

D = len(decl_kind)
mark = A('i', [-1]) * N
dags = A('q'); trees = A('d'); ratios = A('d'); ddepth = A('i')
for di in range(D):
    rs = roots[root_off[di]:root_off[di + 1]]
    cnt = 0; stack = list(rs)
    while stack:
        e = stack.pop()
        if mark[e] == di: continue
        mark[e] = di; cnt += 1
        c = ch1[e]
        if c >= 0:
            if mark[c] != di: stack.append(c)
            c = ch2[e]
            if c >= 0:
                if mark[c] != di: stack.append(c)
                c = ch3[e]
                if c >= 0 and mark[c] != di: stack.append(c)
    t = sum(tree[r] for r in rs)
    dags.append(cnt); trees.append(t); ratios.append(t / cnt if cnt else 0.0)
    ddepth.append(max((depth[r] for r in rs), default=0))
del mark

def q(xs, p):
    s = sorted(xs); return s[min(len(s) - 1, int(p * len(s)))]
print("decls", D)
print("DAG nodes per decl: sum %d median %d p90 %d p99 %d max %d" % (sum(dags), q(dags, .5), q(dags, .9), q(dags, .99), max(dags)))
tt = sum(trees)
print("tree nodes per decl: sum %.3e median %d p90 %d p99 %.3e max %.3e" % (tt, q(trees, .5), q(trees, .9), q(trees, .99), max(trees)))
print("tree/DAG ratio: median %.2f p90 %.2f p99 %.1f max %.3e; total tree/total dag %.3e" % (q(ratios, .5), q(ratios, .9), q(ratios, .99), max(ratios), tt / sum(dags)))
for th in (10**4, 10**6, 10**9, 10**12):
    print("decls with tree size > %.0e: %d" % (th, sum(1 for t in trees if t > th)))
print("decls with DAG size > 64: %d, > 1e4: %d, > 1e5: %d" % (sum(1 for d in dags if d > 64), sum(1 for d in dags if d > 10**4), sum(1 for d in dags if d > 10**5)))
print("sum DAG per decl / distinct exprs = %.2f" % (sum(dags) / N))
print("expression depth per decl: median %d p99 %d max %d" % (q(ddepth, .5), q(ddepth, .99), max(ddepth)))
for label, xs in (("DAG size", dags), ("tree size", trees)):
    print("top 10 declarations by %s:" % label)
    for v, di in heapq.nlargest(10, ((xs[j], j) for j in range(D))):
        print("  %-14.6g %-10s %s" % (v, decl_kind[di], name_str(decl_name[di])))
