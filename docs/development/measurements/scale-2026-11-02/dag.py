# Per-declaration DAG size (distinct reachable expr nodes) vs tree size (paths).
import sys, json, array, statistics, math
kids = {}  # idx -> tuple
N = 0
decl_roots = []
ch1 = array.array('q'); ch2 = array.array('q'); ch3 = array.array('q')
def add(i, a=-1, b=-1, c=-1):
    global N
    assert i == N, (i, N)
    ch1.append(a); ch2.append(b); ch3.append(c); N += 1
with open(sys.argv[1], 'rb') as f:
    for line in f:
        if line.startswith(b'{"in"') or line.startswith(b'{"il"') or line.startswith(b'{"meta"'): continue
        o = json.loads(line)
        if 'ie' in o:
            i = o['ie']
            if 'app' in o: add(i, o['app']['fn'], o['app']['arg'])
            elif 'lam' in o: add(i, o['lam']['type'], o['lam']['body'])
            elif 'forallE' in o: add(i, o['forallE']['type'], o['forallE']['body'])
            elif 'letE' in o: d=o['letE']; add(i, d['type'], d['value'], d['body'])
            elif 'proj' in o: add(i, o['proj']['struct'])
            elif 'mdata' in o: add(i, o['mdata']['expr'])
            else: add(i)
        elif 'in' in o or 'il' in o: continue
        else:
            k = next(iter(o)); d = o[k]
            roots = []
            if k == 'inductive':
                for t in d['types']: roots.append(t['type'])
                for c in d['ctors']: roots.append(c['type'])
                for r in d['recs']:
                    roots.append(r['type']); roots += [ru['rhs'] for ru in r['rules']]
            else:
                if 'type' in d: roots.append(d['type'])
                if 'value' in d: roots.append(d['value'])
            decl_roots.append((k, roots))
# tree size and depth, children precede parents
tree = [0]*N; depth = array.array('l', [0])*N
for i in range(N):
    s = 1; dp = 0
    for c in (ch1[i], ch2[i], ch3[i]):
        if c >= 0:
            s += tree[c]
            if depth[c] > dp: dp = depth[c]
    tree[i] = s; depth[i] = dp + 1
print("exprs", N, "max depth", max(depth))
mark = array.array('l', [-1])*N
dags = []; trees = []; ratios = []
for di, (k, roots) in enumerate(decl_roots):
    cnt = 0; stack = list(roots)
    while stack:
        e = stack.pop()
        if mark[e] == di: continue
        mark[e] = di; cnt += 1
        for c in (ch1[e], ch2[e], ch3[e]):
            if c >= 0 and mark[c] != di: stack.append(c)
    t = sum(tree[r] for r in roots)
    dags.append(cnt); trees.append(t); ratios.append(t / cnt)
def q(xs, p):
    s = sorted(xs); return s[min(len(s)-1, int(p*len(s)))]
print("decls", len(decl_roots))
print("DAG nodes per decl: sum %d median %d p90 %d p99 %d max %d" % (sum(dags), q(dags,.5), q(dags,.9), q(dags,.99), max(dags)))
tt = sum(trees)
print("tree nodes per decl: sum %.3e median %d p90 %d p99 %.3e max %.3e" % (tt, q(trees,.5), q(trees,.9), q(trees,.99), max(trees)))
print("tree/DAG ratio: median %.2f p90 %.2f p99 %.1f max %.3e; total tree/total dag %.3e" % (q(ratios,.5), q(ratios,.9), q(ratios,.99), max(ratios), tt/sum(dags)))
for th in (10**4, 10**6, 10**9, 10**12):
    print("decls with tree size > %.0e: %d" % (th, sum(1 for t in trees if t > th)))
print("decls with DAG size > 64: %d, > 1e4: %d, > 1e5: %d" % (sum(1 for d in dags if d > 64), sum(1 for d in dags if d > 10**4), sum(1 for d in dags if d > 10**5)))
print("sum DAG per decl / distinct exprs = %.2f" % (sum(dags)/N))
