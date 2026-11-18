#!/usr/bin/env python3
"""perf-scan: insert counters into the scratch copy build/perf/inst (never src/).
usage: patch.py ROOT  (applies the PATCHES list; each old text must occur once)"""
import sys, os
root = sys.argv[1]
PATCHES = [
    ('src/lib/portability.fs', None, 'require ./zzcnt.fs\n'),
    ('src/core/names.fs', ": lf-name-entries-valid? ( -- flag )\n",
     ": lf-name-entries-valid? ( -- flag )\n  0 cnt+ lf-name-count @ dup 1 cnt-add 2 cnt-max\n"),
    ('src/core/names.fs', ": lf-name-find-num ( prefix number -- id true | false )\n",
     ": lf-name-find-num ( prefix number -- id true | false )\n  3 cnt+ lf-name-count @ 4 cnt-add\n"),
    ('src/core/names.fs', ": lf-name-find-str ( prefix length -- id true | false )\n",
     ": lf-name-find-str ( prefix length -- id true | false )\n  5 cnt+ lf-name-count @ 6 cnt-add\n"),
    ('src/front/lib-decode.fs', ": lbd-decode ( d -- r outcome )\n",
     ": lbd-decode ( d -- r outcome )\n  7 cnt+\n"),
    ('src/cli/leanforth.fs', ": cli-leave ( code -- ) 100 + (bye) ;",
     ": cli-leave ( code -- ) cnt-dump 100 + (bye) ;"),
]
extra = os.environ.get('PATCH_EXTRA')
if extra:
    exec(open(extra).read())
for path, old, new in PATCHES:
    p = os.path.join(root, path)
    t = open(p).read()
    if old is None:
        if not t.startswith(new):
            t = new + t
    else:
        if new in t:
            continue
        assert t.count(old) == 1, (path, old, t.count(old))
        t = t.replace(old, new)
    open(p, 'w').write(t)
print('patched')
