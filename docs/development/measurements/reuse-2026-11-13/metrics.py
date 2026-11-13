#!/usr/bin/env python3
"""Reuse metrics of src/ at a git revision: lines per folder (all, code), colon definitions, and per lib file:
the src files outside lib/ that require it (directly) and the distinct lib words used outside lib/."""
import re, subprocess, sys, collections, os
rev = sys.argv[1] if len(sys.argv) > 1 else 'HEAD'
root = subprocess.run(['git', 'rev-parse', '--show-toplevel'], capture_output=True, text=True, check=True).stdout.strip()
def git(*a): return subprocess.run(['git', '-C', root, *a], capture_output=True, text=True, check=True).stdout
files = [f for f in git('ls-tree', '-r', '--name-only', rev, 'src').split() if f.endswith('.fs')]
text = {f: git('show', f'{rev}:{f}') for f in files}
def code_lines(t):
    n = 0
    for line in t.split('\n'):
        s = re.sub(r'(^|\s)\\(\s.*)?$', '', line).strip()
        s = re.sub(r'\(\s[^)]*\)', '', s).strip()
        if s: n += 1
    return n
defn = re.compile(r'(?:^|\s):\s+(\S+)')
folders = collections.OrderedDict()
for f in files:
    d = f.split('/')[1] if f.count('/') > 1 else '(top)'
    a = folders.setdefault(d, [0, 0, 0, 0])
    t = text[f]; a[0] += 1; a[1] += t.count('\n'); a[2] += code_lines(t); a[3] += len(defn.findall(t))
tot = [sum(v[i] for v in folders.values()) for i in range(4)]
print(f'rev {git("rev-parse", "--short", rev).strip()}')
print('folder   files  lines  code  words')
for d, v in folders.items(): print(f'{d:8} {v[0]:5} {v[1]:6} {v[2]:5} {v[3]:6}')
print(f'{"TOTAL":8} {tot[0]:5} {tot[1]:6} {tot[2]:5} {tot[3]:6}')
req = re.compile(r'^\s*(?:require|include|needs)\s+(\S+)', re.M)
users = collections.defaultdict(set)
for f in files:
    for m in req.finditer(text[f]):
        p = os.path.normpath(os.path.join(os.path.dirname(f), m.group(1)))
        users[p].add(f)
libs = [f for f in files if f.startswith('src/lib/')]
words_of = {f: set(defn.findall(text[f])) for f in libs}
outside = ' '.join(re.sub(r'\\\s.*', '', text[f]) for f in files if not f.startswith('src/lib/'))
tokens = collections.Counter(outside.split())
print('\nlib file          req-by-nonlib  words  used-outside  call-sites')
tw = tu = tc = 0
for f in sorted(libs):
    w = words_of[f]; used = [x for x in w if tokens[x]]; calls = sum(tokens[x] for x in w)
    nl = len([u for u in users[f] if not u.startswith('src/lib/')])
    tw += len(w); tu += len(used); tc += calls
    print(f'{os.path.basename(f):17} {nl:13} {len(w):6} {len(used):12} {calls:11}')
print(f'{"TOTAL":17} {"":13} {tw:6} {tu:12} {tc:11}')
