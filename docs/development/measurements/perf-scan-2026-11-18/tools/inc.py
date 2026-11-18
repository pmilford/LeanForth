#!/usr/bin/env python3
"""inclusive share of each WORD (once per sample); usage: inc.py FILE.prof WORD..."""
import sys
rows=[]
for l in open(sys.argv[1]):
    if l.startswith('#'): continue
    c,s=l.rstrip('\n').split('\t',1); rows.append((int(c),set(s.split(';'))))
N=sum(c for c,_ in rows)
print('samples',N)
for w in sys.argv[2:]:
    t=sum(c for c,r in rows if w in r); print('%6.2f%% %6d  %s'%(100*t/N,t,w))
