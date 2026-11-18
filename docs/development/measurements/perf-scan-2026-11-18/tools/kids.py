#!/usr/bin/env python3
"""callees of WORD (the word just inside it on the stack); usage: kids.py FILE.prof WORD [N]"""
import sys, collections
rows=[]
for l in open(sys.argv[1]):
    if l.startswith('#'): continue
    c,s=l.rstrip('\n').split('\t',1); r=s.split(';')
    if r[0]=='<libc>': r=r[1:]
    rows.append((int(c),r))
N=sum(c for c,_ in rows); w=sys.argv[2]; k=collections.Counter(); t=0
for c,r in rows:
    if w in r:
        i=len(r)-1-r[::-1].index(w); t+=c   # outermost occurrence
        k[r[i-1] if i>0 else '(self)']+=c
print('== %s %.2f%% of %d'%(w,100*t/N,N))
for x,c in k.most_common(int(sys.argv[3]) if len(sys.argv)>3 else 12): print('%6.2f%%  %s'%(100*c/N,x))
