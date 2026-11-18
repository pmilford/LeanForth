"""Measurement only: for a root class and a pattern of its arguments
(None = a metavariable, else a key dict or "star"), the instance records of
the data whose keys may unify, in the order Lean's search tries them (stable
ascending sort by priority over rank order, tried from the last).
Usage: python3 tried.py DATA CLASS ARG..."""
import json
import sys


def tree(keys, i=0):
    k = keys[i]
    n = k.get("arity", 0) if isinstance(k, dict) else 0
    kids, j = [], i + 1
    for _ in range(n):
        kid, j = tree(keys, j)
        kids.append(kid)
    return (k, kids), j


def unify(rec, query):
    if rec[0] == "star" or query is None:
        return True
    return rec[0] == query


cls = sys.argv[2].split(".")
args = [None if a == "?" else json.loads(a) for a in sys.argv[3:]]
found = []
for line in open(sys.argv[1]):
    if not line.startswith('{"instance'):
        continue
    kind, r = next(iter(json.loads(line).items()))
    if [str(p) for p in r.get("class", [])] != cls and r["keys"][0].get("const") != cls:
        continue
    t, _ = tree(r["keys"])
    if all(unify(t[1][i], a) for i, a in enumerate(args) if i < len(t[1])):
        found.append((r.get("priority", 1000), r["rank"], kind, ".".join(map(str, r.get("name", ["?"])))))
found.sort(key=lambda x: (x[0], x[1]))
for f in reversed(found[-8:]):
    print(*f)
print(len(found), "candidates; tried first:", found[-1] if found else None)
