#!/usr/bin/env python3
"""Independent check of the compact-store prototype's data words.

Streams a lean4export 3.1.0 NDJSON file with Python's json module and
computes, for every expression, the fields of the prototype's data word
following Lean's rules (src/Lean/Expr.lean, the `data` computed field):
loose bound-variable range, "has level parameters", and approximate depth
(leaves 0, otherwise the deepest child + 1), capped at 1023 as the
prototype stores it. Prints the same sums as the prototype's data-sums.
Usage: python3 -I data_check.py FILE.ndjson
"""
import json
import sys

CAP = 1023


def main(path):
    lp_level = [False]          # level 0 is zero
    rng, dep, lp = [], [], []
    with open(path, encoding="utf-8") as f:
        for line in f:
            r = json.loads(line)
            if "il" in r:
                if "succ" in r:
                    lp_level.append(lp_level[r["succ"]])
                elif "max" in r or "imax" in r:
                    a, b = r.get("max") or r.get("imax")
                    lp_level.append(lp_level[a] or lp_level[b])
                else:
                    lp_level.append(True)
                continue
            if "ie" not in r:
                continue
            k = next(key for key in r if key != "ie")
            v = r[k]
            if k == "bvar":
                x = (v + 1, 0, False)
            elif k == "sort":
                x = (0, 0, lp_level[v])
            elif k == "const":
                x = (0, 0, any(lp_level[u] for u in v["us"]))
            elif k == "app":
                f_, a_ = v["fn"], v["arg"]
                x = (max(rng[f_], rng[a_]), min(max(dep[f_], dep[a_]) + 1, CAP), lp[f_] or lp[a_])
            elif k in ("lam", "forallE"):
                t, b = v["type"], v["body"]
                x = (max(rng[t], max(rng[b] - 1, 0)), min(max(dep[t], dep[b]) + 1, CAP),
                     lp[t] or lp[b])
            elif k == "letE":
                t, val, b = v["type"], v["value"], v["body"]
                x = (max(rng[t], rng[val], max(rng[b] - 1, 0)),
                     min(max(dep[t], dep[val], dep[b]) + 1, CAP), lp[t] or lp[val] or lp[b])
            elif k == "proj":
                s = v["struct"]
                x = (rng[s], min(dep[s] + 1, CAP), lp[s])
            elif k in ("natVal", "strVal"):
                x = (0, 0, False)
            else:
                raise SystemExit("unexpected expression kind " + k)
            rng.append(x[0]); dep.append(x[1]); lp.append(x[2])
    print("data: sum-range=%d sum-depth=%d has-level-param=%d"
          % (sum(rng), sum(dep), sum(lp)))
    print("max loose range=%d max depth (clamped 1023)=%d" % (max(rng), max(dep)))


if __name__ == "__main__":
    main(sys.argv[1])
