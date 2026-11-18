import collections, json, sys
rows = [json.loads(l) for l in open(sys.argv[1])]
nn = [r["norm_num"] for r in rows if "norm_num" in r]
names = collections.Counter(".".join(map(str, r["name"])) for r in nn)
print("entries", len(nn), "extensions", len(names),
      "pre-only", sum(1 for r in nn if not r["post"]), "post-only", sum(1 for r in nn if not r["pre"]),
      "bytes", sum(len(l) for l in open(sys.argv[1])))
mods = collections.Counter(n.split(".")[3] if n.startswith("Mathlib.Meta.NormNum.") else n for n in names)
print(sorted(names))
print(rows[-1])
