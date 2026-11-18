"""Statistics for docs/design/SIMP_DATA.md from count_simp.lean's output.
Usage: python3 -I analyse.py SIMP.ndjson [EXPORT.ndjson]"""
import collections, json, pathlib, sys
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[4] / "scripts"))
import export_elab  # noqa: E402  (export_decls)

def name(parts):
    return ".".join(str(p) for p in parts)

recs = collections.defaultdict(list)
for line in open(sys.argv[1], encoding="utf-8"):
    r = json.loads(line)
    (kind, body), = r.items()
    recs[kind].append((body, len(line.encode())))

decls = None
if len(sys.argv) > 2:
    decls, _ = export_elab.export_decls(sys.argv[2])
    print("export declarations:", len(decls))

def has(n):
    return tuple(n) in decls

print("simp sets:", len(recs["simp_set"]), "non-empty:",
      sum(1 for b, _ in recs["simp_set"] if b["pre"] + b["post"]))
for b, _ in sorted(recs["simp_set"], key=lambda x: -(x[0]["pre"] + x[0]["post"])):
    if b["pre"] + b["post"] or b["to_unfold"]:
        print("  set", name(b["set"]), {k: v for k, v in b.items() if k != "set"})

by_set = collections.defaultdict(list)
for b, size in recs["simp"]:
    by_set[name(b["set"])].append((b, size))
for s, rows in sorted(by_set.items(), key=lambda x: -len(x[1])):
    c = collections.Counter()
    origins = set()
    for b, size in rows:
        c["records"] += 1
        c["bytes"] += size
        c["keys"] += len(b["keys"])
        origins.add((json.dumps(b["origin"]), b["inv"]))
        c["inv"] += b["inv"]
        c["pre"] += not b["post"]
        c["rfl"] += b["rfl"]
        c["perm"] += b["perm"]
        c["prio_not_1000"] += b["priority"] != 1000
        c["origin_other"] += isinstance(b["origin"], dict)
        c["head_star"] += b["keys"][:1] == ["star"]
        c["head_other"] += b["keys"][:1] == ["other"]
        p = b["proof"]
        aux = isinstance(p, list) and any(isinstance(x, str) and x.startswith("_simp") for x in p)
        c["proof_aux_simp"] += aux
        c["proof_is_origin"] += p == b["origin"]
        if decls is not None and isinstance(p, list):
            c["proof_in_export"] += has(p)
            if aux:
                c["aux_in_export"] += has(p)
            if not isinstance(b["origin"], dict):
                c["origin_in_export"] += has(b["origin"])
        c["max_keys"] = max(c["max_keys"], len(b["keys"]))
    c["distinct_origins"] = len(origins)
    print("  lemmas of", s, dict(c))

unf = [b for b, _ in recs["unfold"]]
if unf:
    print("unfold:", len(unf), "with eqns:", sum(1 for b in unf if b["eqns"]),
          "eqns:", sum(len(b["eqns"]) for b in unf),
          "eqns in export:", sum(has(e) for b in unf for e in b["eqns"]) if decls else "-")

sp = collections.defaultdict(list)
for b, size in recs["simproc"]:
    sp[name(b["set"])].append((b, size))
for s, rows in sp.items():
    names = {name(b["name"]) for b, _ in rows}
    roots = collections.Counter(b["name"][0] if len(b["name"]) > 1 else "(root)" for b, _ in rows)
    print("  simprocs of", s, "records", len(rows), "names", len(names), "dsimprocs",
          sum(b["dsimproc"] for b, _ in rows), "bytes", sum(z for _, z in rows),
          "in export", sum(has(b["name"]) for b, _ in rows) if decls else "-")
    print("    by namespace:", roots.most_common(40))
for b, _ in recs["simproc_decls"]:
    print("simproc decls:", b)
for b, _ in recs["defeq_tags"]:
    print("defeq tags:", b)

cg = [b for b, _ in recs["congr"]]
print("congr lemmas:", len(cg), "functions:", len({name(b["fun"]) for b in cg}),
      "prio != 1000:", sum(b["priority"] != 1000 for b in cg),
      "in export:", sum(has(b["name"]) for b in cg) if decls else "-")
