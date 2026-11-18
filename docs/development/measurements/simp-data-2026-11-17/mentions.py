"""Count source mentions of each default simproc (a proxy for which ones proofs
name explicitly, e.g. in `simp only [Nat.reduceAdd]`), and the number of
`simp`-family tactic calls. Usage: python3 -I mentions.py SIMP.ndjson DIR..."""
import collections, json, pathlib, re, sys

procs = set()
for line in open(sys.argv[1]):
    r = json.loads(line)
    if "simproc" in r and r["simproc"]["set"] == ["simprocAttr"]:
        parts = [p for p in r["simproc"]["name"] if isinstance(p, str)]
        if "_@" in parts:
            parts = parts[:parts.index("_@")]
        procs.add(".".join(parts))
short = collections.defaultdict(set)
for p in procs:
    short[p.rsplit(".", 1)[-1]].add(p)
word = re.compile(r"[A-Za-z_][A-Za-z0-9_.!?']*")
tactic = re.compile(r"\b(simp_all|simp_arith|simpa|dsimp|simp|norm_num|ring_nf|ring|field_simp|push_cast)\b(\?|!)?( only)?")
for d in sys.argv[2:]:
    hits, tactics, files = collections.Counter(), collections.Counter(), 0
    for f in pathlib.Path(d).rglob("*.lean"):
        files += 1
        text = f.read_text(encoding="utf-8", errors="replace")
        for m in tactic.finditer(text):
            tactics[m.group(1) + (" only" if m.group(3) else "")] += 1
        for w in word.findall(text):
            if w in procs:
                hits[w] += 1
            elif "." not in w and w in short and len(short[w]) == 1:
                hits[next(iter(short[w]))] += 0  # bare names are ambiguous; not counted
    print(d, "files", files, "procs mentioned", len([p for p in hits if hits[p]]), "of", len(procs))
    print("  tactic words:", dict(tactics.most_common()))
    print("  top:", [(p, n) for p, n in hits.most_common(25) if n])
