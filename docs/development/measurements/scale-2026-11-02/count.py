import sys, json, collections
kinds = collections.Counter(); nbytes = collections.Counter()
decl_kinds = collections.Counter()
maxus = 0; maxlp = 0; lp_hist = collections.Counter()
inductive_types = 0; ctors = 0; recs = 0
name_bytes = 0
with open(sys.argv[1], 'rb') as f:
    for line in f:
        o = json.loads(line)
        if 'in' in o:
            k = 'name'
            if 'str' in o: name_bytes += len(o['str']['str'].encode())
        elif 'il' in o: k = 'level'
        elif 'ie' in o:
            ks = [x for x in o if x != 'ie']
            k = 'expr.' + ks[0]
            if ks[0] == 'const': maxus = max(maxus, len(o['const']['us']))
        elif 'meta' in o: k = 'meta'
        else:
            ks = list(o)
            k = 'decl.' + ks[0]
            d = o[ks[0]]
            if ks[0] == 'inductive':
                inductive_types += len(d.get('types', [])); ctors += len(d.get('ctors', [])); recs += len(d.get('recs', []))
                lps = d['types'][0].get('levelParams', []) if d.get('types') else []
            else:
                lps = d.get('levelParams', [])
            lp_hist[len(lps)] += 1; maxlp = max(maxlp, len(lps))
        kinds[k] += 1; nbytes[k] += len(line)
tot = sum(nbytes.values())
for k in sorted(kinds): print(f"{k:20s} {kinds[k]:>12,d} {nbytes[k]:>14,d} B  {nbytes[k]/kinds[k]:6.1f} B/rec")
print("names", kinds['name'], "levels", kinds['level'], "exprs", sum(v for k,v in kinds.items() if k.startswith('expr.')))
print("total bytes", tot, "name string bytes", name_bytes)
print("max const universe args", maxus, "max decl level params", maxlp, "lp histogram", sorted(lp_hist.items()))
print("inductive types", inductive_types, "ctors", ctors, "recursors", recs)
