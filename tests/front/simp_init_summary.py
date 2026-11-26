#!/usr/bin/env python3
"""Summarise tests/front/simp-init.lean's NDJSON: what Init's one-line simp
proofs use, as shares of L (the theorems pinned Lean's re-run closes).

    python3 tests/front/simp_init_summary.py OUT.ndjson [--export INIT.ndjson]
        [--src TOOLCHAIN/src/lean]

--export: an Init export (lean4export NDJSON); a `_simp_N` helper constant in a
  proof term counts as left out (H) when the export declares no such name.
--src: Lean's source tree; the script re-counts docs/design/TACTIC_SIMP.md's
  grep (`:= by simp` / `:= by simp [..]` / `:= by simp only [..]` at a line's
  end in Init) and classes the hits the harness did not measure.

The decision numbers follow .claude/work/briefs/simp-group-4-architect.md,
section 1 "Numbers that decide". Measured shares are counted from the run;
the K figure is an estimate from the flags (see BUILT and blockers()).
"""
import argparse
import collections
import json
import os
import re
import sys

# Simproc families whose actions the first by-simp is assumed to have.
BUILT_FAMILIES = {"core-ite", "nat-lit"}
# Binder congruence as on main: arrow, forall and one-binder fun.
BUILT_BINDERS = {"forall_congr", "implies_congr", "funext"}
# @[congr] lemmas as on main.
BUILT_CONGR = {"ite_congr"}
CASTS = {"cast", "Eq.rec", "Eq.ndrec", "HEq", "Eq.recOn", "Eq.casesOn"}
P_KINDS = {"hyp-other", "thm-other", "term", "star"}


def load(path):
    with open(path, encoding="utf-8") as f:
        return [json.loads(l) for l in f if l.startswith("{")]


def export_names(path):
    """Names the export declares (thm, def, opaque, axiom records)."""
    parts, decl = {}, []
    with open(path, encoding="utf-8") as f:
        for line in f:
            if line.startswith('{"in"'):
                r = json.loads(line)
                body = r.get("str") or r.get("num")
                parts[r["in"]] = (body["pre"], body.get("str", body.get("i")))
            elif line.startswith(('{"thm"', '{"def"', '{"opaque"', '{"axiom"')):
                r = json.loads(line)
                decl.append(next(iter(r.values()))["name"])
    memo = {0: ""}

    def name(i):
        if i not in memo:
            pre, s = parts[i]
            p = name(pre)
            memo[i] = f"{p}.{s}" if p else str(s)
        return memo[i]
    return {name(i) for i in decl}


def flags(r, exported):
    """The features theorem r uses, each a short key."""
    f = set()
    if r["discharge"]["attempts"] > 0:
        f.add("discharger")
    for p in r["simprocs"]:
        f.add("simproc:" + p["family"])
    left = [h for h in r["helpers"] if exported is not None and h not in exported]
    if left:
        f.add("helper-left-out")
    if r["binder"]:
        f.add("binders")
    if set(r["binder"]) - BUILT_BINDERS or r["funext_nested"]:
        f.add("binders-beyond-main")
    if r["reduce_ablation"] != "same":
        f.add("reduce-step")
    items = r.get("items", [])
    if any(i["kind"] == "def" for i in items):
        f.add("unfold")
    if any(i["arrow"] or i["kind"] in P_KINDS for i in items):
        f.add("preprocess")
    if set(r["congr"]) - BUILT_CONGR:
        f.add("congr-other")
    if set(r["casts"]) & CASTS:
        f.add("cast")
    if r["congr_simp"] and set(r["casts"]) & CASTS:
        f.add("dep-cast")
    return f


def built(key):
    if key.startswith("simproc:"):
        return key[8:] in BUILT_FAMILIES
    return key == "binders"  # main has arrow, forall, one-binder fun


def blockers(r, exported):
    return {k for k in flags(r, exported) if not built(k)}


def pct(k, n):
    return f"{k} ({100.0 * k / n:.1f}%)" if n else f"{k}"


GREP = re.compile(r":= by simp( \[[^]]*\]| only \[[^]]*\])?$")
MODS = ("@[", "private", "protected", "nonrec", "public", "noncomputable", "local", "scoped", "unsafe", "partial")


def grep_hits(src):
    hits = {}
    for root, _, files in os.walk(os.path.join(src, "Init")):
        for fn in files:
            if not fn.endswith(".lean"):
                continue
            path = os.path.join(root, fn)
            mod = os.path.relpath(path, src)[:-5].replace(os.sep, ".")
            with open(path, encoding="utf-8") as f:
                ls = f.read().split("\n")
            for j, l in enumerate(ls):
                if GREP.search(l):
                    hits[(mod, j + 1)] = (ls, j)
    return hits


def hit_kind(ls, j):
    """The command a grep hit belongs to: the nearest line at column 0."""
    line = ls[j]
    if "$" in line:
        return "a macro's template"
    if line[:1] in (" ", "\t") and re.match(r"\s*(\(|_ |·|\||case|next|calc|have|show|suffices|obtain|[\w.']+ :=)", line):
        return "inside a declaration (have, calc step, field, case)"
    k = j
    while k > 0 and (not ls[k] or ls[k][0] in " \t)" or ls[k].startswith(("--", "/-", "-/"))):
        k -= 1
    words = ls[k].split()
    while words and (words[0].startswith(MODS) or words[0].endswith("]")):
        words = words[1:]
    w = words[0] if words else "?"
    if w in ("theorem", "lemma"):
        return "theorem (not measured)"
    if w in ("instance", "example", "def", "abbrev"):
        return w
    return "other: " + w


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("ndjson")
    ap.add_argument("--export")
    ap.add_argument("--src")
    a = ap.parse_args()
    rs = load(a.ndjson)
    exported = export_names(a.export) if a.export else None
    main_shapes = [r for r in rs if r["shape"] in ("bare", "brackets")]
    only = [r for r in rs if r["shape"] == "only"]
    print(f"Measured theorems: {len(rs)} "
          f"(bare {sum(r['shape'] == 'bare' for r in rs)}, brackets "
          f"{sum(r['shape'] == 'brackets' for r in rs)}, only {len(only)})")
    if a.src:
        hits = grep_hits(a.src)
        seen = {(r["module"], r["line"]) for r in rs}
        print(f"TACTIC_SIMP.md's grep: {len(hits)} lines; measured {len(seen & set(hits))};"
              f" measured but not a grep hit {len(seen - set(hits))}")
        kinds = collections.Counter(hit_kind(*v) for k, v in hits.items() if k not in seen)
        for k, n in kinds.most_common():
            print(f"  not measured: {k}: {n}")
    L = [r for r in main_shapes if r["closed"]]
    N = len(main_shapes)
    print(f"\nN (simp / simp [..], measured) = {N}; L (closed by Lean's re-run) = {len(L)}")
    why = collections.Counter(r["why"] for r in main_shapes if not r["closed"])
    print("  not closed: " + ", ".join(f"{k} {n}" for k, n in why.most_common()))
    print(f"  simp only [..]: {len(only)} measured, {sum(r['closed'] for r in only)} closed")
    print(f"  term equal to Init's stored value: {pct(sum(r['same_as_stored'] for r in L), len(L))}")
    fl = {r["name"]: flags(r, exported) for r in L}
    count = collections.Counter(k for f in fl.values() for k in f)
    n = len(L)
    print("\nDecision numbers (share of L):")
    print(f"  D  discharger (an attempt): {pct(count['discharger'], n)};"
          f" attempts {sum(r['discharge']['attempts'] for r in L)},"
          f" succeeded {sum(r['discharge']['ok'] for r in L)},"
          f" theorems with a successful discharge {sum(r['discharge']['ok'] > 0 for r in L)}")
    fams = sorted(k for k in count if k.startswith("simproc:"))
    for k in fams:
        print(f"  S  {k[8:]}: {pct(count[k], n)}")
    print(f"  H  left-out helper: " + (pct(count['helper-left-out'], n) if exported is not None else "needs --export")
          + f"; any _simp_N helper {pct(sum(bool(r['helpers']) for r in L), n)}")
    print(f"  B  binder congruence: {pct(count['binders'], n)}; beyond main (other kinds,"
          f" nested funext): {pct(count['binders-beyond-main'], n)}")
    print(f"  Dep congr_simp with a cast: {pct(count['dep-cast'], n)};"
          f" any .congr_simp {pct(sum(bool(r['congr_simp']) for r in L), n)};"
          f" any cast {pct(count['cast'], n)}")
    print(f"  R  reduceStep proj/matcher/iota/let (ablation): {pct(count['reduce-step'], n)}")
    print(f"  U  simp [f] unfolding a definition: {pct(count['unfold'], n)}")
    print(f"  P  bracket items needing preprocessing: {pct(count['preprocess'], n)}")
    print(f"     @[congr] other than {sorted(BUILT_CONGR)}: {pct(count['congr-other'], n)}")
    for what, test in (("a ← item", lambda i: i["arrow"]), ("a hypothesis that is not an equation",
                       lambda i: i["kind"] == "hyp-other"), ("[*]", lambda i: i["kind"] == "star"),
                       ("a term item", lambda i: i["kind"] == "term"), ("a theorem that is not an equation",
                       lambda i: i["kind"] == "thm-other")):
        print(f"     P with {what}: {pct(sum(any(test(i) for i in r.get('items', [])) for r in L), n)}")
    kinds = collections.Counter(i["kind"] + ("<-" if i["arrow"] else "") for r in L for i in r.get("items", []))
    print("     bracket item kinds: " + ", ".join(f"{k} {v}" for k, v in kinds.most_common()))
    congr = collections.Counter(c for r in L for c in r["congr"])
    print("     @[congr] lemmas: " + ", ".join(f"{k} {v}" for k, v in congr.most_common()))
    print("\nWhat a first by-simp WITHOUT x would lose (theorems of L using x):")
    for k, v in count.most_common():
        print(f"  {k:24s} {pct(v, n)}{'   (assumed built)' if built(k) else ''}")
    bl = {r["name"]: blockers(r, exported) for r in L}
    K = [r for r in L if not bl[r["name"]]]
    print(f"\nK estimate (needs none of the unbuilt things): {pct(len(K), n)} of L,"
          f" {len(K)} of N={N}")
    print(f"  assumed built: default-set rewriting, rfl lemmas, congruence as on main"
          f" ({', '.join(sorted(BUILT_CONGR))}, realized congr_simp without casts), binders"
          f" {sorted(BUILT_BINDERS)} (one-binder fun), simproc families {sorted(BUILT_FAMILIES)}")
    single = collections.Counter(next(iter(b)) for b in bl.values() if len(b) == 1)
    print("  theorems whose only blocker is x: " + ", ".join(f"{k} {v}" for k, v in single.most_common()))
    lem = collections.Counter(x for r in L for x in set(r["lemmas"]))
    print("\nTop 15 lemmas (theorems of L using each):")
    for k, v in lem.most_common(15):
        print(f"  {k}: {v}")
    procs = collections.Counter(p["name"] for r in L for p in r["simprocs"])
    print("Simprocs: " + ", ".join(f"{k} {v}" for k, v in procs.most_common()))
    sizes = sorted(r["size"] for r in L)
    print(f"\nTerm size (tree nodes): median {sizes[len(sizes) // 2]}, max {sizes[-1]},"
          f" over 20000 (no S-expression) {sum(s > 20000 for s in sizes)}")
    print(f"Lean time in simp runs: {sum(r.get('ms', 0) for r in rs)} ms over {len(rs)} theorems")
    return 0


if __name__ == "__main__":
    sys.exit(main())
