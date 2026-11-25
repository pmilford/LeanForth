#!/usr/bin/env python3
"""Tables of where a profiled LeanForth run spent its time.

usage: profile-summary.py OUT.prof SYMS [--top N] [--under WORD]

Reads the stacks scripts/profile-sample.py wrote (OUT.prof) and the symbol
table scripts/profile-symbols.fs wrote (SYMS: each word's file and line),
and prints, as shares of the samples (each sample one interval of the
run's time):
- the phases: loading, stage, feed, check, the rest (by the first of their
  words found on a sample's stack);
- the word families (FAMILIES below; a word's family is the first rule its
  file and name match): exclusive, where the CPU was (the innermost word,
  "<libc>" counted to it); inclusive, the samples with any word of the
  family on the stack, once each, so they overlap; and owner, the nearest
  word outwards from the innermost that is not a service word (validity
  checks, term construction, store reads, caches, walk machinery, other
  library, runtime), so the owner column partitions the samples;
- the N costliest words, exclusive and inclusive.
--under WORD keeps only the samples with WORD on the stack (a part of the
run, such as lf-check-declaration). A development tool, not part of the
product: the families are LeanForth's files of 2026-11-25; a word in a
file no rule names is "other". Exit 2 for an empty profile.
"""
import argparse
import collections
import re
import sys

VALID = re.compile(r"(valid\?|intact\?|-ours|^lf-env-current|^between\?|^store-check|"
                   r"^store-mark|^mark-shape\?|^mark-this\?|^lf-input-all\?|^lf-env-input\?|"
                   r"^store-count-valid\?|^lf-term-input\?|^lf-live@|-live\?)$")
CONS = re.compile(r"^(lf-term-cons|lf-term-share|lf-term-make)")
TERM_CONS = "term construction and hashing (lf-term-cons, htab, hash32)"
READS = "reads of terms, stores, slabs (src/core, store.fs, slab.fs)"
FAMILIES = [
    # (family, file pattern, name pattern); the first match wins
    ("validity checks", r"", VALID),
    (TERM_CONS, r"src/core/terms\.fs", CONS),
    (TERM_CONS, r"src/lib/(htab|cons|hash32)\.fs", None),
    ("instantiation memo (replace memo)", r"src/kernel/replace-memo\.fs", None),
    ("caches (infer, whnf, defeq, free-variable memo)", r"src/kernel/caches\.fs|src/lib/memo\.fs", None),
    ("universe substitution", r"src/kernel/(mixed-)?level-substitute\.fs", None),
    ("instantiation and abstraction (replace passes)",
     r"src/kernel/mixed-(instantiate|open|rebuild|shift)\.fs", None),
    ("whnf_core: beta", r"src/kernel/mixed-beta\.fs", None),
    ("whnf_core: recursors, quotients (iota)",
     r"src/kernel/(iota|generated-recursor|inductive-recursor|quot)\.fs", None),
    ("whnf: Nat and String literals",
     r"src/kernel/(reduce-nat|string-literals)\.fs|src/core/(nat-ops|literals|string-literals)\.fs|"
     r"src/lib/(bignum|bigint)\.fs", None),
    ("whnf_core, whnf: rest (head, delta, projection, let)",
     r"src/kernel/(whnf|mixed-head)\.fs|src/core/(let-terms|projections)\.fs", None),
    ("definitional equality", r"src/kernel/(defeq|mixed-compare|mixed-convert)\.fs", None),
    ("type inference, declaration checks",
     r"src/kernel/(mixed-infer|infer-proj|check-declaration|check-block|inductive-\w+|"
     r"mixed-signature-\w+|mixed-definition-probe)\.fs|src/core/(statement-match|local-context)\.fs", None),
    ("level operations", r"src/kernel/level-\w+\.fs|src/core/(levels|level-scope)\.fs", None),
    (READS, r"src/core/|src/lib/(store|slab)\.fs", None),
    ("scheduler, environment, publishing", r"src/kernel/(env-\w+|environment)\.fs|src/lib/task\.fs", None),
    ("import and decoding", r"src/import/|src/lib/(json|bytes|sha256)\.fs", None),
    ("walk machinery (frames)", r"src/lib/(frame|walk)\.fs", None),
    ("other library", r"src/lib/", None),
    ("command line", r"src/cli/", None),
    ("Gforth runtime", r"gforth|/prim$|^kernel/", None),
]
SERVICE = {"validity checks", TERM_CONS, "instantiation memo (replace memo)",
           READS,
           "caches (infer, whnf, defeq, free-variable memo)", "walk machinery (frames)",
           "other library", "Gforth runtime", "C library", "other"}
PHASES = [("loading main.fs", "included"), ("stage (read the export)", "ck-stage-phase"),
          ("snapshot load", "ck-snapshot-load"), ("feed", "ck-feed-phase"), ("check", "ck-check")]


def read_symbols(path):
    """Each word's source file (its first definition's)."""
    where = {}
    for line in open(path, encoding="utf-8", errors="replace"):
        part = line.rstrip("\n").split(" ")
        if len(part) >= 4 and part[1] in "cdo":
            path = part[3].rsplit(":", 1)[0]
            where.setdefault(part[2], path[path.rfind("/src/") + 1:] if "/src/" in path else path)
    return where


def family_of(word, where, cache):
    if word in cache:
        return cache[word]
    if word == "<libc>":
        return "C library"
    path = where.get(word, "")
    fam = "other"
    for name, files, names in FAMILIES:
        if files and not re.search(files, path):
            continue
        if names is not None and not names.search(word):
            continue
        fam = name
        break
    cache[word] = fam
    return fam


def read_profile(path, under):
    head, rows = "", []
    for line in open(path, encoding="utf-8"):
        if line.startswith("#"):
            head = line.strip()
            continue
        if "\t" in line:
            count, stack = line.rstrip("\n").split("\t", 1)
            words = stack.split(";")
            if under is None or under in words:
                rows.append((int(count), words))
    return head, rows


def pct(c, n):
    return "%6.2f%%" % (100.0 * c / n)


def summarise(rows, where, top):
    n = sum(c for c, _ in rows)
    cache = {}
    phase, excl, incl = collections.Counter(), collections.Counter(), collections.Counter()
    fexcl, fincl, fown = collections.Counter(), collections.Counter(), collections.Counter()
    for c, words in rows:
        seen = set(words)
        phase[next((p for p, w in PHASES if w in seen), "other")] += c
        leaf = words[0]
        excl[leaf] += c
        for w in seen:
            incl[w] += c
        fams = [family_of(w, where, cache) for w in words]
        fexcl[fams[0]] += c
        for f in set(fams):
            fincl[f] += c
        fown[next((f for f in fams if f not in SERVICE), fams[0])] += c
    out = ["-- phases"]
    out += ["%s  %s" % (pct(phase[p], n), p) for p, _ in PHASES + [("other", "")] if phase[p]]
    out.append("-- families: exclusive, inclusive, owner")
    names = list(dict.fromkeys([f for f, _, _ in FAMILIES] + ["C library", "other"]))
    for f in sorted(names, key=lambda f: -fexcl[f]):
        if fexcl[f] or fincl[f]:
            out.append("%s %s %s  %s" % (pct(fexcl[f], n), pct(fincl[f], n), pct(fown[f], n), f))
    out.append("-- words, exclusive (file)")
    out += ["%s  %s  %s" % (pct(c, n), w, where.get(w, "")) for w, c in excl.most_common(top)]
    out.append("-- words, inclusive, but the runtime's and the command line's (file)")
    inner = [(w, c) for w, c in incl.most_common()
             if family_of(w, where, cache) not in ("Gforth runtime", "command line")]
    out += ["%s  %s  %s" % (pct(c, n), w, where.get(w, "")) for w, c in inner[:top]]
    return n, out


def main(argv):
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("profile")
    parser.add_argument("symbols")
    parser.add_argument("--top", type=int, default=25)
    parser.add_argument("--under")
    args = parser.parse_args(argv)
    head, rows = read_profile(args.profile, args.under)
    n, out = summarise(rows, read_symbols(args.symbols), args.top)
    if n == 0:
        print("profile-summary: no samples", file=sys.stderr)
        return 2
    print("%s%s; %d samples kept" % (head, " under " + args.under if args.under else "", n))
    print("\n".join(out))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
