#!/usr/bin/env python3
"""Report style metrics for LeanForth's Forth source. Read-only; never fails.

Usage: python3 scripts/forth-metrics.py [--words N] [PATH ...]
Default paths: src/. Prints, per file and in total:
  - colon definitions and their length in source lines (1-2, 3-5, 6-10, >10)
  - definitions without a stack comment `( ... -- ... )` right after the name
  - globals: VARIABLE, 2VARIABLE, VALUE, CREATE, BUFFER:, and every top-level
    use of a project defining word (a colon definition whose body uses
    CREATE, such as store: or walk:), since each use creates mutable state.
    CONSTANTs are counted separately; structure words define layouts, not
    state, and are not counted
  - locals: Gforth `{: ... :}` / `{ ... }` and standard `LOCALS|`
  - deep stack shuffling (ROT -ROT PICK ROLL 2SWAP 2OVER 2ROT) and
    return-stack use (>R R> R@ 2>R 2R> 2R@)
  - source lines longer than 90 characters, which make the line-based
    length buckets look better than the code is
With --words N, also lists the N longest definitions.

These are review signals for docs/development/FORTH_REVIEWER.md, not proofs
of quality: a long word can be the clearest choice, and a short one can hide
a bad stack contract.
"""
import pathlib
import re
import sys
from collections import Counter

GLOBALS = {"variable", "2variable", "value", "2value", "create", "buffer:", "fvariable"}
CONSTANTS = {"constant", "2constant"}
SHUFFLES = {"rot", "-rot", "pick", "roll", "2swap", "2over", "2rot"}
RSTACK = {">r", "r>", "r@", "2>r", "2r>", "2r@"}
STRING_WORDS = {'."', 's"', 'c"', 'abort"', '.(', 's\\"'}
# Defining words that create layouts or constants, not mutable state.
NOT_STATE = {"begin-structure", "end-structure", "+field", "field:", "cfield:"}


def tokens(text):
    """Yield (line, token) with comments and string bodies removed.

    Paren comments are yielded as the single token "(comment)" so the caller
    can see a stack comment's position.
    """
    for number, line in enumerate(text.splitlines(), 1):
        i, n = 0, len(line)
        while i < n:
            while i < n and line[i].isspace():
                i += 1
            if i >= n:
                break
            j = i
            while j < n and not line[j].isspace():
                j += 1
            word = line[i:j]
            low = word.lower()
            if low == "\\":
                break
            if low == "(":
                close = line.find(")", j)
                yield number, "(comment)"
                i = n if close < 0 else close + 1
                continue
            if low in STRING_WORDS:
                close = line.find(")" if low == ".(" else '"', j + 1)
                yield number, low
                i = n if close < 0 else close + 1
                continue
            yield number, low
            i = j


def definers(paths):
    """Names of colon definitions whose body uses CREATE, directly or through
    another defining word (such as walk2: through walk-sized)."""
    bodies = {}
    for path in paths:
        toks = [t for _, t in tokens(path.read_text(encoding="utf-8", errors="replace"))]
        for k, tok in enumerate(toks[:-1]):
            if tok == ":":
                end = toks.index(";", k) if ";" in toks[k:] else len(toks)
                if toks[k + 1] not in NOT_STATE:
                    bodies[toks[k + 1]] = set(toks[k + 2:end])
    found, grown = set(), True
    while grown:
        new = {name for name, body in bodies.items()
               if name not in found and ("create" in body or body & found)}
        found |= new
        grown = bool(new)
    return found


def analyse(path, defining=frozenset()):
    text = path.read_text(encoding="utf-8", errors="replace")
    toks = list(tokens(text))
    defs, stats = [], Counter()
    stats["long lines"] = sum(len(line) > 90 for line in text.splitlines())
    k = 0
    while k < len(toks):
        line, tok = toks[k]
        if tok in GLOBALS or tok in defining:
            stats["globals"] += 1
            stats["global:" + tok] += 1
        elif tok in CONSTANTS:
            stats["constants"] += 1
        if tok in (":", ":noname"):
            name = toks[k + 1][1] if tok == ":" and k + 1 < len(toks) else ":noname"
            body_start = k + (2 if tok == ":" else 1)
            has_comment = body_start < len(toks) and toks[body_start][1] == "(comment)"
            end = body_start
            while end < len(toks) and toks[end][1] != ";":
                end += 1
            body = [t for _, t in toks[body_start:end]]
            last = toks[end][0] if end < len(toks) else toks[-1][0]
            locals_used = any(t in ("{:", "{", "locals|") for t in body)
            defs.append({
                "name": name, "line": line, "lines": last - line + 1,
                "words": sum(1 for t in body if t != "(comment)"),
                "comment": has_comment, "locals": locals_used,
                "shuffles": sum(t in SHUFFLES for t in body),
                "rstack": sum(t in RSTACK for t in body),
            })
            k = end + 1
            continue
        k += 1
    return defs, stats


def bucket(lines):
    return "1-2" if lines <= 2 else "3-5" if lines <= 5 else "6-10" if lines <= 10 else ">10"


def summarise(label, defs, stats):
    sizes = Counter(bucket(d["lines"]) for d in defs)
    total = len(defs) or 1
    share = lambda key: f"{sizes[key]} ({100 * sizes[key] // total}%)"
    return (f"{label}: {len(defs)} words; lines 1-2 {share('1-2')}, 3-5 {share('3-5')}, "
            f"6-10 {share('6-10')}, >10 {share('>10')}; "
            f"no stack comment {sum(not d['comment'] for d in defs)}; "
            f"globals {stats['globals']}, constants {stats['constants']}; "
            f"locals {sum(d['locals'] for d in defs)}; "
            f"deep shuffles {sum(d['shuffles'] for d in defs)}; "
            f"return-stack ops {sum(d['rstack'] for d in defs)}; "
            f"lines over 90 chars {stats['long lines']}")


def main(argv):
    longest = 0
    if "--words" in argv:
        index = argv.index("--words")
        longest = int(argv[index + 1])
        argv = argv[:index] + argv[index + 2:]
    roots = [pathlib.Path(p) for p in (argv or ["src"])]
    files = sorted(f for r in roots for f in ([r] if r.is_file() else r.rglob("*.fs")))
    all_defs, all_stats = [], Counter()
    by_dir = {}
    # Defining words are found in all of src/, whichever files are reported.
    project = sorted(pathlib.Path(__file__).resolve().parent.parent.glob("src/**/*.fs"))
    defining = definers(files + project)
    for path in files:
        defs, stats = analyse(path, defining)
        print(summarise(str(path), defs, stats))
        all_defs += [dict(d, file=str(path)) for d in defs]
        all_stats.update(stats)
        group = by_dir.setdefault(str(path.parent), [[], Counter(), 0])
        group[0].extend(defs)
        group[1].update(stats)
        group[2] += 1
    if len(by_dir) > 1:
        print()
        for folder, (defs, stats, count) in sorted(by_dir.items()):
            print(summarise(f"{folder}/ ({count} files)", defs, stats))
    print()
    print(summarise(f"TOTAL ({len(files)} files)", all_defs, all_stats))
    kinds = sorted((k[7:], v) for k, v in all_stats.items() if k.startswith("global:"))
    print("Globals by kind: " + ", ".join(f"{k.upper()} {v}" for k, v in kinds))
    if longest:
        print(f"\nLongest {longest} definitions (source lines, words):")
        for d in sorted(all_defs, key=lambda d: -d["lines"])[:longest]:
            print(f"  {d['lines']:3d} lines {d['words']:4d} words  {d['file']}:{d['line']}  {d['name']}")
    return 0


sys.exit(main(sys.argv[1:]))
