#!/usr/bin/env python3
"""Ratchet on duplicated Forth code (owner, 2026-11-13, plan 9.4.8f). Part of `make test`.

Usage: python3 scripts/check-duplicates.py [--update-baseline] [--report] [ROOT]

Parses the colon definitions of ROOT/src/**/*.fs (comments `\\ ...` and `( ... )` dropped; strings after `s"`, `."`,
`c"`, `abort"`, `s\\"`, `.(` and the word after `[char]`/`char` are single tokens), lower-cases the body and
alpha-renames every word defined in the same file (by `:`, `constant`, `variable`, `create`, `value`, `defer`, ...)
to a placeholder numbered by first appearance in the body. A copy whose helpers were renamed, for example `in-foo`
and `ib-foo` for the same operation, therefore has the same normal form as the original. Definitions whose normal
forms are identical form a group; groups of two or more definitions are duplicates. Words defined in src/lib/
are shared vocabulary and stay literal everywhere (otherwise `ok?` would be a placeholder in lib/outcome.fs and a
plain word in the file that copied `ok-with`).

MIN_TOKENS = 8. A definition body shorter than eight tokens is a trivial word (`: x-ok? ok? ;`, `: x-size ( n ) 8 * ;`,
a short wrapper); two files will always agree on those by accident and merging them would not make anything
simpler. Bodies from eight tokens up are real logic: in the 2026-11-13 library audit the copies found by hand all
had a dozen or more tokens. (Stack comments do not count: they are dropped like all comments.)

Ratchet: tests/duplicates-baseline.json holds today's groups, keyed by a hash of the normal form. The check fails
when a group appears that is not in the baseline or a baseline group has more members than recorded, and prints
each new duplicate as file:line. Fixing a group (fewer members) never fails. Rewrite the baseline with
--update-baseline only in a reviewed commit, as for tests/forth-quality-baseline.json; editing one copy of a
duplicate changes its group's key, so the new key then appears here until the baseline is updated or the copies
are merged. --report prints every group, cross-file groups first.
"""
import collections
import hashlib
import json
import pathlib
import re
import sys

DEFAULT_ROOT = pathlib.Path(__file__).resolve().parent.parent
MIN_TOKENS = 8
STRING_OPENERS = {"s\"", ".\"", "c\"", "abort\"", "s\\\"", ".("}
CHAR_WORDS = {"[char]", "char"}
DEFINERS = {"constant", "variable", "2constant", "2variable", "value", "2value", "create", "defer",
            "fvariable", "fconstant", "buffer:", "field:", "cell:"}


def tokens(text):
    """(token, line) pairs of Forth source with comments removed; a string literal is one token."""
    out, i, line, n = [], 0, 1, len(text)
    while i < n:
        if text[i].isspace():
            line += text[i] == "\n"
            i += 1
            continue
        j = i
        while j < n and not text[j].isspace():
            j += 1
        tok, start = text[i:j], line
        i = j
        low = tok.lower()
        if low == "\\":
            while i < n and text[i] != "\n":
                i += 1
        elif low == "(":
            while i < n and text[i] != ")":
                line += text[i] == "\n"
                i += 1
            i += 1
        elif low in STRING_OPENERS:
            end = ")" if low == ".(" else "\""
            k = i + 1
            while k < n and text[k] != end:
                line += text[k] == "\n"
                k += 1
            out.append((low + " " + text[i + 1:k], start))
            i = k + 1
        else:
            out.append((low, start))
    return out


def definitions(path):
    """[(name, line, body tokens)] of the colon definitions of a file, and its set of defined names."""
    toks = tokens(path.read_text(encoding="utf-8", errors="replace"))
    defs, names, i = [], set(), 0
    while i < len(toks):
        word, line = toks[i]
        if word in DEFINERS and i + 1 < len(toks):
            names.add(toks[i + 1][0])
        if word == ":" and i + 1 < len(toks):
            name, j = toks[i + 1][0], i + 2
            while j < len(toks) and toks[j][0] != ";":
                j += 1
            defs.append((name, line, [t for t, _ in toks[i + 2:j]]))
            names.add(name)
            i = j
        i += 1
    return defs, names


def normal_form(body, names):
    """The body with each file-local word replaced by a placeholder numbered by first appearance."""
    seen, out, skip = {}, [], False
    for t in body:
        if skip:
            out.append(t)
            skip = False
        elif t in CHAR_WORDS:
            out.append(t)
            skip = True
        elif t in names:
            out.append("#%d" % seen.setdefault(t, len(seen)))
        else:
            out.append(t)
    return out


def groups(root):
    """{key: {"tokens": n, "members": [(file, line, name)]}} for every group of 2 or more identical bodies."""
    root = root.resolve()
    table = collections.defaultdict(list)
    parsed = {path: definitions(path) for path in sorted((root / "src").rglob("*.fs"))}
    shared = set().union(*[names for path, (_, names) in parsed.items() if path.parent.name == "lib"])
    for path, (defs, names) in parsed.items():
        for name, line, body in defs:
            norm = normal_form(body, names - shared)
            if len(norm) >= MIN_TOKENS:
                key = hashlib.sha1(" ".join(norm).encode()).hexdigest()[:12]
                table[key].append((str(path.relative_to(root)), line, name, len(norm)))
    return {k: {"tokens": v[0][3], "members": [m[:3] for m in v]} for k, v in table.items() if len(v) > 1}


def spans_files(group):
    return len({f for f, _, _ in group["members"]}) > 1


def label(key, group):
    kind = "across files" if spans_files(group) else "within a file"
    return f"{key} ({group['tokens']} tokens, {len(group['members'])} copies, {kind})"


def ratchet(now, base):
    problems = []
    for key, group in sorted(now.items()):
        old = base.get(key)
        if old is None or len(group["members"]) > old["copies"]:
            what = "new duplicate group" if old is None else f"group grew from {old['copies']} copies"
            problems.append(f"{what}: {label(key, group)}")
            problems += [f"    {f}:{line} {name}" for f, line, name in group["members"]]
    return problems


def baseline_of(now):
    return {k: {"tokens": g["tokens"], "copies": len(g["members"]),
                "members": [f"{f}:{name}" for f, _, name in g["members"]]} for k, g in sorted(now.items())}


def report(now):
    order = sorted(now.items(), key=lambda kv: (not spans_files(kv[1]), -kv[1]["tokens"] * len(kv[1]["members"])))
    for key, group in order:
        print(label(key, group))
        for f, line, name in group["members"]:
            print(f"    {f}:{line} {name}")


def main(argv):
    args = [a for a in argv if not a.startswith("--")]
    root = pathlib.Path(args[0]).resolve() if args else DEFAULT_ROOT
    path = root / "tests/duplicates-baseline.json"
    now = groups(root)
    if "--update-baseline" in argv:
        path.write_text(json.dumps(baseline_of(now), indent=1, sort_keys=True) + "\n")
        print(f"wrote {path.relative_to(root)}: {len(now)} groups")
        return 0
    if "--report" in argv:
        report(now)
    problems = ratchet(now, json.loads(path.read_text()) if path.exists() else {})
    if problems:
        print("duplicates: identical Forth code beyond tests/duplicates-baseline.json (share one word or a "
              "library word; update the baseline only in a reviewed commit):")
        print("\n".join("  " + p for p in problems))
        return 1
    print(f"duplicates: {len(now)} baseline groups, none new or grown (bodies of {MIN_TOKENS}+ tokens)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
