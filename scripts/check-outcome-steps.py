#!/usr/bin/env python3
"""Fail when a step given to ok-apply, ok-apply2 or ok-apply3 has the wrong declared shape. Part of `make test`.

Usage: python3 scripts/check-outcome-steps.py [ROOT]

`lib/outcome.fs`'s chains run a step `xt` on the N values made so far (N = 1, 2, 3 for ok-apply, ok-apply2,
ok-apply3) and, on a failure before it, drop those N values and leave `-1 outcome`. Both arms leave the same
stack only when the step takes exactly N cells and leaves exactly `result outcome`. The review of branch
cleanup-families-3 (H1, 2026-11-19) found a step of `( e i type -- type body outcome )` given to ok-apply3,
which ate a caller's cell on a refusal, and no test or check had seen it.

For every `['] X ok-applyN` (or `' X ok-applyN`) in ROOT/src/**/*.fs, outside comments and strings, this reads
the stack comment of each colon definition or `defer` of X (`: X ( in -- out )`, names compared without case,
as Gforth does) and requires:
- exactly N names before `--`;
- after `--`, each alternative (split on `|`) of exactly two names, the second `outcome` or `status`.

A site whose X has no definition with a stack comment in src/, a stack comment it cannot count (`...`, `..`,
`|` before `--`, brackets or no `--`), or several definitions that disagree, is reported as "not checked" and
does not fail: the check is only as good as the comments it reads. It never reads a word's body: a wrong body
under a right stack comment passes, and only the tests and planted faults prove a body. A step whose xt is not named where the chain
is called (`xt ok-apply`) is not seen at all. Exit 1 when a checked site is wrong, else 0.
"""
import pathlib
import re
import sys

DEFAULT_ROOT = pathlib.Path(__file__).resolve().parent.parent
CHAINS = {"ok-apply": 1, "ok-apply2": 2, "ok-apply3": 3}
TICKS = {"[']", "'"}
DEFINERS = {":", "defer"}
# Words whose text runs to the next `"` (a `\"` inside the escaped forms does not end it).
STRINGS = {'s"', '."', 'c"', 'abort"', ',"', 's\\"', '.\\"', 'c\\"'}
OUTCOME_NAMES = {"outcome", "status"}
UNCOUNTABLE = re.compile(r"\.\.|\[|\]")


def string_end(text, i, escaped):
    """Index of the `"` that ends a string whose text starts at `i`."""
    while i < len(text):
        if escaped and text[i] == "\\":
            i += 2
            continue
        if text[i] == '"':
            return i
        i += 1
    return len(text)


def scan(text):
    """The file's words as (line, word, comment): a `( ... )` comment is one entry with word "(" and its body;
    `\\` comments, `.( ... )` and string bodies are skipped, and the character after `char`/`[char]` is kept
    as one word."""
    out, i, n, line = [], 0, len(text), 1
    while i < n:
        if text[i].isspace():
            line += text[i] == "\n"
            i += 1
            continue
        j = i
        while j < n and not text[j].isspace():
            j += 1
        word = text[i:j].lower()
        if word == "\\":
            k = text.find("\n", j)
            i = n if k < 0 else k
            continue
        if word in ("(", ".("):
            k = text.find(")", j)
            k = n if k < 0 else k
            if word == "(":
                out.append((line, "(", text[j:k]))
            line += text.count("\n", i, k)
            i = k + 1
            continue
        if word in STRINGS:
            k = string_end(text, j + 1, word.endswith('\\"'))
            line += text.count("\n", i, k)
            i = k + 1
            continue
        out.append((line, text[i:j], None))
        i = j
        if word in ("char", "[char]"):
            while i < n and text[i] in " \t":
                i += 1
            j = i
            while j < n and not text[j].isspace():
                j += 1
            out.append((line, text[i:j], None))
            i = j
    return out


def effect(comment):
    """(inputs, [outputs per alternative]) of a stack comment, or None when it cannot be counted."""
    if comment is None or UNCOUNTABLE.search(comment):
        return None
    parts = comment.split("--")
    if len(parts) != 2:
        return None
    ins = parts[0].split()
    if "|" in ins:
        return None
    alts = [a.split() for a in parts[1].split("|")]
    return ins, alts


def definitions(files):
    """{name: [(path, line, comment or None)]} of every colon definition and defer in the files."""
    found = {}
    for path, words in files:
        for k, (line, word, _) in enumerate(words[:-1]):
            if word.lower() in DEFINERS and words[k + 1][2] is None:
                name = words[k + 1][1].lower()
                nxt = words[k + 2] if k + 2 < len(words) else (0, "", None)
                found.setdefault(name, []).append((path, line, nxt[2] if nxt[1] == "(" else None))
    return found


def sites(files):
    """(path, line, step, chain) of every `['] X ok-applyN` in the files."""
    for path, words in files:
        for k in range(len(words) - 2):
            if words[k][1] in TICKS and words[k + 2][1].lower() in CHAINS:
                yield path, words[k][0], words[k + 1][1], words[k + 2][1].lower()


def shape_problem(eff, n):
    """Why a counted effect cannot be a step of n values, or None when it can."""
    ins, alts = eff
    if len(ins) != n:
        return f"takes {len(ins)} cells, the chain passes {n}"
    for alt in alts:
        if len(alt) != 2:
            return f"leaves {len(alt)} cells ({' '.join(alt)}), the chain needs result outcome"
        if alt[1].rstrip("'") not in OUTCOME_NAMES:
            return f"leaves {' '.join(alt)}, whose second cell is not an outcome"
    return None


def check(root):
    """(wrong, unchecked, count): lines describing wrong and not-checked sites, and the number of sites."""
    files = []
    for path in sorted((root / "src").rglob("*.fs")):
        text = path.read_text(encoding="utf-8", errors="replace")
        files.append((path.relative_to(root).as_posix(), scan(text)))
    defs = definitions(files)
    wrong, unchecked, count = [], [], 0
    for path, line, step, chain in sites(files):
        count += 1
        where = f"{path}:{line}: {step} via {chain}"
        found = defs.get(step.lower(), [])
        effs = [effect(c) for _, _, c in found]
        if not found or any(e is None for e in effs):
            reason = "no definition in src/" if not found else "a stack comment that cannot be counted"
            unchecked.append(f"{where}: not checked ({reason})")
            continue
        problems = {shape_problem(e, CHAINS[chain]) for e in effs}
        if problems == {None}:
            continue
        if None in problems:
            unchecked.append(f"{where}: not checked ({len(found)} definitions disagree)")
            continue
        comment = found[0][2].strip()
        wrong.append(f"{where}: ( {comment} ) {sorted(problems)[0]}")
    return wrong, unchecked, count


def main(argv):
    root = pathlib.Path(argv[1]) if len(argv) > 1 else DEFAULT_ROOT
    wrong, unchecked, count = check(root)
    for line in wrong + unchecked:
        print(line)
    print(f"outcome steps: {count} sites, {count - len(wrong) - len(unchecked)} right, "
          f"{len(wrong)} wrong, {len(unchecked)} not checked")
    return 1 if wrong else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
