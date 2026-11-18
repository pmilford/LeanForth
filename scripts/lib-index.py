#!/usr/bin/env python3
"""Generate docs/development/LIBRARY_WORDS.md, the index of the public words of src/lib/ (plan 9.4.8f).

Usage: python3 scripts/lib-index.py [--write] [ROOT]

Without --write the script checks that the file is current and fails, naming the command that regenerates it,
when it is stale (part of `make check-docs`). For every src/lib/*.fs file the index lists, one line each, the
public words: colon definitions, constants, variables, values, defers, created data, structures and their
fields (begin-structure, field:, cfield:, +field, at any indentation), and the words portability.fs defines only
where the host lacks them (`[undefined] name [if]`). Words compiled into
the private wordlist (ADR 0010: between `lf-lib-private module-open` / `lf-lib-private set-current` and the next
`lf-lib set-current`, `dup set-current` (the wordlist current when the file loads, as store.fs uses) or
`module-close`) are left out. Each line gives the word, its stack comment when one
follows the name on the definition line, and the first line of the comment block directly above the definition
(or the comment at the end of the definition line). A reader looking for an existing word, such as the Forth
reviewer (docs/development/FORTH_REVIEWER.md), searches this page first.
"""
import pathlib
import re
import sys

DEFAULT_ROOT = pathlib.Path(__file__).resolve().parent.parent
OUTPUT = "docs/development/LIBRARY_WORDS.md"
COLON = re.compile(r"^:\s+(\S+)\s*(\([^)]*\))?(.*)$")
# Data and defining words, each one a line names before its comment: the standard's, Gforth's
# USER, and the libraries' own (a name ending in a colon, such as cons-class: or reader:).
DATA = re.compile(r"(?:^|\s)(constant|variable|value|defer|create|2constant|2variable|user|[^\s:]\S*:)\s+(\S+)",
                  re.I)
STRUCT = re.compile(r"(?:^|\s)(begin-structure|field:|cfield:|2field:|\+field)\s+(\S+)", re.I)
UNDEFINED = re.compile(r"^\[undefined\]\s+(\S+)\s+\[if\]", re.I)
PRIVATE = re.compile(r"^\s*lf-lib-private\s+(module-open|set-current)\b")
PUBLIC = re.compile(r"^\s*(lf-lib\s+set-current|dup\s+set-current|module-close)\b")
MAX_DESCRIPTION = 110


def comment_above(lines, i):
    """First line of the `\\` comment block directly above line i, without the backslash."""
    j = i - 1
    while j >= 0 and lines[j].lstrip().startswith("\\"):
        j -= 1
    block = lines[j + 1:i]
    return block[0].lstrip()[1:].strip() if block else ""


def trailing(text):
    return text.split("\\", 1)[1].strip() if "\\" in text else ""


def definitions(lines, i):
    """[(name, stack comment, description)] of what line i defines: a word portability.fs defines
    when the host lacks it, a colon definition, structure fields, or data."""
    line = lines[i]
    undefined, colon = UNDEFINED.match(line), COLON.match(line)
    inline = undefined and re.search(r":\s+" + re.escape(undefined.group(1)) + r"\s*(\([^)]*\))?", line)
    if inline:
        return [(undefined.group(1), inline.group(1) or "", comment_above(lines, i)[:MAX_DESCRIPTION])]
    if colon:
        name, stack, rest = colon.groups()
        return [(name, stack or "", (comment_above(lines, i) or trailing(rest))[:MAX_DESCRIPTION])]
    fields = [] if undefined else list(STRUCT.finditer(line))
    if fields:
        text = trailing(line) or (comment_above(lines, i) if fields[0].group(1).lower() == "begin-structure" else "")
        return [(f.group(2), "", text[:MAX_DESCRIPTION]) for f in fields]
    data = list(DATA.finditer(re.split(r"(?:^|\s)\\\s", line)[0])) if line[:1] != " " else []
    text = (comment_above(lines, i) or trailing(line))[:MAX_DESCRIPTION]
    return [(d.group(2), "", text if k == 0 else "") for k, d in enumerate(data)]


def words(path):
    """[(name, stack comment, description)] of the public words of a file, in file order."""
    lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
    out, private = [], False
    for i, line in enumerate(lines):
        if PRIVATE.match(line):
            private = True
        elif PUBLIC.match(line):
            private = False
        elif private or line.lstrip().startswith("\\"):
            continue
        else:
            for entry in definitions(lines, i):
                if entry[0] not in {e[0] for e in out}:   # a name two branches define, once
                    out.append(entry)
    return out


INTERFACE = re.compile(r"^\\ (Interface|Public words)\b[^:]*:(.*)$")


def interface(path):
    """The words a file's header lists as its interface (the `\\ Interface:` or `\\ Public words
    ...:` paragraph, each word also without trailing punctuation), or None without such a list."""
    lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
    start = next((i for i, line in enumerate(lines) if INTERFACE.match(line)), None)
    if start is None:
        return None
    tokens = INTERFACE.match(lines[start]).group(2).split()
    for line in lines[start + 1:]:
        if not line.startswith("\\") or not line[1:].strip():
            break
        tokens += line[1:].split()
    return set(tokens) | {t.rstrip(",.;)") for t in tokens}


def render(root):
    parts = ["# Library words", "",
             "Generated by `python3 scripts/lib-index.py --write`; do not edit. The public words of each `src/lib/` file "
             "(private helpers, ADR 0010, are left out), with the stack comment on the definition line and the first "
             "line of the comment above it. Search here before writing a word "
             "([FORTH_LIBRARY.md](FORTH_LIBRARY.md) has each library's profile).", ""]
    for path in sorted((root / "src/lib").glob("*.fs")):
        entries = words(path)
        parts += [f"## `{path.relative_to(root)}`", ""]
        for name, stack, text in entries:
            parts.append(f"- `{name}`" + (f" `{stack}`" if stack else "") + (f" - {text}" if text else ""))
        parts.append("" if entries else "(no public words)\n")
        if entries:
            parts.append("")
    return "\n".join(parts).rstrip() + "\n"


def main(argv):
    args = [a for a in argv if not a.startswith("--")]
    root = pathlib.Path(args[0]).resolve() if args else DEFAULT_ROOT
    target, text = root / OUTPUT, render(root)
    if "--write" in argv:
        target.write_text(text, encoding="utf-8")
        print(f"wrote {OUTPUT}")
        return 0
    if not target.exists() or target.read_text(encoding="utf-8") != text:
        print(f"{OUTPUT} is stale: regenerate it with `python3 scripts/lib-index.py --write`")
        return 1
    print(f"{OUTPUT} is current")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
