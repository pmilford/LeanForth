#!/usr/bin/env python3
"""Fail if current Forth source could depend on byte order or cell size.

Checks every .fs file under src/ except src/legacy/ (superseded code):

- byte-access words (C@ C! C, W@ L@ X@ and similar host extensions) appear
  only in files listed in BYTE_MODULES, each with a reason; reading a
  cell's bytes is what makes code depend on byte order;
- no numeric literal needs more than 32 bits, so nothing assumes 64-bit
  cells (use cell, cells and max-n instead).

Comments and strings are ignored. See docs/development/FORTH_STYLE.md,
section 8.
"""
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
BYTE_WORDS = {
    "c@", "c!", "c,", "c+!", "w@", "w!", "w,", "l@", "l!", "l,", "x@", "x!",
    "x,", "sw@", "uw@", "sl@", "ul@", "sx@", "ux@", "be-w!", "le-w!",
}
# Files allowed to use byte access, with the reason. Text modules only.
BYTE_MODULES = {
}
LIMIT = 2**31


def strip(text):
    lines = []
    for line in text.splitlines():
        line = re.sub(r"(^|\s)\\(\s.*)?$", " ", line)        # \ comments
        line = re.sub(r'(^|\s)(\.?\(|s"|\."|c"|abort")\s[^")]*[")]', " ", line, flags=re.I)
        lines.append(line)
    return "\n".join(lines)


def number(token):
    t = token.lower()
    for prefix, base in (("$", 16), ("#", 10), ("%", 2)):
        if t.startswith(prefix):
            t, b = t[1:], base
            break
    else:
        b = 10
    t = t.lstrip("-")
    try:
        return int(t, b)
    except ValueError:
        return None


def main():
    problems = []
    for path in sorted((ROOT / "src").rglob("*.fs")):
        rel = path.relative_to(ROOT).as_posix()
        if rel.startswith("src/legacy/"):
            continue
        for lineno, line in enumerate(strip(path.read_text()).splitlines(), 1):
            for tok in line.split():
                if tok.lower() in BYTE_WORDS and rel not in BYTE_MODULES:
                    problems.append(f"{rel}:{lineno}: byte access '{tok}' outside a listed text module")
                value = number(tok)
                if value is not None and value >= LIMIT:
                    problems.append(f"{rel}:{lineno}: literal {tok} assumes cells wider than 32 bits")
    for p in problems:
        print(p)
    if problems:
        return 1
    print("No byte-order or cell-size dependence found in current Forth source.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
