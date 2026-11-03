#!/usr/bin/env python3
"""Fail on Forth that is not portable across the hosts CI runs.

1. Byte order and cell size, in every .fs file under src/:

- byte-access words (C@ C! C, W@ L@ X@ and similar host extensions) appear
  only in files listed in BYTE_MODULES, each with a reason; reading a
  cell's bytes is what makes code depend on byte order;
- no numeric literal needs more than 32 bits, so nothing assumes 64-bit
  cells (use cell, cells and max-n instead).

2. Compile-only words used outside a colon definition, in every .fs file
   under src/ and tests/: Gforth 1.0 accepts some of them interpretively
   (abort", if, do, ...), Gforth 0.7.3 and Forth-2012 do not.

3. Source modules are loaded with REQUIRE, never INCLUDE, in every .fs file
   under src/ and tests/: INCLUDE reloads a file, which would make a second
   copy of its stores. Each module requires its direct dependencies.

4. Every module under src/ that uses a word src/lib/portability.fs defines
   for hosts that lack it (cell, max-n, field:, -rot, ...; read from that
   file's [undefined] guards) has portability.fs among the files it loads,
   directly or through other files: otherwise it works on Gforth only.
   Test helpers are loaded after the modules under test and are not checked.

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
    "src/lib/bytes.fs": "line reader and UTF-8 checks read and write text bytes",
    "src/lib/json.fs": "JSON tokenizer reads text bytes and decodes escapes in place",
    "src/lib/bignum.fs":
        "big numbers read and write decimal digit characters; limbs are only read as cells",
    "src/program/ir-reader.fs":
        "program reader splits source lines into tokens, checks that every character is "
        "printable ASCII and folds A-Z to a-z, as Gforth finds names",
}
LIMIT = 2**31
COMPILE_ONLY = {
    "if", "else", "then", "begin", "while", "repeat", "until", "again",
    "do", "?do", "loop", "+loop", "leave", "unloop", "case", "of", "endof",
    "endcase", "exit", "recurse", ">r", "r>", "r@", "2>r", "2r>", "2r@",
    "abort\"", "__abort__", "does>", "[\']", "[char]", "literal", "postpone",
}


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


def interpreted(text):
    """(line, word) for compile-only words outside colon definitions."""
    found, depth = [], 0
    for lineno, line in enumerate(text.splitlines(), 1):
        for tok in line.split():
            low = tok.lower()
            if low in (":", ":noname", "]"):
                depth = 1
            elif low in (";", "["):
                depth = 0
            elif depth == 0 and low in COMPILE_ONLY:
                found.append((lineno, tok))
    return found


def raw_strip(text):
    """Comments and strings removed, but abort" kept as a token."""
    text = re.sub(r'(^|\s)abort"\s[^"]*"', ' __abort__ ', text, flags=re.I)
    return strip(text)


PORTABILITY = ROOT / "src/lib/portability.fs"
LOAD = re.compile(r"^\s*(?:require|include)\s+(\S+)", re.I)


def adapted_words():
    """The words portability.fs defines where the host lacks them."""
    text = PORTABILITY.read_text()
    return {w.lower() for w in re.findall(r"\[undefined\]\s+(\S+)\s+\[if\]", text, re.I)}


def loaded(path):
    """The repository files that path loads with REQUIRE or INCLUDE. Paths
    starting with ./ or ../ are relative to the loading file, as Gforth
    reads them; others to the repository root; host library files such as
    test/ttester.fs are not in the repository and are skipped."""
    for line in strip(path.read_text(errors="replace")).splitlines():
        hit = LOAD.match(line)
        if hit:
            name = hit.group(1)
            base = path.parent if name.startswith(("./", "../")) else ROOT
            target = (base / name).resolve()
            if target.is_file():
                yield target


def closure(path):
    """Every file that loading path loads, directly or indirectly."""
    seen, todo = set(), [path.resolve()]
    while todo:
        for target in loaded(todo.pop()):
            if target not in seen:
                seen.add(target)
                todo.append(target)
    return seen


def unadapted(words):
    """(module, words) for modules under src/ that use adapted words without
    loading portability.fs."""
    found = []
    for path in sorted((ROOT / "src").rglob("*.fs")):
        if path.resolve() == PORTABILITY.resolve():
            continue
        used = sorted({t.lower() for t in strip(path.read_text()).split()} & words)
        if used and PORTABILITY.resolve() not in closure(path):
            found.append((path.relative_to(ROOT).as_posix(), used))
    return found


def main():
    problems = []
    for path in sorted(list((ROOT / "src").rglob("*.fs")) + list((ROOT / "tests").rglob("*.fs"))):
        rel = path.relative_to(ROOT).as_posix()
        for lineno, line in enumerate(path.read_text(errors="replace").splitlines(), 1):
            if re.match(r"\s*include\s+\S*src/\S+\.fs\b", line, re.I) or \
               (rel.startswith("src/") and re.match(r"\s*include\s+\S+\.fs\b", line, re.I)):
                problems.append(f"{rel}:{lineno}: source module loaded with include; use require")
        for lineno, tok in interpreted(raw_strip(path.read_text(errors="replace"))):
            word = 'abort"' if tok == "__abort__" else tok
            problems.append(f"{rel}:{lineno}: compile-only '{word}' outside a definition")
    for path in sorted((ROOT / "src").rglob("*.fs")):
        rel = path.relative_to(ROOT).as_posix()
        for lineno, line in enumerate(strip(path.read_text()).splitlines(), 1):
            for tok in line.split():
                if tok.lower() in BYTE_WORDS and rel not in BYTE_MODULES:
                    problems.append(f"{rel}:{lineno}: byte access '{tok}' outside a listed text module")
                value = number(tok)
                if value is not None and value >= LIMIT:
                    problems.append(f"{rel}:{lineno}: literal {tok} assumes cells wider than 32 bits")
    for rel, used in unadapted(adapted_words()):
        problems.append(f"{rel}: uses {' '.join(used)} without loading src/lib/portability.fs")
    for p in problems:
        print(p)
    if problems:
        return 1
    print("No byte-order, cell-size, compile-only, include or adapter problems found.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
