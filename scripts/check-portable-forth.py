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
   file's [undefined] guards) loads portability.fs, directly or through
   other files, before its first use of such a word: otherwise it works on
   Gforth only. Loads are REQUIRE or INCLUDE anywhere in a line, outside
   comments (including ( ... ) across lines) and outside an [IF] branch
   that a literal condition skips (0 [IF], FALSE [IF], or the [ELSE] of
   a nonzero or TRUE one). Other conditions cannot be read statically, so
   a load under one, such as lib.fs's load-once guard, counts. A word
   named after [UNDEFINED] or [DEFINED] is not a use. Test helpers are
   loaded after the modules under test and are not checked. Before the
   repository, the check runs on a scratch tree of its own (LOAD_CASES)
   and fails if it misjudges a module there.

Comments and strings are ignored. See docs/development/FORTH_STYLE.md,
section 8.
"""
import pathlib
import re
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
BYTE_WORDS = {
    "c@", "c!", "c,", "c+!", "w@", "w!", "w,", "l@", "l!", "l,", "x@", "x!",
    "x,", "sw@", "uw@", "sl@", "ul@", "sx@", "ux@", "be-w!", "le-w!",
}
# Files allowed to use byte access, with the reason. Text modules only.
BYTE_MODULES = {
    "src/lib/bytes.fs": "line reader and UTF-8 checks read and write text bytes",
    "src/lib/json.fs": "JSON tokenizer reads text bytes and decodes escapes in place",
    "src/lib/json-write.fs":
        "JSON writer reads string bytes to escape them and builds digits and escapes as text",
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


PORTABILITY = "src/lib/portability.fs"
LOADING = {"require", "include"}
NAMING = {"[undefined]", "[defined]"}   # the next word is named, not used
STRINGS = {'s"', 'c"', '."', 'abort"'}


def source_words(text):
    """The words of Forth source in order, as written, without comments or
    the text of strings: \\ to the end of the line, ( ... ) and .( ... )
    across lines, and s" c" ." abort" and s\\" strings."""
    words, i, n = [], 0, len(text)
    while True:
        while i < n and text[i].isspace():
            i += 1
        if i >= n:
            return words
        j = i
        while j < n and not text[j].isspace():
            j += 1
        low = text[i:j].lower()
        if low == "\\":
            end = text.find("\n", j)
        elif low in ("(", ".("):
            end = text.find(")", j)
        elif low in STRINGS:
            end = text.find('"', j + 1)
        elif low == 's\\"':
            end = j + 1
            while end < n and text[end] != '"':
                end += 2 if text[end] == "\\" else 1
        else:
            words.append(text[i:j])
            i = j
            continue
        i = n if end < 0 else end + 1


def literal_flag(word):
    """True or False for a flag a static check can read (a number, TRUE or
    FALSE); None for anything else."""
    low = (word or "").lower()
    if low in ("true", "false"):
        return low == "true"
    value = number(low)
    return None if value is None else value != 0


def compiled_words(text):
    """The words of Forth source that may be compiled: those inside an
    [IF] branch a literal condition skips are left out, with the [IF],
    [ELSE] and [THEN] words themselves."""
    words, branches, previous = [], [], None
    for word in source_words(text):
        low = word.lower()
        if low == "[if]":
            branches.append(literal_flag(previous))
        elif low == "[else]" and branches:
            branches[-1] = None if branches[-1] is None else not branches[-1]
        elif low == "[then]" and branches:
            branches.pop()
        elif False not in branches:
            words.append(word)
        previous = word
    return words


def adapted_words(portability):
    """The words portability.fs defines where the host lacks them."""
    text = portability.read_text()
    return {w.lower() for w in re.findall(r"\[undefined\]\s+(\S+)\s+\[if\]", text, re.I)}


def loads(path, words, root):
    """(position, file) for each file of the tree under root that path loads
    with REQUIRE or INCLUDE, position being the index in words, path's
    compiled words. Paths starting with ./ or ../ are relative to the
    loading file, as Gforth reads them; others to root; host library files
    such as test/ttester.fs are not in the tree and are skipped."""
    for k in range(len(words) - 1):
        if words[k].lower() in LOADING:
            name = words[k + 1]
            base = path.parent if name.startswith(("./", "../")) else root
            target = (base / name).resolve()
            if target.is_file():
                yield k, target


def closure(path, root):
    """Every file that loading path loads, directly or indirectly."""
    seen, todo = set(), [path.resolve()]
    while todo:
        file = todo.pop()
        words = compiled_words(file.read_text(errors="replace"))
        for _, target in loads(file, words, root):
            if target not in seen:
                seen.add(target)
                todo.append(target)
    return seen


def uses(words, adapted):
    """(position, word) for each use of an adapted word in words."""
    for k, word in enumerate(words):
        if word.lower() in adapted and (k == 0 or words[k - 1].lower() not in NAMING):
            yield k, word.lower()


def unadapted(root):
    """(module, words) for each module under root/src that uses adapted words
    before it loads portability.fs (or never loads it)."""
    port = (root / PORTABILITY).resolve()
    adapted, found = adapted_words(port), []
    for path in sorted((root / "src").rglob("*.fs")):
        if path.resolve() == port:
            continue
        words = compiled_words(path.read_text(errors="replace"))
        loaded = (k for k, target in loads(path, words, root)
                  if target == port or port in closure(target, root))
        first = next(loaded, len(words))
        early = sorted({word for k, word in uses(words, adapted) if k < first})
        if early:
            found.append((path.relative_to(root).as_posix(), early))
    return found


# The load check's own test: a scratch tree with this portability.fs and
# one module per case under src/m/, and whether the check must report it.
SCRATCH_PORTABILITY = """\\ Adapted words for the load check's test.
[undefined] cell [if] 1 cells constant cell [then]
[undefined] max-n [if] -1 1 rshift constant max-n [then]
[undefined] -rot [if] : -rot ( x y z -- z x y ) rot rot ; [then]
"""
LOAD_CASES = {
    "plain.fs": (": a ( -- n ) cell ;\n", True),
    "loads.fs": ("require ../lib/portability.fs\n: a ( -- n ) cell ;\n", False),
    "through.fs": ("require ./loads.fs\n: b ( -- n ) max-n ;\n", False),
    "late.fs": (": a ( -- n ) cell ;\nrequire ../lib/portability.fs\n", True),
    "comment.fs": ("( Once this file did\nrequire ../lib/portability.fs\nbut no more. )\n"
                   ": a ( -- n ) cell ;\n", True),
    "skipped.fs": ("0 [if]\nrequire ../lib/portability.fs\n[then]\n"
                   ": a ( x y z -- z x y ) -rot ;\n", True),
    "else.fs": ("true [if] [else] require ../lib/portability.fs [then]\n"
                ": a ( -- n ) max-n ;\n", True),
    "guarded.fs": ("[undefined] max-n [if] require ../lib/portability.fs [then]\n"
                   ": a ( -- n ) max-n ;\n", False),
    "midline.fs": ("decimal require ../lib/portability.fs hex\n: a ( -- n ) cell ;\n", False),
    "texts.fs": (': a ( -- c-addr u ) s\\" say \\"hi\\" to a cell here\\n" ;\n'
                 ': b ( -- ) ." a cell here" ;\n: c ( -- c-addr u ) s" cell size" ;\n'
                 ".( no cell here ) cr \\ nor cell here\n[undefined] cell [if] [then]\n",
                 False),
}


def load_check_misjudged():
    """The modules of LOAD_CASES that the load check judges wrongly."""
    with tempfile.TemporaryDirectory() as scratch:
        root = pathlib.Path(scratch)
        (root / "src/m").mkdir(parents=True)
        (root / "src/lib").mkdir()
        (root / PORTABILITY).write_text(SCRATCH_PORTABILITY)
        for name, (text, _) in LOAD_CASES.items():
            (root / "src/m" / name).write_text(text)
        reported = {pathlib.PurePosixPath(rel).name for rel, _ in unadapted(root)}
    expected = {name for name, (_, report) in LOAD_CASES.items() if report}
    return sorted(reported ^ expected)


def main():
    problems = [f"load check misjudges its test module src/m/{name}"
                for name in load_check_misjudged()]
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
    for rel, used in unadapted(ROOT):
        problems.append(f"{rel}: uses {' '.join(used)} before loading {PORTABILITY}")
    for p in problems:
        print(p)
    if problems:
        return 1
    print("No byte-order, cell-size, compile-only, include or adapter problems found.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
