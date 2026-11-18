"""Every src/lib file requires, directly, each library file whose words it uses (plan task 1.1.8).

The standalone test (test_standalone.py) loads each file with the files it requires,
transitively, so a file that uses a word of a file it reaches only through another require
still loads: bytes.fs without `require ./blocks.fs` passed, because store.fs requires it
(review lib-tidy, finding 2). This test reads the source instead. For each library file it
finds the names every library file defines (with `:`, CONSTANT, CREATE, VARIABLE, VALUE,
DEFER, the structure words and the library's own defining words), and the words each file
uses; a word a file uses but does not define itself, defined by another library file, must
come from a file that it requires directly (`require ./x.fs`). A name that two library files
define (a private helper of each) is satisfied by either. lib.fs, a loader of a group of
files that uses none of their words, is not checked as a user. A require of a file none of
whose words are used is reported too (portability.fs excepted: its words are the host's on
Gforth, and a file requires it for other hosts).

Run from the repository root: python3 tests/lib/test_requires.py
"""
from pathlib import Path
import re
import unittest

from test_sha256 import source_words

ROOT = Path(__file__).resolve().parents[2]
LIB = ROOT / "src" / "lib"
REQUIRE = re.compile(r"^\s*require\s+\./(\S+)", re.M)
# Words that define the next name in the source: Forth-2012's, Gforth's and the library's own.
DEFINERS = {":", "constant", "2constant", "create", "variable", "2variable", "value", "defer",
            "begin-structure", "field:", "cfield:", "+field", "synonym",
            "xt-table:", "cons-class:", "context-record:", "context-store:", "context-walk:",
            "context-walk2:", "context-frames:", "context-slab:", "walk:", "walk2:", "frames:",
            "reader:", "json:", "sha256:", "sections:", "store:", "json-writer:", "sorter:",
            "slab:", "memo:", "pqueue:", "htab:", "big-arena:"}
# Words after which a defining word is named, not run.
QUOTING = {"[undefined]", "[defined]", "'", "[']", "postpone"}
STRINGS = ('s"', '."', 'c"', 'abort"', 's\\"')
NOT_A_USER = {"lib.fs"}
ALWAYS_ALLOWED = {"portability.fs"}


def code_words(text):
    """The words of Forth source without comments and the text of strings."""
    words, out, string = source_words(text), [], False
    for word in words:
        low = word.lower()
        if string:
            string = not word.endswith('"')
        elif low in STRINGS:
            string = True
        else:
            out.append(low)
    return out


def definitions(words):
    """The names the words define when they are interpreted: a defining word inside a colon
    definition defines nothing now."""
    names, compiling = set(), False
    for i, word in enumerate(words[:-1]):
        if word == ";":
            compiling = False
        elif compiling:
            continue
        elif word == ":noname":
            compiling = True
        elif word in DEFINERS and (i == 0 or words[i - 1] not in QUOTING):
            names.add(words[i + 1])
            compiling = word == ":"
    return names


def audit(sources):
    """{file: (missing, extra)} for {file: source text}: missing maps each library file used
    but not required directly to the words used from it; extra lists the files required whose
    words are not used."""
    words = {f: code_words(t) for f, t in sources.items()}
    defs = {f: definitions(w) for f, w in words.items()}
    owners = {}
    for f, names in defs.items():
        for name in names:
            owners.setdefault(name, set()).add(f)
    result = {}
    for f in sorted(sources):
        if f in NOT_A_USER:
            continue
        required = set(REQUIRE.findall(sources[f]))
        used = {}
        for word in set(words[f]) - defs[f]:
            for g in owners.get(word, ()):
                used.setdefault(g, set()).add(word)
        missing = {g: ws for g, ws in used.items()
                   if g not in required and not (owners_of(ws, owners) & required)}
        extra = sorted(r for r in required if r not in used and r not in ALWAYS_ALLOWED)
        if missing or extra:
            result[f] = (missing, extra)
    return result


def owners_of(words, owners):
    """The files that define every one of the words (a name two files define is satisfied by
    either)."""
    common = None
    for word in words:
        common = owners[word] if common is None else common & owners[word]
    return common or set()


class Requires(unittest.TestCase):
    def test_each_file_requires_what_it_uses(self):
        sources = {p.name: p.read_text() for p in sorted(LIB.glob("*.fs"))}
        problems = audit(sources)
        report = "\n".join(
            f"{f}: " + "; ".join([f"uses {g} ({' '.join(sorted(ws)[:6])}) without requiring it"
                                  for g, ws in sorted(m.items())]
                                 + [f"requires {r} but uses none of its words" for r in x])
            for f, (m, x) in problems.items())
        self.assertEqual(problems, {}, "\n" + report)

    def test_the_audit_sees_a_missing_and_an_extra_require(self):
        # Regression pins of the check itself, on a small library of three files.
        a = ": a-word ( -- ) ;\n"
        b = "require ./a.fs\n: b-word ( -- ) a-word ;\n"
        c = "require ./b.fs\n: c-word ( -- ) b-word a-word ;   \\ a-word only through b.fs\n"
        self.assertEqual(audit({"a.fs": a, "b.fs": b, "c.fs": c}),
                         {"c.fs": ({"a.fs": {"a-word"}}, [])})
        c2 = "require ./a.fs\nrequire ./b.fs\n: c-word ( -- ) b-word a-word ;\n"
        self.assertEqual(audit({"a.fs": a, "b.fs": b, "c.fs": c2}), {})
        d = 'require ./a.fs\n: d-word ( -- ) ." a-word" ;  ( a-word )\n'
        self.assertEqual(audit({"a.fs": a, "d.fs": d}), {"d.fs": ({}, ["a.fs"])})
        e = "require ./a.fs\n: a-word ( -- ) ;\n: e-word ( -- ) a-word ;\n"
        self.assertEqual(audit({"a.fs": a, "e.fs": e}), {"e.fs": ({}, ["a.fs"])})


if __name__ == "__main__":
    unittest.main()
