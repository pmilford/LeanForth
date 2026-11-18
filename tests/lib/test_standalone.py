"""Every src/lib file used on its own, from a folder outside the project (plan task 1.1.8).

For each of the library's files the test copies the file and exactly the files it requires,
transitively (its `require ./x.fs` lines), into a temporary folder outside the checkout and
loads it there with BASE 7 on Gforth (GFORTH) and on gforth-fast beside it (GFORTH_FAST, when
it exists). So a file that uses a word from a file it does not require fails to load: the
"requires only what it uses, and everything it uses" rule is checked, not claimed. After
loading, BASE, the search order and the data stack must be as before, and lf-lib-private
must not be searched (a file that changes BASE or the search order and does not restore it
fails). When the header has an example (indented `\\   ` lines after a line starting
`\\ Example`, with `\\ prints: TEXT` in it), the example runs there too, in decimal, after the file was loaded
with BASE 7, and must print TEXT (whitespace compared as single spaces); an example may
`require lib/x.fs` another library file, which is copied with its own requirements. Every
file has such an example. BASE 7 is unusual on purpose: a number with a digit 7, 8 or 9 does
not read in it and others read as different values, so a file whose numbers depend on the
BASE it is loaded with fails to load or prints a wrong example, where under HEX or decimal it
could pass. A source check finds the rest: a file with any number other than 0, 1 and -1
sets `base @ decimal` before it (and the load check sees BASE restored at its end).

Run from the repository root with GFORTH set (the Makefile does this):
    GFORTH=.tools/gforth/bin/gforth python3 tests/lib/test_standalone.py
"""
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import unittest

from test_sha256 import source_words

ROOT = Path(__file__).resolve().parents[2]
LIB = ROOT / "src" / "lib"
TEST_LIMIT = int(os.environ.get("TEST_TIMEOUT", "300"))
GFORTH = os.environ.get("GFORTH", "gforth")
if "/" in GFORTH:
    GFORTH = str(Path(GFORTH).absolute())
FAST = os.environ.get("GFORTH_FAST") or (GFORTH + "-fast" if "/" in GFORTH else "gforth-fast")
REQUIRE = re.compile(r"^\s*require\s+\./(\S+)", re.M)
EXAMPLE_REQUIRE = re.compile(r"^\s*require\s+lib/(\S+)", re.M)
# What a load leaves: BASE, the depth, the search order's depth and whether lf-lib-private
# is in it. The probe word is defined before loading, so it sees the order as it was.
PROBE = """: order-has? ( wid -- flag ) >r get-order 0 swap 0 ?do swap r@ = or loop r> drop ;
: state. ( -- ) base @ dup decimal . base ! depth . get-order dup . 0 ?do drop loop
  s" lf-lib-private" find-name if s" lf-lib-private" evaluate order-has? . else ." x " then ;
"""


def closure(name):
    """The file and every file it requires, transitively, in src/lib."""
    seen, todo = [], [name]
    while todo:
        f = todo.pop()
        if f in seen:
            continue
        seen.append(f)
        todo += REQUIRE.findall((LIB / f).read_text())
    return seen


def example(name):
    """(program, expected output) of the header's example, or None."""
    lines = (LIB / name).read_text().splitlines()
    start = next((i for i, l in enumerate(lines) if re.match(r"\\ Example", l)), None)
    if start is None:
        return None
    body = []
    for line in lines[start + 1:]:
        if not line.startswith("\\   "):
            if body or not line.startswith("\\"):
                break
            continue   # the example's title goes on, before its code
        body.append(line[4:])
    text = "\n".join(body)
    m = re.search(r"\\ prints: (.*)", text)
    return (text + "\n", " ".join(m.group(1).split())) if m else None


def run(engine, folder, program):
    (folder / "run.fs").write_text(program)
    out = subprocess.run([engine, "run.fs", "-e", "bye"], cwd=folder, stdin=subprocess.DEVNULL,
                         capture_output=True, timeout=TEST_LIMIT)
    return out.returncode, out.stdout.decode(errors="replace"), out.stderr.decode(errors="replace")


class Standalone(unittest.TestCase):
    def engines(self):
        found = [GFORTH] + ([FAST] if shutil.which(FAST) or Path(FAST).exists() else [])
        return found

    def folder(self, name, extra=()):
        scratch = tempfile.TemporaryDirectory(prefix="lf-lib-")
        self.addCleanup(scratch.cleanup)
        folder = Path(scratch.name)
        self.assertFalse(folder.resolve().is_relative_to(ROOT), "the folder must be outside")
        (folder / "lib").mkdir()
        for f in {g for n in (name, *extra) for g in closure(n)}:
            shutil.copy(LIB / f, folder / "lib" / f)
        return folder

    def test_every_file_loads_alone_and_restores_the_interpreter(self):
        files = sorted(p.name for p in LIB.glob("*.fs"))
        self.assertEqual(len(files), 35)
        for name in files:
            folder = self.folder(name)
            # Ends in decimal: under make coverage Gforth writes its block counts with "."
            # at BYE (scripts/coverage-prelude.fs), which scripts/coverage.py reads as decimal.
            program = PROBE + f"7 base ! state. require lib/{name} state. cr decimal\n"
            for engine in self.engines():
                with self.subTest(file=name, engine=Path(engine).name):
                    code, out, err = run(engine, folder, program)
                    self.assertEqual(code, 0, f"{name} does not load alone: {out} {err}")
                    before, after = out.split()[:4], out.split()[4:8]
                    # BASE 7 and the depth, order depth and private flag as before.
                    self.assertEqual(after[0], "7", f"{name} leaves BASE changed")
                    self.assertEqual(after[1], before[1], f"{name} leaves the stack changed")
                    # module.fs, loaded once, puts lf-lib in the search order for good.
                    grown = int(after[2], 7) - int(before[2], 7)
                    lib = "module.fs" in closure(name)
                    self.assertEqual(grown, 1 if lib else 0, f"{name} changes the search order")
                    self.assertEqual(after[3], "0" if lib else "x",
                                     f"{name} leaves lf-lib-private searched")

    def test_examples_run_as_written(self):
        files = sorted(p.name for p in LIB.glob("*.fs"))
        missing = {f for f in files if example(f) is None}
        self.assertEqual(missing, set(), "a header without a runnable example")
        for name in files:
            program, expected = example(name)
            folder = self.folder(name, EXAMPLE_REQUIRE.findall(program))
            for engine in self.engines():
                with self.subTest(file=name, engine=Path(engine).name):
                    code, out, err = run(engine, folder,
                                         f"7 base ! require lib/{name}\ndecimal\n" + program + "decimal\n")
                    self.assertEqual(code, 0, f"{name}'s example fails: {out} {err}")
                    self.assertEqual(" ".join(out.split()), expected, f"{name}'s example")


# A number token of Forth source: digits, perhaps signed or ending in "." (a double).
# Numbers written with #, $ or % name their base and are not matched.
NUMBER = re.compile(r"^-?[0-9]+\.?$")
STRINGS = ('s"', '."', 'c"', 'abort"', 's\\"')


def base_dependent_numbers(text):
    """The numbers of Forth source read before an interpreted `base @ decimal`, other than
    0, 1 and -1 (which read the same in every BASE). Strings and the character after CHAR
    and [CHAR] are skipped."""
    words, found, i, colon, string = source_words(text), [], 0, False, False
    while i < len(words):
        word = words[i].lower()
        if string:
            string = not word.endswith('"')
        elif word in STRINGS:
            string = True
        elif word in ("char", "[char]"):
            i += 1
        elif word == "decimal" and not colon and [w.lower() for w in words[max(i - 2, 0):i]] == ["base", "@"]:
            return found
        elif word in (":", ":noname"):
            colon = True
        elif word == ";":
            colon = False
        elif NUMBER.match(word) and word.rstrip(".") not in ("0", "1", "-1"):
            found.append(words[i])
        i += 1
    return found


class Numbers(unittest.TestCase):
    def test_numbers_are_read_in_decimal(self):
        for p in sorted(LIB.glob("*.fs")):
            with self.subTest(file=p.name):
                self.assertEqual(base_dependent_numbers(p.read_text()), [],
                                 f"{p.name}: numbers before `base @ decimal`")

    def test_the_source_check_sees_numbers(self):
        # Regression pins of the check itself.
        self.assertEqual(base_dependent_numbers("16 constant k ( 99 ) \\ 42\n"), ["16"])
        self.assertEqual(base_dependent_numbers(': f 0 1 -1 ; s" 7 8" [char] 9 #10 $1f'), [])
        self.assertEqual(base_dependent_numbers("base @ decimal 16 constant k base !"), [])
        self.assertEqual(base_dependent_numbers(": f base @ decimal ; 2 constant two"), ["2"])
        self.assertEqual(base_dependent_numbers("-4111 constant x 3. 2constant d"), ["-4111", "3."])


if __name__ == "__main__":
    unittest.main()
