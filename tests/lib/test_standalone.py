"""Every src/lib file used on its own, from a folder outside the project (plan task 1.1.8).

For each of the library's files the test copies the file and exactly the files it requires,
transitively (its `require ./x.fs` lines), into a temporary folder outside the checkout and
loads it there under HEX on Gforth (GFORTH) and on gforth-fast beside it (GFORTH_FAST, when
it exists). So a file that uses a word from a file it does not require fails to load: the
"requires only what it uses, and everything it uses" rule is checked, not claimed. After
loading, BASE, the search order and the data stack must be as before, and lf-lib-private
must not be searched (a file that changes BASE or the search order and does not restore it
fails). When the header has an example (indented `\\   ` lines after a line starting
`\\ Example`, with `\\ prints: TEXT` in it), the example runs there too, in decimal, and must
print TEXT (whitespace compared as single spaces). Files without such an example are listed
in NO_EXAMPLE, which may only shrink.

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

ROOT = Path(__file__).resolve().parents[2]
LIB = ROOT / "src" / "lib"
TEST_LIMIT = int(os.environ.get("TEST_TIMEOUT", "300"))
GFORTH = os.environ.get("GFORTH", "gforth")
if "/" in GFORTH:
    GFORTH = str(Path(GFORTH).absolute())
FAST = os.environ.get("GFORTH_FAST") or (GFORTH + "-fast" if "/" in GFORTH else "gforth-fast")
REQUIRE = re.compile(r"^\s*require\s+\./(\S+)", re.M)
# Files whose header has no runnable example yet (plan task 1.1.8): may only shrink.
NO_EXAMPLE = {
    "bigint.fs", "bits.fs", "blocks.fs", "cons.fs", "context.fs", "decimal.fs", "frame.fs",
    "hash32.fs", "htab.fs", "lib.fs", "memo.fs", "module.fs", "node.fs", "outcome.fs",
    "pools.fs", "portability.fs", "pqueue.fs", "runs.fs", "sections.fs", "sha256.fs",
    "slab.fs", "sort.fs", "store-columns.fs", "store.fs", "task.fs", "text-rule.fs",
    "text-run.fs", "walk.fs", "xt-table.fs",
}
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
            break
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

    def folder(self, name):
        scratch = tempfile.TemporaryDirectory(prefix="lf-lib-")
        self.addCleanup(scratch.cleanup)
        folder = Path(scratch.name)
        self.assertFalse(folder.resolve().is_relative_to(ROOT), "the folder must be outside")
        (folder / "lib").mkdir()
        for f in closure(name):
            shutil.copy(LIB / f, folder / "lib" / f)
        return folder

    def test_every_file_loads_alone_and_restores_the_interpreter(self):
        files = sorted(p.name for p in LIB.glob("*.fs"))
        self.assertEqual(len(files), 35)
        for name in files:
            folder = self.folder(name)
            program = PROBE + f"hex state. require lib/{name} state. cr\n"
            for engine in self.engines():
                with self.subTest(file=name, engine=Path(engine).name):
                    code, out, err = run(engine, folder, program)
                    self.assertEqual(code, 0, f"{name} does not load alone: {out} {err}")
                    before, after = out.split()[:4], out.split()[4:8]
                    # BASE 16 and the depth, order depth and private flag as before.
                    self.assertEqual(after[0], "16", f"{name} leaves BASE changed")
                    self.assertEqual(after[1], before[1], f"{name} leaves the stack changed")
                    # module.fs, loaded once, puts lf-lib in the search order for good.
                    grown = int(after[2], 16) - int(before[2], 16)
                    lib = "module.fs" in closure(name)
                    self.assertEqual(grown, 1 if lib else 0, f"{name} changes the search order")
                    self.assertEqual(after[3], "0" if lib else "x",
                                     f"{name} leaves lf-lib-private searched")

    def test_examples_run_as_written(self):
        files = sorted(p.name for p in LIB.glob("*.fs"))
        missing = {f for f in files if example(f) is None}
        self.assertLessEqual(missing, NO_EXAMPLE, "a header lost its example")
        self.assertEqual(missing, NO_EXAMPLE, "a new example: take the file off NO_EXAMPLE")
        for name in sorted(set(files) - missing):
            program, expected = example(name)
            folder = self.folder(name)
            for engine in self.engines():
                with self.subTest(file=name, engine=Path(engine).name):
                    code, out, err = run(engine, folder, f"require lib/{name}\ndecimal\n" + program)
                    self.assertEqual(code, 0, f"{name}'s example fails: {out} {err}")
                    self.assertEqual(" ".join(out.split()), expected, f"{name}'s example")


if __name__ == "__main__":
    unittest.main()
