"""Oracle and standalone tests of the Forth SHA-256 library (src/lib/sha256.fs).

1. Oracle: seeded random messages (every length from 0 to 300 bytes, a
   few of 1 to 200 KiB, and one of 1 MiB), each written to a file, are
   hashed by tests/lib/sha256-driver.fs in updates of random sizes (0 to
   139 bytes, so empty updates and updates across block boundaries
   occur). Every digest must equal Python's hashlib.sha256, once with the
   fast round and schedule of 64-bit cells and once with the plain
   definitions (sha256-portable defined first). One file is also checked
   against the sha256sum program when the host has it.
2. Standalone: the library and the four files it requires,
   src/lib/portability.fs, bits.fs, decimal.fs and module.fs, are copied into a fresh
   folder outside the project, and the example in the library's header
   runs there as a program of its own and prints the SHA-256 of "abc".
   There, too, the interface is exactly the documented one (ADR 0010):
   every public word is found and every other name the library defines,
   read from its source, is hidden in the private word list; and the
   public names are exactly PUBLIC, each starting sha- or sha256-.

Run with GFORTH set to the Forth binary (the Makefile does this). Set
LF_SHA256_SEED to change the seed (default 20261103).
"""
import hashlib
import os
from pathlib import Path
import random
import shutil
import subprocess
import tempfile
import unittest
TEST_LIMIT = int(os.environ.get("TEST_TIMEOUT", "1800"))  # seconds; make exports it

ROOT = Path(__file__).resolve().parents[2]
GFORTH = os.environ.get("GFORTH", "gforth")
if "/" in GFORTH:   # a path, such as the Makefile's relative one: valid in any folder
    GFORTH = str(Path(GFORTH).absolute())
DRIVER = ROOT / "tests" / "lib" / "sha256-driver.fs"
LIBRARY = ROOT / "src" / "lib" / "sha256.fs"
PORTABILITY = ROOT / "src" / "lib" / "portability.fs"
MODULE = ROOT / "src" / "lib" / "module.fs"
BITS = ROOT / "src" / "lib" / "bits.fs"
DECIMAL = ROOT / "src" / "lib" / "decimal.fs"
# The documented interface: the hashing words and FIPS 180-4's functions.
PUBLIC = {"/sha256", "sha256:", "sha256-init", "sha256-update", "sha256-line", "sha256-final",
          "sha256-hex", "sha-digest-bytes", "sha-w32", "sha-shr", "sha-rotr", "sha-ch",
          "sha-maj", "sha-big-sigma0", "sha-big-sigma1", "sha-small-sigma0",
          "sha-small-sigma1"}
DEFINERS = {":", "constant", "create", "begin-structure", "field:", "+field", "variable",
            "value", "2constant"}
SEED = int(os.environ.get("LF_SHA256_SEED", "20261103"))
ABC = hashlib.sha256(b"abc").hexdigest()


def gforth(args, cwd=ROOT):
    """Run Gforth on files (no standard input) and give its output lines."""
    run = subprocess.run([GFORTH, *map(str, args), "-e", "bye"], cwd=cwd,
                         stdin=subprocess.DEVNULL, capture_output=True, timeout=TEST_LIMIT)
    if run.returncode != 0:
        raise AssertionError(f"gforth failed ({run.returncode}): "
                             f"{run.stdout.decode()} {run.stderr.decode()}")
    return run.stdout.decode().split()


def messages(rng):
    lengths = list(range(301)) + [1024, 4096 + 63, 65536 + 1, 200 * 1024 + 55, 1 << 20]
    return [rng.randbytes(n) for n in lengths]


def source_words(text):
    """The words of Forth source, without \\ comments, ( ) comments and the
    text of .( ) messages."""
    words, skipping = [], None
    for line in text.splitlines():
        tokens = line.split()
        if "\\" in tokens:
            tokens = tokens[:tokens.index("\\")]
        for token in tokens:
            if skipping:
                if token.endswith(")"):
                    skipping = None
            elif token in ("(", ".("):
                skipping = token
            else:
                words.append(token)
    return words


def defined_names(text):
    """{name: public} for every name the library defines, public when it is
    defined while lf-lib is the compilation word list."""
    words, public, names, compiling = source_words(text), False, {}, False
    for i, word in enumerate(words):
        low = word.lower()
        if low == ";":
            compiling = False
        elif compiling:
            continue   # a defining word inside a definition defines nothing now
        elif low == "module-open":
            public = False
        elif low == "set-current" and i > 0:
            public = words[i - 1].lower() == "lf-lib"
        elif low in DEFINERS and i + 1 < len(words):
            names[words[i + 1].lower()] = public
            compiling = low == ":"
    return names


def header_example():
    """The example program of the library's header comment."""
    lines = LIBRARY.read_text().splitlines()
    start = next(i for i, l in enumerate(lines) if l.startswith("\\   sha256: hasher"))
    end = next(i for i in range(start, len(lines)) if not lines[i].startswith("\\   "))
    return "\n".join(l[4:] for l in lines[start:end]) + "\n"


class Sha256Oracle(unittest.TestCase):
    def setUp(self):
        self.scratch = tempfile.TemporaryDirectory()
        self.dir = Path(self.scratch.name)
        rng = random.Random(SEED)
        self.cases = []
        commands = []
        for n, data in enumerate(messages(rng)):
            path = self.dir / f"m{n}.bin"
            path.write_bytes(data)
            seed = rng.randrange(1, 1 << 30)
            self.cases.append((path, hashlib.sha256(data).hexdigest()))
            commands.append(f's" {path}" {seed} hash-file')
        (self.dir / "cases.fs").write_text("\n".join(commands) + "\n")
        (self.dir / "plain.fs").write_text(": sha256-portable ( -- ) ;\n")

    def tearDown(self):
        self.scratch.cleanup()

    def check(self, prelude):
        digests = gforth(prelude + [DRIVER, self.dir / "cases.fs"])
        self.assertEqual(len(digests), len(self.cases))
        for (path, expected), got in zip(self.cases, digests):
            self.assertEqual(got, expected, f"{path.name}: {path.stat().st_size} bytes")

    def test_fast(self):
        self.check([])

    def test_plain(self):
        self.check([self.dir / "plain.fs"])

    @unittest.skipUnless(shutil.which("sha256sum"), "no sha256sum on this host")
    def test_sha256sum(self):
        path, expected = self.cases[-1]
        out = subprocess.run(["sha256sum", str(path)], capture_output=True, check=True)
        self.assertEqual(out.stdout.split()[0].decode(), expected)


class Sha256Standalone(unittest.TestCase):
    def test_example_outside_the_project(self):
        with tempfile.TemporaryDirectory() as scratch:
            folder = Path(scratch)
            self.assertFalse(folder.resolve().is_relative_to(ROOT.resolve()))
            (folder / "lib").mkdir()
            for source in (LIBRARY, PORTABILITY, MODULE, BITS, DECIMAL):
                shutil.copy(source, folder / "lib" / source.name)
            (folder / "example.fs").write_text("require lib/sha256.fs\n" + header_example())
            self.assertEqual(gforth(["example.fs"], cwd=folder), [ABC])
            names = defined_names(LIBRARY.read_text())
            checks = ["require lib/sha256.fs"]
            for name, public in sorted(names.items()):
                test = "0=" if public else ""
                label = "missing" if public else "visible"
                checks.append(f"[defined] {name} {test} [if] .( {label}:{name}) cr [then]")
            (folder / "interface.fs").write_text("\n".join(checks) + "\n.( checked) cr\n")
            self.assertEqual(gforth(["interface.fs"], cwd=folder), ["checked"])
        self.assertEqual({name for name, public in names.items() if public}, PUBLIC)
        self.assertGreater(len(names), 60)   # the source was read, helpers and all
        self.assertTrue(all(n.startswith(("sha-", "sha256", "/sha256")) for n in PUBLIC))


if __name__ == "__main__":
    unittest.main()
