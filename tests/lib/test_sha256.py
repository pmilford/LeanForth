"""Oracle and standalone tests of the Forth SHA-256 library (src/lib/sha256.fs).

1. Oracle: seeded random messages (every length from 0 to 300 bytes, a
   few of 1 to 200 KiB, and one of 1 MiB), each written to a file, are
   hashed by tests/lib/sha256-driver.fs in updates of random sizes (0 to
   139 bytes, so empty updates and updates across block boundaries
   occur). Every digest must equal Python's hashlib.sha256, once with the
   fast round and schedule of 64-bit cells and once with the plain
   definitions (sha256-portable defined first). One file is also checked
   against the sha256sum program when the host has it.
2. Standalone: the library and the one file it requires,
   src/lib/portability.fs, are copied into a fresh folder outside the
   project, and the example in the library's header runs there as a
   program of its own and prints the SHA-256 of "abc".

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

ROOT = Path(__file__).resolve().parents[2]
GFORTH = os.environ.get("GFORTH", "gforth")
if "/" in GFORTH:   # a path, such as the Makefile's relative one: valid in any folder
    GFORTH = str(Path(GFORTH).absolute())
DRIVER = ROOT / "tests" / "lib" / "sha256-driver.fs"
LIBRARY = ROOT / "src" / "lib" / "sha256.fs"
PORTABILITY = ROOT / "src" / "lib" / "portability.fs"
SEED = int(os.environ.get("LF_SHA256_SEED", "20261103"))
ABC = hashlib.sha256(b"abc").hexdigest()


def gforth(args, cwd=ROOT):
    """Run Gforth on files (no standard input) and give its output lines."""
    run = subprocess.run([GFORTH, *map(str, args), "-e", "bye"], cwd=cwd,
                         stdin=subprocess.DEVNULL, capture_output=True, timeout=300)
    if run.returncode != 0:
        raise AssertionError(f"gforth failed ({run.returncode}): "
                             f"{run.stdout.decode()} {run.stderr.decode()}")
    return run.stdout.decode().split()


def messages(rng):
    lengths = list(range(301)) + [1024, 4096 + 63, 65536 + 1, 200 * 1024 + 55, 1 << 20]
    return [rng.randbytes(n) for n in lengths]


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
            shutil.copy(LIBRARY, folder / "lib" / "sha256.fs")
            shutil.copy(PORTABILITY, folder / "lib" / "portability.fs")
            (folder / "example.fs").write_text("require lib/sha256.fs\n" + header_example())
            self.assertEqual(gforth(["example.fs"], cwd=folder), [ABC])


if __name__ == "__main__":
    unittest.main()
