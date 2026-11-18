"""Independent tests of the sectioned-file library (src/lib/sections.fs).

1. Reader: tests/lib/sections-driver.fs writes the fixture file; this
   file parses it with Python alone (magic, version, byte-order value,
   header fields, table, offsets and 4096-byte alignment, zero padding,
   every section's SHA-256 with hashlib, the header's SHA-256, the data
   itself).
2. Paths: the file written by the block path (default), by the forced
   field-by-field path (lf-u32-fields) and with the Forth-2012 u32 words
   (lf-u32-portable) is byte for byte the same, and a second write
   repeats it (determinism).
3. Faults: the Forth reader refuses the file after one byte is changed in
   the header (rejected), after each section's byte changes (that section
   rejected) and after truncation (invalid).
4. Standalone: the library and the five files it requires are copied
   into a folder outside the project; the header's example runs there
   and the public interface is exactly the documented one (ADR 0010).

Run with GFORTH set to the Forth binary (the Makefile does this).
"""
import hashlib
import os
from pathlib import Path
import shutil
import struct
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
from test_sha256 import defined_names   # noqa: E402  (the Forth source reader)

TEST_LIMIT = int(os.environ.get("TEST_TIMEOUT", "1800"))
ROOT = Path(__file__).resolve().parents[2]
GFORTH = os.environ.get("GFORTH", "gforth")
if "/" in GFORTH:
    GFORTH = str(Path(GFORTH).absolute())
DRIVER = ROOT / "tests" / "lib" / "sections-driver.fs"
LIB = ROOT / "src" / "lib"
LIBRARY = LIB / "sections.fs"
NEEDED = ["sections.fs", "portability.fs", "module.fs", "outcome.fs", "u32.fs", "sha256.fs",
          "bits.fs", "decimal.fs"]
PUBLIC = {"/sections", "sections:", "sections-init", "sections-field!", "sections-field@",
          "sections-add", "sections-write", "sections-open", "sections-count",
          "sections-info", "sections-read", "sections-close", "sections-align",
          "sections-max", "sections-suffix"}
OK, INVALID, REJECTED = "0", "1", "4"


def gforth(args, env=None, cwd=ROOT):
    run = subprocess.run([GFORTH, *map(str, args), "-e", "bye"], cwd=cwd, env=env,
                         stdin=subprocess.DEVNULL, capture_output=True, timeout=TEST_LIMIT)
    if run.returncode != 0:
        raise AssertionError(f"gforth failed ({run.returncode}): "
                             f"{run.stdout.decode()} {run.stderr.decode()}")
    return run.stdout.decode().split("\n")


def driver(cmd, path, mode=None):
    env = dict(os.environ, SECT_CMD=cmd, SECT_PATH=str(path))
    if mode:
        env["SECT_MODE"] = mode
    return [line.strip() for line in gforth([DRIVER], env=env) if line.strip()]


def fixture_sections():
    a = b"".join(struct.pack("<I", (i * i + 7) & 0xFFFFFFFF) for i in range(1000))
    c = bytes((i * 31) % 251 for i in range(5000))
    d = bytes((i * 31) % 251 for i in range(4096))
    return [(1, 4, 1000, a), (2, 1, 0, b""), (3, 1, 5000, c), (4, 8, 512, d)]


def padded(n):
    return (n + 4095) // 4096 * 4096


def parse(data):
    """The format, read from its description alone: [(kind, unit, count, bytes)], fields."""
    assert data[:8] == b"SECTFILE"
    version, order, n = struct.unpack_from("<III", data, 8)
    assert (version, order) == (1, 0x01020304) and n <= 62
    fields = struct.unpack_from("<16I", data, 24)
    assert hashlib.sha256(data[:4064]).digest() == data[4064:4096]
    assert len(data) % 4096 == 0
    assert not any(data[96 + 64 * n:4064])   # unused table is zero
    pos, out = 4096, []
    for i in range(n):
        kind, unit, count, offset, length, digest = struct.unpack_from("<IIQQQ32s", data, 96 + 64 * i)
        assert length == unit * count and offset == pos and offset % 4096 == 0
        body = data[offset:offset + length]
        assert hashlib.sha256(body).digest() == digest
        assert not any(data[offset + length:offset + padded(length)])   # zero padding
        pos += padded(length)
        out.append((kind, unit, count, body))
    assert pos == len(data)
    return out, fields


class Sections(unittest.TestCase):
    def setUp(self):
        self.scratch = tempfile.TemporaryDirectory()
        self.dir = Path(self.scratch.name)

    def tearDown(self):
        self.scratch.cleanup()

    def written(self, name, mode=None):
        path = self.dir / name
        self.assertEqual(driver("write", path, mode), [OK])
        return path.read_bytes()

    def test_independent_reader(self):
        sections, fields = parse(self.written("a.bin"))
        self.assertEqual(sections, fixture_sections())
        self.assertEqual(list(fields), [1000 * i + 1 for i in range(16)])
        self.assertEqual(len(self.written("a.bin")), 4096 + 4096 + 8192 + 4096)

    def test_paths_and_determinism(self):
        block = self.written("block.bin")
        self.assertEqual(block, self.written("block2.bin"))
        self.assertEqual(block, self.written("fields.bin", "fields"))
        self.assertEqual(block, self.written("portable.bin", "portable"))

    def test_forth_reads_what_python_reads(self):
        path = self.dir / "r.bin"
        self.written("r.bin")
        self.assertEqual(driver("read", path), ["open 0"] + [f"section {i} 0" for i in range(4)])

    def test_faults(self):
        path = self.dir / "f.bin"
        good = self.written("f.bin")
        for offset in (0, 20, 30, 100, 3000, 4064, 4095):   # header bytes
            data = bytearray(good)
            data[offset] ^= 1
            path.write_bytes(data)
            expected = INVALID if offset < 8 else REJECTED
            self.assertEqual(driver("read", path), [f"open {expected}"], f"header byte {offset}")
        for index, offset in enumerate((4096, 8192, 8192, 16384)):   # a byte of each section
            if index == 1:
                continue
            data = bytearray(good)
            data[offset + 3] ^= 0x80
            path.write_bytes(data)
            expected = ["open 0"] + [f"section {i} {REJECTED if i == index else OK}"
                                      for i in range(4)]
            self.assertEqual(driver("read", path), expected, f"section {index}")
        for size in (0, 100, 4095, 4096, 5000, len(good) - 1):
            path.write_bytes(good[:size])
            self.assertEqual(driver("read", path), [f"open {INVALID}"], f"truncated to {size}")
        path.write_bytes(good + b"\0")
        self.assertEqual(driver("read", path), [f"open {INVALID}"])


def header_example():
    lines = LIBRARY.read_text().splitlines()
    start = next(i for i, l in enumerate(lines) if l.startswith("\\   sections: sf"))
    end = next(i for i in range(start, len(lines)) if not lines[i].startswith("\\   "))
    return "\n".join(l[4:] for l in lines[start:end]) + "\n"


class SectionsStandalone(unittest.TestCase):
    def test_example_outside_the_project(self):
        with tempfile.TemporaryDirectory() as scratch:
            folder = Path(scratch)
            self.assertFalse(folder.resolve().is_relative_to(ROOT.resolve()))
            (folder / "lib").mkdir()
            for name in NEEDED:
                shutil.copy(LIB / name, folder / "lib" / name)
            (folder / "example.fs").write_text("require lib/sections.fs\n" + header_example()
                                               + "cr\n")
            out = gforth(["example.fs"], cwd=folder)
            self.assertEqual(out[0].split(), ["0"] * 5 + ["8", "0"])
            self.assertEqual((folder / "out.sect").stat().st_size, 8192)
            parse((folder / "out.sect").read_bytes())
            names = defined_names(LIBRARY.read_text())
            checks = ["require lib/sections.fs"]
            for name, public in sorted(names.items()):
                test = "0=" if public else ""
                label = "missing" if public else "visible"
                checks.append(f"[defined] {name} {test} [if] .( {label}:{name}) cr [then]")
            (folder / "interface.fs").write_text("\n".join(checks) + "\n.( checked) cr\n")
            self.assertEqual([l for l in gforth(["interface.fs"], cwd=folder) if l], ["checked"])
        self.assertEqual({n for n, public in names.items() if public}, PUBLIC)
        self.assertGreater(len(names), 60)
        self.assertTrue(all(n.startswith(("sections", "/sections")) for n in PUBLIC))


if __name__ == "__main__":
    unittest.main()
