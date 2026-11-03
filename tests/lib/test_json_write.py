"""Oracle and corpus tests of the Forth JSON writer (src/lib/json-write.fs).

1. Corpus: every line of tests/reference/*.ndjson and of
   tests/lib/json-write-corpus.ndjson is canonical, equal to Python's
   compact json.dumps both as given and with sorted keys. The Forth unit
   test (tests/lib/json-write.fs) copies each of those lines back through
   json.fs and jw-copy and needs the bytes unchanged.
2. Writer oracle: seeded random JSON values, written with the writer's own
   words (jw-string, jw-n, jw-u, jw-digits, jw-bool, jw-null, objects and
   arrays; one case in four with sorted keys), must give exactly the bytes
   of Python's json.dumps(value, separators=(",", ":"), ensure_ascii=False),
   with sort_keys for the sorted cases, and outcome ok.
3. Copy oracle: the same kind of values printed non-canonically (ASCII
   escapes, surrogate pairs, \\/, spaces), read by json.fs and copied with
   jw-copy, must give the same bytes.
4. Refusals: invalid UTF-8 at a random place in an array, keys out of
   order in sorted mode, and a real number given to jw-copy fail as
   invalid, invalid and unsupported, with exactly the canonical prefix
   written before the failing call.

The Forth side (tests/lib/json-write-driver.fs) runs every write under HEX.
Run with GFORTH set to the Forth binary (the Makefile does this). Set
LF_JSON_WRITE_CASES to change the number of random values (default 300).
"""
import json
import os
from pathlib import Path
import random
import subprocess
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
GFORTH = os.environ.get("GFORTH", "gforth")
DRIVER = "tests/lib/json-write-driver.fs"
CORPUS = sorted((ROOT / "tests" / "reference").glob("*.ndjson")) + [
    ROOT / "tests" / "lib" / "json-write-corpus.ndjson"]
SEED = 20261102
CASES = int(os.environ.get("LF_JSON_WRITE_CASES", "300"))

CHARS = (["\x00", "\x01", "\x08", "\t", "\n", "\x0b", "\x0c", "\r", "\x1f", '"', "\\", "/",
          "\x7f", " ", "~", "é", "ß", "€", " ", "퟿", "", "�", "￿",
          "\U00010000", "\U0001f600", "\U0010ffff"] + list("abcxyzABZ019"))
BAD_UTF8 = [b"\x80", b"\xc3", b"\xc3(", b"\xc0\xaf", b"\xed\xa0\x80", b"\xf4\x90\x80\x80",
            b"\xff", b"ab\xe2\x82", b"\xf0\x9f\x98", b"\xf8\x88\x80\x80\x80"]


def canonical(value, sort=False):
    return json.dumps(value, separators=(",", ":"), ensure_ascii=False,
                      sort_keys=sort).encode("utf-8")


def gen_string(rng):
    return "".join(rng.choice(CHARS) for _ in range(rng.randint(0, 10)))


def gen_int(rng, bits):
    r = rng.random()
    if r < 0.4:
        return rng.randint(-1000, 1000)
    if r < 0.7:
        return rng.randint(-2 ** (bits - 1), 2 ** (bits - 1) - 1)
    if r < 0.85:
        return rng.randint(2 ** (bits - 1), 2 ** bits - 1)
    return rng.choice([-1, 1]) * rng.randint(2 ** bits, 10 ** 40)


def gen_value(rng, bits, depth=0):
    r = rng.random()
    if depth < 4 and r < 0.2:
        return {gen_string(rng): gen_value(rng, bits, depth + 1) for _ in range(rng.randint(0, 4))}
    if depth < 4 and r < 0.4:
        return [gen_value(rng, bits, depth + 1) for _ in range(rng.randint(0, 4))]
    r = rng.random()
    if r < 0.4:
        return gen_string(rng)
    if r < 0.75:
        return gen_int(rng, bits)
    if r < 0.85:
        return rng.choice([True, False])
    return None


def forth_string(data):
    """A Forth s\\" literal holding exactly the bytes data."""
    text = "".join(chr(b) if 0x20 <= b < 0x7f and b not in (0x22, 0x5c) else f"\\x{b:02x}"
                   for b in data)
    return f's\\" {text}"'


def forth_int(i, bits, rng):
    """Writer calls for the integer i: jw-n or jw-u for a cell, else jw-digits."""
    digits = forth_string(str(i).encode()) + " dw jw-digits"
    if -2 ** (bits - 1) <= i < 2 ** (bits - 1):
        choice = rng.random()
        if choice < 0.25 and i >= 0:
            return f"#{i} dw jw-u"
        return digits if choice < 0.5 else f"#{i} dw jw-n"
    if 0 <= i < 2 ** bits:
        return f"#{i} dw jw-u" if rng.random() < 0.7 else digits
    return digits


def forth_value(v, bits, rng, sort):
    """Writer calls for the value v, members in sorted order when sort."""
    if isinstance(v, bool):
        return ("true" if v else "false") + " dw jw-bool"
    if v is None:
        return "dw jw-null"
    if isinstance(v, int):
        return forth_int(v, bits, rng)
    if isinstance(v, str):
        return forth_string(v.encode("utf-8")) + " dw jw-string"
    if isinstance(v, list):
        return " ".join(["dw jw-open-array"] + [forth_value(x, bits, rng, sort) for x in v]
                        + ["dw jw-close-array"])
    items = sorted(v.items()) if sort else list(v.items())
    return " ".join(["dw jw-open-object"]
                    + [forth_string(k.encode("utf-8")) + " dw jw-key "
                       + forth_value(x, bits, rng, sort) for k, x in items]
                    + ["dw jw-close-object"])


def messy(value, sort, rng):
    """A non-canonical JSON text of value: ASCII escapes, \\/ and spaces."""
    text = json.dumps(value, ensure_ascii=True, sort_keys=sort,
                      separators=rng.choice([(",", ":"), (" , ", " : "), (",\t", ":  ")]))
    return " " * rng.randint(0, 2) + text.replace("/", "\\/") + " " * rng.randint(0, 2)


def run_cases(lines):
    """Run the driver on lines of Forth; one (bytes, outcome) per case."""
    program = "".join(line + "\n" for line in lines).encode("ascii")
    result = subprocess.run([GFORTH, DRIVER, "-e", "run-cases bye"], cwd=ROOT, input=program,
                            capture_output=True, timeout=600)
    if result.returncode != 0 or result.stderr:
        raise AssertionError(f"gforth failed: {result.stderr.decode(errors='replace')[-2000:]}")
    out = result.stdout.split(b"\n")
    if out[-1] != b"" or len(out) - 1 != len(lines):
        raise AssertionError(f"expected {len(lines)} cases, got {len(out) - 1}")
    return [tuple(line.rsplit(b"\t", 1)) for line in out[:-1]]


def cell_bits():
    result = subprocess.run([GFORTH, "-e", "1 cells 8 * . bye"], cwd=ROOT, capture_output=True,
                            stdin=subprocess.DEVNULL, timeout=60)
    return int(result.stdout.split()[0])


class JsonWriteTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.bits = cell_bits()

    def check(self, cases):
        """cases: (forth line, expected bytes, expected outcome)."""
        got = run_cases([line for line, _, _ in cases])
        bad = [(line, want, outcome, have) for (line, want, outcome), have in zip(cases, got)
               if have != (want, outcome)]
        self.assertEqual(bad[:3], [], f"{len(bad)} of {len(cases)} cases differ")
        return len(cases)

    def test_corpus_is_canonical(self):
        lines = 0
        for path in CORPUS:
            for line in path.read_bytes().split(b"\n")[:-1]:
                value = json.loads(line)
                self.assertEqual(canonical(value), line, f"{path.name}: {line[:80]!r}")
                self.assertEqual(canonical(value, sort=True), line, f"{path.name}: {line[:80]!r}")
                lines += 1
        self.assertEqual(lines, 35 + 32 + 12 + 30 + 29 + 16)

    def test_writer_oracle(self):
        rng = random.Random(SEED)
        cases, counts = [], {"sorted": 0, "objects": 0}
        for n in range(CASES):
            value = gen_value(rng, self.bits)
            sort = n % 4 == 3
            mode = "sorted" if sort else "unsorted"
            calls = forth_value(value, self.bits, rng, sort)
            cases.append((f"{mode} case-start {calls} case-end unsorted",
                          canonical(value, sort), b"ok"))
            counts["sorted"] += sort
            counts["objects"] += "jw-open-object" in calls
        self.assertGreater(counts["objects"], CASES // 10)
        print(f"writer oracle: seed {SEED}, {self.check(cases)} values, "
              f"{counts['sorted']} sorted, {counts['objects']} with objects", file=sys.stderr)

    def test_copy_oracle(self):
        rng = random.Random(SEED + 1)
        cases = []
        for n in range(CASES // 2):
            value = gen_value(rng, self.bits)
            sort = n % 3 == 2
            mode = "sorted" if sort else "unsorted"
            text = forth_string(messy(value, sort, rng).encode("ascii"))
            cases.append((f"{mode} case-start {text} copy-text case-end unsorted",
                          canonical(value, sort), b"ok"))
        print(f"copy oracle: seed {SEED + 1}, {self.check(cases)} values", file=sys.stderr)

    def test_refusals(self):
        rng = random.Random(SEED + 2)
        cases = []
        for _ in range(20):
            items = [gen_value(rng, self.bits) for _ in range(rng.randint(0, 4))]
            k = rng.randint(0, len(items))
            calls = [forth_value(x, self.bits, rng, False) for x in items]
            calls.insert(k, forth_string(rng.choice(BAD_UTF8)) + " dw jw-string")
            prefix = canonical(items[:k])[:-1]
            cases.append((" ".join(["case-start dw jw-open-array"] + calls
                                   + ["dw jw-close-array case-end"]), prefix, b"invalid"))
        for _ in range(20):
            keys = sorted({gen_string(rng) for _ in range(rng.randint(2, 5))})
            if len(keys) < 2:
                keys = ["a", "b"]
            order = keys[:]
            while order == keys:
                rng.shuffle(order)
            raw = [k.encode("utf-8") for k in order]
            j = next(i for i in range(1, len(raw)) if raw[i] <= raw[i - 1])
            values = {k: gen_value(rng, self.bits, 3) for k in order}
            members = [forth_string(k.encode("utf-8")) + " dw jw-key "
                       + forth_value(values[k], self.bits, rng, True) for k in order]
            prefix = b"{" + b",".join(canonical(k) + b":" + canonical(values[k], True)
                                      for k in order[:j])
            cases.append((" ".join(["sorted case-start dw jw-open-object"] + members
                                   + ["dw jw-close-object case-end unsorted"]), prefix, b"invalid"))
        for _ in range(10):
            items = [gen_value(rng, self.bits, 3) for _ in range(rng.randint(0, 3))]
            k = rng.randint(0, len(items))
            text = json.dumps(items[:k] + [rng.choice([0.5, -1.25, 1e300])] + items[k:],
                              ensure_ascii=True)
            cases.append((f"case-start {forth_string(text.encode('ascii'))} copy-text case-end",
                          canonical(items[:k])[:-1], b"unsupported"))
        print(f"refusals: seed {SEED + 2}, {self.check(cases)} cases", file=sys.stderr)


if __name__ == "__main__":
    unittest.main()
