"""File-level tests of the Forth NDJSON reader (src/import/ndjson.fs).

1. Differentials on every reference fixture: the Forth record counts must
   equal docs/development/measurements/scale-2026-11-02/count.py, and the
   Forth field-by-field dump must equal tests/support/ndjson_dump.py.
2. Framing and stream failures on temporary files: each must fail closed
   with the expected outcome and line.
3. A seeded mutation sweep over the fixtures: whenever the Forth reader
   accepts a mutated file, Python's json module must read every line and
   the two field-by-field dumps must agree, and an independent Python
   check of indices and references must pass; whenever a line is not
   JSON, the Forth reader must fail. So the reader never decodes a
   different term than the file holds, and never accepts what is not JSON
   or refers forward.

Run with GFORTH set to the Forth binary (the Makefile does this). Set
LF_NDJSON_MUTATIONS to change the number of mutated files (default 300).
"""
import os
from pathlib import Path
import random
import re
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
GFORTH = os.environ.get("GFORTH", "gforth")
FIXTURES = sorted((ROOT / "tests" / "reference").glob("*.ndjson"))
COUNT_PY = ROOT / "docs" / "development" / "measurements" / "scale-2026-11-02" / "count.py"
DUMP_PY = ROOT / "tests" / "support" / "ndjson_dump.py"
COUNT_FS = "src/import/ndjson-count.fs"
DUMP_FS = "tests/core/ndjson-dump.fs"
SEED = 20261102
MUTATIONS = int(os.environ.get("LF_NDJSON_MUTATIONS", "300"))
MARK = "@@@"


def forth_each(driver, word, paths, batch=400):
    """Apply word to each file, one Forth process per batch; one output per file."""
    outputs = []
    for start in range(0, len(paths), batch):
        outputs += forth_batch(driver, word, paths[start:start + batch])
    return outputs


def forth_batch(driver, word, paths):
    for path in paths:
        if '"' in str(path) or " " in str(path):
            raise ValueError("path not usable in a Forth string")
    calls = " ".join(f's" {path}" {word} cr .( {MARK}) cr' for path in paths)
    result = subprocess.run([GFORTH, driver, "-e", calls + " bye"], cwd=ROOT, stdin=subprocess.DEVNULL,
                            capture_output=True, timeout=600)
    if result.returncode != 0:
        raise AssertionError(f"gforth failed: {result.stderr.decode(errors='replace')[-2000:]}")
    text = result.stdout.decode("utf-8", errors="replace")
    parts = text.split(MARK + "\n")[:-1]
    if len(parts) != len(paths):
        raise AssertionError(f"expected {len(paths)} outputs, got {len(parts)}")
    return [part.rstrip("\n") + "\n" for part in parts]


def python_output(script, path, *options):
    result = subprocess.run([sys.executable, "-I", str(script), *options, str(path)],
                            capture_output=True, timeout=600)
    return result.returncode, result.stdout.decode("utf-8", errors="replace")


def error_of(output):
    """(outcome, line) of the count driver's error line, or None."""
    match = re.search(r"^error: (\w+).*line (\d+)", output, re.M)
    return None if match is None else (match.group(1), int(match.group(2)))


class FixtureDifferential(unittest.TestCase):
    def test_counts_equal_count_py(self):
        outputs = forth_each(COUNT_FS, "count-export", FIXTURES)
        for path, output in zip(FIXTURES, outputs):
            code, expected = python_output(COUNT_PY, path)
            self.assertEqual(code, 0)
            self.assertEqual(output, expected, path.name)

    def test_dumps_equal_python(self):
        outputs = forth_each(DUMP_FS, "dump-export", FIXTURES)
        for path, output in zip(FIXTURES, outputs):
            code, expected = python_output(DUMP_PY, path, "--check")
            self.assertEqual(code, 0)
            self.assertEqual(output, expected, path.name)
            self.assertTrue(output.endswith("ok\n"))


class FramingFailures(unittest.TestCase):
    """Each broken file fails with the expected outcome at the expected line."""

    def cases(self):
        good = (ROOT / "tests" / "reference" / "composition.ndjson").read_bytes()
        lines = good.split(b"\n")[:-1]
        meta = lines[0]
        bad_meta = meta.replace(b'"version":"3.1.0"}', b'"version":"3.2.0"}', 1)
        return [
            ("no final line feed", good[:-1], ("invalid", 35)),
            ("cut inside a line", good[:900], ("invalid", good[:900].count(b"\n") + 1)),
            ("CRLF line ends", good.replace(b"\n", b"\r\n"), ("invalid", 1)),
            ("byte-order mark", b"\xef\xbb\xbf" + good, ("invalid", 1)),
            ("empty file", b"", ("invalid", 0)),
            ("blank line", b"\n".join(lines[:3] + [b""] + lines[3:]) + b"\n", ("invalid", 4)),
            ("metadata only", meta + b"\n", ("invalid", 1)),
            ("invalid UTF-8", good.replace(b'"composition"', b'"comp\xffosition"', 1), ("invalid", 2)),
            ("syntax error", good.replace(b'{"in":1,', b'{"in":1;', 1), ("invalid", 2)),
            ("unsupported exporter", bad_meta + b"\n" + b"\n".join(lines[1:]) + b"\n", ("unsupported", 1)),
            ("metadata twice", meta + b"\n" + good, ("invalid", 2)),
            ("line swapped", b"\n".join([lines[0], lines[2], lines[1]] + lines[3:]) + b"\n", ("invalid", 2)),
            ("not an object", b"\n".join([lines[0], b"[1,2]"] + lines[1:]) + b"\n", ("invalid", 2)),
        ]

    def test_failures(self):
        cases = self.cases()
        with tempfile.TemporaryDirectory() as folder:
            paths = []
            for index, (_, data, _) in enumerate(cases):
                path = Path(folder) / f"case{index}.ndjson"
                path.write_bytes(data)
                paths.append(path)
            outputs = forth_each(COUNT_FS, "count-export", paths)
        for (name, _, expected), output in zip(cases, outputs):
            self.assertEqual(error_of(output), expected, f"{name}: {output}")
            self.assertEqual(output.count("\n"), 1, f"{name}: partial output {output}")


def mutate(rng, lines):
    """One random edit of a copy of the fixture lines (bytes, no line feeds)."""
    lines = list(lines)
    i = rng.randrange(len(lines))
    line = bytearray(lines[i])
    choice = rng.randrange(8)
    alphabet = b'{}[]":,0123456789-.eE abcxyz\\u'
    if choice == 0 and len(line) > 1:
        del line[rng.randrange(len(line))]
    elif choice == 1:
        line.insert(rng.randrange(len(line) + 1), rng.choice(alphabet))
    elif choice == 2 and line:
        line[rng.randrange(len(line))] = rng.choice(alphabet)
    elif choice == 3:
        digits = [k for k, c in enumerate(line) if 48 <= c <= 57]
        if digits:
            line[rng.choice(digits)] = rng.choice(b"0123456789")
    elif choice == 4 and len(lines) > 2:
        j = rng.randrange(1, len(lines))
        lines.insert(j, lines[rng.randrange(1, len(lines))])
        return lines
    elif choice == 5 and len(lines) > 3:
        j = rng.randrange(1, len(lines) - 1)
        lines[j], lines[j + 1] = lines[j + 1], lines[j]
        return lines
    elif choice == 6:
        line = bytearray(line.replace(b":", b": ", 1).replace(b",", b" ,", 1))
    else:
        cut = rng.randrange(len(line) + 1)
        line = line[:cut] + line[rng.randrange(cut, len(line) + 1):]
    lines[i] = bytes(line)
    return lines


def all_json(data):
    import json
    try:
        for raw in data.split(b"\n")[:-1]:
            json.loads(raw.decode("utf-8"))
    except (ValueError, UnicodeDecodeError):
        return False
    return True


class MutationSweep(unittest.TestCase):
    def test_accepted_means_same_decoding(self):
        rng = random.Random(SEED)
        sources = [p.read_bytes().split(b"\n")[:-1] for p in FIXTURES]
        with tempfile.TemporaryDirectory() as folder:
            paths, datas = [], []
            for n in range(MUTATIONS):
                data = b"\n".join(mutate(rng, rng.choice(sources))) + b"\n"
                path = Path(folder) / f"m{n}.ndjson"
                path.write_bytes(data)
                paths.append(path)
                datas.append(data)
            outputs = forth_each(DUMP_FS, "dump-export", paths)
            accepted = rejected = 0
            for path, data, output in zip(paths, datas, outputs):
                if output.endswith("ok\n"):
                    accepted += 1
                    self.assertTrue(all_json(data), f"accepted non-JSON: {data[:300]!r}")
                    code, expected = python_output(DUMP_PY, path, "--check")
                    self.assertEqual(code, 0, f"python check failed on accepted file {path.name}")
                    self.assertEqual(output, expected, f"different decoding: {path.name}")
                else:
                    rejected += 1
                    self.assertRegex(output.splitlines()[-1], r"^error: -?\d+ \d+$")
        print(f"mutation sweep: seed {SEED}, {MUTATIONS} files, {accepted} accepted, "
              f"{rejected} rejected", file=sys.stderr)
        self.assertGreater(rejected, 0)
        self.assertGreater(accepted, 0)


if __name__ == "__main__":
    unittest.main()
