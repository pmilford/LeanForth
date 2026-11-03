"""File-level tests of the Forth NDJSON reader (src/import/ndjson.fs).

1. Differentials on every reference fixture: the Forth record counts must
   equal docs/development/measurements/scale-2026-11-02/count.py, and the
   Forth field-by-field dump must equal both tests/support/ndjson_dump.py
   (Python's json module) and the strict oracle
   tests/support/ndjson_oracle.py.
2. Framing and stream failures on temporary files: each must fail closed
   with the expected outcome and line.
3. The line limit through export-read: a line of exactly 64 MiB is read,
   one byte more is full at that line.
4. A seeded mutation sweep over the fixtures, with ASCII and non-ASCII
   bytes: for every mutated file the Forth reader must agree with the
   strict oracle on the outcome, the line of a failure and every record it
   hands over, so it never decodes a different term than the file holds,
   never accepts what is not JSON or not a record, and never hands over a
   record of a line that fails.

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
sys.path.insert(0, str(ROOT / "tests" / "support"))
import ndjson_oracle  # noqa: E402

GFORTH = os.environ.get("GFORTH", "gforth")
FIXTURES = sorted((ROOT / "tests" / "reference").glob("*.ndjson"))
COUNT_PY = ROOT / "docs" / "development" / "measurements" / "scale-2026-11-02" / "count.py"
DUMP_PY = ROOT / "tests" / "support" / "ndjson_dump.py"
COUNT_FS = "src/import/ndjson-count.fs"
DUMP_FS = "tests/core/ndjson-dump.fs"
SEED = 20261102
MUTATIONS = int(os.environ.get("LF_NDJSON_MUTATIONS", "300"))
MARK = "@@@"
OUTCOMES = {1: "invalid", 2: "exhausted", 3: "unknown", 4: "rejected", 5: "unsupported",
            6: "full"}


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


def disagreement(data, output):
    """None when the Forth dump of data agrees with the strict oracle, else why."""
    dump, result = ndjson_oracle.oracle(data)
    lines = output.rstrip("\n").split("\n") if output.strip() else []
    if result == "ok":
        return None if lines == dump + ["ok"] else "accepted with a different decoding"
    outcomes, line = result
    match = re.fullmatch(r"error: (-?\d+) (\d+)", lines[-1]) if lines else None
    if match is None:
        return f"accepted; the oracle expects {sorted(outcomes)} at line {line}"
    problems = []
    outcome = OUTCOMES.get(int(match.group(1)), match.group(1))
    if outcome not in outcomes:
        problems.append(f"outcome {outcome}, the oracle expects {sorted(outcomes)}")
    if int(match.group(2)) != line:
        problems.append(f"line {match.group(2)}, the oracle expects {line}")
    if lines[:-1] != dump:
        problems.append(f"{len(lines) - 1} records handed over, the oracle expects {len(dump)}")
    return "; ".join(problems) or None


class FixtureDifferential(unittest.TestCase):
    def test_counts_equal_count_py(self):
        outputs = forth_each(COUNT_FS, "count-report", FIXTURES)
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
            self.assertIsNone(disagreement(path.read_bytes(), output), path.name)


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
            outputs = forth_each(COUNT_FS, "count-report", paths)
        for (name, _, expected), output in zip(cases, outputs):
            self.assertEqual(error_of(output), expected, f"{name}: {output}")
            self.assertEqual(output.count("\n"), 1, f"{name}: partial output {output}")


class ExitStatus(unittest.TestCase):
    """The documented command line exits with status 0 after the report and
    1 after the error line, for a broken file and for a missing one."""

    def run_tool(self, path):
        command = f's" {path}" count-export bye'
        result = subprocess.run([GFORTH, COUNT_FS, "-e", command], cwd=ROOT,
                                stdin=subprocess.DEVNULL, capture_output=True, timeout=600)
        return result.returncode, result.stdout.decode("utf-8", errors="replace")

    def test_exit_status(self):
        good = ROOT / "tests" / "reference" / "composition.ndjson"
        code, output = self.run_tool(good)
        self.assertEqual((code, output), (0, python_output(COUNT_PY, good)[1]))
        with tempfile.TemporaryDirectory() as folder:
            broken = Path(folder) / "broken.ndjson"
            broken.write_bytes(good.read_bytes()[:-1])
            code, output = self.run_tool(broken)
            self.assertEqual(code, 1, output)
            self.assertEqual(error_of(output), ("invalid", 35), output)
            self.assertEqual(output.count("\n"), 1, output)
            code, output = self.run_tool(Path(folder) / "missing.ndjson")
            self.assertEqual(code, 1, output)
            self.assertTrue(output.startswith("error: "), output)


class LineLimit(unittest.TestCase):
    """A line of exactly 64 MiB (line 4) is read, and one byte more is full
    there. The two files, 128 MiB in all, are deleted by name afterwards."""

    def test_line_limit(self):
        meta = (ROOT / "tests" / "reference" / "composition.ndjson").read_bytes().split(b"\n")[0]
        head = [meta, b'{"in":1,"str":{"pre":0,"str":"x"}}', b'{"ie":0,"sort":0}']
        last = b'{"axiom":{"isUnsafe":false,"levelParams":[],"name":1,"type":0}}'
        start, end = b'{"ie":1,"strVal":"', b'"}'
        folder = tempfile.mkdtemp(prefix="lf-line-limit-")
        paths = []
        try:
            for extra in (0, 1):
                path = os.path.join(folder, f"limit{extra}.ndjson")
                paths.append(path)
                size = ndjson_oracle.LINE_LIMIT + extra - len(start) - len(end)
                long_line = start + b"a" * size + end
                with open(path, "wb") as f:
                    f.write(b"\n".join(head + [long_line, last]) + b"\n")
            outputs = forth_each(COUNT_FS, "count-report", paths)
        finally:
            for path in paths:
                if os.path.exists(path):
                    os.remove(path)
            os.rmdir(folder)
        self.assertIsNone(error_of(outputs[0]), outputs[0])
        self.assertRegex(outputs[0], r"(?m)^expr\.strVal +1 +67,108,865 B ")
        self.assertEqual(error_of(outputs[1]), ("full", 4))


SEQUENCES = [b"\xc3\xa9", b"\xe2\x82\xac", b"\xf0\x9f\x98\x80", b"\xed\xa0\x80", b"\xc0\xaf",
             b"\xf4\x90\x80\x80", b"\xe2\x82", b"\\ud800", b"\\udc00\\ud800", b"\\u00e9", b"NaN",
             b"1e400", b"-0", b"12345678901234567890"]
ALPHABET = b'{}[]":,0123456789-.eE abcxyz\\u' + bytes(
    [0, 9, 13, 0x7f, 0x80, 0xa9, 0xbf, 0xc0, 0xc3, 0xe2, 0xed, 0xef, 0xf0, 0xf4, 0xff])


def mutate(rng, lines):
    """One random edit of a copy of the fixture lines (bytes, no line feeds)."""
    lines = list(lines)
    i = rng.randrange(len(lines))
    line = bytearray(lines[i])
    choice = rng.randrange(9)
    if choice == 0 and len(line) > 1:
        del line[rng.randrange(len(line))]
    elif choice == 1:
        line.insert(rng.randrange(len(line) + 1), rng.choice(ALPHABET))
    elif choice == 2 and line:
        line[rng.randrange(len(line))] = rng.choice(ALPHABET)
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
    elif choice == 7:
        k = rng.randrange(len(line) + 1)
        line[k:k] = rng.choice(SEQUENCES)
    else:
        cut = rng.randrange(len(line) + 1)
        line = line[:cut] + line[rng.randrange(cut, len(line) + 1):]
    lines[i] = bytes(line)
    return lines


class MutationSweep(unittest.TestCase):
    def test_agrees_with_strict_oracle(self):
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
        accepted = sum(output.endswith("ok\n") for output in outputs)
        for path, data, output in zip(paths, datas, outputs):
            self.assertIsNone(disagreement(data, output), f"{path.name}: {data[:300]!r}")
        print(f"mutation sweep: seed {SEED}, {MUTATIONS} files, {accepted} accepted, "
              f"{MUTATIONS - accepted} rejected", file=sys.stderr)
        self.assertGreater(MUTATIONS - accepted, 0)
        self.assertGreater(accepted, 0)


if __name__ == "__main__":
    unittest.main()
