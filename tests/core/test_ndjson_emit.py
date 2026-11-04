"""File-level tests of the Forth re-exporter (src/import/ndjson-emit.fs) and
of scripts/ndjson-reexport.sh (plan task 3.2.4; docs/development/
NDJSON_READER.md, "Re-export").

1. Every NDJSON export of the repository, that is every *.ndjson file under
   tests/ that starts with lean4export's metadata, is re-exported through
   files with the command-line word: the copy must equal the file byte for
   byte, and the reader must read the copy back into the same
   field-by-field dump (tests/core/ndjson-dump.fs) as the file. The one
   NDJSON file that is not an export, tests/lib/json-write-corpus.ndjson
   (lines of every record kind without metadata or the records they refer
   to, for the JSON writer's tests), is listed apart; any other file
   without metadata fails the test.
2. A seeded spelling sweep: each export rewritten line by line in other
   JSON spellings of the same records (white space, members in another
   order, other escapes) must re-export to the original bytes, which are
   lean4export's.
3. A seeded fuzz sweep with the reader's mutations
   (tests/core/test_ndjson_reader.py): a mutated export the reader
   refuses is refused with an error line; one it accepts comes back as a
   copy that the reader reads into the same dump, and that re-exports to
   itself byte for byte (the exporter's form is a fixed point).
4. The tool: identical files give exit 0 with both modes; a file in
   another spelling reports its first differing line and byte, exit 1,
   with equal dumps; a file the reader refuses gives the reader's error
   and exit 1; bad usage gives exit 2.

Run with GFORTH set to the Forth binary (the Makefile does this). Set
LF_REEXPORT_SPELLINGS to change the spellings per export (default 2) and
LF_REEXPORT_MUTATIONS the mutated exports (default 200).
"""
import json
import os
from pathlib import Path
import random
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tests" / "core"))
from test_ndjson_reader import mutate  # noqa: E402
GFORTH = os.environ.get("GFORTH", "gforth")
EMIT_FS = "src/import/ndjson-emit.fs"
DUMP_FS = "tests/core/ndjson-dump.fs"
TOOL = "scripts/ndjson-reexport.sh"
META = b'{"meta":{"exporter":{"name":"lean4export","version":"3.1.0"}'
NOT_EXPORTS = {
    "tests/lib/json-write-corpus.ndjson":
        "the JSON writer's corpus: record lines without metadata or the records they name",
}
SEED = 20261103
SPELLINGS = int(os.environ.get("LF_REEXPORT_SPELLINGS", "2"))
MUTATIONS = int(os.environ.get("LF_REEXPORT_MUTATIONS", "200"))
MARK = "@@@"
NL = b"\n"


def ndjson_files():
    return sorted(path.relative_to(ROOT).as_posix() for path in (ROOT / "tests").rglob("*.ndjson"))


def exports():
    return [name for name in ndjson_files() if name not in NOT_EXPORTS]


def forth_calls(driver, calls, batch=200):
    """Run each Forth call after loading driver, batch calls per process; one output each."""
    outputs = []
    for start in range(0, len(calls), batch):
        outputs += forth_batch(driver, calls[start:start + batch])
    return outputs


def forth_batch(driver, calls):
    text = " ".join(f"{call} cr .( {MARK}) cr" for call in calls)
    result = subprocess.run([GFORTH, driver, "-e", text + " bye"], cwd=ROOT,
                            stdin=subprocess.DEVNULL, capture_output=True, timeout=600)
    if result.returncode != 0:
        raise AssertionError(f"gforth failed: {result.stderr.decode(errors='replace')[-2000:]}")
    parts = result.stdout.decode("utf-8", errors="replace").split(MARK + "\n")[:-1]
    if len(parts) != len(calls):
        raise AssertionError(f"expected {len(calls)} outputs, got {len(parts)}")
    return [part.strip("\n") for part in parts]


def forth_string(path):
    if '"' in str(path) or " " in str(path):
        raise ValueError("path not usable in a Forth string")
    return f's" {path}"'


def reexport_all(pairs):
    """Re-export each (input, output) pair; the report line of each."""
    return forth_calls(EMIT_FS, [f"{forth_string(a)} {forth_string(b)} reexported? drop"
                                 for a, b in pairs])


def dumps(paths):
    return forth_calls(DUMP_FS, [f"{forth_string(path)} dump-export" for path in paths])


def line_count(path):
    return Path(ROOT / path).read_bytes().count(b"\n")


# Other spellings of the same JSON value: random white space (space and
# tab; the reader refuses carriage returns), members in random order, and
# characters written with other escapes.
SHORT = {'"': '\\"', "\\": "\\\\", "\b": "\\b", "\f": "\\f", "\n": "\\n", "\r": "\\r", "\t": "\\t"}


def white(rng):
    return rng.choice(["", "", " ", "\t", "  "])


def u_escape(code, rng):
    text = f"\\u{code:04x}"
    return text.upper().replace("\\U", "\\u") if rng.random() < 0.5 else text


def spell_char(char, rng):
    code = ord(char)
    if char in SHORT and (code < 0x20 or char in '"\\') and rng.random() < 0.6:
        return SHORT[char]
    if code < 0x20 or char in '"\\' or rng.random() < 0.2:
        if code > 0xFFFF:
            code -= 0x10000
            return u_escape(0xD800 + (code >> 10), rng) + u_escape(0xDC00 + (code & 0x3FF), rng)
        return u_escape(code, rng)
    if char == "/" and rng.random() < 0.5:
        return "\\/"
    return char


def spell_string(text, rng):
    return '"' + "".join(spell_char(char, rng) for char in text) + '"'


def spell(value, rng):
    if isinstance(value, dict):
        items = list(value.items())
        rng.shuffle(items)
        return "{" + white(rng) + ",".join(
            white(rng) + spell_string(key, rng) + white(rng) + ":" + white(rng)
            + spell(item, rng) + white(rng) for key, item in items) + "}"
    if isinstance(value, list):
        return "[" + white(rng) + ",".join(
            white(rng) + spell(item, rng) + white(rng) for item in value) + "]"
    if isinstance(value, str):
        return spell_string(value, rng)
    if value is True or value is False or value is None:
        return json.dumps(value)
    return str(value)


def respelled(data, rng):
    lines = data.decode("utf-8").split("\n")[:-1]
    return "".join(spell(json.loads(line), rng) + "\n" for line in lines).encode("utf-8")


class Exports(unittest.TestCase):
    def test_every_ndjson_file_is_an_export_or_listed(self):
        files = ndjson_files()
        self.assertGreaterEqual(len(exports()), 11)
        for name in files:
            starts = (ROOT / name).read_bytes().startswith(META)
            self.assertEqual(starts, name not in NOT_EXPORTS, name)

    def test_every_export_comes_back_byte_for_byte_and_reads_back(self):
        names = exports()
        with tempfile.TemporaryDirectory() as directory:
            copies = [Path(directory) / f"{index}.ndjson" for index in range(len(names))]
            reports = reexport_all(list(zip(names, copies)))
            for name, copy, report in zip(names, copies, reports):
                self.assertEqual(report, f"reexported {line_count(name)} lines", name)
                self.assertEqual(copy.read_bytes(), (ROOT / name).read_bytes(), name)
            originals = dumps(names)
            again = dumps(copies)
            for name, first, second in zip(names, originals, again):
                self.assertTrue(first.endswith("ok"), name)
                self.assertEqual(first, second, name)

    def test_other_spellings_come_back_as_the_exporter_writes(self):
        rng = random.Random(SEED)
        names = exports()
        with tempfile.TemporaryDirectory() as directory:
            pairs, expected = [], []
            for name in names:
                original = (ROOT / name).read_bytes()
                for spelling in range(SPELLINGS):
                    base = Path(directory) / f"{len(pairs)}"
                    source = base.with_suffix(".in")
                    source.write_bytes(respelled(original, rng))
                    pairs.append((source, base.with_suffix(".out")))
                    expected.append((name, original))
            reports = reexport_all(pairs)
            different = 0
            for (source, copy), (name, original), report in zip(pairs, expected, reports):
                different += source.read_bytes() != original
                self.assertEqual(report, f"reexported {original.count(NL)} lines", name)
                self.assertEqual(copy.read_bytes(), original, name)
            self.assertEqual(different, len(pairs))

    def test_accepted_fuzz_cases_come_back_and_stay(self):
        rng = random.Random(SEED + 1)
        sources = [(ROOT / name).read_bytes().split(b"\n")[:-1] for name in exports()]
        with tempfile.TemporaryDirectory() as directory:
            folder = Path(directory)
            mutants = [folder / f"m{n}.ndjson" for n in range(MUTATIONS)]
            copies = [folder / f"c{n}.ndjson" for n in range(MUTATIONS)]
            again = [folder / f"a{n}.ndjson" for n in range(MUTATIONS)]
            for path in mutants:
                path.write_bytes(b"\n".join(mutate(rng, rng.choice(sources))) + b"\n")
            reports = reexport_all(list(zip(mutants, copies)))
            read = dumps(mutants)
            accepted = [n for n in range(MUTATIONS) if read[n].endswith("ok")]
            for n in range(MUTATIONS):
                if n not in accepted:
                    self.assertTrue(reports[n].startswith("error: "), f"m{n}: {reports[n]}")
            for n in accepted:
                lines = mutants[n].read_bytes().count(NL)
                self.assertEqual(reports[n], f"reexported {lines} lines", f"m{n}")
            chosen = [copies[n] for n in accepted]
            self.assertEqual(dumps(chosen), [read[n] for n in accepted])
            reexport_all([(copies[n], again[n]) for n in accepted])
            same = sum(mutants[n].read_bytes() == copies[n].read_bytes() for n in accepted)
            for n in accepted:
                self.assertEqual(again[n].read_bytes(), copies[n].read_bytes(), f"m{n}")
        print(f"fuzz sweep: seed {SEED + 1}, {MUTATIONS} mutated exports, {len(accepted)} "
              f"accepted ({same} already in the exporter's form), "
              f"{MUTATIONS - len(accepted)} refused", file=sys.stderr)
        self.assertGreater(len(accepted), 0)
        self.assertGreater(MUTATIONS - len(accepted), 0)


class Tool(unittest.TestCase):
    def run_tool(self, *arguments):
        result = subprocess.run(["bash", TOOL, *map(str, arguments)], cwd=ROOT,
                                stdin=subprocess.DEVNULL, capture_output=True, timeout=600,
                                env={**os.environ, "GFORTH": GFORTH})
        return result.returncode, result.stdout.decode("utf-8", errors="replace")

    def test_identical_in_both_modes(self):
        with tempfile.TemporaryDirectory() as directory:
            copy = Path(directory) / "copy.ndjson"
            status, output = self.run_tool("--reimport", "tests/reference/identity.ndjson", copy)
            self.assertEqual(status, 0, output)
            self.assertIn("identical\n", output)
            self.assertIn("reimport: equal dumps\n", output)
            sums = [line.split()[1] for line in output.splitlines()[:3] if line[:6] in
                    ("export", "copy  ")]
            self.assertEqual(len(sums), 2)
            self.assertEqual(sums[0], sums[1])
        status, output = self.run_tool("tests/reference/composition.ndjson", "-")
        self.assertEqual(status, 0, output)
        self.assertIn("identical\n", output)

    def test_another_spelling_reports_its_first_difference(self):
        original = (ROOT / "tests/reference/composition.ndjson").read_bytes().split(b"\n")
        self.assertEqual(original[26], b'{"app":{"arg":12,"fn":1},"ie":13}')
        original[26] = b'{"ie":13, "app":{"fn":1,"arg":12}}'
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "spelled.ndjson"
            source.write_bytes(b"\n".join(original))
            for copy in (Path(directory) / "copy.ndjson", "-"):
                arguments = ["--reimport"] if copy != "-" else []
                status, output = self.run_tool(*arguments, source, copy)
                self.assertEqual(status, 1, output)
                self.assertIn("different: first at line 27, byte 3 of the line", output)
                self.assertIn('export: {"ie":13, "app"', output)
                if copy != "-":
                    self.assertIn('copy:   {"app":{"arg":12,"fn":1},"ie":13}', output)
                    self.assertIn("reimport: equal dumps\n", output)

    def test_a_refused_export_fails(self):
        data = (ROOT / "tests/reference/identity.ndjson").read_bytes()
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "cut.ndjson"
            source.write_bytes(data[:-1])
            status, output = self.run_tool(source, Path(directory) / "copy.ndjson")
            self.assertEqual(status, 1, output)
            self.assertIn("error: invalid: missing final line feed", output)
            self.assertIn("the re-export failed", output)

    def test_bad_usage(self):
        self.assertEqual(self.run_tool()[0], 2)
        self.assertEqual(self.run_tool("tests/reference/identity.ndjson")[0], 2)
        self.assertEqual(self.run_tool("tests/reference/identity.ndjson",
                                       "tests/reference/identity.ndjson")[0], 2)
        self.assertEqual(self.run_tool("--reimport", "tests/reference/identity.ndjson", "-")[0], 2)
        self.assertEqual(self.run_tool("tests/no-such.ndjson", "-")[0], 2)


if __name__ == "__main__":
    unittest.main()
