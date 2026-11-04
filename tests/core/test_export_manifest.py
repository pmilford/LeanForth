"""Export manifests (plan task 3.2.6): the writer and the Forth check.

1. Writer: scripts/export_manifest.py gives exactly the committed manifest
   of every reference export (tests/reference/*.ndjson.manifest.json),
   each valid under schemas/export-manifest-1.schema.json; it refuses,
   writing nothing, a file without a final line feed, a line that is not
   JSON, an unknown record kind, metadata that is not first, an empty
   file and a malformed Mathlib commit.
2. The Forth check (src/import/manifest.fs, through the counting tool's
   count-report, which checks by default): every reference export with
   its manifest gives the same report as count.py; every failure case
   gives invalid with the expected reason and field, and line 0: an
   export truncated at a line boundary (which the unchecked reader
   accepts), one changed byte, a missing manifest, another format
   version, other exporter or Lean versions, the manifest of another
   file, each number changed, and a corpus of malformed manifests, each
   also refused by the schema where JSON can express it. A manifest named
   with count-manifest is used; count-report-unchecked skips the check.

Run with GFORTH set to the Forth binary (the Makefile does this).
"""
import contextlib
import copy
import io
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))
sys.path.insert(0, str(ROOT / "tests" / "support"))
import export_manifest  # noqa: E402
from schema_subset import Validator, load_strict  # noqa: E402

GFORTH = os.environ.get("GFORTH", "gforth")
COUNT_FS = "src/import/ndjson-count.fs"
COUNT_PY = ROOT / "docs" / "development" / "measurements" / "scale-2026-11-02" / "count.py"
REFERENCE = ROOT / "tests" / "reference"
FIXTURES = sorted(REFERENCE.glob("*.ndjson"))
SCHEMA = ROOT / "schemas" / "export-manifest-1.schema.json"
MARK = "@@@"
ERROR = re.compile(r"^error: (\w+): (.*?) \((?:field (\S+), )?line (\d+)\)$")


def forth(calls):
    """Run Forth calls, each printing one output followed by MARK."""
    text = " ".join(f"{call} .( {MARK}) cr" for call in calls) + " bye"
    result = subprocess.run([GFORTH, COUNT_FS, "-e", text], cwd=ROOT, stdin=subprocess.DEVNULL,
                            capture_output=True, timeout=600)
    if result.returncode != 0:
        raise AssertionError(result.stderr.decode(errors="replace")[-2000:])
    parts = result.stdout.decode("utf-8", errors="replace").split(MARK + "\n")[:-1]
    if len(parts) != len(calls):
        raise AssertionError(f"expected {len(calls)} outputs, got {len(parts)}")
    return parts


def report(path, word="count-report"):
    return f's" {path}" {word}'


def error(output):
    """(outcome, reason, field, line) of an error line, or None."""
    match = ERROR.match(output.strip())
    return None if match is None else (match.group(1), match.group(2), match.group(3) or "",
                                       int(match.group(4)))


def count_py(path):
    result = subprocess.run([sys.executable, "-I", str(COUNT_PY), str(path)],
                            capture_output=True, check=True, timeout=600)
    return result.stdout.decode()


def manifest_of(path):
    return export_manifest.manifest(path)


def text_of(record):
    return export_manifest.manifest_text(record)


def changed(record, path, value):
    """A deep copy of the manifest with the member at the dotted path set,
    or removed when value is REMOVE."""
    record = copy.deepcopy(record)
    *parents, last = path.split("/")
    node = record
    for part in parents:
        node = node[part]
    if value is REMOVE:
        del node[last]
    else:
        node[last] = value
    return record


REMOVE = object()
MALFORMED = "manifest malformed"
DIFFERS = "export differs from its manifest"
VERSIONS = "manifest names another exporter or Lean version"
UNREAD = "manifest missing, unreadable or too large"
NOT_JSON = "manifest is not valid JSON"
FORMAT_VERSION = "unsupported manifest format version"


def manifest_cases(base):
    """(name, manifest text, (reason, field)) for manifests of composition.ndjson."""
    good = text_of(base)
    edits = [
        ("format version 2", ("format_version", 2), (FORMAT_VERSION, "format_version")),
        ("format version as text", ("format_version", "1"), (FORMAT_VERSION, "format_version")),
        ("format version 1.0", ("format_version", 1.0), (FORMAT_VERSION, "format_version")),
        ("another format", ("format", "lean-manifest"), (MALFORMED, "format")),
        ("no format", ("format", REMOVE), (MALFORMED, "format")),
        ("Lean 4.36.0", ("lean_version", "4.36.0"), (VERSIONS, "lean_version")),
        ("another Lean commit", ("lean_githash", "0" * 40), (VERSIONS, "lean_githash")),
        ("another exporter", ("exporter", "lean4export2"), (VERSIONS, "exporter")),
        ("exporter 3.2.0", ("exporter_version", "3.2.0"), (VERSIONS, "exporter_version")),
        ("export format 3.2.0", ("export_format", "3.2.0"), (VERSIONS, "export_format")),
        ("Lean version a number", ("lean_version", 4), (MALFORMED, "lean_version")),
        ("no sha256", ("sha256", REMOVE), (MALFORMED, "")),
        ("an extra member", ("note", "x"), (MALFORMED, "")),
        ("sha256 in capitals", ("sha256", base["sha256"].upper()), (MALFORMED, "sha256")),
        ("sha256 short", ("sha256", base["sha256"][:63]), (MALFORMED, "sha256")),
        ("sha256 a number", ("sha256", 7), (MALFORMED, "sha256")),
        ("bytes negative", ("bytes", -1), (MALFORMED, "bytes")),
        ("bytes real", ("bytes", 1787.0), (MALFORMED, "bytes")),
        ("bytes as text", ("bytes", "1787"), (MALFORMED, "bytes")),
        ("lines null", ("lines", None), (MALFORMED, "lines")),
        ("records missing a kind", ("records/expr.app", REMOVE), (MALFORMED, "records")),
        ("records with another kind", ("records/expr.fvar", 0), (MALFORMED, "records")),
        ("records a list", ("records", [1]), (MALFORMED, "records")),
        ("a record count negative", ("records/meta", -1), (MALFORMED, "records")),
        ("a record count real", ("records/meta", 1.5), (MALFORMED, "records")),
        ("Mathlib commit short", ("mathlib_commit", "ab" * 19), (MALFORMED, "mathlib_commit")),
        ("Mathlib commit in capitals", ("mathlib_commit", "AB" * 20), (MALFORMED, "mathlib_commit")),
        ("Mathlib commit a number", ("mathlib_commit", 1), (MALFORMED, "mathlib_commit")),
        ("lines one more", ("lines", base["lines"] + 1), (DIFFERS, "lines")),
        ("bytes one more", ("bytes", base["bytes"] + 1), (DIFFERS, "bytes")),
        ("an application more", ("records/expr.app", base["records"]["expr.app"] + 1),
         (DIFFERS, "expr.app")),
        ("an inductive type more", ("records/inductive.type", 1), (DIFFERS, "inductive.type")),
        ("another sha256", ("sha256", "0" * 64), (DIFFERS, "sha256")),
    ]
    cases = [(name, text_of(changed(base, path, value)), expected)
             for name, (path, value), expected in edits]
    lines_member = f'  "lines": {base["lines"]},\n'
    cases += [
        ("not JSON", good[:-3], (NOT_JSON, "")),
        ("empty", "", (NOT_JSON, "")),
        ("an array", "[" + good + "]", (MALFORMED, "")),
        ("a string", '"manifest"', (MALFORMED, "")),
        ("a member twice", good.replace(lines_member, lines_member * 2), (MALFORMED, "")),
        ("a number with a leading zero", good.replace(f'"bytes": {base["bytes"]}',
                                                      f'"bytes": 0{base["bytes"]}'), (NOT_JSON, "")),
        ("bytes -0", good.replace(f'"bytes": {base["bytes"]}', '"bytes": -0'), (MALFORMED, "bytes")),
        ("bytes with an exponent", good.replace(f'"bytes": {base["bytes"]}', '"bytes": 1787e0'),
         (MALFORMED, "bytes")),
        ("larger than 64 KiB", good + " " * (65537 - len(good.encode())), (UNREAD, "")),
    ]
    return cases


# Refused by the Forth check only: JSON Schema counts 1.0, 1787e0 and -0 as
# integers, but the check wants canonical decimal (the schema says so).
CANONICAL_ONLY = {"format version 1.0", "bytes real", "bytes -0", "bytes with an exponent"}


def schema_refuses(validator, text):
    try:
        instance = load_strict(text)
    except Exception:  # noqa: BLE001 - not strict JSON: refused before the schema
        return True
    return bool(validator.errors(instance))


class Writer(unittest.TestCase):
    def test_committed_manifests(self):
        validator = Validator(load_strict(SCHEMA.read_text()))
        for path in FIXTURES:
            committed = Path(f"{path}.manifest.json").read_text()
            self.assertEqual(text_of(manifest_of(path)), committed, path.name)
            self.assertEqual(validator.errors(load_strict(committed)), [], path.name)

    def test_refusals(self):
        good = (REFERENCE / "composition.ndjson").read_bytes()
        lines = good.split(b"\n")[:-1]
        cases = {
            "no final line feed": good[:-1],
            "not JSON": good.replace(b'{"in":1,', b'{"in":1;', 1),
            "unknown kind": good.replace(b'"sort":0', b'"fvar":0', 1),
            "metadata not first": b"\n".join([lines[1], lines[0]] + lines[2:]) + b"\n",
            "empty": b"",
        }
        with tempfile.TemporaryDirectory() as folder, contextlib.redirect_stderr(io.StringIO()) as err:
            for name, data in cases.items():
                path = Path(folder) / "export.ndjson"
                path.write_bytes(data)
                self.assertEqual(export_manifest.main([str(path)]), 1, name)
                self.assertFalse(Path(f"{path}.manifest.json").exists(), name)
            path.write_bytes(good)
            self.assertEqual(export_manifest.main([str(path), "--mathlib-commit", "abc"]), 1)
            self.assertEqual(err.getvalue().count("export_manifest.py: "), len(cases) + 1)
            self.assertEqual(export_manifest.main([str(path), "--mathlib-commit", "a" * 40]), 0)
            self.assertEqual(json.loads(Path(f"{path}.manifest.json").read_text())["mathlib_commit"],
                             "a" * 40)


class ForthCheck(unittest.TestCase):
    def test_reference_exports(self):
        """Checked by default, each report equals count.py's and the
        unchecked report."""
        outputs = forth([report(path) for path in FIXTURES]
                        + [report(path, "count-report-unchecked") for path in FIXTURES])
        for path, checked, unchecked in zip(FIXTURES, outputs, outputs[len(FIXTURES):]):
            self.assertEqual(checked, count_py(path), path.name)
            self.assertEqual(unchecked, checked, path.name)

    def test_failures(self):
        base_path = REFERENCE / "composition.ndjson"
        base = manifest_of(base_path)
        good = base_path.read_bytes()
        validator = Validator(load_strict(SCHEMA.read_text()))
        constant = (REFERENCE / "constant-fixture.ndjson").read_bytes()
        truncated = b"".join(constant.splitlines(keepends=True)[:21])
        identity = (REFERENCE / "identity.ndjson.manifest.json").read_text()
        with tempfile.TemporaryDirectory() as folder:
            folder = Path(folder)
            calls, expected = [], []

            def case(name, data, manifest, outcome, word="count-report"):
                path = folder / f"case{len(calls)}.ndjson"
                path.write_bytes(data)
                if manifest is not None:
                    Path(f"{path}.manifest.json").write_text(manifest)
                calls.append(report(path, word))
                expected.append((name, outcome))

            constant_manifest = (REFERENCE / "constant-fixture.ndjson.manifest.json").read_text()
            case("truncated at a line boundary", truncated, constant_manifest, (DIFFERS, "lines"))
            case("truncated, unchecked", truncated, None, "ok", "count-report-unchecked")
            case("one changed byte", good.replace(b'"composition"', b'"compositioN"', 1),
                 text_of(base), (DIFFERS, "sha256"))
            case("missing manifest", good, None, (UNREAD, ""))
            case("another file's manifest", good, identity, (DIFFERS, "lines"))
            case("a valid Mathlib commit", good,
                 text_of(changed(base, "mathlib_commit", "0123456789abcdef" * 2 + "01234567")), "ok")
            case("exactly 64 KiB", good, (text_of(base) + " " * 65536)[:65536], "ok")
            case("the reader's own failure stays", good[:-1], text_of(base),
                 ("missing final line feed, or a read error", ""))
            case("the manifest is checked before the read", good[:-1],
                 text_of(changed(base, "lean_version", "4.36.0")), (VERSIONS, "lean_version"))
            for name, text, outcome in manifest_cases(base):
                if outcome[0] not in (DIFFERS, UNREAD, VERSIONS):
                    self.assertEqual(schema_refuses(validator, text), name not in CANONICAL_ONLY,
                                     f"schema: {name}")
                case(name, good, text, outcome)
            named = folder / "named.json"
            named.write_text(text_of(base))
            calls.append(f's" {named}" count-manifest {report(folder / "case3.ndjson")}')
            expected.append(("a manifest named with count-manifest", "ok"))
            outputs = forth(calls)
        for (name, outcome), output in zip(expected, outputs):
            if outcome == "ok":
                self.assertIsNone(error(output), f"{name}: {output}")
                self.assertTrue(output.startswith("decl."), f"{name}: {output}")
                continue
            got = error(output)
            self.assertIsNotNone(got, f"{name}: {output}")
            line = 35 if outcome[0].startswith("missing final") else 0
            self.assertEqual(got, ("invalid", outcome[0], outcome[1], line), name)


if __name__ == "__main__":
    unittest.main()
