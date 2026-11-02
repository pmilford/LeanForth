"""Compare one pinned Lean export fixture with a manually built Forth DAG.

This is a test-only inspector for a single known fixture, not an importer,
proof checker, or declaration registration interface.
"""

import json
import os
from pathlib import Path
import subprocess
import sys


def unique_object(pairs):
    """Reject duplicate keys at every object depth, including metadata."""
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError("duplicate JSON object key")
        result[key] = value
    return result


def fixture_nodes(lines):
    """Extract the fixture's supported expression records or fail closed."""
    nodes = []
    metadata_seen = False
    theorem_seen = False
    name_count = 0
    for line_number, line in enumerate(lines, start=1):
        record = json.loads(line, object_pairs_hook=unique_object)
        if not isinstance(record, dict):
            raise ValueError("record is not an object")
        if line_number == 1 and set(record) != {"meta"}:
            raise ValueError("metadata must be the first record")
        if set(record) == {"meta"}:
            if metadata_seen or nodes:
                raise ValueError("unexpected metadata")
            metadata = record["meta"]
            if not isinstance(metadata, dict):
                raise ValueError("metadata is not an object")
            format_info = metadata.get("format")
            lean_info = metadata.get("lean")
            if not isinstance(format_info, dict) or format_info.get("version") != "3.1.0":
                raise ValueError("unexpected export format")
            if not isinstance(lean_info, dict) or lean_info.get("githash") != "eb6cafb7290e8bd5f2937522d8d804f58f02bafc":
                raise ValueError("unexpected Lean revision")
            metadata_seen = True
        elif "ie" in record:
            if not metadata_seen or theorem_seen:
                raise ValueError("expression outside fixture body")
            index = record["ie"]
            if type(index) is not int or index != len(nodes):
                raise ValueError("expression index is not sequential")
            kinds = set(record) - {"ie"}
            if kinds == {"sort"} and type(record["sort"]) is int and record["sort"] == 0:
                node = (1, 0, 0)
            elif kinds == {"bvar"} and type(record["bvar"]) is int and record["bvar"] >= 0:
                node = (2, record["bvar"], 0)
            elif len(kinds) == 1 and next(iter(kinds)) in {"app", "lam", "forallE"}:
                kind = next(iter(kinds))
                fields = record[kind]
                if not isinstance(fields, dict):
                    raise ValueError("expression fields are not an object")
                expected_fields = {"fn", "arg"} if kind == "app" else {"name", "binderInfo", "type", "body"}
                if set(fields) != expected_fields:
                    raise ValueError("unexpected expression fields")
                if kind != "app":
                    name = fields["name"]
                    if type(name) is not int or not 0 <= name <= name_count:
                        raise ValueError("binder name is not an earlier name")
                    if fields["binderInfo"] not in ("default", "implicit", "strictImplicit", "instImplicit"):
                        raise ValueError("unsupported binder information")
                first_key, second_key = ("fn", "arg") if kind == "app" else ("type", "body")
                first, second = fields.get(first_key), fields.get(second_key)
                if any(type(value) is not int or not 0 <= value < index for value in (first, second)):
                    raise ValueError("expression child is not an earlier node")
                node = ({"app": 3, "lam": 4, "forallE": 5}[kind], first, second)
            else:
                raise ValueError("unsupported expression record")
            nodes.append(node)
        elif set(record) == {"thm"}:
            theorem = record["thm"]
            if not isinstance(theorem, dict):
                raise ValueError("theorem is not an object")
            if set(theorem) != {"all", "levelParams", "name", "type", "value"}:
                raise ValueError("unexpected theorem fields")
            if any(type(theorem[key]) is not int for key in ("name", "type", "value")):
                raise ValueError("invalid theorem references")
            if theorem_seen or len(nodes) != 21 or theorem["name"] != 1 or theorem["type"] != 10 or theorem["value"] != 20:
                raise ValueError("unexpected theorem references")
            if theorem["levelParams"] != [] or theorem["all"] != [1] or type(theorem["all"][0]) is not int:
                raise ValueError("unexpected theorem metadata")
            theorem_seen = True
        elif set(record) in ({"in", "str"}, {"in", "num"}):
            if not metadata_seen or theorem_seen:
                raise ValueError("name outside fixture body")
            name_index = record["in"]
            if type(name_index) is not int or name_index != name_count + 1:
                raise ValueError("name index is not sequential")
            kind = "str" if "str" in record else "num"
            fields = record[kind]
            if not isinstance(fields, dict):
                raise ValueError("name fields are not an object")
            expected_keys = {"pre", "str"} if kind == "str" else {"pre", "i"}
            if set(fields) != expected_keys:
                raise ValueError("unexpected name fields")
            prefix = fields["pre"]
            if type(prefix) is not int or not 0 <= prefix < name_index:
                raise ValueError("name prefix is not an earlier name")
            if kind == "str" and not isinstance(fields["str"], str):
                raise ValueError("name component is not a string")
            if kind == "num" and (type(fields["i"]) is not int or fields["i"] < 0):
                raise ValueError("name component is not a nonnegative integer")
            name_count += 1
        else:
            raise ValueError("unexpected fixture record")
    if not metadata_seen or not theorem_seen or len(nodes) != 21:
        raise ValueError("incomplete composition fixture")
    return nodes


def main():
    """Compare the emitted Forth node fields with the pinned fixture."""
    fixture = Path("tests/reference/composition.ndjson")
    expected = fixture_nodes(fixture.read_text(encoding="utf-8").splitlines())
    gforth = os.environ.get("GFORTH", "gforth")
    result = subprocess.run(
        [gforth, "tests/legacy/composition-table.fs"],
        check=True,
        text=True,
        capture_output=True,
    )
    actual = []
    for line in result.stdout.splitlines():
        fields = [int(field) for field in line.split()]
        if len(fields) != 4 or fields[0] != len(actual):
            raise ValueError("unexpected Forth table row")
        actual.append(tuple(fields[1:]))
    if actual != expected:
        raise ValueError("Forth composition DAG differs from the pinned Lean fixture")
    print("Forth composition DAG matches the 21 pinned Lean expression records.")

    # The compact byte stream is a test adapter for this small fixture, not a
    # public wire format. It is passed to Forth as data, never as source code.
    stream = bytes(value for index, node in enumerate(expected) for value in (index, *node))
    staged = subprocess.run(
        [gforth, "tests/legacy/load-fixture-stream.fs"], input=stream,
        check=True, capture_output=True,
    )
    staged_rows = [tuple(map(int, line.split())) for line in staged.stdout.splitlines()]
    if staged_rows != [(index, *node) for index, node in enumerate(expected)]:
        raise ValueError("Staged Forth DAG differs from decoded fixture records")
    for bad_stream in (
        b"", stream[:-1], bytes((0, 255, 0, 0)), bytes((1, 1, 0, 0)),
        bytes((0, 1, 0, 0, 1, 3, 0, 1)),  # Forward child after a valid node.
    ):
        failed = subprocess.run(
            [gforth, "tests/legacy/load-fixture-stream.fs"], input=bad_stream,
            capture_output=True,
        )
        if failed.returncode == 0 or failed.stdout.strip():
            raise ValueError("Malformed fixture stream did not fail closed")
    altered = bytearray(stream)
    altered[-1] = 18  # Give the outer lambda the wrong body while keeping a DAG.
    mismatch = subprocess.run(
        [gforth, "tests/legacy/load-fixture-stream.fs"], input=altered,
        capture_output=True,
    )
    if mismatch.returncode == 0 or mismatch.stdout.strip():
        raise ValueError("Altered composition unexpectedly passed experimental comparison")
    print("Staged fixture inference matches its claim; malformed or altered input fails.")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        print(f"Composition fixture test failed: {error}", file=sys.stderr)
        sys.exit(1)
