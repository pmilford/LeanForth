"""Test-only encoder for tests/core/export-definition-stream.fs.

It turns one previewed declaration (tests/support/ndjson_preview.py) into the
bounded u32 stream that stages the declaration's universe parameters, level
records and expression records as handle terms and runs the current
definition probe. Not a public format, importer or checker.
"""
import io
import os
from pathlib import Path
import struct
import subprocess

from ndjson_preview import preview

STREAM = "tests/core/export-definition-stream.fs"
LEVEL_TAGS = {"zero": 0, "succ": 1, "max": 2, "imax": 3, "param": 4}
NODE_TAGS = {"sort": 1, "bvar": 2, "app": 3, "lam": 4, "forallE": 5}


def decode(name):
    """Preview a pinned export from tests/reference by its base name."""
    return preview(io.BytesIO(Path(f"tests/reference/{name}.ndjson").read_bytes()))


def _level_row(level, params, names):
    tag = level["tag"]
    if tag == "zero":
        return (0, 0, 0)
    if tag == "succ":
        return (1, level["of"], 0)
    if tag in ("max", "imax"):
        return (LEVEL_TAGS[tag], level["left"], level["right"])
    if tag == "param":
        component = names[level["name"]]["component"]
        return (4, [names[p]["component"] for p in params].index(component), 0)
    raise ValueError(f"unsupported level {tag}")


def _node_row(node):
    tag = node["tag"]
    if tag == "sort":
        return (1, node["levelIndex"], 0)
    if tag == "bvar":
        return (2, node["index"], 0)
    if tag == "app":
        return (3, node["fn"], node["arg"])
    if tag in ("lam", "forallE"):
        return (NODE_TAGS[tag], node["type"], node["body"])
    raise ValueError(f"unsupported expression {tag}")


def encode(decoded, declaration=0, claim=None, value=None, actuals=(), fuel=50000,
           extra_levels=()):
    """Encode one declaration; claim/value override its roots.

    actuals lists one level record per universe parameter (empty for none);
    extra_levels are level rows appended after the exported ones, so that
    replacements such as succ^k zero can be named.
    """
    decl = decoded["declarations"][declaration]
    names = decoded["names"]
    params = decl["levelParams"]
    fields = [len(params)]
    for param in params:
        encoded = names[param]["component"].encode("utf-8")
        fields.extend((len(encoded), *encoded))
    levels = [_level_row(level, params, names) for level in decoded["levelExpressions"]]
    levels.extend(extra_levels)
    fields.append(len(levels))
    for row in levels:
        fields.extend(row)
    nodes = decoded["expressions"]
    fields.append(len(nodes))
    for index, node in enumerate(nodes):
        fields.extend((index, *_node_row(node)))
    fields.extend((decl["type"] if claim is None else claim,
                   decl["value"] if value is None else value, len(actuals), *actuals, fuel))
    return bytearray(struct.pack("<" + "I" * len(fields), *fields))


def run(data):
    """Run the Forth stream on encoded bytes and return the completed process."""
    return subprocess.run([os.environ.get("GFORTH", "gforth"), STREAM],
                          input=bytes(data), capture_output=True)


def succ_chain(base, count, steps):
    """Level rows succ^1..succ^steps of zero, appended after count records.

    Returns the rows and the record index of succ^k zero for k = 0..steps.
    """
    rows = []
    records = [base]
    for k in range(steps):
        rows.append((1, records[-1], 0))
        records.append(count + k)
    return rows, records
