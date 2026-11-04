#!/usr/bin/env python3
"""Write the manifest of a Lean export (plan task 3.2.6).

Usage (from any folder):
  python3 scripts/export_manifest.py EXPORT.ndjson [--output MANIFEST.json]
                                     [--mathlib-commit SHA]

Lean's exporter (leanexport, lean4export 3.1.0) writes no checksum, so a
file cut off cleanly between two lines would read as a shorter, valid
library. LeanForth's export step (scripts/export.sh) therefore writes this
manifest beside each export, by default as EXPORT.ndjson.manifest.json, and
LeanForth's reader checks it by default (src/import/manifest.fs, in Forth:
end users need no Python). The manifest, format version 1
(schemas/export-manifest-1.schema.json), holds:

  sha256          SHA-256 of the whole file, 64 lowercase hexadecimal digits
  bytes, lines    the file's size and its number of lines
  records         records of each kind: every line is one record (meta,
                  name.*, level.*, expr.*, decl.*), and each type,
                  constructor and recursor of an inductive block counts too
                  (inductive.type, .ctor, .recursor)
  exporter, exporter_version, export_format, lean_version, lean_githash
                  as the export's first line (its metadata) states them
  mathlib_commit  the Mathlib commit exported, or null when not given

The writer reads the export once, with Python's hashlib and json modules: an
implementation independent of the Forth reader, so the check compares two.
It refuses (exit status 1, no manifest written) a file that is not
lean4export NDJSON as it reads it: a line that is not one JSON object, a
missing final line feed, an unknown record kind, no metadata first. The
manifest is JSON with sorted keys, two-space indentation and a final line
feed, so the same export always gives the same bytes. It runs on the
developer's machine, at export time; nothing on the user's path needs it.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import sys

FORMAT = "leanforth-export-manifest"
VERSION = 1
KINDS = (["meta", "name.str", "name.num"]
         + [f"level.{k}" for k in ("succ", "max", "imax", "param")]
         + [f"expr.{k}" for k in ("bvar", "sort", "const", "app", "lam", "forallE", "letE",
                                   "proj", "natVal", "strVal", "mdata")]
         + [f"decl.{k}" for k in ("axiom", "def", "thm", "opaque", "quot", "inductive")]
         + ["inductive.type", "inductive.ctor", "inductive.recursor"])
FAMILIES = {"in": "name", "il": "level", "ie": "expr"}
BLOCK_LISTS = {"types": "inductive.type", "ctors": "inductive.ctor", "recs": "inductive.recursor"}
COMMIT = re.compile(r"[0-9a-f]{40}")


class ExportError(Exception):
    pass


def record_kind(obj, number):
    """The record kind of one decoded line (KINDS), or ExportError."""
    if not isinstance(obj, dict):
        raise ExportError(f"line {number}: not a JSON object")
    keys = set(obj)
    family = keys & set(FAMILIES)
    if len(family) == 1 and len(keys) == 2:
        index = family.pop()
        kind = f"{FAMILIES[index]}.{(keys - {index}).pop()}"
    elif len(keys) == 1:
        key = next(iter(keys))
        kind = "meta" if key == "meta" else f"decl.{key}"
    else:
        kind = None
    if kind not in KINDS:
        raise ExportError(f"line {number}: unknown record kind")
    return kind


def meta_fields(meta):
    """The manifest's version members, from the metadata record."""
    try:
        return {"exporter": meta["exporter"]["name"],
                "exporter_version": meta["exporter"]["version"],
                "export_format": meta["format"]["version"],
                "lean_version": meta["lean"]["version"],
                "lean_githash": meta["lean"]["githash"]}
    except (KeyError, TypeError) as error:
        raise ExportError(f"line 1: metadata without {error}") from None


def count_block(block, counts):
    for key, kind in BLOCK_LISTS.items():
        counts[kind] += len(block.get(key, []))


def manifest(path, mathlib_commit=None):
    """The manifest of the export at path, as a dict."""
    if mathlib_commit is not None and not COMMIT.fullmatch(mathlib_commit):
        raise ExportError("the Mathlib commit must be 40 lowercase hexadecimal digits")
    digest, size, lines = hashlib.sha256(), 0, 0
    counts = dict.fromkeys(KINDS, 0)
    versions = None
    with open(path, "rb") as export:
        for line in export:
            lines += 1
            digest.update(line)
            size += len(line)
            if not line.endswith(b"\n"):
                raise ExportError(f"line {lines}: no final line feed")
            try:
                obj = json.loads(line)
            except ValueError:
                raise ExportError(f"line {lines}: not JSON") from None
            kind = record_kind(obj, lines)
            if (kind == "meta") != (lines == 1):
                raise ExportError(f"line {lines}: metadata must be the first line, once")
            counts[kind] += 1
            if kind == "meta":
                versions = meta_fields(obj["meta"])
            elif kind == "decl.inductive":
                count_block(obj["inductive"], counts)
    if versions is None:
        raise ExportError("empty export")
    return {"format": FORMAT, "format_version": VERSION, "sha256": digest.hexdigest(),
            "bytes": size, "lines": lines, "records": counts,
            "mathlib_commit": mathlib_commit, **versions}


def manifest_text(record):
    return json.dumps(record, indent=2, sort_keys=True, ensure_ascii=False) + "\n"


def write(path, text):
    """Write text to path through a temporary file, so that a failure
    never leaves a partial manifest."""
    partial = Path(f"{path}.partial")
    partial.write_text(text)
    os.replace(partial, path)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("export", type=Path)
    parser.add_argument("--output", type=Path, help="default: EXPORT.manifest.json")
    parser.add_argument("--mathlib-commit", help="the Mathlib commit exported")
    args = parser.parse_args(argv)
    output = args.output or Path(f"{args.export}.manifest.json")
    try:
        text = manifest_text(manifest(args.export, args.mathlib_commit))
    except (ExportError, OSError) as error:
        print(f"export_manifest.py: {args.export}: {error}", file=sys.stderr)
        return 1
    write(output, text)
    return 0


if __name__ == "__main__":
    sys.exit(main())
