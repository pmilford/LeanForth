#!/usr/bin/env python3
"""Finish LeanForth's elaboration data (plan row FE1d; ADR 0021 D10).

Usage (from any folder):
  python3 scripts/export_elab.py RAW EXPORT OUTPUT

scripts/export-elab.sh runs this after scripts/export_elab.lean, with pinned
Lean, has written RAW for the modules of the Lean export EXPORT (made by
scripts/export.sh, so with its manifest beside it). It writes OUTPUT, the
elaboration data LeanForth reads (`leanforth check --elab-data OUTPUT`;
src/front/elab-data.fs), format version 1, documented in
docs/programming/ELABORATION_DATA.md and schemas/elab-data-1.schema.json:

  line 1    {"elab_data": {...}}: the format and its version, the export's
            SHA-256 (as its manifest records it), the Lean version and
            revision, the modules, the records of each kind and the
            SHA-256 of every line after this one, each with its line feed
  then      one record per line, sorted by kind (instance,
            default_instance, reducibility, eliminator) and then by text

Only records whose every name is a declaration of EXPORT are kept, so that
a slice of a library (scripts/export.sh MODULE -- NAMES) gets the data of
its own declarations; the number left out is printed. A record whose names
are all there but of the wrong kind (a class that is not an inductive
type, an instance or eliminator that is one) is an error: then the export
and the modules do not belong together. It refuses (exit status 1, nothing
written) RAW that is not as export_elab.lean writes it, an export whose
SHA-256 differs from its manifest's, and a Lean version other than the
pinned one. JSON is written with sorted keys and no spaces, UTF-8 as it
is, so the same input always gives the same bytes. It runs at export time,
on the developer's machine: nothing on a LeanForth user's path needs it.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import sys

FORMAT = "leanforth-elab-data"
VERSION = 1
LEAN_VERSION = "4.35.0"
LEAN_GITHASH = "eb6cafb7290e8bd5f2937522d8d804f58f02bafc"
KINDS = ("instance", "default_instance", "reducibility", "eliminator")
STATUSES = ("reducible", "irreducible", "implicit_reducible", "instance_reducible")
ELIMINATOR_KINDS = ("induction", "cases")
# The record's members: which are names, and which kind each name must be
# ("type": an inductive type; "not-type": a declaration that is not one;
# None: any declaration). An eliminator's target types are any constant
# (Lean keys them by the head constant of each target's type, which may be
# a definition: Std.PlausibleIterStep in Init).
NAMES = {"instance": {"name": "not-type", "class": "type"},
         "default_instance": {"name": "not-type", "class": "type"},
         "reducibility": {"name": None},
         "eliminator": {"name": "not-type"}}
MEMBERS = {"instance": {"name", "class", "priority", "synth_order"},
           "default_instance": {"name", "class", "priority"},
           "reducibility": {"name", "status"},
           "eliminator": {"name", "kind", "types"}}
DECLS = {b'{"axiom":': "axiom", b'{"def":': "def", b'{"thm":': "thm",
         b'{"opaque":': "opaque", b'{"quot":': "quot", b'{"inductive":': "inductive"}
BLOCK = {"types": "type", "ctors": "ctor", "recs": "recursor"}


class ElabError(Exception):
    pass


def text(obj):
    """The canonical JSON text of obj: sorted keys, no spaces, UTF-8."""
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def natural(value):
    return isinstance(value, int) and not isinstance(value, bool) and value >= 0


def name_of(value):
    """A name as a tuple of parts; ElabError unless a nonempty JSON array
    of strings and natural numbers."""
    if (not isinstance(value, list) or not value
            or not all(isinstance(p, str) or natural(p) for p in value)):
        raise ElabError(f"not a name: {text(value)}")
    return tuple(value)


def export_decls(path):
    """The export's declarations, {name: kind}, and its SHA-256 and size."""
    names, decls = {0: ()}, {}
    digest = hashlib.sha256()
    with open(path, "rb") as export:
        for line in export:
            digest.update(line)
            if line.startswith(b'{"in":'):
                record = json.loads(line)
                part = record.get("str") or record.get("num")
                value = part["str"] if "str" in record else part["i"]
                names[record["in"]] = names[part["pre"]] + (value,)
                continue
            kind = next((k for p, k in DECLS.items() if line.startswith(p)), None)
            if kind == "inductive":
                block = json.loads(line)["inductive"]
                for key, member in BLOCK.items():
                    for decl in block.get(key, []):
                        decls[names[decl["name"]]] = member
            elif kind is not None:
                decls[names[json.loads(line)[kind]["name"]]] = kind
    return decls, digest.hexdigest()


def manifest_sha(path):
    manifest = Path(f"{path}.manifest.json")
    try:
        return json.loads(manifest.read_text())["sha256"]
    except (OSError, ValueError, KeyError, TypeError):
        raise ElabError(f"{manifest}: missing or not an export manifest") from None


def check_shape(kind, body):
    """Fail unless the record's members are exactly its kind's, each well typed."""
    if not isinstance(body, dict) or set(body) != MEMBERS[kind]:
        raise ElabError(f"{kind}: members are not {sorted(MEMBERS[kind])}")
    for member in NAMES[kind]:
        name_of(body[member])
    if "priority" in body and not natural(body["priority"]):
        raise ElabError(f"{kind}: priority is not a natural number")
    if kind == "instance" and not (isinstance(body["synth_order"], list)
                                   and all(natural(k) for k in body["synth_order"])):
        raise ElabError("instance: synth_order is not a list of natural numbers")
    if kind == "reducibility" and body["status"] not in STATUSES:
        raise ElabError(f"reducibility: unknown status {text(body['status'])}")
    if kind == "eliminator":
        if body["kind"] not in ELIMINATOR_KINDS:
            raise ElabError(f"eliminator: unknown kind {text(body['kind'])}")
        if not isinstance(body["types"], list):
            raise ElabError("eliminator: types is not a list")
        for name in body["types"]:
            name_of(name)


def wanted(kind, body):
    """(name, kind wanted) for every name the record holds."""
    pairs = [(name_of(body[m]), want) for m, want in NAMES[kind].items()]
    if kind == "eliminator":
        pairs += [(name_of(t), None) for t in body["types"]]
    return pairs


def kept(kind, body, decls):
    """Whether every name is a declaration of the export; ElabError when
    one is of the wrong kind."""
    pairs = wanted(kind, body)
    if any(name not in decls for name, _ in pairs):
        return False
    for name, want in pairs:
        have = decls[name]
        if (want == "type") != (have == "type") and want is not None:
            raise ElabError(f"{kind} {text(list(name))}: a {have}, not of the kind expected")
    return True


def read_raw(path):
    """The modules and the records of RAW, as (kind, body) pairs."""
    lines = Path(path).read_bytes().split(b"\n")
    if lines[-1] != b"" or len(lines) < 2:
        raise ElabError("RAW is empty or has no final line feed")
    head = json.loads(lines[0])
    if head.get("lean") != {"githash": LEAN_GITHASH, "version": LEAN_VERSION}:
        raise ElabError(f"RAW was written by another Lean: {text(head.get('lean'))}")
    records = []
    for line in lines[1:-1]:
        record = json.loads(line)
        if not isinstance(record, dict) or len(record) != 1 or next(iter(record)) not in KINDS:
            raise ElabError(f"not a record: {line[:80]!r}")
        kind, body = next(iter(record.items()))
        check_shape(kind, body)
        records.append((kind, body))
    return head["modules"], records


def finish(raw, export):
    """The text of the elaboration data, and the number of records left out."""
    modules, records = read_raw(raw)
    decls, digest = export_decls(export)
    if manifest_sha(export) != digest:
        raise ElabError(f"{export} differs from its manifest's SHA-256")
    keep = [(k, b) for k, b in records if kept(k, b, decls)]
    lines = sorted((KINDS.index(k), text({k: b})) for k, b in keep)
    body = "".join(line + "\n" for _, line in lines)
    head = {"elab_data": {"export_sha256": digest, "format": FORMAT, "format_version": VERSION,
                          "lean_githash": LEAN_GITHASH, "lean_version": LEAN_VERSION,
                          "modules": modules,
                          "records": {k: sum(1 for x, _ in keep if x == k) for k in KINDS},
                          "records_sha256": hashlib.sha256(body.encode()).hexdigest()}}
    return text(head) + "\n" + body, len(records) - len(keep)


def write(path, data):
    """Write through a temporary file, so a failure never leaves a partial file."""
    partial = Path(f"{path}.partial")
    partial.write_text(data, encoding="utf-8")
    os.replace(partial, path)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("raw", type=Path)
    parser.add_argument("export", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args(argv)
    try:
        data, left_out = finish(args.raw, args.export)
    except (ElabError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"export_elab.py: {error}", file=sys.stderr)
        return 1
    write(args.output, data)
    counts = json.loads(data.split("\n", 1)[0])["elab_data"]["records"]
    print(f"{args.output}: " + ", ".join(f"{counts[k]} {k}" for k in KINDS)
          + f"; {left_out} records left out (not declarations of the export)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
