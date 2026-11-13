#!/usr/bin/env python3
"""Finish LeanForth's elaboration data (plan rows FE1d and FE1e1; ADR 0021 D10).

Usage (from any folder):
  python3 scripts/export_elab.py RAW EXPORT OUTPUT

scripts/export-elab.sh runs this after scripts/export_elab.lean, with pinned
Lean, has written RAW for the modules of the Lean export EXPORT (made by
scripts/export.sh, so with its manifest beside it). It writes OUTPUT, the
elaboration data LeanForth reads (`leanforth check --elab-data OUTPUT`;
src/front/elab-data.fs), format version 2, documented in
docs/programming/ELABORATION_DATA.md and schemas/elab-data-2.schema.json:

  line 1    {"elab_data": {...}}: the format and its version, the export's
            SHA-256 (as its manifest records it), the Lean version and
            revision, the modules, the records of each kind and the
            SHA-256 of every line after this one, each with its line feed
  then      one record per line, sorted by kind (class, instance,
            instance_left_out, default_instance, reducibility, eliminator,
            tag) and then by text

Only records whose every name is a declaration of EXPORT are kept, so that
a slice of a library (scripts/export.sh MODULE -- NAMES) gets the data of
its own declarations. Lean's instance tree is kept whole under every root
key the export can reach: a value of the tree whose declaration the export
lacks, or which is erased, becomes an instance_left_out record (its keys,
rank, priority and why), so that the ranks under each kept root stay
0, 1, 2, ... without a gap; a root whose own names the export lacks is
left out with all its values (no query of the export can reach it). The
records left out, by kind, are printed (for a whole module: those of the
internal and unsafe declarations leanexport does not write). A record whose
names are all there but of the wrong kind (a class that is not an inductive
type, an instance, eliminator or tagged declaration that is one), or an
instance of the export whose class or keys name what the export lacks, is
an error: then the export and the modules do not belong together. It
refuses (exit status 1, nothing written) RAW that is not as
export_elab.lean writes it (a key that is not one of Lean's, a key list
that is not one term, ranks under a root that are not 0, 1, 2, ...), an
export whose SHA-256 differs from its manifest's, and a Lean version other
than the pinned one. JSON is written with sorted keys and no spaces, UTF-8
as it is, so the same input always gives the same bytes. It runs at export
time, on the developer's machine: nothing on a LeanForth user's path needs it.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import sys

FORMAT = "leanforth-elab-data"
VERSION = 2
LEAN_VERSION = "4.35.0"
LEAN_GITHASH = "eb6cafb7290e8bd5f2937522d8d804f58f02bafc"
# The kinds of records, in the order of the file. sunfold (smart-unfolding
# bodies, plan row FE1d2) is in format 2 but not written yet: always 0.
KINDS = ("class", "instance", "instance_left_out", "default_instance", "reducibility",
         "eliminator", "tag", "matcher", "projection", "sunfold")
RAW_KINDS = ("class", "instance", "default_instance", "reducibility", "eliminator", "tag",
             "matcher", "projection")
STATUSES = ("reducible", "irreducible", "implicit_reducible", "instance_reducible")
ELIMINATOR_KINDS = ("induction", "cases")
TAGS = ("elab_as_elim", "elab_without_expected_type", "aux_recursor", "no_confusion",
        "cases_on", "rec_on", "brec_on")
REASONS = ("erased", "not_exported")
# The record's name members and which kind each name must be ("type": an
# inductive type; "not-type": a declaration that is not one; "def": a
# definition; "ctor": a constructor; None: any declaration). An
# eliminator's target types are any constant (Lean keys them by the head
# constant of each target's type, which may be a definition:
# Std.PlausibleIterStep in Init). A projection function is a definition,
# or a theorem for a structure in Prop (Iff.mp). Key names are checked
# apart (key_names); a left-out instance's own name is the one the export
# lacks.
NAMES = {"class": {"name": "type"},
         "instance": {"name": "not-type", "class": "type"},
         "instance_left_out": {},
         "default_instance": {"name": "not-type", "class": "type"},
         "reducibility": {"name": None},
         "eliminator": {"name": "not-type"},
         "tag": {"name": "not-type"},
         "matcher": {"name": "def"},
         "projection": {"name": "not-type", "ctor": "ctor"}}
MEMBERS = {"class": {"name", "out_params", "out_level_params"},
           "instance": {"name", "class", "priority", "synth_order", "keys", "rank"},
           "instance_left_out": {"name", "keys", "priority", "rank", "reason"},
           "default_instance": {"name", "class", "priority", "rank"},
           "reducibility": {"name", "status"},
           "eliminator": {"name", "kind", "types"},
           "tag": {"name", "tag"},
           "matcher": {"name", "num_params", "num_discrs", "u_elim_pos", "alt_infos",
                       "discr_names"},
           "projection": {"name", "ctor", "num_params", "idx", "from_class"}}
ALT_MEMBERS = {"num_fields", "num_overlaps", "has_unit_thunk"}
RAW_MEMBERS = dict(MEMBERS, instance=MEMBERS["instance"] | {"erased"})
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


def naturals(value):
    return isinstance(value, list) and all(natural(k) for k in value)


def name_of(value):
    """A name as a tuple of parts; ElabError unless a nonempty JSON array
    of strings and natural numbers."""
    if (not isinstance(value, list) or not value
            or not all(isinstance(p, str) or natural(p) for p in value)):
        raise ElabError(f"not a name: {text(value)}")
    return tuple(value)


# ---- Keys: Lean's DiscrTree.Key, as export_elab.lean writes them.
DIGITS = re.compile(r"0|[1-9][0-9]*")   # a natural number's canonical decimal digits
KEY_FORMS = {"const": {"const", "arity"}, "proj": {"proj", "idx", "arity"},
             "lit": {"lit"}, "lit_str": {"lit_str"}}


def key_arity(key):
    """Lean's Key.arity: the subterms that follow the key in a path; ElabError
    unless the key is one of Lean's forms (an fvar key is not: no global
    instance has one)."""
    if key in ("star", "other"):
        return 0
    if key == "arrow":
        return 1
    form = next((f for f, members in KEY_FORMS.items()
                 if isinstance(key, dict) and set(key) == members), None)
    if form is None or (form == "lit_str" and not isinstance(key["lit_str"], str)):
        raise ElabError(f"not a key: {text(key)}")
    if form == "lit" and not (isinstance(key["lit"], str) and DIGITS.fullmatch(key["lit"])):
        raise ElabError(f"not a key: {text(key)}")
    if form in ("const", "proj"):
        name_of(key[form])
        if not natural(key["arity"]) or (form == "proj" and not natural(key["idx"])):
            raise ElabError(f"not a key: {text(key)}")
        return key["arity"] + (form == "proj")
    return 0


def check_keys(keys):
    """Fail unless keys is a nonempty list of keys making one term, each key
    followed by as many complete terms as its arity."""
    if not isinstance(keys, list) or not keys:
        raise ElabError(f"not a key list: {text(keys)}")
    open_terms = 1
    for key in keys:
        if open_terms == 0:
            raise ElabError(f"keys after the term ends: {text(keys)}")
        open_terms += key_arity(key) - 1
    if open_terms:
        raise ElabError(f"keys end before the term: {text(keys)}")


def key_names(keys):
    """(name, kind wanted) of every key: a constant any declaration, a
    projection's structure an inductive type."""
    return [(name_of(k["const"]), None) if "const" in k else (name_of(k["proj"]), "type")
            for k in keys if isinstance(k, dict) and ("const" in k or "proj" in k)]


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


def check_matcher(body):
    """Fail unless a matcher's elimination position is a natural or null,
    its alternatives' members are well typed and its discriminants' names
    are names or null."""
    if body["u_elim_pos"] is not None and not natural(body["u_elim_pos"]):
        raise ElabError("matcher: u_elim_pos is not a natural number or null")
    alts = body["alt_infos"]
    if not isinstance(alts, list) or not all(
            isinstance(a, dict) and set(a) == ALT_MEMBERS and natural(a["num_fields"])
            and natural(a["num_overlaps"]) and isinstance(a["has_unit_thunk"], bool)
            for a in alts):
        raise ElabError(f"matcher: alt_infos is not a list of alternatives: {text(alts)}")
    if not isinstance(body["discr_names"], list):
        raise ElabError("matcher: discr_names is not a list")
    for name in body["discr_names"]:
        if name is not None:
            name_of(name)


def check_shape(kind, body, members=MEMBERS):
    """Fail unless the record's members are exactly its kind's, each well typed."""
    if not isinstance(body, dict) or set(body) != members[kind]:
        raise ElabError(f"{kind}: members are not {sorted(members[kind])}")
    for member in NAMES[kind]:
        name_of(body[member])
    for member in ("priority", "rank", "num_params", "num_discrs", "idx"):
        if member in body and not natural(body[member]):
            raise ElabError(f"{kind}: {member} is not a natural number")
    for member in ("synth_order", "out_params", "out_level_params"):
        if member in body and not naturals(body[member]):
            raise ElabError(f"{kind}: {member} is not a list of natural numbers")
    if "keys" in body:
        check_keys(body["keys"])
    for member, allowed in {"status": STATUSES, "tag": TAGS, "reason": REASONS}.items():
        if member in body and body[member] not in allowed:
            raise ElabError(f"{kind}: unknown {member} {text(body[member])}")
    for member in ("erased", "from_class"):
        if member in body and not isinstance(body[member], bool):
            raise ElabError(f"{kind}: {member} is not true or false")
    if kind == "instance_left_out":
        name_of(body["name"])
    if kind == "matcher":
        check_matcher(body)
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
    return pairs + key_names(body.get("keys", []))


def fits(want, have):
    """Whether a declaration of kind have is of the kind wanted."""
    if want in ("def", "ctor", "type"):
        return have == want
    return want is None or have != "type"


def kind_checked(kind, pairs, decls):
    """ElabError when a name the export has is of the wrong kind."""
    for name, want in pairs:
        have = decls.get(name)
        if have is not None and not fits(want, have):
            raise ElabError(f"{kind} {text(list(name))}: a {have}, not of the kind expected")


def kept(kind, body, decls):
    """Whether every name is a declaration of the export; ElabError when
    one is of the wrong kind."""
    pairs = wanted(kind, body)
    kind_checked(kind, pairs, decls)
    return all(name in decls for name, _ in pairs)


def left_out(body, reason):
    return {"name": body["name"], "keys": body["keys"], "priority": body["priority"],
            "rank": body["rank"], "reason": reason}


def tree_record(body, decls):
    """A value of Lean's instance tree as (kind, body) to write, or None
    when its root key names what the export lacks."""
    kind_checked("instance", wanted("instance_left_out", body), decls)
    if not all(name in decls for name, _ in key_names(body["keys"][:1])):
        return None
    if body["erased"]:
        return "instance_left_out", left_out(body, "erased")
    if name_of(body["name"]) not in decls:
        return "instance_left_out", left_out(body, "not_exported")
    plain = {k: v for k, v in body.items() if k != "erased"}
    if not kept("instance", plain, decls):
        raise ElabError(f"instance {text(body['name'])}: the export has it but not every "
                        "name of its class and keys")
    return "instance", plain


def check_ranks(records):
    """Fail unless the ranks of the tree's values under each root key are
    0, 1, 2, ... (each once)."""
    roots = {}
    for kind, body in records:
        if kind == "instance":
            roots.setdefault(text(body["keys"][0]), []).append(body["rank"])
    for root, ranks in roots.items():
        if sorted(ranks) != list(range(len(ranks))):
            raise ElabError(f"the ranks under root {root} are not 0, 1, 2, ...")


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
        if (not isinstance(record, dict) or len(record) != 1
                or next(iter(record)) not in RAW_KINDS):
            raise ElabError(f"not a record: {line[:80]!r}")
        kind, body = next(iter(record.items()))
        check_shape(kind, body, RAW_MEMBERS)
        records.append((kind, body))
    check_ranks(records)
    return head["modules"], records


def finish(raw, export):
    """The text of the elaboration data, and the records left out of each kind."""
    modules, records = read_raw(raw)
    decls, digest = export_decls(export)
    if manifest_sha(export) != digest:
        raise ElabError(f"{export} differs from its manifest's SHA-256")
    keep = []
    for kind, body in records:
        if kind == "instance":
            keep += [r for r in [tree_record(body, decls)] if r is not None]
        elif kept(kind, body, decls):
            keep.append((kind, body))
    left = {k: sum(1 for x, _ in records if x == k) for k in RAW_KINDS}
    for kind, _ in keep:
        left[kind if kind != "instance_left_out" else "instance"] -= 1
    lines = sorted((KINDS.index(k), text({k: b})) for k, b in keep)
    body = "".join(line + "\n" for _, line in lines)
    head = {"elab_data": {"export_sha256": digest, "format": FORMAT, "format_version": VERSION,
                          "lean_githash": LEAN_GITHASH, "lean_version": LEAN_VERSION,
                          "modules": modules,
                          "records": {k: sum(1 for x, _ in keep if x == k) for k in KINDS},
                          "records_sha256": hashlib.sha256(body.encode()).hexdigest()}}
    return text(head) + "\n" + body, left


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
        data, left_out_counts = finish(args.raw, args.export)
    except (ElabError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"export_elab.py: {error}", file=sys.stderr)
        return 1
    write(args.output, data)
    counts = json.loads(data.split("\n", 1)[0])["elab_data"]["records"]
    print(f"{args.output}: " + ", ".join(f"{counts[k]} {k}" for k in KINDS)
          + "; left out (not declarations of the export): "
          + ", ".join(f"{left_out_counts[k]} {k}" for k in RAW_KINDS))
    return 0


if __name__ == "__main__":
    sys.exit(main())
