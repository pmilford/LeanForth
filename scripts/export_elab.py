#!/usr/bin/env python3
"""Finish LeanForth's elaboration data (plan rows FE1d and FE1e1; ADR 0021 D10).

Usage (from any folder):
  python3 scripts/export_elab.py RAW EXPORT OUTPUT [--bind]

With --bind (as scripts/export-elab.sh runs it) it then adds the member
elab_records_sha256, the new data's records SHA-256, to EXPORT's manifest,
so that `leanforth check` refuses other data for that export (S1 note M6).

scripts/export-elab.sh runs this after scripts/export_elab.lean, with pinned
Lean, has written RAW for the modules of the Lean export EXPORT (made by
scripts/export.sh, so with its manifest beside it). It writes OUTPUT, the
elaboration data LeanForth reads (`leanforth check --elab-data OUTPUT`;
src/front/elab-data.fs and, for format 4, src/front/simp-data.fs), format
version 4 with --format 4 (RAW then written with export_elab.lean --simp:
also the @[congr] lemmas and the defeq tags simp reads, docs/design/
SIMP_DATA.md section 3, slice SD-a of docs/design/TACTIC_SIMP.md), else
format version 3, or 3.1 when a smart-unfolding
body holds metadata LeanForth does not carry (Lean's save_info and
noImplicitLambda annotations, Mathlib's TermCongr hole: each written as
an inert node of its kind, which the front end refuses to use), documented
in docs/programming/ELABORATION_DATA.md and schemas/elab-data-3.schema.json:

  line 1    {"elab_data": {...}}: the format and its version, the export's
            SHA-256 (as its manifest records it), the Lean version and
            revision, the modules, the records of each kind and the
            SHA-256 of every line after this one, each with its line feed
  then      one record per line, sorted by kind (class, instance,
            instance_left_out, default_instance, reducibility, eliminator,
            tag, matcher, projection, sunfold, binder_kinds, congr) and
            then by text, the congr records by their function's name and
            then their rank, so that each function's lemmas are a run of
            lines in the order simp tries them

Only records whose every name is a declaration of EXPORT are kept, so that
a slice of a library (scripts/export.sh MODULE -- NAMES) gets the data of
its own declarations. Lean's instance tree is kept whole under every root
key the export can reach: a value of the tree whose declaration the export
lacks, or which is erased, becomes an instance_left_out record (its keys,
rank, priority and why), so that the ranks under each kept root stay
0, 1, 2, ... without a gap; a root whose own names the export lacks is
left out with all its values (no query of the export can reach it). The
records left out, by kind, are printed (for a whole module: those of the
internal and unsafe declarations leanexport does not write). A smart-unfolding
record (sunfold) is kept when its definition is in the export, whatever its
body names: a body naming a constant the export lacks is counted and
printed ("bodies naming what the export lacks"), and LeanForth answers
unsupported when it would use one. A record whose
names are all there but of the wrong kind (a class that is not an inductive
type, an instance, eliminator or tagged declaration that is one), or an
instance of the export whose class or keys name what the export lacks, is
an error: then the export and the modules do not belong together. It
refuses (exit status 1, nothing written) RAW that is not as
export_elab.lean writes it (a key that is not one of Lean's, a key list
that is not one term, ranks under a root that are not 0, 1, 2, ...), an
export whose SHA-256 differs from its manifest's, and a Lean version other
than the pinned one. JSON is written with sorted keys and no spaces, UTF-8
as it is, so the same input always gives the same bytes. A congruence
lemma is kept when the export has its function and the lemma; an export
that has the function but not the lemma is refused (simp would otherwise
take another route than Lean's, docs/design/TACTIC_SIMP.md section 4:
add the lemma to the slice's roots). It runs at export
time, on the developer's machine: nothing on a LeanForth user's path needs it.
"""
import argparse
from array import array
import bisect
import hashlib
import json
import os
from pathlib import Path
import re
import sys

FORMAT = "leanforth-elab-data"
VERSION = 3
FORMAT_SIMP = 4   # --format 4: also the congr records and the defeq tags
LEAN_VERSION = "4.35.0"
LEAN_GITHASH = "eb6cafb7290e8bd5f2937522d8d804f58f02bafc"
# The kinds of records, in the order of the file; sunfold (smart-unfolding
# bodies, plan S2) is written from format 3 on, every one of the modules.
KINDS = ("class", "instance", "instance_left_out", "default_instance", "reducibility",
         "eliminator", "tag", "matcher", "projection", "sunfold", "binder_kinds", "congr")
RAW_KINDS = ("class", "instance", "default_instance", "reducibility", "eliminator", "tag",
             "matcher", "projection", "sunfold", "binder_kinds", "congr")
SIMP_KINDS = ("congr",)     # format 4's kinds
SIMP_TAGS = ("defeq",)      # format 4's tags
DEFEQ_TAG = '"tag":"defeq"'
STATUSES = ("reducible", "irreducible", "implicit_reducible", "instance_reducible")
ELIMINATOR_KINDS = ("induction", "cases")
TAGS = ("elab_as_elim", "elab_without_expected_type", "aux_recursor", "no_confusion",
        "cases_on", "rec_on", "brec_on", "match_pattern") + SIMP_TAGS
REASONS = ("erased", "not_exported")
# The record's name members and which kind each name must be ("type": an
# inductive type; "not-type": a declaration that is not one; "def": a
# definition; "ctor": a constructor; None: any declaration). An
# eliminator's target types are any constant; a congruence lemma ("thm":
# a theorem) any function, and a defeq tag a theorem (wanted); an (Lean keys them by the head
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
         "projection": {"name": "not-type", "ctor": "ctor"},
         "sunfold": {"name": "def"},
         "binder_kinds": {"name": None},
         "congr": {"name": "thm", "fun": None}}
MEMBERS = {"class": {"name", "out_params", "out_level_params"},
           "instance": {"name", "class", "priority", "synth_order", "keys", "rank"},
           "instance_left_out": {"name", "keys", "priority", "rank", "reason"},
           "default_instance": {"name", "class", "priority", "rank"},
           "reducibility": {"name", "status"},
           "eliminator": {"name", "kind", "types"},
           "tag": {"name", "tag"},
           "matcher": {"name", "num_params", "num_discrs", "u_elim_pos", "alt_infos",
                       "discr_names"},
           "projection": {"name", "ctor", "num_params", "idx", "from_class"},
           "sunfold": {"name", "level_params", "levels", "nodes", "value", "rec_arg"},
           "binder_kinds": {"name", "kinds"},
           "congr": {"name", "fun", "hyps", "priority", "rank"}}
KINDS_TEXT = re.compile("[0-3]+")   # one binder's kind, then its domain's binders'
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
    """The export's declarations, {name: kind}, its SHA-256, and its Pi nodes
    with each declaration's type node (Pis, types {name: node})."""
    names, decls, pis = {0: ()}, {}, Pis()
    pis.types = {}
    digest = hashlib.sha256()
    with open(path, "rb") as export:
        for line in export:
            digest.update(line)
            if line.startswith(b'{"forallE":'):
                pis.add(line)
                continue
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
                        pis.types[names[decl["name"]]] = decl["type"]
            elif kind is not None:
                decl = json.loads(line)[kind]
                decls[names[decl["name"]]] = kind
                pis.types[names[decl["name"]]] = decl["type"]
    return decls, digest.hexdigest(), pis


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


# ---- Smart-unfolding bodies: a table of levels and one of nodes, each
# entry referring only to earlier entries (export_elab.lean's forms).
LEVEL_FORMS = {"succ": 1, "max": 2, "imax": 2}
BINDER_MEMBERS = {"name", "info", "type", "body"}
LET_MEMBERS = {"name", "type", "value", "body", "non_dep"}
INFOS = ("default", "implicit", "strict", "inst")
ANNOTATIONS = (["sunfoldMatch"], ["sunfoldMatchAlt"], ["borrowed"])
# Format 3.1 (docs/design/MATHLIB_FRONT.md O1): three kinds of metadata
# LeanForth does not carry, each written as an inert node of its kind, which
# the front end refuses to use: Lean's save_info and noImplicitLambda
# annotations (one entry, true) and Mathlib's TermCongr hole (its two private
# keys, a boolean and a number). Each entry: (key, the value's form).
CONGR = ["_private", "Mathlib", "Tactic", "TermCongr", 0, "Mathlib", "Tactic", "TermCongr"]
INERT = {"save_info": ((["save_info"], "true"),),
         "noImplicitLambda": ((["noImplicitLambda"], "true"),),
         "congrHole": ((CONGR + ["congrHoleForLhsKey"], "bool"),
                       (CONGR + ["congrHoleIndex"], "nat"))}
FORMAT_INERT = "3.1"   # the format version of a file holding an inert node (a
                       # text: LeanForth's JSON formats hold no fractions)
INERT_NODE = '{"inert":'   # its text in the data (a string's quotes are escaped)
FORMAT_KINDS = "3.2"   # a file holding a binder_kinds record (and perhaps inert nodes)
# lean4export's binder kinds, as the data writes them (Lean's BinderInfo constructors).
BINDER_DIGITS = {b"default": "0", b"implicit": "1", b"strictImplicit": "2", b"instImplicit": "3"}
PI_LINE = re.compile(rb'\{"forallE":\{"binderInfo":"(\w+)","body":(\d+),"name":\d+,'
                     rb'"type":(\d+)\},"ie":(\d+)\}')


class Pis:
    """The export's Pi nodes (forallE): kind, domain and body by expression index,
    in arrays (Mathlib has 5.4 million), found by bisection (lean4export writes
    the indices in increasing order)."""

    def __init__(self):
        self.ie, self.kind = array("I"), array("B")
        self.dom, self.body = array("I"), array("I")

    def add(self, line):
        match = PI_LINE.fullmatch(line.rstrip(b"\n"))
        if match is None or match[1] not in BINDER_DIGITS:
            raise ElabError(f"a Pi node not as lean4export writes it: {line[:80]!r}")
        self.ie.append(int(match[4]))
        self.kind.append(int(BINDER_DIGITS[match[1]]))
        self.dom.append(int(match[3]))
        self.body.append(int(match[2]))

    def find(self, e):
        i = bisect.bisect_left(self.ie, e)
        return i if i < len(self.ie) and self.ie[i] == e else None

    def lead(self, e):
        """The kinds of e's leading Pi binders, as a text, and their nodes."""
        kinds, nodes = "", []
        while (i := self.find(e)) is not None:
            kinds += str(self.kind[i])
            nodes.append(i)
            e = self.body[i]
        return kinds, nodes

    def texts(self, e):
        """binderTexts of export_elab.lean on the export's type node e."""
        kinds, nodes = self.lead(e)
        return [k + self.lead(self.dom[i])[0] for k, i in zip(kinds, nodes)]


def binder_record(body, export):
    """Whether Lean's kinds of a declaration differ from the export's (keep the
    record); ElabError when they do not fit its type: other numbers of binders."""
    have = export.texts(export.types[name_of(body["name"])])
    want = body["kinds"]
    if [len(t) for t in have] != [len(t) for t in want]:
        raise ElabError(f"binder_kinds {text(body['name'])}: {len(want)} binders, the "
                        f"export's type has {len(have)} or their domains differ")
    return have != want


def below(value, limit):
    return natural(value) and value < limit


def binder_name(value):
    """A binder's name as a tuple of parts: a name, or Lean's anonymous
    name, [] (a binder of Mathlib's Ring.ExProd.evalIntCast has one)."""
    return () if value == [] else name_of(value)


def entry_fits(entry, key, form):
    """Whether an mdata entry is key with a value of the form given."""
    if not (isinstance(entry, list) and len(entry) == 2 and isinstance(entry[1], dict)
            and len(entry[1]) == 1 and name_of(entry[0]) == tuple(key)):
        return False
    (kind, value), = entry[1].items()
    if form == "nat":
        return kind == "nat" and isinstance(value, str) and DIGITS.fullmatch(value) is not None
    return kind == "bool" and (value is True if form == "true" else isinstance(value, bool))


def inert_kind(entries):
    """The kind of inert metadata an mdata node's entries are, or None."""
    return next((kind for kind, form in INERT.items()
                 if isinstance(entries, list) and len(entries) == len(form)
                 and all(entry_fits(e, k, f) for e, (k, f) in zip(entries, form))), None)


def annotation(entries):
    """Whether an mdata node's entries are one of S2's annotations, true."""
    return (isinstance(entries, list) and len(entries) == 1 and isinstance(entries[0], list)
            and len(entries[0]) == 2 and entries[0][0] in ANNOTATIONS
            and entries[0][1] == {"bool": True} and entries[0][1]["bool"] is True)


def check_level(level, i, params):
    """Fail unless the level is one of the forms, its parts earlier levels."""
    if level == "zero":
        return
    if isinstance(level, dict) and len(level) == 1:
        (form, part), = level.items()
        if form == "param" and name_of(part) in params:
            return
        parts = part if LEVEL_FORMS.get(form) == 2 else [part]
        if (form in LEVEL_FORMS and isinstance(parts, list)
                and len(parts) == LEVEL_FORMS[form] and all(below(k, i) for k in parts)):
            return
    raise ElabError(f"sunfold: not a level of the table: {text(level)}")


def node_names(node, i, levels):
    """The constants a node names, after checking its form: (name, kind
    wanted) pairs, a projection's structure an inductive type."""
    if isinstance(node, dict) and set(node) == {"const", "levels"}:
        if isinstance(node["levels"], list) and all(below(k, levels) for k in node["levels"]):
            return [(name_of(node["const"]), None)]
    elif isinstance(node, dict) and len(node) == 1:
        (form, part), = node.items()
        refs = None
        if form == "bvar" and natural(part):
            refs = []
        elif form == "sort" and below(part, levels):
            refs = []
        elif form == "app" and isinstance(part, list) and len(part) == 2:
            refs = part
        elif form in ("lam", "forall") and isinstance(part, dict) and set(part) == BINDER_MEMBERS:
            binder_name(part["name"])
            refs = [part["type"], part["body"]] if part["info"] in INFOS else None
        elif form == "let" and isinstance(part, dict) and set(part) == LET_MEMBERS:
            binder_name(part["name"])
            ok = isinstance(part["non_dep"], bool)
            refs = [part["type"], part["value"], part["body"]] if ok else None
        elif form == "lit" and isinstance(part, str) and DIGITS.fullmatch(part):
            refs = []
        elif form == "str" and isinstance(part, str):
            refs = []
        elif form == "proj" and isinstance(part, dict) and set(part) == {"struct", "idx", "expr"}:
            refs = [part["expr"]] if natural(part["idx"]) else None
        elif form == "mdata" and isinstance(part, dict) and set(part) == {"entries", "expr"}:
            ok = annotation(part["entries"]) or inert_kind(part["entries"]) is not None
            refs = [part["expr"]] if ok else None
        if refs is not None and all(below(k, i) for k in refs):
            return [(name_of(part["struct"]), "type")] if form == "proj" else []
    raise ElabError(f"sunfold: not a node of the table: {text(node)[:200]}")


def sunfold_names(body):
    """The constants a smart-unfolding body names, after checking its
    tables: forms, each entry referring only to earlier entries, the
    root a node, the recursion argument a natural number or null."""
    params = [name_of(p) for p in body["level_params"]] if isinstance(
        body["level_params"], list) else None
    levels, nodes = body["levels"], body["nodes"]
    if params is None or not isinstance(levels, list) or not isinstance(nodes, list):
        raise ElabError("sunfold: level_params, levels and nodes are not lists")
    for i, level in enumerate(levels):
        check_level(level, i, params)
    names = []
    for i, node in enumerate(nodes):
        names += node_names(node, i, len(levels))
    if not below(body["value"], len(nodes)) or not (
            body["rec_arg"] is None or natural(body["rec_arg"])):
        raise ElabError("sunfold: value is not a node, or rec_arg not a natural number or null")
    return names


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
    if kind == "sunfold":
        sunfold_names(body)
    if kind == "congr" and not (naturals(body["hyps"])
                                and all(a < b for a, b in zip(body["hyps"], body["hyps"][1:]))):
        raise ElabError("congr: hyps is not a list of increasing natural numbers")
    if kind == "binder_kinds" and not (
            isinstance(body["kinds"], list) and body["kinds"]
            and all(isinstance(t, str) and KINDS_TEXT.fullmatch(t) for t in body["kinds"])):
        raise ElabError(f"binder_kinds: kinds is not a list of texts of the digits 0-3")
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
    if kind == "tag" and body["tag"] in SIMP_TAGS:
        pairs = [(name_of(body["name"]), "thm")]
    if kind == "eliminator":
        pairs += [(name_of(t), None) for t in body["types"]]
    return pairs + key_names(body.get("keys", []))


def fits(want, have):
    """Whether a declaration of kind have is of the kind wanted."""
    if want in ("def", "ctor", "type", "thm"):
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


def gapless(records, kind, group, what):
    """Fail unless the ranks of the records of kind in each group (its text
    of the record) are 0, 1, 2, ... (each once)."""
    groups = {}
    for k, body in records:
        if k == kind:
            groups.setdefault(group(body), []).append(body["rank"])
    for name, ranks in groups.items():
        if sorted(ranks) != list(range(len(ranks))):
            raise ElabError(f"{what} {name} are not 0, 1, 2, ...")


def check_ranks(records):
    """Fail unless the ranks of the tree's values under each root key, and
    of each function's congruence lemmas, are 0, 1, 2, ... (each once)."""
    gapless(records, "instance", lambda b: text(b["keys"][0]), "the ranks under root")
    gapless(records, "congr", lambda b: text(b["fun"]), "the ranks of the congruence lemmas of")


def congr_kept(body, decls):
    """Whether a congr record is kept: its function and lemma both in the
    export; ElabError for an export with the function but not the lemma."""
    if name_of(body["fun"]) not in decls:
        return False
    if name_of(body["name"]) not in decls:
        raise ElabError(f"the export has {text(body['fun'])} but not its congruence lemma "
                        f"{text(body['name'])}: add it to the slice's roots")
    return kept("congr", body, decls)


def simp_record(kind, body):
    """Whether a raw record is one of format 4's (a congr record, a defeq tag)."""
    return kind in SIMP_KINDS or (kind == "tag" and body["tag"] in SIMP_TAGS)


def read_raw(path, simp=False):
    """The modules and the records of RAW, as (kind, body) pairs; RAW
    written with --simp exactly when simp (format 4)."""
    lines = Path(path).read_bytes().split(b"\n")
    if lines[-1] != b"" or len(lines) < 2:
        raise ElabError("RAW is empty or has no final line feed")
    head = json.loads(lines[0])
    if head.get("lean") != {"githash": LEAN_GITHASH, "version": LEAN_VERSION}:
        raise ElabError(f"RAW was written by another Lean: {text(head.get('lean'))}")
    if head.get("simp", False) is not simp:
        raise ElabError("RAW was written " + ("without" if simp else "with")
                        + " export_elab.lean --simp: run the finisher with --format "
                        + ("3" if simp else "4"))
    records = []
    for line in lines[1:-1]:
        record = json.loads(line)
        if (not isinstance(record, dict) or len(record) != 1
                or next(iter(record)) not in RAW_KINDS):
            raise ElabError(f"not a record: {line[:80]!r}")
        kind, body = next(iter(record.items()))
        check_shape(kind, body, RAW_MEMBERS)
        if simp_record(kind, body) and not simp:
            raise ElabError(f"a format-4 record in RAW without --simp: {line[:80]!r}")
        records.append((kind, body))
    check_ranks(records)
    return head["modules"], records


def foreign_body(body, decls):
    """Whether a kept smart-unfolding body names a constant the export
    lacks (LeanForth answers unsupported at its use); ElabError when one it
    has is of the wrong kind."""
    names = sunfold_names(body)
    kind_checked("sunfold", names, decls)
    return not all(name in decls for name, _ in names)


def written_node(node):
    """A node as the data writes it: inert metadata as an inert node."""
    kind = inert_kind(node["mdata"]["entries"]) if "mdata" in node else None
    return node if kind is None else {"inert": {"expr": node["mdata"]["expr"], "key": kind}}


def written(kind, body):
    """A kept record as the data writes it."""
    return dict(body, nodes=[written_node(n) for n in body["nodes"]]) if kind == "sunfold" else body


def order(kind, body):
    """A record's place within its kind before its text: a congr record
    by its function's name and its rank (the order simp tries them in)."""
    return (text(body["fun"]), body["rank"]) if kind == "congr" else ("", 0)


def finish(raw, export, form=VERSION):
    """The text of the elaboration data of format form (3: 3, 3.1 or 3.2
    by what it holds; 4), the records left out of each kind and the
    smart-unfolding bodies kept that name what the export lacks."""
    modules, records = read_raw(raw, form == FORMAT_SIMP)
    decls, digest, pis = export_decls(export)
    if manifest_sha(export) != digest:
        raise ElabError(f"{export} differs from its manifest's SHA-256")
    keep = []
    foreign = same = 0
    for kind, body in records:
        if kind == "instance":
            keep += [r for r in [tree_record(body, decls)] if r is not None]
        elif kind == "congr":
            keep += [(kind, body)] if congr_kept(body, decls) else []
        elif kind == "binder_kinds" and kept(kind, body, decls):
            differs = binder_record(body, pis)
            keep += [(kind, body)] if differs else []
            same += not differs
        elif kept(kind, body, decls):
            keep.append((kind, body))
            foreign += kind == "sunfold" and foreign_body(body, decls)
    left = {k: sum(1 for x, _ in records if x == k) for k in RAW_KINDS}
    left["binder_kinds"] -= same
    for kind, _ in keep:
        left[kind if kind != "instance_left_out" else "instance"] -= 1
    lines = sorted((KINDS.index(k), order(k, b), text({k: written(k, b)})) for k, b in keep)
    body = "".join(line + "\n" for _, _, line in lines)
    counts = {k: sum(1 for x, _ in keep if x == k) for k in KINDS}
    version = FORMAT_INERT if INERT_NODE in body else VERSION
    if form == FORMAT_SIMP:
        version = FORMAT_SIMP        # every kind counted
    elif counts["binder_kinds"]:
        version = FORMAT_KINDS
        del counts["congr"]
    else:
        del counts["binder_kinds"], counts["congr"]   # format 3 and 3.1 have neither
    head = {"elab_data": {"export_sha256": digest, "format": FORMAT, "format_version": version,
                          "lean_githash": LEAN_GITHASH, "lean_version": LEAN_VERSION,
                          "modules": modules, "records": counts,
                          "records_sha256": hashlib.sha256(body.encode()).hexdigest()}}
    return text(head) + "\n" + body, left, foreign, same


def write(path, data):
    """Write through a temporary file, so a failure never leaves a partial file."""
    partial = Path(f"{path}.partial")
    partial.write_text(data, encoding="utf-8")
    os.replace(partial, path)


def bind(export, data):
    """Name the data's records SHA-256 in the export's manifest (S1 note M6,
    ADR 0021 D10): `leanforth check` then refuses any other data for it."""
    path = Path(f"{export}.manifest.json")
    record = json.loads(path.read_text())
    record["elab_records_sha256"] = json.loads(data.split("\n", 1)[0])["elab_data"]["records_sha256"]
    write(path, json.dumps(record, indent=2, sort_keys=True, ensure_ascii=False) + "\n")


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("raw", type=Path)
    parser.add_argument("export", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--bind", action="store_true",
                        help="also name the data's records SHA-256 in EXPORT's manifest")
    parser.add_argument("--format", type=int, choices=(VERSION, FORMAT_SIMP), default=VERSION,
                        help="4: also the congr records and defeq tags (RAW from --simp)")
    args = parser.parse_args(argv)
    try:
        data, left_out_counts, foreign, same = finish(args.raw, args.export, args.format)
    except (ElabError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"export_elab.py: {error}", file=sys.stderr)
        return 1
    write(args.output, data)
    if args.bind:
        bind(args.export, data)
    head = json.loads(data.split("\n", 1)[0])["elab_data"]
    counts, version = head["records"], head["format_version"]
    kinds = KINDS if version == FORMAT_SIMP else KINDS[:-1]
    print(f"{args.output}: " + ", ".join(f"{counts.get(k, 0)} {k}" for k in kinds)
          + "; left out (not declarations of the export): "
          + ", ".join(f"{left_out_counts[k]} {k}" for k in RAW_KINDS if k in kinds)
          + f"; {foreign} sunfold bodies naming what the export lacks"
          + f"; {data.count(INERT_NODE)} inert markers (format {version})"
          + f"; {same} binder_kinds as the export's, left out"
          + (f"; {data.count(DEFEQ_TAG)} defeq tags" if version == FORMAT_SIMP else ""))
    return 0


if __name__ == "__main__":
    sys.exit(main())
