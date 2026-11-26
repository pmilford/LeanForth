#!/usr/bin/env python3
"""Finish LeanForth's elaboration data of format 4 or 4.1 with the default simp set (simp
group 4; docs/programming/ELABORATION_DATA.md, "Format 4.1: the default simp set").

Usage (from any folder):
  python3 scripts/export_simp.py RAW EXPORT OUTPUT [--bind] --format 4|4.1

scripts/export-elab.sh runs this, for ELAB_FORMAT 4 and 4.1, in place of
scripts/export_elab.py, on RAW: export_elab.lean's records joined with
export_simp.lean's under the latter's header. It hands every record but the
default set's to export_elab.py's finish() (that file is imported, never changed:
its digest keys the Mathlib slice's data step, scripts/mathlib-slice.py), and with
--format 4.1 adds the default set's records, finished against EXPORT:

  simp_set       the default set and its simproc set, kept as written
  simp_lemma     a lemma of the default set whose origin is a declaration and
                 whose proof a theorem of the export (SIMP_DATA.md's kind of
                 that name, renamed so that no record kind is a folder name of
                 the checkout)
  simp_left_out  a lemma of the default set whose origin or proof the export
                 lacks: its set, phase (post), keys, rank, priority, origin,
                 proof and why (not_exported), so that each root's ranks stay
                 0, 1, 2, ... (LeanForth answers unsupported when simp reaches it)
  simp_unfold    a definition the default set unfolds, kept when the export has it
  simproc        an entry of the default simproc set: its name (a Lean function,
                 whatever the export holds), keys, phase, rank and whether it is a
                 dsimproc

A lemma or simproc whose root key names what the export lacks is left out with
its whole root (no term of the export reaches it); its other keys may name
constants the export lacks (foreign keys, as instance_left_out's). It refuses
(exit status 1, nothing written) a kept lemma whose proof is no theorem of the
export, ranks of a root that are not 0, 1, 2, ..., and whatever finish() refuses.
With --format 4 the default set's records are dropped, so the output is
export_elab.py's format 4 byte for byte. The header counts every kind, the
records' SHA-256 covers every line after it, and --bind names it in EXPORT's
manifest, as export_elab.py does.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import export_elab as ee  # noqa: E402

SET_KINDS = ("simp_set", "simp_lemma", "simp_left_out", "simp_unfold", "simproc")
MEMBERS = {"simp_set": {"name", "simprocs"},
           "simp_lemma": {"set", "origin", "inv", "post", "proof", "priority", "perm", "rfl",
                          "backward_rfl", "keys", "rank"},
           "simp_unfold": {"set", "name"},
           "simproc": {"name", "keys", "post", "rank", "dsimproc"}}


def split(raw):
    """RAW's lines: (the other records' RAW text, the default set's (kind, body))."""
    lines = Path(raw).read_bytes().split(b"\n")
    keep, mine = [lines[0]], []
    for line in lines[1:-1]:
        record = json.loads(line)
        kind = next(iter(record)) if isinstance(record, dict) and len(record) == 1 else None
        if kind in MEMBERS:
            body = record[next(iter(record))]
            if not isinstance(body, dict) or set(body) != MEMBERS[kind]:
                raise ee.ElabError(f"not a {kind} record: {line[:80]!r}")
            mine.append((kind, body))
        else:
            keep.append(line)
    return b"\n".join(keep) + b"\n", mine


def reachable(keys, decls):
    """Whether the root key names only what the export has."""
    ee.check_keys(keys)
    return all(name in decls for name, _ in ee.key_names(keys[:1]))


def lemma(body, decls):
    """A lemma's finished (kind, body), or None when its root is unreachable."""
    if not reachable(body["keys"], decls):
        return None
    origin, proof = ee.name_of(body["origin"]), ee.name_of(body["proof"])
    if origin in decls and proof in decls:
        if decls[proof] != "thm":
            raise ee.ElabError(f"simp lemma {ee.text(body['proof'])}: its proof is no theorem")
        ee.kind_checked("simp_lemma", ee.key_names(body["keys"]), decls)
        if not all(name in decls for name, _ in ee.key_names(body["keys"])):
            raise ee.ElabError(f"simp lemma {ee.text(body['origin'])}: keys the export lacks")
        return "simp_lemma", body
    out = {m: body[m] for m in ("set", "post", "keys", "rank", "priority", "origin", "proof")}
    return "simp_left_out", dict(out, reason="not_exported")


def finished(kind, body, decls):
    """The record as written, or None when it is left out."""
    if kind == "simp_lemma":
        return lemma(body, decls)
    if kind == "simp_unfold":
        return (kind, body) if ee.name_of(body["name"]) in decls else None
    if kind == "simproc":
        ee.name_of(body["name"])
        return (kind, body) if reachable(body["keys"], decls) else None
    return kind, body


def check_ranks(records):
    """Fail unless each phase's ranks under each root are 0, 1, 2, ..."""
    lemmas = [("lemma", b) for k, b in records if k in ("simp_lemma", "simp_left_out")]
    ee.gapless(lemmas, "lemma", lambda b: ee.text([b["post"], b["keys"][0]]),
               "the ranks of the default set's lemmas under")
    ee.gapless(records, "simproc", lambda b: ee.text([b["post"], b["keys"][0]]),
               "the ranks of the default simprocs under")


def order(kind, body):
    """A line's place: its kind, then its phase, root key and rank."""
    place = (body["post"], ee.text(body["keys"][0]), body["rank"]) if "rank" in body else ()
    return SET_KINDS.index(kind), place, ee.text({kind: body})


def finish(raw, export, form):
    """The data's text (format form), the default set's records left out, and
    export_elab.finish's report (left out by kind, foreign bodies, binder kinds)."""
    rest, mine = split(raw)
    with tempfile.NamedTemporaryFile(suffix=".ndjson") as tmp:
        tmp.write(rest)
        tmp.flush()
        data, left, foreign, same = ee.finish(tmp.name, export, form)
    if form != ee.FORMAT_REALIZED:
        return data, len(mine), (left, foreign, same)
    decls = ee.export_decls(export)[0]
    records = [r for r in (finished(k, b, decls) for k, b in mine) if r is not None]
    check_ranks(records)
    head_line, body = data.split("\n", 1)
    body += "".join(line + "\n" for _, _, line in sorted(order(k, b) for k, b in records))
    head = json.loads(head_line)
    counts = head["elab_data"]["records"]
    counts.update({k: sum(1 for x, _ in records if x == k) for k in SET_KINDS})
    head["elab_data"]["records_sha256"] = hashlib.sha256(body.encode()).hexdigest()
    return ee.text(head) + "\n" + body, len(mine) - len(records), (left, foreign, same)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("raw", type=Path)
    parser.add_argument("export", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--bind", action="store_true")
    parser.add_argument("--format", choices=("4", ee.FORMAT_REALIZED), required=True)
    args = parser.parse_args(argv)
    form = ee.FORMAT_REALIZED if args.format == ee.FORMAT_REALIZED else ee.FORMAT_SIMP
    try:
        data, dropped, _ = finish(args.raw, args.export, form)
    except (ee.ElabError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"export_simp.py: {error}", file=sys.stderr)
        return 1
    ee.write(args.output, data)
    if args.bind:
        ee.bind(args.export, data)
    counts = json.loads(data.split("\n", 1)[0])["elab_data"]["records"]
    print(f"{args.output}: format {args.format}; "
          + ", ".join(f"{counts.get(k, 0)} {k}" for k in SET_KINDS)
          + f"; {dropped} default-set records left out or dropped")
    return 0


if __name__ == "__main__":
    sys.exit(main())
