#!/usr/bin/env python3
"""Tests of the elaboration data (plan rows FE1d, FE1e1 and S2; docs/programming/ELABORATION_DATA.md).

Usage: python3 tests/front/test_elab_data.py   (from the repository root;
GFORTH names the Forth engine bin/leanforth runs, as make sets it)

1. The finisher, scripts/export_elab.py, on small RAW files against the
   init slice (tests/author/init-slice.ndjson): records kept and left out,
   the instance tree kept whole under each root the export reaches (a
   value the export lacks or that is erased becomes instance_left_out, a
   root it cannot reach is left out with its values), sorted and hashed
   the same way twice; a record of the wrong kind, a malformed record or
   key, keys that are not one term, ranks with a gap, another Lean and an
   export that differs from its manifest refused with exit status 1 and
   nothing written.
2. The synthetic eliminators fixture (tests/front/eliminators.elab.ndjson:
   records written here by hand, of real declarations of the slice, so
   that the eliminator path is used; no Lean attribute says them; and the
   slice's smart-unfolding body of Nat.add with nodes of every other form
   added after its root, one a projection of a structure the slice lacks,
   so that tests/front/elab-data.fs reads each form back) is what this
   file's generator writes, and so is tests/front/cut-off.elab.ndjson (its
   last line cut off). Every line of the two good fixtures is valid under
   schemas/elab-data-3.schema.json, and lines the schema can judge alone (a
   wrong member, status, kind, part, key, node, level or number) are
   invalid.
3. `leanforth check --env SLICE --elab-data DATA TEXT.lf` with the good
   data (exit 0, the counts line, the verdicts exactly those of the run
   without it), with a snapshot of the slice in place of the export, and
   with damaged data: every case refused, fail closed, with its exit code
   (4 invalid, 2 unsupported, 3 full), the line and the reason, the text
   never run. Every damaged file but the ones about the header's numbers
   gets a header recomputed, so that the one check it is about is reached.
   Format-1 and format-2 files are refused as another format version (a
   format-2 file says "sunfold":0, which would read as "no definition has
   a smart-unfolding body").
"""
import concurrent.futures
import hashlib
import json
import os
import pathlib
import re
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))
sys.path.insert(0, str(ROOT / "tests/support"))
import export_elab  # noqa: E402
from schema_subset import Validator, load_strict  # noqa: E402

SLICE = ROOT / "tests/author/init-slice.ndjson"
GOOD = ROOT / "tests/front/init-slice.elab.ndjson"
ELIMINATORS = ROOT / "tests/front/eliminators.elab.ndjson"
TEXT = ROOT / "tests/author/19-add-zero.lf"
LEANFORTH = ROOT / "bin/leanforth"
LIMIT = int(os.environ.get("TEST_TIMEOUT", "1800"))
KINDS = export_elab.KINDS
ADD_NAT = ('{"instance":{"class":["Add"],"keys":[{"arity":1,"const":["Add"]},'
           '{"arity":0,"const":["Nat"]}],"name":["instAddNat"],"priority":1000,"rank":17,'
           '"synth_order":[]}}')
ONE = ADD_NAT
HEAD = json.loads(GOOD.read_text().split("\n", 1)[0])["elab_data"]
GOOD_RECORDS = GOOD.read_text().split("\n")[1:-1]
failures = []


def fail(message):
    failures.append(message)
    print(f"FAIL: {message}")


def text(obj):
    return export_elab.text(obj)


def assemble(lines, **head):
    """A file of the slice holding lines, its header made for them, with
    head's members replacing the header's."""
    body = "".join(r + "\n" for r in lines)
    counts = dict.fromkeys(KINDS, 0)
    del counts["congr"]   # format 4's (tests/front/test_simp_data.py)
    if head.get("format_version") != "3.2":
        del counts["binder_kinds"]   # formats 3 and 3.1 have no such kind
    for line in lines:
        try:
            kind = next(iter(json.loads(line)))
        except (ValueError, StopIteration, TypeError):
            continue
        if kind in counts:
            counts[kind] += 1
    header = dict(HEAD, records=counts, records_sha256=hashlib.sha256(body.encode()).hexdigest())
    header.update(head)
    for key in [k for k, v in head.items() if v is DROP]:
        del header[key]
    return text({"elab_data": header}) + "\n" + body


DROP = object()   # assemble(..., member=DROP) leaves the member out


BITVEC_CONST = '{"arity":1,"const":["BitVec"]},"star"],"name":["BitVec","instAdd"]'
BITVEC_PROJ = '{"arity":0,"idx":0,"proj":["BitVec"]},"star"],"name":["BitVec","instAdd"]'


SUN = '"name":["Nat","add"],"nodes":['
SUN_END = '],"rec_arg":1,"value":23}}'
# Nodes of every other form, after the root of Nat.add's body: a sort, an
# anonymous instance-implicit pi, a have and a let, literals, a projection
# of a structure the slice lacks (the record foreign) and of Nat, a
# borrowed mark, and sorts of the levels max and imax (MORE_LEVELS).
MORE_NODES = ('{"sort":1}',
              '{"forall":{"body":0,"info":"inst","name":[],"type":24}}',
              '{"let":{"body":5,"name":["y"],"non_dep":true,"type":0,"value":7}}',
              '{"lit":"18446744073709551616"}', '{"str":"ab"}',
              '{"proj":{"expr":0,"idx":1,"struct":["Prod"]}}',
              '{"mdata":{"entries":[[["borrowed"],{"bool":true}]],"expr":27}}',
              '{"let":{"body":0,"name":["z"],"non_dep":false,"type":0,"value":0}}',
              '{"proj":{"expr":26,"idx":0,"struct":["Nat"]}}', '{"sort":2}', '{"sort":3}')
MORE_LEVELS = ('"levels":["zero",{"succ":0}]', '"levels":["zero",{"succ":0},{"max":[0,1]},{"imax":[1,0]}]')


def eliminators_text():
    """The synthetic fixture: the slice's data with four eliminators,
    BitVec.instAdd's key BitVec (a constant the slice lacks) made a
    projection of BitVec, so that a foreign projection is read back
    (tests/front/elab-data.fs) beside BitVec.instOfNat's foreign constant,
    and Nat.add's smart-unfolding body with MORE_NODES after its root."""
    elims = [text({"eliminator": {"kind": k, "name": n, "types": t}}) for k, n, t in (
        ("induction", ["Nat", "rec"], [["Nat"]]),
        ("cases", ["Nat", "casesOn"], [["Nat"]]),
        ("induction", ["And", "rec"], [["And"]]),
        ("induction", ["Eq", "rec"], [["Eq"], ["Nat"]]))]
    records = swap(MORE_LEVELS[0] + ',"name":["Nat","add"]', MORE_LEVELS[1] + ',"name":["Nat","add"]',
                   swap(SUN_END, "," + ",".join(MORE_NODES) + SUN_END,
                        swap(BITVEC_CONST, BITVEC_PROJ)))
    return assemble(records + elims)


def cut_off_text():
    """The eliminators fixture with its last record cut off: refused only
    after every other record was read (tests/front/elab-data.fs)."""
    return eliminators_text().rsplit("\n", 2)[0] + "\n"


# Format 3.1 (docs/design/MATHLIB_FRONT.md O1, O2): after the root of
# Nat.add's body, an inert node of each kind (nodes 24-26) and a lambda
# with an anonymous binder (27); instHAdd a default instance of HAdd a
# second time, at rank 1, as Mathlib makes instHSMul one twice.
INERT_NODES = ('{"inert":{"expr":0,"key":"save_info"}}',
               '{"inert":{"expr":24,"key":"noImplicitLambda"}}',
               '{"inert":{"expr":0,"key":"congrHole"}}',
               '{"lam":{"body":0,"info":"default","name":[],"type":0}}')
DFLT_HADD = '{"default_instance":{"class":["HAdd"]'
HADD_AGAIN = DFLT_HADD + ',"name":["instHAdd"],"priority":1000,"rank":1}}'
FORMAT31 = ROOT / "tests/front/format31.elab.ndjson"


def format31_records():
    records = swap(SUN_END, "," + ",".join(INERT_NODES) + SUN_END)
    i = records.index(first(DFLT_HADD)) + 1
    return records[:i] + [HADD_AGAIN] + records[i:]


def format31_text():
    """The format-3.1 fixture: the slice's data with format31_records()."""
    return assemble(format31_records(), format_version="3.1")


# Format 3.2 (plan FE1c-bk): binder kinds of two declarations of the
# slice: Nat.add's first binder implicit, and the first field of Nat.rec's
# minor premise succ (the reader takes any kinds whose numbers
# fit the export's type; the finisher writes only those that differ).
BK_ADD = '{"binder_kinds":{"kinds":["1","0"],"name":["Nat","add"]}}'
BK_REC = '{"binder_kinds":{"kinds":["10","0","010","0"],"name":["Nat","rec"]}}'
FORMAT32 = ROOT / "tests/front/format32.elab.ndjson"


def format32_text():
    """The format-3.2 fixture: the slice's data with BK_ADD and BK_REC."""
    return assemble(GOOD_RECORDS + [BK_ADD, BK_REC], format_version="3.2")


# The fixtures this file writes (--write-fixtures) and checks.
FIXTURES = {ELIMINATORS: eliminators_text,
            ROOT / "tests/front/cut-off.elab.ndjson": cut_off_text,
            FORMAT31: format31_text, FORMAT32: format32_text}


def first(needle, records=None):
    """The first record holding needle."""
    return next(r for r in (GOOD_RECORDS if records is None else records) if needle in r)


def line_of(needle, records):
    """The line of the file assemble(records) on which the first record
    holding needle stands (the header is line 1)."""
    return next(i for i, r in enumerate(records) if needle in r) + 2


def swap(old, new, records=None):
    """The good records with the first record holding old changed to new."""
    records = list(GOOD_RECORDS if records is None else records)
    i = next(i for i, r in enumerate(records) if old in r)
    records[i] = records[i].replace(old, new, 1)
    return records


def changed(old, new):
    """(file text, line of the record changed) of the good records with
    old changed to new in the first record holding it."""
    return assemble(swap(old, new)), line_of(old, GOOD_RECORDS)


def without(needle):
    return [r for r in GOOD_RECORDS if needle not in r]


def twice(needle):
    """The good records with the first holding needle given twice: (text, line of the second)."""
    i = next(i for i, r in enumerate(GOOD_RECORDS) if needle in r)
    records = GOOD_RECORDS[:i + 1] + [GOOD_RECORDS[i]] + GOOD_RECORDS[i + 1:]
    return assemble(records), i + 3


# ---- 1. The finisher.
RAW_HEAD = ('{"lean":{"githash":"eb6cafb7290e8bd5f2937522d8d804f58f02bafc","version":"4.35.0"},'
            '"modules":["Init"]}')


def raw_instance(name, cls, keys, rank, priority=1000, erased=False):
    return text({"instance": {"class": cls, "erased": erased, "keys": keys, "name": name,
                              "priority": priority, "rank": rank, "synth_order": []}})


ADD = {"arity": 1, "const": ["Add"]}
NAT = {"arity": 0, "const": ["Nat"]}
# Mathlib's TermCongr hole, as export_elab.lean writes its mdata entries.
HOLE = [[export_elab.CONGR + ["congrHoleForLhsKey"], {"bool": False}],
        [export_elab.CONGR + ["congrHoleIndex"], {"nat": "24"}]]


def raw_inert_body(hole=None):
    """Nat.add's body as export_elab.lean would write it with the three
    kinds of inert metadata (mdata) and an anonymous binder after its root
    (the format-3.1 fixture's INERT_NODES); hole replaces the TermCongr
    hole's entries."""
    marks = [[[["save_info"], {"bool": True}]], [[["noImplicitLambda"], {"bool": True}]],
             HOLE if hole is None else hole]
    nodes = [text({"mdata": {"entries": e, "expr": x}}) for e, x in zip(marks, (0, 24, 0))]
    return first(SUN).replace(SUN_END, "," + ",".join(nodes + [INERT_NODES[3]]) + SUN_END)


def binder_finisher_cases(run, out):
    """Format 3.2 (plan FE1c-bk): binder kinds equal to the export's are left
    out, the data byte for byte as without them; others are kept, format
    3.2, and leanforth check reads them; other numbers of binders, or a
    malformed text, are refused."""
    rec_same = BK_REC.replace('"010"', '"000"')
    run([RAW_HEAD, first(SUN)])
    plain = out.read_bytes() if out.exists() else b""
    done = run([RAW_HEAD, first(SUN), BK_ADD.replace('"1"', '"0"'), rec_same])
    if (done.returncode != 0 or out.read_bytes() != plain
            or "2 binder_kinds as the export's, left out" not in done.stdout):
        fail(f"finisher: binder kinds as the export's not left out: {done.stdout} {done.stderr}")
    done = run([RAW_HEAD, first(SUN), BK_ADD, BK_REC])
    lines = out.read_text().split("\n") if out.exists() else [""]
    head = json.loads(lines[0])["elab_data"] if lines[0] else {}
    if (done.returncode != 0 or head.get("format_version") != "3.2"
            or head["records"].get("binder_kinds") != 2 or lines[2:4] != [BK_ADD, BK_REC]):
        fail(f"finisher: binder kinds that differ not kept as 3.2: {done.stdout} {lines[:4]}")
    status, said = check(out)
    if status != 0:
        fail(f"the finisher's format-3.2 data refused: {status} {said[-300:]}")
    for bad in (BK_ADD.replace('["1","0"]', '["1"]'), BK_REC.replace('"010"', '"01"'),
                BK_ADD.replace('"1"', '"4"'), BK_ADD.replace('["1","0"]', '[]')):
        done = run([RAW_HEAD, bad])
        if done.returncode != 1 or out.exists():
            fail(f"finisher: binder kinds {bad} not refused: {done.returncode}")


def finisher_cases(work):
    outside = '{"reducibility":{"name":["Nat","noSuchName"],"status":"reducible"}}'
    raw_ok = [RAW_HEAD,
              raw_instance(["instAddNat"], ["Add"], [ADD, NAT], 1),
              raw_instance(["instAddInt"], ["Add"], [ADD, {"arity": 0, "const": ["Int"]}], 0),
              raw_instance(["Old", "instAdd"], ["Add"], [ADD, "star"], 2, erased=True),
              raw_instance(["instMulNat"], ["Mul"], [{"arity": 1, "const": ["Mul"]}, NAT], 0),
              '{"class":{"name":["Add"],"out_level_params":[],"out_params":[]}}',
              '{"class":{"name":["Mul"],"out_level_params":[],"out_params":[]}}',
              '{"tag":{"name":["Nat","casesOn"],"tag":"cases_on"}}',
              '{"projection":{"ctor":["Add","mk"],"from_class":true,"idx":0,"name":["Add","add"],'
              '"num_params":1}}',
              outside, '{"reducibility":{"name":["Nat","add"],"status":"reducible"}}',
              first(SUN), first(SUN).replace('["Nat","add"],"nodes"', '["Nat","noSuchDef"],"nodes"')]
    raw = work / "raw.ndjson"
    out = work / "out.ndjson"

    def run(lines, export=SLICE):
        raw.write_text("".join(line + "\n" for line in lines))
        out.unlink(missing_ok=True)
        return subprocess.run([sys.executable, str(ROOT / "scripts/export_elab.py"), str(raw),
                               str(export), str(out)], capture_output=True, text=True,
                              timeout=LIMIT)
    binder_finisher_cases(run, out)
    done = run(raw_ok)
    want = ("left out (not declarations of the export): 1 class, 1 instance, 0 default_instance, "
            "1 reducibility, 0 eliminator, 0 tag, 0 matcher, 0 projection, 1 sunfold, "
            "0 binder_kinds; "
            "0 sunfold bodies naming what the export lacks")
    if done.returncode != 0 or want not in done.stdout:
        fail(f"finisher on a good RAW: {done.returncode} {done.stdout} {done.stderr}")
    first_bytes = out.read_bytes()
    run([raw_ok[0]] + list(reversed(raw_ok[1:])))
    if out.read_bytes() != first_bytes:
        fail("finisher: the same records in another order give other bytes")
    lines = first_bytes.decode().split("\n")
    left = [json.loads(x)["instance_left_out"] for x in lines
            if x.startswith('{"instance_left_out"')]
    if (lines[2] != ONE.replace('"rank":17', '"rank":1')
            or sorted((x["name"][-1], x["reason"], x["rank"]) for x in left)
            != [("instAdd", "erased", 2), ("instAddInt", "not_exported", 0)]
            or json.loads(lines[0])["elab_data"]["records"]["reducibility"] != 1):
        fail(f"finisher: unexpected output {lines[:5]}")
    if json.loads(lines[0])["elab_data"]["format_version"] != 3 or "inert" in first_bytes.decode():
        fail(f"finisher: data without inert metadata not format 3: {lines[0][:120]}")
    done = run([RAW_HEAD, first(SUN).replace('{"const":["Nat","succ"]', '{"const":["Nat","noSuch"]')])
    if done.returncode != 0 or "1 sunfold bodies naming what the export lacks" not in done.stdout:
        fail(f"finisher on a body naming what the export lacks: {done.returncode} {done.stdout}")
    # Format 3.1 (MATHLIB_FRONT.md O1): the three kinds of inert metadata
    # written as inert nodes and an anonymous binder kept, the header
    # format 3.1; the format-3.1 fixture's body exactly, which leanforth
    # check reads.
    done = run([RAW_HEAD, raw_inert_body()])
    body = out.read_text().split("\n")[1] if out.exists() else ""
    if (done.returncode != 0 or "3 inert markers (format 3.1)" not in done.stdout
            or body != first(SUN, format31_records())
            or json.loads(out.read_text().split("\n")[0])["elab_data"]["format_version"] != "3.1"):
        fail(f"finisher on inert metadata: {done.returncode} {done.stdout} {done.stderr}")
    status, said = check(out)
    if status != 0 or "1 smart-unfolding bodies" not in said:
        fail(f"the finisher's format-3.1 data refused: {status} {said[-300:]}")
    # One instance alone, rank 0: each change below is the only thing wrong.
    base = raw_instance(["instAddNat"], ["Add"], [ADD, NAT], 0)
    bad = {
        "an instance whose class is no type": base.replace('"class":["Add"]',
                                                           '"class":["instAddNat"]'),
        "an instance that is a type": base.replace('"name":["instAddNat"]', '"name":["Nat"]'),
        "a record with another member": base.replace('"priority"', '"prio"'),
        "an unknown status": '{"reducibility":{"name":["Nat"],"status":"semireducible"}}',
        "a name that is no list": base.replace('["Add"]', '"Add"'),
        "a negative priority": base.replace("1000", "-1"),
        "an fvar key": base.replace('{"arity":0,"const":["Nat"]}', '{"arity":0,"fvar":1}'),
        "a literal as a number": base.replace('{"arity":0,"const":["Nat"]}', '{"lit":0}'),
        "a literal with a leading zero": base.replace('{"arity":0,"const":["Nat"]}',
                                                      '{"lit":"01"}'),
        "keys that are not one term": base.replace(',{"arity":0,"const":["Nat"]}', ''),
        "keys after the term": base.replace('{"arity":0,"const":["Nat"]}]',
                                            '{"arity":0,"const":["Nat"]},"star"]'),
        "erased not a boolean": base.replace('"erased":false', '"erased":0'),
        "a class that is no type": '{"class":{"name":["instAddNat"],"out_level_params":[],'
                                   '"out_params":[]}}',
        "a tag on a type": '{"tag":{"name":["Nat"],"tag":"cases_on"}}',
        "an unknown tag": '{"tag":{"name":["Nat","add"],"tag":"simp"}}',
        "a projection of no constructor": '{"projection":{"ctor":["Add"],"from_class":true,'
                                          '"idx":0,"name":["Add","add"],"num_params":1}}',
        "a matcher that is a theorem": '{"matcher":{"alt_infos":[],"discr_names":[],'
                                       '"name":["Nat","add_comm"],"num_discrs":0,'
                                       '"num_params":0,"u_elim_pos":null}}',
        "a matcher's alternative malformed": '{"matcher":{"alt_infos":[{"num_fields":1}],'
                                             '"discr_names":[],"name":["Nat","add","match_1"],'
                                             '"num_discrs":0,"num_params":0,"u_elim_pos":0}}',
        "a body of a theorem": first(SUN).replace('["Nat","add"],"nodes"', '["Nat","zero_add"],"nodes"'),
        "a body naming a later node": first(SUN).replace('{"app":[1,3]}', '{"app":[1,4]}'),
        "a body's level naming a later one": first(SUN).replace('{"succ":0}', '{"succ":1}'),
        "a body's unknown annotation": first(SUN).replace('"sunfoldMatch"]', '"noIndex"]'),
        "a body's root beyond its nodes": first(SUN).replace('"value":23', '"value":24'),
        "a body's binder info": first(SUN).replace('"default"', '"explicit"', 1),
        "a body's binder name malformed": first(SUN).replace('"name":["a"]', '"name":[1.5]', 1),
        "a body's save_info false": raw_inert_body().replace(
            '[["save_info"],{"bool":true}]', '[["save_info"],{"bool":false}]'),
        "Lean's noindex": raw_inert_body().replace('"save_info"', '"noindex"'),
        "a TermCongr hole's keys swapped": raw_inert_body(list(reversed(HOLE))),
        "a TermCongr hole without its index": raw_inert_body(HOLE[:1]),
        "a TermCongr hole whose index is no number": raw_inert_body(
            [HOLE[0], [HOLE[1][0], {"nat": "x"}]]),
        "a TermCongr hole whose flag is a number": raw_inert_body(
            [[HOLE[0][0], {"nat": "1"}], HOLE[1]]),
        "save_info with a second entry": raw_inert_body().replace(
            '[["save_info"],{"bool":true}]', '[["save_info"],{"bool":true}],[["borrowed"],{"bool":true}]'),
    }
    for what, line in bad.items():
        done = run([RAW_HEAD, line])
        if done.returncode != 1 or out.exists():
            fail(f"finisher accepts {what}: {done.returncode} {done.stdout}")
    gap = raw_ok[:2] + raw_ok[3:]   # instAddInt (rank 0) missing under Add
    done = run(gap)
    if done.returncode != 1 or "not 0, 1, 2" not in done.stderr:
        fail(f"finisher accepts ranks with a gap: {done.returncode} {done.stderr}")
    done = run([RAW_HEAD.replace("4.35.0", "4.34.0"), base])
    if done.returncode != 1 or "another Lean" not in done.stderr:
        fail(f"finisher accepts another Lean: {done.stderr}")
    copy = work / "slice.ndjson"
    copy.write_bytes(SLICE.read_bytes() + b"")
    (work / "slice.ndjson.manifest.json").write_text(
        (ROOT / "tests/author/init-slice.ndjson.manifest.json").read_text().replace("5f90", "5f91"))
    done = run([RAW_HEAD, base], export=copy)
    if done.returncode != 1 or "differs from its manifest" not in done.stderr:
        fail(f"finisher accepts an export that differs from its manifest: {done.stderr}")
    print(f"finisher: kept, left out, tree kept whole, sorted, deterministic; "
          f"{len(bad) + 3} refusals")


# ---- 3. The command line.
def check(data, library=("--env", str(SLICE))):
    done = subprocess.run([str(LEANFORTH), "check", *library, "--elab-data", str(data), str(TEXT)],
                          stdin=subprocess.DEVNULL, capture_output=True, text=True, timeout=LIMIT)
    return done.returncode, done.stdout + done.stderr


REFUSED = "the elaboration data was refused at line"
# The reader's error codes and texts, which are stable: the catalogue of
# docs/programming/ELABORATION_DATA.md, "Errors" (checked in errors_documented).
ERRORS = ["file missing or unreadable", "no line, or a line without its line feed",
          "a line longer than the limit", "not one JSON value within the limits", "no header",
          "not elaboration data", "another format version", "another Lean version",
          "elaboration data of another export", "malformed line", "unknown record kind",
          "unknown name", "a name several declarations have", "a declaration of the wrong kind",
          "an instance named twice", "a default instance of two classes",
          "a reducibility named twice", "two eliminators for the same types",
          "a number beyond 2^32 - 1", "records differ in number from the header",
          "records differ from their SHA-256", "no room", "name lookup failed",
          "the library's stage is sealed: its names cannot be looked up", "a read in progress",
          "the library's export could not be hashed",
          "a class without its class record before it", "a class named twice",
          "a tag named twice", "keys that are not one term",
          "two values of one root key with one rank", "ranks of a root key with a gap",
          "two default instances of one class with one rank",
          "a left-out instance the library has", "a matcher named twice",
          "a projection named twice", "numbers that do not fit the declaration's type",
          "a record kind this reader does not read yet",
          "other records than the export's manifest names",
          "a default instance's rank beyond 65535", "a smart-unfolding body named twice",
          "an index to no earlier entry", "a loose bound variable",
          "universe parameters other than the definition's",
          "an annotation this reader does not know", "binder kinds named twice",
          "a congruence lemma named twice", "congruence lemmas out of their function's order"]


def refusal(line, reason):
    """The refusal line's text for a reason, written whole or by its start."""
    (found,) = [t for t in ERRORS if t.startswith(reason)]
    return f"{REFUSED} {line} (error {ERRORS.index(found) + 1}): {found}"


def errors_documented():
    """The documentation's catalogue lists exactly ERRORS, in order."""
    doc = (ROOT / "docs/programming/ELABORATION_DATA.md").read_text()
    rows = re.findall(r"^\| (\d+) \| `([^`]+)` \|", doc.split("## Errors", 1)[-1], re.M)
    if rows != [(str(k), t) for k, t in enumerate(ERRORS, 1)]:
        fail(f"the error catalogue of ELABORATION_DATA.md differs: {rows}")


INST_NAT = '"name":["instAddNat"]'
DFLT_OFNAT = '{"default_instance":{"class":["OfNat"]'
DFLT_RANK0 = '"name":["instOfNatNat"],"priority":100,"rank":0}'
MATCH = '"discr_names":[null,null],"name":["Nat","add","match_1"]'
PROJ = '"idx":0,"name":["Add","add"]'
LEFT0 = '"name":["Lean","Grind","AddCommMonoid","toAdd"]'
DYADIC = '"name":["Dyadic","instAdd"]'


def case(name, pair, code, reason):
    content, line = pair
    return name, content, code, line, reason


def format2_text():
    """A format-2 file: the header of version 2 (sunfold 0) over the records
    format 2 had: no smart-unfolding body, no match_pattern tag."""
    records = [r for r in GOOD_RECORDS
               if not r.startswith('{"sunfold"') and '"match_pattern"' not in r]
    return assemble(records, format_version=2)


def format1_text():
    """A format-1 file: the header of version 1 over records of version 1."""
    records = ['{"instance":{"class":["Add"],"name":["instAddNat"],"priority":1000,'
               '"synth_order":[]}}']
    body = "".join(r + "\n" for r in records)
    header = dict(HEAD, format_version=1,
                  records={"default_instance": 0, "eliminator": 0, "instance": 1,
                           "reducibility": 0},
                  records_sha256=hashlib.sha256(body.encode()).hexdigest())
    return text({"elab_data": header}) + "\n" + body


def format1_cases():
    """Damaged files of the checks format 1 already had."""
    big = 4294967296
    longest = '{"reducibility":{"name":["' + "x" * 1100000 + '"],"status":"reducible"}}'
    n = len(GOOD_RECORDS)
    c = changed
    return [
        case("unknown name", c('["instAddNat"]', '["instAddNot"]'), 4, "unknown name"),
        case("unknown numeric part", c('["instAddNat"]', '["Nat",7]'), 4, "unknown name"),
        case("part beyond 32 bits", c('["instAddNat"]', f'["Nat",{big}]'), 4, "unknown name"),
        case("class of the wrong kind", c('"class":["Add"],"keys"', '"class":["instHAdd"],"keys"'),
             4, "a declaration of the wrong kind"),
        case("instance that is a type", c(INST_NAT, '"name":["Nat"]'), 4,
             "a declaration of the wrong kind"),
        case("default class of the wrong kind",
             c(DFLT_OFNAT, '{"default_instance":{"class":["id"]'), 4,
             "a declaration of the wrong kind"),
        ("eliminator that is a type", assemble(GOOD_RECORDS + [text({"eliminator": {
            "kind": "cases", "name": ["Nat"], "types": [["Nat"]]}})]), 4, n + 2,
         "a declaration of the wrong kind"),
        ("another export", assemble(GOOD_RECORDS, export_sha256="0" * 64), 4, 1,
         "elaboration data of another export"),
        ("not JSON", assemble(["{not json"] + GOOD_RECORDS), 4, 2, "not one JSON value"),
        case("extra member", c('"synth_order":[]', '"synth_order":[],"x":1'), 4, "malformed line"),
        case("missing member", c(',"synth_order":[]}', '}'), 4, "malformed line"),
        case("name not a list", c('["instAddNat"]', '"instAddNat"'), 4, "malformed"),
        case("empty name", c('["instAddNat"]', '[]'), 4, "malformed"),
        case("real part", c('["instAddNat"]', '["Nat",1.5]'), 4, "malformed"),
        case("negative part", c('["instAddNat"]', '["Nat",-1]'), 4, "malformed"),
        case("boolean part", c('["instAddNat"]', '[true]'), 4, "malformed"),
        ("unknown kind", assemble(['{"simp":{"name":["id"]}}'] + GOOD_RECORDS), 4, 2,
         "unknown record kind"),
        ("two members", assemble([GOOD_RECORDS[0][:-1] + ',"x":{}}'] + GOOD_RECORDS[1:]), 4, 2,
         "malformed line"),
        ("value no object", assemble(['{"instance":[]}'] + GOOD_RECORDS), 4, 2,
         "malformed line"),
        ("an array", assemble(["[1]"] + GOOD_RECORDS), 4, 2, "malformed line"),
        case("unknown status", c('"implicit_reducible"', '"semireducible"'), 4, "malformed"),
        ("unknown eliminator kind", assemble(GOOD_RECORDS + [text({"eliminator": {
            "kind": "recursion", "name": ["Nat", "rec"], "types": [["Nat"]]}})]), 4, n + 2,
         "malformed"),
        ("types not a list", assemble(GOOD_RECORDS + [text({"eliminator": {
            "kind": "cases", "name": ["Nat", "rec"], "types": ["Nat"]}})]), 4, n + 2,
         "malformed"),
        case("negative priority", c('"priority":1000,"rank":17', '"priority":-1,"rank":17'), 4,
             "malformed"),
        case("priority text", c('"priority":1000,"rank":17', '"priority":"1000","rank":17'), 4,
             "malformed"),
        case("synth order no list", c('"rank":17,"synth_order":[]', '"rank":17,"synth_order":1'),
             4, "malformed"),
        case("synth order real", c('"rank":17,"synth_order":[]', '"rank":17,"synth_order":[0.5]'),
             4, "malformed"),
        case("priority beyond 32 bits", c('"priority":1000,"rank":17',
                                          f'"priority":{big},"rank":17'),
             2, "a number beyond 2^32 - 1"),
        case("synth order beyond 32 bits", c('"rank":17,"synth_order":[]',
                                             f'"rank":17,"synth_order":[{big}]'),
             2, "a number beyond 2^32 - 1"),
        case("instance twice", twice(INST_NAT), 4, "an instance named twice"),
        case("default instance twice at one rank", twice(DFLT_OFNAT), 4,
             "two default instances of one class with one rank"),
        ("reducibility twice", assemble(GOOD_RECORDS + [first('"name":["Id"]').replace(
            '"implicit_reducible"', '"irreducible"')]), 4, n + 2, "a reducibility named twice"),
        ("eliminator twice", assemble(GOOD_RECORDS + [text({"eliminator": {
            "kind": "induction", "name": nm, "types": [["Nat"]]}}) for nm in
            (["Nat", "rec"], ["Nat", "casesOn"])]), 4, n + 3, "two eliminators for the same types"),
        ("record cut off", GOOD.read_text().rsplit("\n", 2)[0] + "\n", 4, n,
         "records differ in number from the header"),
        ("record added", GOOD.read_text() + first('"name":["Id"]').replace('["Id"]', '["Nat"]')
         + "\n", 4, n + 2, "records differ in number from the header"),
        ("no final line feed", GOOD.read_text()[:-1], 4, n + 1,
         "no line, or a line without its line feed"),
        ("empty file", "", 4, 1, "no line, or a line without its line feed"),
        ("record changed", GOOD.read_text().replace('"priority":1000', '"priority":1001', 1),
         4, n + 1, "records differ from their SHA-256"),
        ("no header", "\n".join(GOOD.read_text().split("\n")[1:]), 4, 1, "no header"),
        ("another format", assemble(GOOD_RECORDS, format="lean-elab"), 4, 1,
         "not elaboration data"),
        ("another format version", assemble(GOOD_RECORDS, format_version=4, extra=1), 2, 1,
         "another format version"),
        ("format version 1", format1_text(), 2, 1, "another format version"),
        ("format version 2", format2_text(), 2, 1, "another format version"),
        ("another Lean", assemble(GOOD_RECORDS, lean_version="4.34.0"), 2, 1,
         "another Lean version"),
        ("another Lean revision", assemble(GOOD_RECORDS, lean_githash="0" * 40), 2, 1,
         "another Lean version"),
        ("header member added", assemble(GOOD_RECORDS, extra=1), 4, 1, "malformed line"),
        ("records kind missing", assemble(GOOD_RECORDS, records={"instance": 3}), 4, 1,
         "malformed"),
        ("records hash no hex", assemble(GOOD_RECORDS, records_sha256="X" * 64), 4, 1,
         "malformed"),
        ("modules no list", assemble(GOOD_RECORDS, modules="Init"), 4, 1, "malformed"),
        ("modules of numbers", assemble(GOOD_RECORDS, modules=[1]), 4, 1, "malformed"),
        ("line too long", assemble(GOOD_RECORDS + [longest]), 3, n + 2,
         "a line longer than the limit"),
        ("no such file", None, 4, 0, "file missing or unreadable"),
        case("reducibility of an unknown name", c('"name":["Id"]', '"name":["Ix"]'), 4,
             "unknown name"),
        case("reducibility with another member",
             c('"status":"implicit_reducible"', '"status":"implicit_reducible","x":1'), 4,
             "malformed"),
        case("status a number", c('"name":["Id"],"status":"implicit_reducible"',
                                  '"name":["Id"],"status":3'), 4, "malformed"),
        case("default instance with another member",
             c('{"default_instance":{"class":["HAdd"]', '{"default_instance":{"klass":["HAdd"]'),
             4, "malformed"),
        ("eliminator with another member", assemble(GOOD_RECORDS + [text({"eliminator": {
            "kind": "cases", "name": ["Nat", "rec"], "types": [["Nat"]], "x": 1}})]), 4, n + 2,
         "malformed"),
        case("a binder's name", c('["instAddNat"]', '["motive"]'), 4, "unknown name"),
        case("unknown class", c('"class":["Add"],"keys"', '"class":["Addd"],"keys"'), 4,
             "unknown name"),
        ("version a text", assemble(GOOD_RECORDS, format_version="2"), 2, 1,
         "another format version"),
        ("format missing", assemble(GOOD_RECORDS, format=DROP), 4, 1, "not elaboration data"),
        ("format a number", assemble(GOOD_RECORDS, format=1), 4, 1, "not elaboration data"),
        ("count a text", assemble(GOOD_RECORDS, records=dict(HEAD["records"], instance="3")),
         4, 1, "malformed"),
        ("records hash a number", assemble(GOOD_RECORDS, records_sha256=5), 4, 1,
         "malformed"),
        ("header an array", "[]\n" + "".join(r + "\n" for r in GOOD_RECORDS), 4, 1,
         "no header"),
    ]


def format2_cases():
    """Damaged files of the checks format 2 adds (plan row FE1e1)."""
    big = 4294967296
    n = len(GOOD_RECORDS)
    c = changed
    nat = '{"arity":0,"const":["Nat"]}],"name":["instAddNat"]'
    no_add_class = without('{"class":{"name":["Add"]')
    rank0 = swap('"rank":17', '"rank":0')
    no_left1 = without('"name":["Lean","Grind","Semiring","toAdd"]')
    dflt = text({"default_instance": {"class": ["HAdd"], "name": ["instAddNat"],
                                      "priority": 10, "rank": 0}})
    return [
        # 27: a class without its class record.
        ("instance of a class without record", assemble(no_add_class), 4,
         line_of(INST_NAT, no_add_class), "a class without"),
        case("default instance of a type no class", c(DFLT_OFNAT,
                                                      '{"default_instance":{"class":["Nat"]'),
             4, "a class without"),
        # 28, 29, 35, 36: named twice.
        case("class twice", twice('{"class":{"name":["HAdd"]'), 4, "a class named twice"),
        case("tag twice", twice('"tag":"cases_on"'), 4, "a tag named twice"),
        case("matcher twice", twice(MATCH), 4, "a matcher named twice"),
        case("projection twice", twice(PROJ), 4, "a projection named twice"),
        # 30: keys not one term.
        case("keys short of the term", c(',' + nat, '],"name":["instAddNat"]'), 4,
             "keys that are not one term"),
        case("keys after the term", c(nat, '{"arity":0,"const":["Nat"]},"star"],'
                                           '"name":["instAddNat"]'), 4,
             "keys that are not one term"),
        case("no keys", c('"keys":[{"arity":1,"const":["Add"]},' + nat,
                          '"keys":[],"name":["instAddNat"]'), 4, "keys that are not one term"),
        # 31, 32: ranks.
        ("two values with one rank", assemble(rank0), 4, line_of(LEFT0, rank0),
         "two values of one root key"),
        ("ranks with a gap", assemble(no_left1), 4, len(no_left1) + 1, "ranks of a root key"),
        # 33: default ranks.
        ("two default instances with one rank", assemble(GOOD_RECORDS + [dflt]), 4, n + 2,
         "two default instances"),
        # 40: a default rank beyond 65535 (FE1e3 answers a cell per rank).
        case("default rank beyond the limit",
             c(DFLT_RANK0, DFLT_RANK0.replace('"rank":0', '"rank":65536')), 4,
             "a default instance's rank beyond 65535"),
        # 34: a left-out instance the library has (an erased one may be).
        case("left out but in the library", c(LEFT0, INST_NAT), 4, "a left-out instance"),
        # 37: numbers that do not fit the type.
        case("matcher with too many parameters", c('"num_params":0,"u_elim_pos":0}',
                                                   '"num_params":5,"u_elim_pos":0}'),
             4, "numbers that do not fit"),
        case("matcher universe beyond its parameters", c('"num_params":0,"u_elim_pos":0}',
                                                         '"num_params":0,"u_elim_pos":1}'),
             4, "numbers that do not fit"),
        case("matcher with one discriminant too few",
             c('"discr_names":[null,null],"name":["Nat","add","match_1"],"num_discrs":2',
               '"discr_names":[null],"name":["Nat","add","match_1"],"num_discrs":1'),
             4, "numbers that do not fit"),
        case("class out-parameter beyond its parameters", c('"out_params":[2]', '"out_params":[3]'),
             4, "numbers that do not fit"),
        case("class out-level beyond its universes", c('"out_level_params":[2]',
                                                       '"out_level_params":[3]'),
             4, "numbers that do not fit"),
        case("projection field beyond the constructor", c('"idx":0,"name":["Add","add"]',
                                                          '"idx":1,"name":["Add","add"]'),
             4, "numbers that do not fit"),
        case("projection with too many parameters",
             c('"name":["Add","add"],"num_params":1', '"name":["Add","add"],"num_params":2'),
             4, "numbers that do not fit"),
        # 14: wrong kinds.
        case("class no type", c('{"class":{"name":["Add"]', '{"class":{"name":["instAddNat"]'),
             4, "a declaration of the wrong kind"),
        case("tag on a type", c('"name":["Nat","below"],"tag"', '"name":["Nat"],"tag"'), 4,
             "a declaration of the wrong kind"),
        case("matcher a theorem",
             c(MATCH, '"discr_names":[null,null],"name":["Nat","add_comm"]'), 4,
             "a declaration of the wrong kind"),
        case("projection constructor a type", c('"ctor":["Add","mk"]', '"ctor":["Add"]'), 4,
             "a declaration of the wrong kind"),
        case("projection key of no type", c('{"arity":0,"const":["Nat"]}],"name":["instAddNat"]',
                                            '{"arity":0,"idx":0,"proj":["instAddNat"]}],'
                                            '"name":["instAddNat"]'),
             4, "a declaration of the wrong kind"),
        # 12: unknown names in keys.
        case("unknown key constant", c(nat, '{"arity":0,"const":["Natt"]}],'
                                            '"name":["instAddNat"]'), 4, "unknown name"),
        ("unknown key constant after a left-out instance", assemble(GOOD_RECORDS + [text(
            {"instance": {"class": ["Add"], "keys": [{"arity": 1, "const": ["Add"]},
                                                     {"arity": 0, "const": ["Natt"]}],
                          "name": ["Nat", "add"], "priority": 1000, "rank": 30,
                          "synth_order": []}})]), 4, n + 2, "unknown name"),
        case("left-out name not a list", c(LEFT0, '"name":"toAdd"'), 4, "malformed"),
        case("constant key name malformed", c(nat, '{"arity":0,"const":[1.5]}],'
                                                   '"name":["instAddNat"]'), 4, "malformed"),
        case("projection key name malformed", c(nat, '{"arity":0,"idx":0,"proj":[1.5]}],'
                                                     '"name":["instAddNat"]'), 4, "malformed"),
        case("projection key index a text", c(nat, '{"arity":0,"idx":"0","proj":["Nat"]}],'
                                                   '"name":["instAddNat"]'), 4, "malformed"),
        case("foreign projection arity a text",
             c(BITVEC_CONST, BITVEC_PROJ.replace('"arity":0', '"arity":"0"')), 4, "malformed"),
        case("left-out with another member", c(LEFT0, LEFT0 + ',"x":1'), 4, "malformed"),
        case("class with another member", c('{"class":{"name":["Add"]',
                                            '{"class":{"x":1,"name":["Add"]'), 4, "malformed"),
        case("tag with another member", c('"tag":"cases_on"', '"tag":"cases_on","x":1'), 4,
             "malformed"),
        case("matcher with another member", c(MATCH, MATCH + ',"x":1'), 4, "malformed"),
        case("projection with another member", c(PROJ, PROJ + ',"x":1'), 4, "malformed"),
        case("discriminant names not a list",
             c('"discr_names":[null,null],"name":["Nat","add","match_1"]',
               '"discr_names":2,"name":["Nat","add","match_1"]'), 4, "malformed"),
        case("instance projection key unknown", c(nat, '{"arity":0,"idx":0,"proj":["Natt"]}],'
                                                       '"name":["instAddNat"]'), 4, "unknown name"),
        case("left-out projection key malformed", c('{"arity":0,"const":["Dyadic"]}',
                                                    '{"arity":0,"idx":"0","proj":["Dyadic"]}'),
             4, "malformed"),
        # 10: malformed keys and members.
        case("key word unknown", c('"star","star","star"', '"star","starr","star"'), 4,
             "malformed"),
        case("fvar key", c(nat, '{"arity":0,"fvar":["x"]}],"name":["instAddNat"]'), 4,
             "malformed"),
        case("literal as a number", c('{"lit":"0"}', '{"lit":0}'), 4, "malformed"),
        case("literal with a leading zero", c('{"lit":"0"}', '{"lit":"00"}'), 4, "malformed"),
        case("literal not digits", c('{"lit":"0"}', '{"lit":"-1"}'), 4, "malformed"),
        case("string literal a number", c('{"lit":"0"}', '{"lit_str":0}'), 4, "malformed"),
        case("constant key without arity", c(nat, '{"const":["Nat"]}],"name":["instAddNat"]'),
             4, "malformed"),
        case("keys not a list", c('"keys":[{"arity":1,"const":["Add"]},' + nat,
                                  '"keys":"Add","name":["instAddNat"]'), 4, "malformed"),
        case("unknown reason", c('"reason":"not_exported"', '"reason":"private"'), 4,
             "malformed"),
        case("left-out name malformed", c(LEFT0, '"name":["Lean",1.5]'), 4, "malformed"),
        case("rank a text", c('"rank":17', '"rank":"17"'), 4, "malformed"),
        case("rank beyond 32 bits", c('"rank":17', f'"rank":{big}'), 2,
             "a number beyond 2^32 - 1"),
        case("arity beyond 32 bits", c(nat, f'{{"arity":{big},"const":["Nat"]}}],'
                                            '"name":["instAddNat"]'), 2, "a number beyond"),
        case("foreign numeric part beyond 32 bits", c('"const":["Dyadic"]',
                                                      f'"const":["Dyadic",{big}]'), 2,
             "a number beyond"),
        case("out params not a list", c('"out_level_params":[2],"out_params":[2]',
                                        '"out_level_params":[2],"out_params":2'), 4, "malformed"),
        case("unknown tag", c('"tag":"cases_on"', '"tag":"simp"'), 4, "malformed"),
        case("matcher discriminant names too few", c('"discr_names":[null,null],"name":["Nat",'
                                                     '"add","match_1"]',
                                                     '"discr_names":[null],"name":["Nat",'
                                                     '"add","match_1"]'), 4, "malformed"),
        case("matcher discriminant name malformed", c('"discr_names":[null,null],"name":["Nat",'
                                                      '"add","match_1"]',
                                                      '"discr_names":[null,[1.5]],"name":["Nat",'
                                                      '"add","match_1"]'), 4, "malformed"),
        case("matcher alternative member missing", c('{"has_unit_thunk":false,"num_fields":1,'
                                                     '"num_overlaps":0},',
                                                     '{"num_fields":1,"num_overlaps":0},'), 4,
             "malformed"),
        case("matcher universe a text", c('"num_params":0,"u_elim_pos":0}',
                                          '"num_params":0,"u_elim_pos":"0"}'), 4, "malformed"),
        case("projection class not a boolean", c('"from_class":true,"idx":0,"name":["Add","add"]',
                                                 '"from_class":1,"idx":0,"name":["Add","add"]'),
             4, "malformed"),
    ]


# A body of a universe-polymorphic definition: instHAdd.{u_1}, Sort u_1.
POLY = ('{"sunfold":{"level_params":[["u_1"]],"levels":[{"param":["u_1"]}],"name":["instHAdd"],'
        '"nodes":[{"sort":0}],"rec_arg":null,"value":0}}')
NAT_NODE = '{"const":["Nat"],"levels":[]}'


def poly(record):
    """The good records and a second body, record: (text, line of record)."""
    return assemble(GOOD_RECORDS + [record]), len(GOOD_RECORDS) + 2


def format3_cases():
    """Damaged files of the checks format 3 adds (plan S2): the
    smart-unfolding bodies."""
    c = changed
    sun = '"levels":["zero",{"succ":0}],' + SUN
    more = swap(MORE_LEVELS[0] + ',"name":["Nat","add"]', MORE_LEVELS[1] + ',"name":["Nat","add"]',
                swap(SUN_END, "," + ",".join(MORE_NODES) + SUN_END))
    sun_line = line_of(SUN, GOOD_RECORDS)
    return [
        # 41: named twice.
        case("smart-unfolding body twice", twice(SUN), 4, "a smart-unfolding body named twice"),
        # 42: an index to no earlier entry.
        case("node naming itself", c('{"app":[1,3]}', '{"app":[1,4]}'), 4, "an index to no earlier"),
        case("level naming itself", c(sun, sun.replace('{"succ":0}', '{"succ":1}')), 4,
             "an index to no earlier"),
        case("constant's level beyond the table", c('"levels":[1]}', '"levels":[2]}'), 4,
             "an index to no earlier"),
        case("sort's level beyond the table", (assemble(swap('{"sort":1}', '{"sort":4}', more)),
                                               sun_line), 4, "an index to no earlier"),
        case("max naming a later level", (assemble(swap('{"max":[0,1]}', '{"max":[0,2]}', more)),
                                          sun_line), 4, "an index to no earlier"),
        case("imax of one level", (assemble(swap('{"imax":[1,0]}', '{"imax":[1]}', more)),
                                   sun_line), 4, "malformed"),
        case("root beyond the nodes", c('"value":23}}', '"value":24}}'), 4,
             "an index to no earlier"),
        # The same checks in a second body, whose node and level tables
        # start past the first's (review s2-unfold-a re-check M2-new).
        case("second body's root beyond its nodes", poly(POLY.replace('"value":0}}', '"value":1}}')),
             4, "an index to no earlier"),
        case("second body's node naming itself", poly(POLY.replace('{"sort":0}', '{"app":[0,0]}')),
             4, "an index to no earlier"),
        case("second body's level beyond its table", poly(POLY.replace('{"sort":0}', '{"sort":1}')),
             4, "an index to no earlier"),
        # 37: a constant node with other than its declaration's number of
        # universe arguments (review s2-unfold-a L1).
        case("constant with a universe argument too many",
             c('{"const":["Nat"],"levels":[]}', '{"const":["Nat"],"levels":[0]}'), 4,
             "numbers that do not fit"),
        case("constant with a universe argument too few", c('"levels":[1]}', '"levels":[]}'), 4,
             "numbers that do not fit"),
        # 43: a loose bound variable at the root.
        case("loose root", c('"value":23}}', '"value":21}}'), 4, "a loose bound variable"),
        # 44: universe parameters.
        case("a universe parameter too many", c('{"sunfold":{"level_params":[]',
                                                '{"sunfold":{"level_params":[["u"]]'),
             4, "universe parameters other than"),
        case("a level naming no parameter", c(sun, sun.replace('"zero",', '{"param":["u"]},"zero",')
                                              .replace('{"succ":0}', '{"succ":1}')
                                              .replace('"levels":[1]}', '"levels":[2]}')),
             4, "universe parameters other than"),
        # 45: an annotation not Lean's three.
        case("unknown annotation", c('[["sunfoldMatch"],{"bool":true}]',
                                     '[["noImplicitLambda"],{"bool":true}]'), 2,
             "an annotation this reader"),
        case("annotation false", c('[["sunfoldMatch"],{"bool":true}]',
                                   '[["sunfoldMatch"],{"bool":false}]'), 2, "an annotation this reader"),
        # 12 and 14: the definition.
        case("body of an unknown definition", c(SUN, SUN.replace('"add"', '"adder"')), 4,
             "unknown name"),
        case("body of a theorem", c(SUN, SUN.replace('["Nat","add"]', '["Nat","zero_add"]')), 4,
             "a declaration of the wrong kind"),
        case("projection of a constructor", (assemble(swap('"struct":["Nat"]', '"struct":["Nat","succ"]',
                                                           more)), sun_line), 4,
             "a declaration of the wrong kind"),
        # 10: malformed nodes and levels.
        case("negative bound variable", c('{"bvar":1}', '{"bvar":-1}'), 4, "malformed"),
        case("binder without its info", c('"info":"default","name":["a"]', '"name":["a"]'), 4,
             "malformed"),
        case("unknown binder info", c('"info":"default","name":["a"]', '"info":"explicit","name":["a"]'),
             4, "malformed"),
        case("application of one", c('{"app":[1,3]}', '{"app":[1]}'), 4, "malformed"),
        case("unknown node", c('{"bvar":1}', '{"fvar":1}'), 4, "malformed"),
        case("constant without levels", c('{"const":["Nat"],"levels":[]}', '{"const":["Nat"]}'), 4,
             "malformed"),
        case("unknown level", c(sun, sun.replace('"zero"', '"one"')), 4, "malformed"),
        case("literal with a leading zero", (assemble(swap('"18446744073709551616"', '"01"', more)),
                                             sun_line), 4, "malformed"),
        case("annotation of two entries", c('[["sunfoldMatch"],{"bool":true}]',
                                            '[["sunfoldMatch"],{"bool":true}],[["borrowed"],'
                                            '{"bool":true}]'), 4, "malformed"),
        case("body with another member", c('"rec_arg":1,', '"rec_arg":1,"x":1,'), 4, "malformed"),
        case("rec_arg a text", c('"rec_arg":1,', '"rec_arg":"1",'), 4, "malformed"),
        # 44 for instHAdd.{u_1}: no universe parameter, or another one.
        case("polymorphic body without its parameter",
             poly(POLY.replace('"level_params":[["u_1"]],"levels":[{"param":["u_1"]}]',
                               '"level_params":[],"levels":[]').replace('{"sort":0}', NAT_NODE)),
             4, "universe parameters other than"),
        case("polymorphic body with another parameter",
             poly(POLY.replace('"level_params":[["u_1"]],"levels":[{"param":["u_1"]}]',
                               '"level_params":[["v"]],"levels":[]').replace('{"sort":0}', NAT_NODE)),
             4, "universe parameters other than"),
        case("rec_arg beyond 32 bits", c('"rec_arg":1,', '"rec_arg":4294967296,'), 2,
             "a number beyond"),
        case("unknown tag", c('"tag":"match_pattern"', '"tag":"match_patterns"'), 4, "malformed"),
        # Each reader's other refusals (malformed unless said).
        case("application not an array", c('{"app":[1,3]}', '{"app":5}'), 4, "malformed"),
        case("application's function later", c('{"app":[1,3]}', '{"app":[4,3]}'), 4,
             "an index to no earlier"),
        case("reference not a natural", c('{"app":[1,3]}', '{"app":[1,-1]}'), 4, "malformed"),
        case("node a number", c('{"bvar":1}', '5'), 4, "malformed"),
        case("level a number", c(sun, sun.replace('"zero"', '7')), 4, "malformed"),
        case("unknown level form", c(sun, sun.replace('{"succ":0}', '{"plus":0}')), 4, "malformed"),
        case("parameter level of no name", c(sun, sun.replace('{"succ":0}', '{"param":[1.5]}')), 4,
             "malformed"),
        case("universe parameter of no name", c('{"sunfold":{"level_params":[]',
                                                '{"sunfold":{"level_params":[[1.5]]'), 4, "malformed"),
        case("string node a number", (assemble(swap('{"str":"ab"}', '{"str":5}', more)), sun_line), 4,
             "malformed"),
        case("constant of no name", c('{"const":["Nat"],"levels":[]}', '{"const":[1.5],"levels":[]}'),
             4, "malformed"),
        case("projection of no name", (assemble(swap('"struct":["Nat"]', '"struct":[1.5]', more)),
                                       sun_line), 4, "malformed"),
        case("annotation value not an object", c('[["sunfoldMatch"],{"bool":true}]',
                                                 '[["sunfoldMatch"],5]'), 2, "an annotation this reader"),
        case("annotation value a number", c('[["sunfoldMatch"],{"bool":true}]',
                                            '[["sunfoldMatch"],{"bool":1}]'), 2, "an annotation this reader"),
        case("annotation key of two parts", c('[["sunfoldMatch"],{"bool":true}]',
                                              '[["sunfold","Match"],{"bool":true}]'), 2,
             "an annotation this reader"),
        case("annotation key a number", c('[["sunfoldMatch"],{"bool":true}]', '[[5],{"bool":true}]'), 2,
             "an annotation this reader"),
        case("annotation entry of one item", c('[["sunfoldMatch"],{"bool":true}]', '[["sunfoldMatch"]]'),
             4, "malformed"),
    ]


def format31_cases():
    """Damaged files of format 3.1 (MATHLIB_FRONT.md O1, O2): inert nodes,
    the version, a default instance named twice."""
    records = format31_records()
    sun_line = line_of(SUN, records)
    again_line = line_of(HADD_AGAIN, records)

    def v31(old, new):
        return assemble(swap(old, new, records), format_version="3.1"), sun_line
    save = '{"inert":{"expr":0,"key":"save_info"}}'
    head31 = assemble(GOOD_RECORDS, format_version="3.1")
    return [
        # An inert node is format 3.1's: in a format-3 file it is
        # malformed, as the readers of format 3 had it.
        ("inert node in a format-3 file", assemble(records), 4, sun_line, "malformed line"),
        case("inert node of S2's sunfoldMatch", v31(save, save.replace("save_info", "sunfoldMatch")),
             2, "an annotation this reader"),
        case("inert node of Lean's noindex", v31(save, save.replace("save_info", "noindex")), 2,
             "an annotation this reader"),
        # A key that is no text is malformed, not an unknown key (review L3 of MF1).
        case("inert key a name", v31(save, save.replace('"save_info"', '["save_info"]')), 4,
             "malformed"),
        case("inert key a number", v31(save, save.replace('"save_info"', '7')), 4, "malformed"),
        case("inert key null", v31(save, save.replace('"save_info"', 'null')), 4, "malformed"),
        case("inert node without its term", v31(save, '{"inert":{"key":"save_info"}}'), 4,
             "malformed"),
        case("inert node with another member", v31(save, save.replace("}}", ',"x":1}}')), 4,
             "malformed"),
        case("inert node naming itself", v31('{"expr":24,"key"', '{"expr":25,"key"'), 4,
             "an index to no earlier"),
        case("inert node of no object", v31(save, '{"inert":0}'), 4, "malformed"),
        case("save_info as an annotation", v31(save, '{"mdata":{"entries":[[["save_info"],'
                                                     '{"bool":true}]],"expr":0}}'), 2,
             "an annotation this reader"),
        # 16 and 33: a default instance named again.
        ("a default instance of two classes", assemble(swap(HADD_AGAIN, HADD_AGAIN.replace(
            '"HAdd"', '"OfNat"'), records), format_version="3.1"), 4, again_line,
         "a default instance of two classes"),
        ("a default instance twice at one rank", assemble(swap(HADD_AGAIN, HADD_AGAIN.replace(
            '"rank":1', '"rank":0'), records), format_version="3.1"), 4, again_line,
         "two default instances of one class with one rank"),
        # 7: other versions (3.1 is a text, LeanForth's JSON having no fractions).
        ("format version 3.1 as a number", head31.replace('"format_version":"3.1"',
                                                          '"format_version":3.1', 1),
         2, 1, "another format version"),
        ("format version 3 as a text", assemble(GOOD_RECORDS, format_version="3"), 2, 1,
         "another format version"),
        ("format version 3.3", assemble(GOOD_RECORDS, format_version="3.3"), 2, 1,
         "another format version"),
        ("format version 3.10", assemble(GOOD_RECORDS, format_version="3.10"), 2, 1,
         "another format version"),
        ("format version 3.1 and a space", assemble(GOOD_RECORDS, format_version="3.1 "), 2, 1,
         "another format version"),
        ("format version 31", assemble(GOOD_RECORDS, format_version=31), 2, 1,
         "another format version"),
    ]


def format32_cases():
    """Damaged files of format 3.2 (plan FE1c-bk): binder kinds malformed,
    named twice, not fitting the export's type, in a file of another
    version, and headers that count them wrongly."""
    records = GOOD_RECORDS + [BK_ADD, BK_REC]
    add_line = len(GOOD_RECORDS) + 2

    def v32(new, old=BK_ADD):
        return assemble([new if r == old else r for r in records], format_version="3.2"), add_line

    def kinds(*texts):
        return v32(BK_ADD.replace('["1","0"]', text(list(texts))))
    head32 = json.loads(format32_text().split("\n", 1)[0])["elab_data"]
    no_count = dict(head32["records"])
    del no_count["binder_kinds"]
    return [
        case("binder kinds in a format-3.1 file",
             (assemble(records, format_version="3.1"), add_line), 4, "unknown record kind"),
        case("binder kinds in a format-3 file", (assemble(records), add_line), 4,
             "unknown record kind"),
        case("binder kinds of a digit 4", kinds("4", "0"), 4, "malformed"),
        case("binder kinds of a letter", kinds("i", "0"), 4, "malformed"),
        case("binder kinds with an empty text", kinds("", "0"), 4, "malformed"),
        case("binder kinds of a number", v32(BK_ADD.replace('"1","0"', '1,0')), 4, "malformed"),
        case("binder kinds not a list", v32(BK_ADD.replace('["1","0"]', '"10"')), 4, "malformed"),
        case("binder kinds with another member", v32(BK_ADD.replace("]}}", '],"x":1}}')), 4,
             "malformed"),
        case("binder kinds without a name", v32('{"binder_kinds":{"kinds":["1","0"]}}'), 4,
             "malformed"),
        case("binder kinds of no declaration", v32(BK_ADD.replace('"add"', '"noSuch"')), 4,
             "unknown name"),
        case("binder kinds for fewer binders", kinds("1"), 4, "numbers that do not fit"),
        case("binder kinds for more binders", kinds("1", "0", "0"), 4, "numbers that do not fit"),
        case("binder kinds none", kinds(), 4, "numbers that do not fit"),
        case("binder kinds of a domain the type lacks", kinds("10", "0"), 4,
             "numbers that do not fit"),
        ("binder kinds missing a domain's binder",
         v32(BK_REC.replace('"010"', '"01"'), BK_REC)[0], 4, add_line + 1,
         "numbers that do not fit"),
        ("binder kinds named twice", v32(BK_ADD + "\n" + BK_ADD.replace('"1"', '"0"'))[0], 4,
         add_line + 1, "binder kinds named twice"),
        ("a 3.2 header without the binder kinds' count",
         assemble(records, format_version="3.2", records=no_count), 4, 1, "malformed"),
        ("a 3.1 header with the binder kinds' count",
         assemble(GOOD_RECORDS, format_version="3.1", records=dict(no_count, binder_kinds=0)),
         4, 1, "malformed"),
    ]


def run_case(work, item):
    name, content, code, line, reason = item
    data = work / (re.sub(r"\W+", "-", name) + ".ndjson")
    if content is not None:
        data.write_text(content, encoding="utf-8")
    status, out = check(data)
    want = refusal(line, reason)
    if status != code or want not in out or "accepted" in out:
        return f"{name}: exit {status} (wanted {code}); wanted '{want}'; got {out[-300:]!r}"
    return None


COUNTS = ("elaboration data: 3 instances, 2 default instances, 18 reducibility statuses, "
          "0 eliminators, 54 instances left out, 3 classes, 10 tags, 4 matchers, 3 projections, "
          "1 smart-unfolding bodies")


def command_line(work):
    status, out = check(GOOD)
    if status != 0 or COUNTS not in out:
        fail(f"good data: exit {status}: {out[-400:]}")
    plain = subprocess.run([str(LEANFORTH), "check", "--env", str(SLICE), str(TEXT)],
                           stdin=subprocess.DEVNULL, capture_output=True, text=True,
                           timeout=LIMIT)
    if plain.returncode != status or plain.stdout != "".join(
            line + "\n" for line in out.splitlines() if not line.startswith("elaboration data:")):
        fail("the verdicts with --elab-data differ from those without it")
    status, out = check(ELIMINATORS)
    if status != 0 or "18 reducibility statuses, 4 eliminators" not in out:
        fail(f"eliminators fixture: exit {status}: {out[-300:]}")
    other = assemble(GOOD_RECORDS + [text({"eliminator": {
        "kind": k, "name": ["Nat", "rec"], "types": [["Nat"]]}}) for k in ("induction", "cases")])
    (work / "both-kinds.ndjson").write_text(other)
    status, out = check(work / "both-kinds.ndjson")
    if status != 0:
        fail(f"one eliminator for induction and one for cases refused: {out[-300:]}")
    # Sixteen eliminators: the table grows past its first 16 slots' 3/4.
    many = assemble(GOOD_RECORDS + [text({"eliminator": {
        "kind": k, "name": ["Nat", "rec"], "types": [[t]]}})
        for t in ("Nat", "And", "Eq", "True", "Unit", "Id", "HAdd", "Add")
        for k in ("induction", "cases")])
    (work / "many.ndjson").write_text(many)
    status, out = check(work / "many.ndjson")
    if status != 0 or "16 eliminators" not in out:
        fail(f"sixteen eliminators: exit {status}: {out[-300:]}")
    # Accepted variants: an erased left-out instance the library has; a
    # discriminant's name; a matcher's universe that is null.
    accepted = {
        "erased in the library": swap(LEFT0, INST_NAT, swap('"reason":"not_exported"',
                                                             '"reason":"erased"')),
        "a discriminant's name": swap('"discr_names":[null,null],"name":["Nat","add","match_1"]',
                                      '"discr_names":[["h"],null],"name":["Nat","add","match_1"]'),
        "a matcher into Prop only": swap('"num_params":0,"u_elim_pos":0}',
                                         '"num_params":0,"u_elim_pos":null}'),
        "a left-out projection of a structure the slice lacks": swap(BITVEC_CONST, BITVEC_PROJ),
        "a projection of a structure of the slice": swap(
            BITVEC_CONST, BITVEC_PROJ.replace('"proj":["BitVec"]', '"proj":["Nat"]')),
        "a default rank at the limit": swap(DFLT_RANK0,
                                            DFLT_RANK0.replace('"rank":0', '"rank":65535')),
        "a string literal key": swap('"star",{"lit":"0"}],"name":["Zero","toOfNat0"]',
                                     '"star",{"lit_str":"0"}],"name":["Zero","toOfNat0"]'),
        "a body naming a constant the slice lacks": swap('{"const":["Nat","succ"]',
                                                         '{"const":["Nat","noSuch"]'),
        "a constant the slice lacks, with universe arguments": swap(
            '{"const":["Nat","succ"],"levels":[]', '{"const":["Nat","noSuch"],"levels":[1,0]'),
        "a body with a node of every form": swap(
            MORE_LEVELS[0] + ',"name":["Nat","add"]', MORE_LEVELS[1] + ',"name":["Nat","add"]',
            swap(SUN_END, "," + ",".join(MORE_NODES) + SUN_END)),
        "a body with no recursion argument": swap('"rec_arg":1,', '"rec_arg":null,'),
        "a recursion argument beyond the type's binders": swap('"rec_arg":1,', '"rec_arg":7,'),
        "a body of a universe-polymorphic definition": list(GOOD_RECORDS) + [POLY],
    }
    for what, records in accepted.items():
        path = work / (re.sub(r"\W+", "-", what) + ".ndjson")
        path.write_text(assemble(records))
        status, out = check(path)
        if status != 0:
            fail(f"{what} refused: {out[-300:]}")
    # Format 3.1: the fixture (inert nodes, an anonymous binder, a default
    # instance named twice at two ranks, both kept), and a 3.1 file
    # without an inert node; the verdicts those of the run without data.
    status, out = check(FORMAT31)
    if status != 0 or "3 default instances" not in out or "1 smart-unfolding bodies" not in out:
        fail(f"format-3.1 fixture: exit {status}: {out[-300:]}")
    if [x for x in out.splitlines() if not x.startswith("elaboration data:")] != \
            plain.stdout.splitlines():
        fail("the verdicts with format-3.1 data differ from those without it")
    (work / "plain31.ndjson").write_text(assemble(GOOD_RECORDS, format_version="3.1"))
    status, out = check(work / "plain31.ndjson")
    if status != 0 or COUNTS not in out:
        fail(f"format 3.1 without an inert node: exit {status}: {out[-300:]}")
    # Format 3.2 holds format 3.1's records too (review data-bk L2; fault
    # fe-bk-v32-not-v31): inert nodes and binder kinds in one file, read.
    (work / "both32.ndjson").write_text(
        assemble(format31_records() + [BK_ADD, BK_REC], format_version="3.2"))
    status, out = check(work / "both32.ndjson")
    if status != 0 or "3 default instances" not in out or "1 smart-unfolding bodies" not in out:
        fail(f"format 3.2 with inert nodes and binder kinds: exit {status}: {out[-300:]}")
    # A 3.2 label with no binder_kinds record (the writer never makes one): read as
    # the same records labelled 3.1 are (review data-bk L4, ELABORATION_DATA.md).
    (work / "plain32.ndjson").write_text(assemble(GOOD_RECORDS, format_version="3.2"))
    status, out = check(work / "plain32.ndjson")
    if status != 0 or COUNTS not in out:
        fail(f"format 3.2 without a binder_kinds record: exit {status}: {out[-300:]}")
    snapshot = work / "slice.lfsnap"
    made = subprocess.run([str(LEANFORTH), "check", "--save-snapshot", str(snapshot), str(SLICE)],
                          stdin=subprocess.DEVNULL, capture_output=True, text=True, timeout=LIMIT)
    if made.returncode != 0:
        fail(f"snapshot of the slice not written: {made.stdout[-300:]}")
    status, out = check(GOOD, ("--snapshot", str(snapshot)))
    if status != 0 or "elaboration data: 3 instances" not in out:
        fail(f"good data with the snapshot: exit {status}: {out[-300:]}")
    (work / "wrong.ndjson").write_text(assemble(GOOD_RECORDS, export_sha256="1" * 64))
    status, out = check(work / "wrong.ndjson", ("--snapshot", str(snapshot)))
    if status != 4 or "elaboration data of another export" not in out:
        fail(f"wrong data with the snapshot: exit {status}: {out[-300:]}")
    no_manifest = ("--no-manifest", "--env", str(SLICE))
    status, out = check(GOOD, no_manifest)
    if status != 0:
        fail(f"good data with --no-manifest: exit {status}: {out[-300:]}")
    status, out = check(work / "wrong.ndjson", no_manifest)
    if status != 4 or "another export" not in out:
        fail(f"wrong data with --no-manifest: exit {status}: {out[-300:]}")
    misuse = [(["--elab-data", str(GOOD), str(TEXT)], "--elab-data needs --env or --snapshot"),
              (["--elab-data", str(GOOD), str(SLICE)], "--elab-data goes only with a LeanForth text"),
              (["--elab-data"], "an option without its value"),
              (["--snapshot", str(snapshot), "--snapshot", str(snapshot), "--elab-data",
                str(GOOD), str(TEXT)], "--elab-data does not go with a layered snapshot yet")]
    for args, message in misuse:
        done = subprocess.run([str(LEANFORTH), "check", *args], stdin=subprocess.DEVNULL,
                              capture_output=True, text=True, timeout=LIMIT)
        if done.returncode != 4 or message not in done.stdout:
            fail(f"misuse {args}: exit {done.returncode}: {done.stdout}")
    cases = format1_cases() + format2_cases() + format3_cases() + format31_cases() + format32_cases()
    with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
        for problem in pool.map(lambda c: run_case(work, c), cases):
            if problem:
                fail(problem)
    print(f"command line: good data (export, snapshot, --no-manifest), verdicts unchanged, "
          f"{len(accepted)} accepted variants, {len(misuse)} misuses and {len(cases)} damaged "
          "files refused")


def bound_cases(work):
    """M6 (S1 note): export_elab.py --bind names the data's records SHA-256
    in a copy of the slice's manifest; leanforth check then reads that data
    and refuses other data (error 39) and a malformed member."""
    copy = work / "bound.ndjson"
    copy.write_bytes(SLICE.read_bytes())
    manifest = work / "bound.ndjson.manifest.json"
    plain = (ROOT / "tests/author/init-slice.ndjson.manifest.json").read_text()
    manifest.write_text(plain)
    raw = work / "bound-raw.ndjson"
    raw.write_text("\n".join([RAW_HEAD, '{"class":{"name":["Add"],"out_level_params":[],"out_params":[]}}',
                              raw_instance(["instAddNat"], ["Add"], [ADD, NAT], 0)]) + "\n")
    out = work / "bound.elab.ndjson"
    done = subprocess.run([sys.executable, str(ROOT / "scripts/export_elab.py"), str(raw), str(copy),
                           str(out), "--bind"], capture_output=True, text=True, timeout=LIMIT)
    records = json.loads(out.read_text().split("\n", 1)[0])["elab_data"]["records_sha256"]
    bound = json.loads(manifest.read_text())
    if (done.returncode != 0 or bound.pop("elab_records_sha256", None) != records
            or bound != json.loads(plain)):
        fail(f"finisher --bind: {done.returncode} {done.stderr} {manifest.read_text()[:200]}")
    library = ("--env", str(copy))
    code, said = check(out, library)
    if code != 0:
        fail(f"bound data refused: {code} {said}")
    code, said = check(GOOD, library)
    if code != 4 or refusal(1, "other records than") not in said:
        fail(f"other data accepted for a bound export: {code} {said}")
    manifest.write_text(manifest.read_text().replace(records, records[:-1] + "G"))
    code, said = check(out, library)
    if code != 4 or "manifest malformed" not in said:
        fail(f"a malformed elab_records_sha256 accepted: {code} {said}")
    code, said = check(GOOD, ("--no-manifest", "--env", str(copy)))
    if code != 0:
        fail(f"--no-manifest binds by the export's SHA-256 alone: {code} {said}")
    print("binding (M6): --bind names the records; that data read, other data and a malformed "
          "member refused")


def schema_cases():
    validator = Validator(load_strict((ROOT / "schemas/elab-data-3.schema.json").read_text()))
    lines = (GOOD.read_text().splitlines() + ELIMINATORS.read_text().splitlines()
             + FORMAT31.read_text().splitlines() + FORMAT32.read_text().splitlines())
    for line in lines:
        for error in validator.errors(load_strict(line)):
            fail(f"schema refuses a line of a fixture: {error}: {line[:80]}")
    proj = first(PROJ)
    match = first(MATCH)
    wrong = [ONE.replace('"priority"', '"prio"'), ONE.replace("1000", "-1"),
             ONE.replace("1000", "4294967296"), ONE.replace('["Add"]', '[]'),
             ONE.replace('["Add"]', '[true]'), ONE.replace('["Add"]', '"Add"'),
             ONE.replace('"rank":17', '"rank":-1'), ONE.replace(',"rank":17', ''),
             ONE.replace('"keys":[', '"keys":["starr",'), ONE.replace('"keys":[', '"keys":[{"lit":0},'),
             ONE.replace('"keys":[', '"keys":[{"lit":"01"},'),
             ONE.replace('"keys":[{"arity":1,"const":["Add"]},{"arity":0,"const":["Nat"]}]',
                         '"keys":[]'),
             '{"reducibility":{"name":["Nat"],"status":"semireducible"}}',
             '{"eliminator":{"kind":"recursion","name":["Nat","rec"],"types":[["Nat"]]}}',
             '{"simp":{"name":["id"]}}', ONE[:-1] + ',"x":{}}',
             first('"reason"').replace('"not_exported"', '"private"'),
             first('"aux_recursor"').replace('"aux_recursor"', '"simp"'),
             proj.replace('"from_class":true', '"from_class":1'),
             match.replace('"u_elim_pos":0', '"u_elim_pos":"0"'),
             '{"class":{"name":["Add"],"out_params":[]}}',
             lines[0].replace('"format_version":3', '"format_version":2')]
    sun = first(SUN)
    wrong += [sun.replace('{"bvar":1}', '{"bvar":-1}'), sun.replace('{"bvar":1}', '{"fvar":1}'),
              sun.replace('"info":"default","name":["a"]', '"info":"explicit","name":["a"]'),
              sun.replace('{"app":[1,3]}', '{"app":[1]}'), sun.replace('"zero"', '"one"'),
              sun.replace('[["sunfoldMatch"],{"bool":true}]', '[["noIndex"],{"bool":true}]'),
              sun.replace('{"bool":true}', '{"bool":false}', 1), sun.replace('"rec_arg":1', '"rec_arg":"1"'),
              sun.replace('"value":23', '"value":-1'), sun.replace(',"rec_arg":1', ''),
              first('"match_pattern"').replace('"match_pattern"', '"match_patterns"')]
    sun31 = first(SUN, format31_records())
    wrong += [sun31.replace('"key":"save_info"', '"key":"sunfoldMatch"'),
              sun31.replace('"key":"save_info"', '"key":["save_info"]'),
              sun31.replace('{"expr":0,"key":"save_info"}', '{"key":"save_info"}'),
              sun31.replace('"key":"save_info"', '"key":"save_info","x":1'),
              lines[0].replace('"format_version":3', '"format_version":"3.3"'),
              lines[0].replace('"format_version":3', '"format_version":"3"')]
    wrong += [BK_ADD.replace('"1"', '"4"'), BK_ADD.replace('"1"', '""'),
              BK_ADD.replace('["1","0"]', '[]'), BK_ADD.replace('"1","0"', '1,0'),
              BK_ADD.replace("]}}", '],"x":1}}'), '{"binder_kinds":{"kinds":["1","0"]}}']
    for line in wrong:
        if not validator.errors(load_strict(line)):
            fail(f"schema accepts {line[:80]}")
    print(f"schema: {len(lines)} fixture lines valid, {len(wrong)} wrong lines invalid")


HINTS = ROOT / "tests/front/unif-hints-mathlib.golden"


def unif_hints():
    """Mathlib's unification hints (MATHLIB_FRONT.md O7): pinned Lean's list
    (tests/front/unif-hints.lean on pinned Mathlib) holds Init's one and
    Mathlib's 27, and each is keyed at a definition or a projection, the
    heads at which src/front/defeq.fs (de-hint-key?) answers unsupported."""
    rows = HINTS.read_text().splitlines()
    if rows[-1] != "28 hints, 26 not keyed at a definition" or len(rows) != 29:
        fail(f"{HINTS.name}: not pinned Lean's 28 hints: {rows[-1]}")
    for row in rows[:-1]:
        name, *key = row.split(" ")
        if not (row.endswith(" definition") or key[0] == "Lean.Meta.DiscrTree.Key.proj"):
            fail(f"unification hint {name} keyed where LeanForth would answer false: {row}")
    print(f"unification hints: {len(rows) - 1}, each keyed at a definition or a projection")


def main():
    for path, made in FIXTURES.items():
        if path.read_text() != made():
            fail(f"{path} is not what {made.__name__}() writes")
    unif_hints()
    schema_cases()
    errors_documented()
    with tempfile.TemporaryDirectory() as work:
        work = pathlib.Path(work)
        finisher_cases(work)
        command_line(work)
        bound_cases(work)
    if failures:
        print(f"{len(failures)} failure(s)")
        return 1
    print("elaboration data: all tests passed")
    return 0


if __name__ == "__main__":
    if len(sys.argv) == 2 and sys.argv[1] == "--write-fixtures":
        for path, made in FIXTURES.items():
            path.write_text(made())
        sys.exit(0)
    sys.exit(main())
