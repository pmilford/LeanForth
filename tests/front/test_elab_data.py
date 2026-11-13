#!/usr/bin/env python3
"""Tests of the elaboration data (plan row FE1d; docs/programming/ELABORATION_DATA.md).

Usage: python3 tests/front/test_elab_data.py   (from the repository root;
GFORTH names the Forth engine bin/leanforth runs, as make sets it)

1. The finisher, scripts/export_elab.py, on small RAW files against the
   init slice (tests/author/init-slice.ndjson): records kept and left out,
   sorted and hashed the same way twice; a record of the wrong kind, a
   malformed record, another Lean and an export that differs from its
   manifest refused with exit status 1 and nothing written.
2. The synthetic eliminators fixture (tests/front/eliminators.elab.ndjson:
   records written here by hand, of real declarations of the slice, so
   that the eliminator path is used; no Lean attribute says them) is what
   this file's generator writes.
3. `leanforth check --env SLICE --elab-data DATA TEXT.lf` with the good
   data (exit 0, the counts line, the verdicts exactly those of the run
   without it), with a snapshot of the slice in place of the export, and
   with damaged data: every case refused, fail closed, with its exit code
   (4 invalid, 2 unsupported, 3 full), the line and the reason, the text
   never run. Every damaged file but the ones about the header's numbers
   gets a header recomputed, so that the one check it is about is reached.
"""
import concurrent.futures
import hashlib
import json
import os
import pathlib
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))
import export_elab  # noqa: E402

SLICE = ROOT / "tests/author/init-slice.ndjson"
GOOD = ROOT / "tests/front/init-slice.elab.ndjson"
ELIMINATORS = ROOT / "tests/front/eliminators.elab.ndjson"
TEXT = ROOT / "tests/author/19-add-zero.lf"
LEANFORTH = ROOT / "bin/leanforth"
LIMIT = int(os.environ.get("TEST_TIMEOUT", "1800"))
KINDS = export_elab.KINDS
ONE = '{"instance":{"class":["Add"],"name":["instAddNat"],"priority":1000,"synth_order":[]}}'
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
    for line in lines:
        try:
            kind = next(iter(json.loads(line)))
        except (ValueError, StopIteration, TypeError):
            continue
        if kind in counts:
            counts[kind] += 1
    header = dict(HEAD, records=counts, records_sha256=hashlib.sha256(body.encode()).hexdigest())
    header.update(head)
    return text({"elab_data": header}) + "\n" + body


def eliminators_text():
    """The synthetic fixture: the slice's data with four eliminators."""
    elims = [text({"eliminator": {"kind": k, "name": n, "types": t}}) for k, n, t in (
        ("induction", ["Nat", "rec"], [["Nat"]]),
        ("cases", ["Nat", "casesOn"], [["Nat"]]),
        ("induction", ["And", "rec"], [["And"]]),
        ("induction", ["Eq", "rec"], [["Eq"], ["Nat"]]))]
    return assemble(GOOD_RECORDS + elims)


def with_record(old, new, records=None):
    records = list(GOOD_RECORDS if records is None else records)
    assert old in records, old
    return [new if r == old else r for r in records]


def swap(old, new):
    """The good records with the first record holding old changed to new."""
    line = next(r for r in GOOD_RECORDS if old in r)
    return with_record(line, line.replace(old, new, 1))


# ---- 1. The finisher.
def finisher_cases(work):
    head = '{"lean":{"githash":"eb6cafb7290e8bd5f2937522d8d804f58f02bafc","version":"4.35.0"},' \
           '"modules":["Init"]}'
    outside = '{"reducibility":{"name":["Nat","noSuchName"],"status":"reducible"}}'
    raw_ok = [head, ONE, outside, '{"reducibility":{"name":["Nat","add"],"status":"reducible"}}']
    raw = work / "raw.ndjson"
    out = work / "out.ndjson"

    def run(lines, export=SLICE):
        raw.write_text("".join(line + "\n" for line in lines))
        out.unlink(missing_ok=True)
        return subprocess.run([sys.executable, str(ROOT / "scripts/export_elab.py"), str(raw),
                               str(export), str(out)], capture_output=True, text=True,
                              timeout=LIMIT)
    done = run(raw_ok)
    if done.returncode != 0 or "left out (not declarations of the export): 0 instance, 0 default_instance, 1 reducibility" not in done.stdout:
        fail(f"finisher on a good RAW: {done.returncode} {done.stdout} {done.stderr}")
    first = out.read_bytes()
    run([raw_ok[0]] + list(reversed(raw_ok[1:])))
    if out.read_bytes() != first:
        fail("finisher: the same records in another order give other bytes")
    lines = first.decode().split("\n")
    if lines[1] != ONE or json.loads(lines[0])["elab_data"]["records"]["reducibility"] != 1:
        fail(f"finisher: unexpected output {lines[:3]}")
    bad = {
        "an instance whose class is no type": ONE.replace('"class":["Add"]',
                                                          '"class":["instAddNat"]'),
        "an instance that is a type": ONE.replace('"name":["instAddNat"]', '"name":["Nat"]'),
        "a record with another member": ONE.replace('"priority"', '"prio"'),
        "an unknown status": '{"reducibility":{"name":["Nat"],"status":"semireducible"}}',
        "a name that is no list": ONE.replace('["Add"]', '"Add"'),
        "a negative priority": ONE.replace("1000", "-1"),
    }
    for what, line in bad.items():
        done = run([head, line])
        if done.returncode != 1 or out.exists():
            fail(f"finisher accepts {what}: {done.returncode} {done.stdout}")
    done = run([head.replace("4.35.0", "4.34.0"), ONE])
    if done.returncode != 1 or "another Lean" not in done.stderr:
        fail(f"finisher accepts another Lean: {done.stderr}")
    copy = work / "slice.ndjson"
    copy.write_bytes(SLICE.read_bytes() + b"")
    (work / "slice.ndjson.manifest.json").write_text(
        (ROOT / "tests/author/init-slice.ndjson.manifest.json").read_text().replace("5f90", "5f91"))
    done = run([head, ONE], export=copy)
    if done.returncode != 1 or "differs from its manifest" not in done.stderr:
        fail(f"finisher accepts an export that differs from its manifest: {done.stderr}")
    print("finisher: kept, left out, sorted, deterministic; 8 refusals")


# ---- 3. The command line.
def check(data, library=("--env", str(SLICE))):
    done = subprocess.run([str(LEANFORTH), "check", *library, "--elab-data", str(data), str(TEXT)],
                          stdin=subprocess.DEVNULL, capture_output=True, text=True, timeout=LIMIT)
    return done.returncode, done.stdout + done.stderr


REFUSED = "the elaboration data was refused at line"


def damaged_cases():
    """(name, file text or None for no file, exit code, line, reason)."""
    big = 4294967296
    longest = '{"reducibility":{"name":["' + "x" * 1100000 + '"],"status":"reducible"}}'
    cases = [
        ("unknown name", assemble(swap('["instAddNat"]', '["instAddNot"]')), 4, 2,
         "unknown name"),
        ("unknown numeric part", assemble(swap('["instAddNat"]', '["Nat",7]')), 4, 2,
         "unknown name"),
        ("part beyond 32 bits", assemble(swap('["instAddNat"]', f'["Nat",{big}]')), 4, 2,
         "unknown name"),
        ("class of the wrong kind", assemble(swap('"class":["Add"]', '"class":["instHAdd"]')),
         4, 2, "a declaration of the wrong kind"),
        ("instance that is a type", assemble(swap('"name":["instAddNat"]', '"name":["Nat"]')),
         4, 2, "a declaration of the wrong kind"),
        ("default class of the wrong kind",
         assemble(swap('{"default_instance":{"class":["OfNat"]',
                       '{"default_instance":{"class":["id"]')), 4, 6,
         "a declaration of the wrong kind"),
        ("eliminator that is a type", assemble(GOOD_RECORDS + [text({"eliminator": {
            "kind": "cases", "name": ["Nat"], "types": [["Nat"]]}})]), 4, 25,
         "a declaration of the wrong kind"),
        ("another export", assemble(GOOD_RECORDS, export_sha256="0" * 64), 4, 1,
         "elaboration data of another export"),
        ("not JSON", assemble(["{not json"] + GOOD_RECORDS), 4, 2, "not one JSON value"),
        ("extra member", assemble(swap('"synth_order":[]', '"synth_order":[],"x":1')), 4, 2,
         "malformed line"),
        ("missing member", assemble(swap(',"synth_order":[]', '')), 4, 2, "malformed line"),
        ("name not a list", assemble(swap('["instAddNat"]', '"instAddNat"')), 4, 2,
         "malformed"),
        ("empty name", assemble(swap('["instAddNat"]', '[]')), 4, 2, "malformed"),
        ("real part", assemble(swap('["instAddNat"]', '["Nat",1.5]')), 4, 2, "malformed"),
        ("negative part", assemble(swap('["instAddNat"]', '["Nat",-1]')), 4, 2, "malformed"),
        ("boolean part", assemble(swap('["instAddNat"]', '[true]')), 4, 2, "malformed"),
        ("unknown kind", assemble(['{"simp":{"name":["id"]}}'] + GOOD_RECORDS), 4, 2,
         "unknown record kind"),
        ("two members", assemble([ONE[:-1] + ',"x":{}}'] + GOOD_RECORDS[1:]), 4, 2,
         "malformed line"),
        ("value no object", assemble(['{"instance":[]}'] + GOOD_RECORDS), 4, 2,
         "malformed line"),
        ("an array", assemble(["[1]"] + GOOD_RECORDS), 4, 2, "malformed line"),
        ("unknown status", assemble(swap('"implicit_reducible"', '"semireducible"')), 4, 7,
         "malformed"),
        ("unknown eliminator kind", assemble(GOOD_RECORDS + [text({"eliminator": {
            "kind": "recursion", "name": ["Nat", "rec"], "types": [["Nat"]]}})]), 4, 25,
         "malformed"),
        ("types not a list", assemble(GOOD_RECORDS + [text({"eliminator": {
            "kind": "cases", "name": ["Nat", "rec"], "types": ["Nat"]}})]), 4, 25,
         "malformed"),
        ("negative priority", assemble(swap('"priority":1000', '"priority":-1')), 4, 2,
         "malformed"),
        ("priority text", assemble(swap('"priority":1000', '"priority":"1000"')), 4, 2,
         "malformed"),
        ("synth order no list", assemble(swap('"synth_order":[]', '"synth_order":1')), 4, 2,
         "malformed"),
        ("synth order real", assemble(swap('"synth_order":[]', '"synth_order":[0.5]')), 4, 2,
         "malformed"),
        ("priority beyond 32 bits", assemble(swap('"priority":1000', f'"priority":{big}')),
         2, 2, "a number beyond 2^32 - 1"),
        ("synth order beyond 32 bits",
         assemble(swap('"synth_order":[]', f'"synth_order":[{big}]')), 2, 2,
         "a number beyond 2^32 - 1"),
        ("instance twice", assemble(GOOD_RECORDS[:1] + [ONE.replace("1000", "10")]
                                    + GOOD_RECORDS[1:]), 4, 3, "an instance named twice"),
        ("default instance twice", assemble(GOOD_RECORDS[:5] + [GOOD_RECORDS[4]]
                                            + GOOD_RECORDS[5:]), 4, 7,
         "a default instance named twice"),
        ("reducibility twice", assemble(GOOD_RECORDS + [GOOD_RECORDS[-1].replace(
            '"reducible"', '"irreducible"')]), 4, 25, "a reducibility named twice"),
        ("eliminator twice", assemble(GOOD_RECORDS + [text({"eliminator": {
            "kind": "induction", "name": n, "types": [["Nat"]]}}) for n in
            (["Nat", "rec"], ["Nat", "casesOn"])]), 4, 26, "two eliminators for the same types"),
        ("record cut off", GOOD.read_text().rsplit("\n", 2)[0] + "\n", 4, 23,
         "records differ in number from the header"),
        ("record added", GOOD.read_text() + ONE.replace("instAddNat", "id") + "\n", 4, 25,
         "records differ in number from the header"),
        ("no final line feed", GOOD.read_text()[:-1], 4, 24,
         "no line, or a line without its line feed"),
        ("empty file", "", 4, 1, "no line, or a line without its line feed"),
        ("record changed", GOOD.read_text().replace('"priority":1000', '"priority":1001', 1),
         4, 24, "records differ from their SHA-256"),
        ("no header", "\n".join(GOOD.read_text().split("\n")[1:]), 4, 1, "no header"),
        ("another format", assemble(GOOD_RECORDS, format="lean-elab"), 4, 1,
         "not elaboration data"),
        ("another format version", assemble(GOOD_RECORDS, format_version=2, extra=1), 2, 1,
         "another format version"),
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
        ("line too long", assemble(GOOD_RECORDS + [longest]), 3, 25,
         "a line longer than the limit"),
        ("no such file", None, 4, 0, "file missing or unreadable"),
    ]
    return cases


def run_case(work, case):
    name, content, code, line, reason = case
    data = work / (name.replace(" ", "-") + ".ndjson")
    if content is not None:
        data.write_text(content, encoding="utf-8")
    status, out = check(data)
    want = f"{REFUSED} {line}: {reason}"
    if status != code or want not in out or "accepted" in out:
        return f"{name}: exit {status} (wanted {code}); wanted '{want}'; got {out[-300:]!r}"
    return None


def command_line(work):
    status, out = check(GOOD)
    if status != 0 or ("elaboration data: 3 instances, 2 default instances, "
                       "18 reducibility statuses, 0 eliminators") not in out:
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
              (["--elab-data"], "an option without its value")]
    for args, message in misuse:
        done = subprocess.run([str(LEANFORTH), "check", *args], stdin=subprocess.DEVNULL,
                              capture_output=True, text=True, timeout=LIMIT)
        if done.returncode != 4 or message not in done.stdout:
            fail(f"misuse {args}: exit {done.returncode}: {done.stdout}")
    cases = damaged_cases()
    with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
        for problem in pool.map(lambda c: run_case(work, c), cases):
            if problem:
                fail(problem)
    print(f"command line: good data (export, snapshot, --no-manifest), verdicts unchanged, "
          f"{len(misuse)} misuses and {len(cases)} damaged files refused")


def main():
    if ELIMINATORS.read_text() != eliminators_text():
        fail(f"{ELIMINATORS} is not what eliminators_text() writes")
    with tempfile.TemporaryDirectory() as work:
        work = pathlib.Path(work)
        finisher_cases(work)
        command_line(work)
    if failures:
        print(f"{len(failures)} failure(s)")
        return 1
    print("elaboration data: all tests passed")
    return 0


if __name__ == "__main__":
    if len(sys.argv) == 2 and sys.argv[1] == "--write-eliminators":
        ELIMINATORS.write_text(eliminators_text())
        sys.exit(0)
    sys.exit(main())
