"""Run records and replay through files (plan task 2.2.5).

Usage (from the repository root):
  GFORTH=... python3 tests/core/test_run_records.py            # make test
  GFORTH=... python3 tests/core/test_run_records.py --update   # rewrite the golden records
  GFORTH=... python3 tests/core/test_run_records.py --other-gforth GFORTH2

The records are written and replayed by Forth alone
(tests/support/run-records.fs, src/import/run-record.fs and run-replay.fs);
Python only drives Gforth and reads what it wrote. For the five pinned
exports and the four broken copies of the composition export: each record
is strict JSON valid against schemas/run-record-0.1.schema.json, with the
input's SHA-256, bytes and lines as Python computes them, the manifest's
outcome, the pinned versions and the expected verdict, label, axioms and
diagnostic of every declaration; two runs in two processes write the same
bytes; each record equals its golden copy in tests/core/run-records/
(written with Gforth 1.0.0) in every field but the two that name the host
Forth's version and engine, and byte for byte on that host; every record
replays as confirmed, and every golden record replays on this host with no
finding but those two fields. Each tampered record is refused with the
code and path named with it, and every replay report is valid against
schemas/replay-report-0.1.schema.json. The schema itself refuses records
that claim more than a checker could: accepted without its label or with
a diagnostic, a label on a rejection, declarations without a run. An
export swapped for another, with its manifest, between two reads of a run
(between rr-start and the import, or during the importer's first pass
only, served through a FIFO, with the manifest checked or not) is refused,
and an input of more declarations than a record keeps gives no record.

--other-gforth runs the same records with a second Gforth (Gforth 0.7.3,
CI's portability host): both write records equal in every field but those
two, and each replays the other's with findings only there.
"""
import argparse
import array
import copy
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import termios
import threading
import time
import unicodedata

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tests" / "support"))
from schema_subset import Validator, load_strict  # noqa: E402
sys.path.insert(0, str(ROOT / "scripts"))
import text_rule_tables  # noqa: E402

GFORTH = os.environ.get("GFORTH", "gforth")
DRIVER = "tests/support/run-records.fs"
GOLDEN = Path("tests/core/run-records")
RECORD_SCHEMA = Validator(json.loads(Path("schemas/run-record-0.1.schema.json").read_text()))
REPORT_SCHEMA = Validator(json.loads(Path("schemas/replay-report-0.1.schema.json").read_text()))
FUEL = 100000
LABEL = "experimental, not independently audited"
HOST_VERSION = ("host", "version")
HOST_ENGINE = ("host", "engine")
CASES = "tests/core/check-declaration-cases/composition-"
FIFO_TIMEOUT = 30                          # seconds for one run served through a FIFO

# Each input: its declarations' (name, verdict, diagnostic code, step), and
# whether a manifest stands beside it.
INPUTS = {
    "tests/reference/composition.ndjson": ([("composition", "accepted", None, None)], True),
    "tests/reference/identity.ndjson": ([("identity", "accepted", None, None)], True),
    "tests/reference/type-identity.ndjson": ([("type_identity", "accepted", None, None)], True),
    "tests/reference/poly-identity.ndjson": ([("poly_identity", "accepted", None, None)], True),
    "tests/reference/constant-fixture.ndjson": (
        [("fixtureId", "accepted", None, None), ("fixturePoly", "accepted", None, None),
         ("fixtureUse", "accepted", None, None)], True),
    CASES + "wrong-argument.ndjson": ([("composition", "rejected", 59, 7)], False),
    CASES + "postulate.ndjson": ([("composition", "unsupported", 42, 1)], False),
    CASES + "literal.ndjson": ([("composition", "unsupported", 43, 1)], False),
    CASES + "loose.ndjson": ([("composition", "invalid", 23, 1)], False),
}
PINNED = {"exporter": "lean4export", "exporterVersion": "3.1.0", "format": "3.1.0",
          "lean": "4.35.0", "leanGithash": "eb6cafb7290e8bd5f2937522d8d804f58f02bafc"}


def forth(gforth, words, source=None):
    """Run the driver with the given words; the completed process."""
    command = [gforth, DRIVER]
    if source:
        command += ["-e", f's" {source[0]}" {source[1]} ni-source']
    command += ["-e", words]
    return subprocess.run(command, cwd=ROOT, stdin=subprocess.DEVNULL, capture_output=True,
                          text=True, timeout=120)


def record(gforth, export, out, fuel=FUEL, source=None):
    done = forth(gforth, f's" {export}" {fuel} s" {out}" ni-record ni-exit', source)
    if done.returncode != 0 or done.stdout or done.stderr:
        raise AssertionError(f"ni-record {export}: {done.returncode} {done.stdout} {done.stderr}")
    return Path(out).read_bytes()


def replay(gforth, export, old, fuel=FUEL, source=None):
    """The replay report, valid against its schema, and the exit status."""
    done = forth(gforth, f's" {export}" {fuel} s" {old}" ni-replay ni-exit', source)
    if done.stderr:
        raise AssertionError(f"ni-replay {export}: {done.stderr}")
    report = load_strict(done.stdout)
    errors = REPORT_SCHEMA.errors(report)
    if errors:
        raise AssertionError(f"replay report invalid: {errors}")
    confirmed = report["result"] == "confirmed"
    if done.returncode != (0 if confirmed else 1):
        raise AssertionError(f"exit status {done.returncode} for {report['result']}")
    return report


def findings(report):
    return [(item["code"], item["path"]) for item in report["findings"]]


def without(data, *fields):
    """A copy of a record without the given (section, member) fields."""
    data = copy.deepcopy(data)
    for section, member in fields:
        data[section].pop(member)
    return data


def compact(data):
    return json.dumps(data, separators=(",", ":"), ensure_ascii=False) + "\n"


def golden_path(export):
    return GOLDEN / (Path(export).stem + ".json")


def definitions(count):
    """An export of count definitions: constant-fixture's fixtureId, then
    copies of it named d5, d6, ..."""
    lines = (ROOT / "tests/reference/constant-fixture.ndjson").read_text().splitlines()[:14]
    for index in range(5, 4 + count):
        lines.append('{"in":%d,"str":{"pre":0,"str":"d%d"}}' % (index, index))
        lines.append('{"def":{"all":[%d],"hints":{"regular":1},"levelParams":[2],"name":%d,'
                     '"safety":"safe","type":4,"value":6}}' % (index, index))
    return "\n".join(lines) + "\n"


def with_manifest(base, data):
    """data and the manifest text of export base's manifest made to fit it."""
    manifest = json.loads((ROOT / f"{base}.manifest.json").read_text())
    manifest.update(sha256=hashlib.sha256(data).hexdigest(), bytes=len(data),
                    lines=data.count(b"\n"))
    return data, json.dumps(manifest)


def unknown_use(spelling):
    """constant-fixture with fixtureUse's constant named by a name entry of
    its own, spelled spelling, and its manifest: with "fixtureIdd", a name
    no declaration has, fixtureUse is rejected; with "fixtureId", accepted."""
    base = "tests/reference/constant-fixture.ndjson"
    lines = []
    for line in (ROOT / base).read_text().splitlines():
        if line == '{"const":{"name":1,"us":[0]},"ie":14}':
            lines.append('{"in":9,"str":{"pre":0,"str":"%s"}}' % spelling)
            line = '{"const":{"name":9,"us":[0]},"ie":14}'
        lines.append(line)
    data, text = with_manifest(base, ("\n".join(lines) + "\n").encode())
    manifest = json.loads(text)
    manifest["records"]["name.str"] += 1
    return data, json.dumps(manifest)


def put(path, text):
    """Replace the file path with text in one step."""
    part = path.with_name(path.name + ".part")
    part.write_text(text)
    os.replace(part, path)


def family(pid):
    """Process pid and its descendants, as /proc lists them (a wrapper's
    Gforth runs as its child)."""
    found, waiting = [], [pid]
    while waiting:
        process = waiting.pop()
        found.append(process)
        try:
            for task in os.listdir(f"/proc/{process}/task"):
                with open(f"/proc/{process}/task/{task}/children") as children:
                    waiting.extend(int(child) for child in children.read().split())
        except OSError:                    # ended, or no children lists
            pass
    return found


def holds(pid, fifo):
    """Whether process pid has the file fifo open (false once it has ended)."""
    try:
        descriptors = os.listdir(f"/proc/{pid}/fd")
    except OSError:
        return False
    for descriptor in descriptors:
        try:
            if os.readlink(f"/proc/{pid}/fd/{descriptor}") == str(fifo):
                return True
        except OSError:                    # closed while we looked
            pass
    return False


def closed(pid, fifo):
    """Wait until process pid and its descendants have closed the file
    fifo: through /proc where there is one, else a pause long enough in
    practice."""
    if not os.path.isdir(f"/proc/{os.getpid()}/fd"):
        time.sleep(0.3)
        return
    while any(holds(process, fifo) for process in family(pid)):
        time.sleep(0.001)


def unread(pipe):
    """How many bytes written to the pipe no reader has read yet."""
    count = array.array("i", [0])
    fcntl.ioctl(pipe, termios.FIONREAD, count, True)
    return count[0]


def serve(fifo, manifest, plan, pid, opens, stop):
    """Serve the FIFO fifo to process pid once per open, in plan's order: an
    item's bytes; once the reader has read them all, its manifest text (if
    any) put at manifest; then the end of the file; then wait until the
    reader has closed its end. Opening again before that would hand the
    next item to the reader that has not yet seen the end of the file.
    opens lists the items read."""
    fifo = fifo.resolve()
    for data, text in plan:
        while True:
            if stop.is_set():
                return
            pipe = os.open(fifo, os.O_WRONLY)
            try:
                os.write(pipe, data)       # less than a pipe holds: whole
                while unread(pipe):
                    if stop.is_set():
                        return
                    time.sleep(0.001)
                if text is not None:
                    put(manifest, text)
                break
            except BrokenPipeError:        # a reader that left without reading
                continue
            finally:
                os.close(pipe)
        opens.append(data)
        closed(pid, fifo)


class Checks:
    def __init__(self, gforth, tmp):
        self.gforth, self.tmp, self.failures = gforth, Path(tmp), []

    def expect(self, condition, message):
        if not condition:
            self.failures.append(message)

    def out(self, export, tag=""):
        return str(self.tmp / (Path(export).stem + tag + ".json"))

    # One record: schema, facts, verdicts.
    def check_record(self, export, text):
        data = load_strict(text.decode("utf-8"))
        errors = RECORD_SCHEMA.errors(data)
        self.expect(not errors, f"{export}: schema: {errors}")
        content = (ROOT / export).read_bytes()
        facts = data["input"]
        self.expect(facts["sha256"] == hashlib.sha256(content).hexdigest(), f"{export}: sha256")
        self.expect(facts["bytes"] == len(content), f"{export}: bytes")
        lines = content.count(b"\n") + (0 if content.endswith(b"\n") else 1)
        self.expect(facts["lines"] == lines, f"{export}: lines")
        expected, manifest = INPUTS[export]
        outcome = facts["manifest"]["outcome"]
        self.expect((outcome == "ok") == manifest, f"{export}: manifest {outcome}")
        self.expect(data["export"] == PINNED, f"{export}: export {data['export']}")
        self.expect(facts["manifest"]["enforced"] is False,
                    f"{export}: the driver reads without the manifest, never enforced")
        self.expect(data["check"] == {"read": "ok", "run": "ok", "mode": "final",
                                      "allowlistVersion": 0}, f"{export}: check")
        self.expect(data["settings"]["fuel"] == FUEL, f"{export}: fuel")
        got = [(d["name"], d["verdict"], (d.get("diagnostic") or {}).get("code"),
                (d.get("diagnostic") or {}).get("step")) for d in data["declarations"]]
        self.expect(got == expected, f"{export}: declarations {got}")
        self.expect([d["index"] for d in data["declarations"]] == list(range(len(expected))),
                    f"{export}: indices")
        for item in data["declarations"]:
            if item["verdict"] == "accepted":
                self.expect(item["label"] == LABEL and item["axioms"] == [],
                            f"{export}: accepted without its label or with axioms")
        return data

    def records(self, update):
        for export in INPUTS:
            first = record(self.gforth, export, self.out(export))
            second = record(self.gforth, export, self.out(export, "-again"))
            self.expect(first == second, f"{export}: two runs differ")
            data = self.check_record(export, first)
            golden = golden_path(export)
            if update:
                golden.write_bytes(first)
                continue
            old = load_strict(golden.read_text(encoding="utf-8"))
            self.expect(without(data, HOST_VERSION, HOST_ENGINE)
                        == without(old, HOST_VERSION, HOST_ENGINE),
                        f"{export}: differs from {golden} beyond the host's version and engine")
            if data["host"] == old["host"]:
                self.expect(first == golden.read_bytes(), f"{export}: bytes differ from {golden}")
            report = replay(self.gforth, export, self.out(export))
            self.expect(findings(report) == [], f"{export}: own replay {findings(report)}")
            report = replay(self.gforth, export, golden)
            allowed = {("tool-differs", "$.host.version"), ("tool-differs", "$.host.engine")}
            self.expect(set(findings(report)) <= allowed,
                        f"{export}: golden replay {findings(report)}")

    # Tampered records: each refused with its code and path; with none
    # expected, a change of spelling only, confirmed.
    def tampered(self, name, export, base, change, expected, fuel=FUEL, source=None):
        text = change(Path(base).read_text(encoding="utf-8"))
        path = self.tmp / f"tampered-{name}.json"
        path.write_text(text, encoding="utf-8")
        report = replay(self.gforth, export, path, fuel, source)
        got = findings(report)
        result = "refused" if expected else "confirmed"
        self.expect(report["result"] == result and got[:len(expected)] == expected,
                    f"tamper {name}: {got}")

    def tamper(self):
        comp = "tests/reference/composition.ndjson"
        wrong = CASES + "wrong-argument.ndjson"
        comp_record, wrong_record = self.out(comp), self.out(wrong)

        def edit(function):
            def change(text):
                data = json.loads(text)
                function(data)
                return compact(data)
            return change

        def set_verdict(data):
            data["declarations"][0]["verdict"] = "unknown"

        def claim_accepted(data):
            item = data["declarations"][0]
            item.pop("diagnostic")
            item.update(verdict="accepted", label=LABEL, axioms=[])

        def flip_hash(data):
            digest = data["input"]["sha256"]
            data["input"]["sha256"] = digest[:-1] + ("0" if digest[-1] != "0" else "1")

        def other_reason(data):
            data["declarations"][0]["diagnostic"]["code"] = 60

        cases = [
            ("verdict", wrong, wrong_record, edit(set_verdict),
             [("verdict-differs", "$.declarations[0].verdict")]),
            ("hash", comp, comp_record, edit(flip_hash), [("input-differs", "$.input.sha256")]),
            ("missing-field", comp, comp_record,
             edit(lambda d: d["settings"].pop("fuel")),
             [("missing-field", "$.settings.fuel")]),
            ("duplicate-key", comp, comp_record,
             lambda t: t.replace('"bytes":', '"bytes":1,"bytes":', 1),
             [("duplicate-key", "$.input.bytes")]),
            ("claims-accepted", wrong, wrong_record, edit(claim_accepted),
             [("accepted-not-established", "$.declarations[0].verdict")]),
            ("unknown-field", comp, comp_record, edit(lambda d: d.update(extra=1)),
             [("unknown-field", "$.extra")]),
            ("host-version", comp, comp_record,
             edit(lambda d: d["host"].update(version="0.0.0")),
             [("tool-differs", "$.host.version")]),
            ("reason", wrong, wrong_record, edit(other_reason),
             [("reason-differs", "$.declarations[0].diagnostic.code")]),
            ("dropped-declaration", comp, comp_record,
             edit(lambda d: d["declarations"].clear()),
             [("declarations-differ", "$.declarations")]),
            ("manifest", wrong, wrong_record,
             edit(lambda d: d["input"]["manifest"].update(outcome="ok", reason="")),
             [("input-differs", "$.input.manifest.outcome")]),
            ("type", comp, comp_record,
             edit(lambda d: d["input"].update(bytes=str(d["input"]["bytes"]))),
             [("input-differs", "$.input.bytes")]),
            ("not-json", comp, comp_record, lambda t: t[:-10], [("not-json", "$")]),
            ("fraction", comp, comp_record,
             lambda t: t.replace('"fuel":100000', '"fuel":100000.0', 1),
             [("settings-differ", "$.settings.fuel")]),
            ("exponent", comp, comp_record,
             lambda t: t.replace('"fuel":100000', '"fuel":1e5', 1),
             [("settings-differ", "$.settings.fuel")]),
            ("escaped-verdict", comp, comp_record,
             lambda t: t.replace('"verdict":"accepted"', '"verdict":"\\u0061ccepted"', 1), []),
            ("schema-version", comp, comp_record,
             edit(lambda d: d.update(schemaVersion="0.2")), [("unknown-schema", "$")]),
        ]
        for name, export, base, change, expected in cases:
            self.tampered(name, export, base, change, expected)
        # A different setting or LeanForth commit at replay time.
        self.tampered("fuel", comp, comp_record, lambda t: t,
                      [("settings-differ", "$.settings.fuel")], fuel=FUEL + 1)
        self.tampered("commit", comp, comp_record, lambda t: t,
                      [("tool-differs", "$.leanforth.commit")],
                      source=("0123456789abcdef0123456789abcdef01234567", "false"))
        # Whitespace is not a difference: a pretty-printed record is confirmed.
        pretty = self.tmp / "pretty.json"
        pretty.write_text(json.dumps(json.loads(Path(comp_record).read_text()), indent=2))
        report = replay(self.gforth, comp, pretty)
        self.expect(report["result"] == "confirmed", f"pretty-printed: {findings(report)}")
        # A record that cannot be read, or an input that cannot be checked again.
        report = replay(self.gforth, comp, self.tmp / "no-such-record.json")
        self.expect(findings(report) == [("unreadable", "$")], f"unreadable: {findings(report)}")
        report = replay(self.gforth, "tests/core/no-such-export.ndjson", comp_record)
        self.expect(findings(report) == [("rerun-failed", "$")], f"rerun: {findings(report)}")

    # The schema refuses claims a checker could not make.
    def schema_refusals(self):
        comp = load_strict(Path(self.out("tests/reference/composition.ndjson")).read_text())
        wrong = load_strict(Path(self.out(CASES + "wrong-argument.ndjson")).read_text())

        def refused(name, data, change):
            data = copy.deepcopy(data)
            change(data)
            self.expect(RECORD_SCHEMA.errors(data), f"schema accepts {name}")

        refused("accepted without label", comp, lambda d: d["declarations"][0].pop("label"))
        refused("accepted with axioms", comp,
                lambda d: d["declarations"][0].update(axioms=["propext"]))
        refused("accepted with diagnostic", comp,
                lambda d: d["declarations"][0].update(diagnostic=None))
        refused("label on rejection", wrong, lambda d: d["declarations"][0].update(label=LABEL))
        refused("rejection without diagnostic", wrong,
                lambda d: d["declarations"][0].pop("diagnostic"))
        refused("declarations without a run", comp,
                lambda d: d["check"].update(read="invalid", run="not-run", mode=None,
                                            allowlistVersion=None))
        refused("run without a read", comp, lambda d: d["check"].update(read="invalid"))
        refused("short hash", comp, lambda d: d["input"].update(sha256="abc"))
        refused("other verdict", comp, lambda d: d["declarations"][0].update(verdict="ok"))
        refused("manifest failure without reason", wrong,
                lambda d: d["input"]["manifest"].update(reason=""))
        refused("modified without commit", comp, lambda d: d["leanforth"].update(modified=True))
        # Review F3: the receipts' text rule, the stated limits, the real
        # mode and allowlist version, and runs that cannot list a verdict.
        host = lambda **kw: lambda d: d["host"].update(**kw)  # noqa: E731
        name = lambda value: lambda d: d["declarations"][0].update(name=value)  # noqa: E731
        refused("engine with U+202E", comp, host(engine="gforth\u202e"))
        refused("version with a zero-width space", comp, host(version="1.0.0\u200b"))
        refused("forth with U+0085", comp, host(forth="gforth\u0085"))
        refused("forth empty", comp, host(forth=""))
        refused("forth blank", comp, host(forth="\u3000 "))
        refused("version over 128 bytes", comp, host(version="x" * 129))
        refused("name with U+2028", comp, name("composition\u2028"))
        refused("name with a line feed", comp, name("composition\n"))
        refused("name with a tag character", comp, name("composition\U000e0041"))
        refused("name blank", comp, name(" "))
        refused("name over 1024 bytes", comp, name("n" * 1025))
        refused("site with a tab", wrong,
                lambda d: d["declarations"][0]["diagnostic"].update(site="mixed-infer\t"))
        refused("reason blank", wrong,
                lambda d: d["declarations"][0]["diagnostic"].update(reason=" "))
        refused("run ok with not-checked", comp,
                lambda d: d["declarations"][0].update(verdict="not-checked"))
        refused("read ok, run not-run", comp,
                lambda d: d.update(check={"read": "ok", "run": "not-run", "mode": None,
                                          "allowlistVersion": None}, declarations=[]))
        refused("mode development", comp, lambda d: d["check"].update(mode="development"))
        refused("allowlist version 7", comp, lambda d: d["check"].update(allowlistVersion=7))
        refused("fuel 1e300", comp, lambda d: d["settings"].update(fuel=1e300))
        refused("fuel 1.5", comp, lambda d: d["settings"].update(fuel=1.5))
        refused("declarations without an environment", comp,
                lambda d: d["check"].update(run="invalid", mode=None, allowlistVersion=None))
        refused("run ok without its mode", comp,
                lambda d: d["check"].update(mode=None, allowlistVersion=None))
        # rvRP round 2: names that look blank, and an enforced manifest the
        # input does not match.
        for label, value in [("U+3164", "\u3164"), ("U+115F", "\u115f"), ("U+1160", "\u1160"),
                             ("U+2800", "\u2800"), ("U+FFA0", "\uffa0"),
                             ("combining marks", "\u0301\u0302"), ("U+034F", "\u034f"),
                             ("variation selectors", "\ufe0f\U000e0100"),
                             ("filler and space", "\u3164 \u2800")]:
            refused(f"name of {label} only", comp, name(value))
        refused("enforced manifest that does not match", wrong,
                lambda d: d["input"]["manifest"].update(enforced=True))
        refused("manifest without enforced", comp,
                lambda d: d["input"]["manifest"].pop("enforced"))
        # Names in any script stay valid.
        data = copy.deepcopy(comp)
        data["declarations"][0]["name"] = "\u03b1.\u03b2\u2081"
        self.expect(not RECORD_SCHEMA.errors(data), "schema refuses a non-ASCII name")

    # Review F2: a key of the old record cut in a path never splits a
    # character, and the report stays one JSON text.
    def long_key(self):
        comp = "tests/reference/composition.ndjson"
        key = "x" + "\u00e9" * 100
        path = self.tmp / "long-key.json"
        data = json.loads(Path(self.out(comp)).read_text())
        data[key] = 1
        path.write_text(compact(data), encoding="utf-8")
        got = findings(replay(self.gforth, comp, path))
        full = "$." + key
        cut = full.encode()[:128].decode("utf-8", "ignore")
        self.expect(got == [("unknown-field", cut)] and len(cut.encode()) == 127,
                    f"long multibyte key: {got}")

    # rvRP3 M1: an export swapped for another one (with its manifest)
    # between rr-start and the checked read, and swapped back before
    # rr-finish (A, then B, then A). The checked read loads B, which matches
    # B's manifest, but its digest is not the one rr-start recorded: the
    # read fails, so the record says enforced with a read that is invalid,
    # and lists no verdict of B.
    def swapped(self):
        folder = self.tmp / "swap"
        folder.mkdir()
        for name, source in (("x", "composition"), ("b", "constant-fixture")):
            for suffix in (".ndjson", ".ndjson.manifest.json"):
                shutil.copyfile(ROOT / f"tests/reference/{source}{suffix}",
                                folder / f"{name}{suffix}")
        words = {}
        for name in ("x", "a", "b"):
            for suffix, tag in ((".ndjson", ""), (".ndjson.manifest.json", "-m")):
                path = f"{folder}/{name}{suffix}"
                words[name + tag] = f": {name}{tag} ( -- c-addr u ) s\" {path}\" ;"

        def move(old, new):
            return [f"{old} {new} rename-file 0= must", f"{old}-m {new}-m rename-file 0= must"]
        lines = (["require ~+/tests/support/run-records.fs",
                  ': must ( flag -- ) 0= abort" swap: refused" ;'] + list(words.values())
                 + ["x rr-start . 100000 64 rr-settings!"] + move("x", "a") + move("b", "x")
                 + ["true rr-import . rr-moved? ."] + move("x", "b") + move("a", "x")
                 + ["rr-finish . rr-write . cr rr-text type cr", "bye"])
        source = folder / "swap.fs"
        source.write_text("\n".join(lines) + "\n")
        done = subprocess.run([self.gforth, str(source)], cwd=ROOT, stdin=subprocess.DEVNULL,
                              capture_output=True, text=True, timeout=120)
        head, _, text = done.stdout.partition("\n")
        self.expect(done.returncode == 0 and head.split() == ["0", "1", "-1", "0", "0"],
                    f"swap: {done.stdout[:200]} {done.stderr[:200]}")
        if done.returncode == 0 and text.strip():
            data = load_strict(text)
            self.expect(not RECORD_SCHEMA.errors(data), "swap: the record breaks the schema")
            self.expect(data["input"]["sha256"] == hashlib.sha256(
                (ROOT / "tests/reference/composition.ndjson").read_bytes()).hexdigest()
                and data["input"]["manifest"]["enforced"] is True
                and data["check"]["read"] == "invalid" and data["declarations"] == [],
                f"swap: {data['input']} {data['check']} {data['declarations']}")

    # rvRP3 R2-1: an export changed, with its manifest, during the
    # importer's first pass only. The first pass builds the names table,
    # the second the terms; each matched the manifest as it stood for that
    # pass, so before the fix the run paired one file's names with the
    # other file's terms, and an enforced record named bytes whose check
    # gives other verdicts; an unchecked read had no tie at all. Now the two
    # passes must read the same bytes, checked or not, else the read is
    # invalid (line 0). The export is a FIFO served once per open
    # (serve), so the order is exact: A, A (rr-start's digest and metadata),
    # A with B's manifest put beside it (rr-start's manifest check), B with
    # A's manifest put back (the first pass), A (the second pass), A
    # (rr-finish); a run read once (rr-read-once, a plain check) has only the
    # two passes. The runs use the words the command line uses (rr-start,
    # rr-import, rr-read-once) without its extra open of the export, which
    # only tests that it opens and would make the order a race. Each reader
    # runs under timeout(1), so none can outlive its deadline. Skipped where
    # FIFOs or timeout(1) are unavailable.
    def run_served(self, name, first, plan, words):
        """Run words (lines of Forth, with x the export) with the export the
        FIFO name/x.ndjson served by plan, its manifest first's text to begin
        with: (exit status, standard output, standard error, opens served);
        the status is None when the run took too long and was stopped."""
        folder = self.tmp / name
        folder.mkdir()
        fifo, manifest = folder / "x.ndjson", folder / "x.ndjson.manifest.json"
        os.mkfifo(fifo)
        put(manifest, first)
        source = folder / "run.fs"
        source.write_text("\n".join(["require ~+/tests/support/run-records.fs",
                                     f': x ( -- c-addr u ) s" {fifo}" ;', *words, "bye"]) + "\n")
        # The reader can never outlive its deadline, even if this test dies:
        # timeout(1) runs it in a process group of its own and stops that
        # whole group (the wrapper and Gforth) when the time is up.
        command = ["timeout", "-k", "2", str(FIFO_TIMEOUT), self.gforth, str(source)]
        process = subprocess.Popen(command, cwd=ROOT, stdin=subprocess.DEVNULL,
                                   stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        opens, stop = [], threading.Event()
        writer = threading.Thread(target=serve, daemon=True,
                                  args=(fifo, manifest, plan, process.pid, opens, stop))
        writer.start()
        status, out, err = None, "", ""
        try:
            out, err = process.communicate(timeout=FIFO_TIMEOUT + 10)
            status = process.returncode if process.returncode < 124 else None
        except subprocess.TimeoutExpired:
            pass
        finally:
            if process.poll() is None:         # this side gave up first: stop the group
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                process.wait()
            stop.set()
            for _ in range(10):                # a writer still waiting for a reader
                if not writer.is_alive():
                    break
                reader = os.open(fifo, os.O_RDONLY | os.O_NONBLOCK)
                writer.join(1)
                os.close(reader)
        return status, out, err, len(opens)

    def first_pass(self):
        if not shutil.which("timeout"):
            print("No timeout(1) here: reads served through a FIFO are not tested")
            return
        try:
            os.mkfifo(self.tmp / "probe.fifo")
        except (AttributeError, OSError) as error:
            print(f"No FIFOs here ({error}): a change during the first pass is not tested")
            return
        changed = "the export changed between the two passes"
        comp = "tests/reference/composition.ndjson"
        a = (ROOT / comp).read_bytes()
        names = (with_manifest(comp, a),
                 with_manifest(comp, a.replace(b'"str":"composition"', b'"str":"compositioX"')))
        use = (unknown_use("fixtureIdd"), unknown_use("fixtureId"))
        # The premise: at rest, use's A is rejected and its B accepted.
        for (data, text), code in zip(use, (1, 0)):
            path = self.tmp / f"use-{code}.ndjson"
            path.write_bytes(data)
            Path(f"{path}.manifest.json").write_text(text)
            status = subprocess.run([str(ROOT / "bin/leanforth"), "check", str(path)], cwd=ROOT,
                                    stdin=subprocess.DEVNULL, capture_output=True,
                                    env=dict(os.environ, GFORTH=self.gforth), timeout=120)
            self.expect(status.returncode == code, f"first pass: {path.name} exit {status}")
        # A recorded run, its manifest checked or not: the import's outcome
        # and rr-moved?, the importer's reason and line, rr-finish's and
        # rr-write's outcomes, the record. A run read once: its outcome, the
        # importer's reason and line.
        def recorded(flag):
            return [": imported ( -- ) x rr-start . 100000 64 rr-settings!",
                    f"  {flag} rr-import dup . rr-moved? . cr cin-error type space 2drop . cr",
                    "  ok? if rr-check then ;",
                    "imported rr-finish . rr-write . cr rr-text type cr"]

        def once(flag):
            return [f"x {flag} rr-read-once . cr cin-error type space 2drop . cr"]

        def facts(text, export):
            data = load_strict(text)
            return (not RECORD_SCHEMA.errors(data),
                    data["input"]["sha256"] == hashlib.sha256(export).hexdigest(),
                    data["input"]["manifest"]["enforced"], data["check"]["read"],
                    data["declarations"])
        # names: B spells composition otherwise; use: B accepts what A rejects.
        # Without the manifest check (--no-manifest, the test driver) the
        # passes are compared all the same; the record then says not enforced.
        refused = changed + " 0 "
        for name, ((a, ma), (b, mb)), flag in (("names", names, "true"), ("use", use, "true"),
                                               ("unchecked", use, "false")):
            plan = [(a, None), (a, None), (a, mb), (b, ma), (a, None), (a, None)]
            status, out, err, opens = self.run_served(name, ma, plan, recorded(flag))
            lines = out.split("\n", 3)
            self.expect(status == 0 and opens == 6 and lines[0].split() == ["0", "1", "0"]
                        and lines[1] == refused and lines[2].split() == ["0", "0"]
                        and facts(lines[3], a) == (True, True, flag == "true", "invalid", []),
                        f"first pass, {name}: {opens} opens, {out[:300]} {err[:300]}")
        # rr-start's own later reads (round 3): its metadata read, then its
        # manifest check (with B's manifest put beside B while the metadata
        # read is served), read B after rr-hash read A; rr-start fails.
        (a, ma), (b, mb) = use
        for name, plan in (("metadata", [(a, None), (b, None)]),
                           ("manifest", [(a, None), (a, mb), (b, ma)])):
            status, out, err, opens = self.run_served(name, ma, plan, ["x rr-start . rr-moved? ."])
            self.expect(status == 0 and opens == len(plan) and out.split() == ["1", "-1"],
                        f"start, {name}: {opens} opens, {out[:300]} {err[:300]}")
        # Read once: the first pass reads B (with B's manifest), the second A.
        for name, flag in (("once", "true"), ("once-unchecked", "false")):
            status, out, err, opens = self.run_served(name, mb, [(b, ma), (a, None)], once(flag))
            self.expect(status == 0 and opens == 2 and out.split("\n")[:2] == ["1 ", refused],
                        f"first pass, {name}: {opens} opens, {out[:300]} {err[:300]}")

    # rvRP3 R2-2: a record keeps at most 32 declarations (lf-input-default,
    # the schema's limit). An input of 32 gives a valid record of 32
    # verdicts; one of 33, with the input store made larger, no record (full).
    def many(self):
        for count, setup, expected in ((32, "", "0"), (33, "40 lf-input-capacity! drop ", "6")):
            export, out = self.tmp / f"many-{count}.ndjson", self.tmp / f"many-{count}.json"
            export.write_text(definitions(count))
            done = forth(self.gforth, f'{setup}s" {export}" {FUEL} s" {out}" ni-record . bye')
            self.expect(done.stdout.split() == [expected] and not done.stderr
                        and out.exists() == (count == 32), f"{count} declarations: {done}")
            if count == 32 and out.exists():
                data = load_strict(out.read_text())
                self.expect(not RECORD_SCHEMA.errors(data) and len(data["declarations"]) == 32
                            and all(d["verdict"] == "accepted" for d in data["declarations"]),
                            "32 declarations: the record is not 32 accepted ones")

    # The schemas' patterns mean the same in ECMA-262 (node, u flag) and in
    # the Python reading of schema_subset.py, on samples of every kind.
    SAMPLES = ["", "a", " ", "x" * 128, "x" * 129, "\u00e9" * 128, "\u00e9" * 129, "a\u200bb",
               "a\u2028b", "a\rb", "a\nb", "\x00", "\x85", "\u00ad", "\ufeff", "\u3164",
               "\u3000", "\u00a0x", "a\U000110bd", "a\U0001d173", "a\U000e0041",
               "a\U0001f600", "a\ud800", "\U000e0001", "0" * 64, "0" * 40, "mixed-infer",
               "$.declarations[0].verdict", "\u03b1", "\u115f", "\u2800", "\uffa0",
               "\u0301\u0302", "a\u0301", "\ufe0f", "\U000e0100", "\u1160x"]

    # The two tables of src/lib/text-rule.fs are exactly the ranges that
    # scripts/text_rule_tables.py computes from Python's Unicode data (15.0
    # and 15.1 give the same; any other version skips the check, except on
    # CI, where it fails), and the schema's text and shown patterns hold
    # exactly the same code points.
    @staticmethod
    def forth_table(name):
        source = Path("src/lib/text-rule.fs").read_text()
        table = source.split(f"create {name}", 1)[1].split(f"here {name}", 1)[0]
        values = [int(v, 16) for v in re.findall(r"\$([0-9a-f]+) ,", table)]
        return list(zip(values[::2], values[1::2]))

    def tables(self):
        if not text_rule_tables.supported():
            message = (f"Python's Unicode is {unicodedata.unidata_version}: the text rule's "
                       "tables are not rebuilt")
            self.expect(not os.environ.get("CI"), message)
            print(message)
            return
        for name, ranges in (("tr-banned", text_rule_tables.banned()),
                             ("tr-unseen", text_rule_tables.unseen())):
            self.expect(self.forth_table(name) == ranges,
                        f"{name} of src/lib/text-rule.fs is not scripts/text_rule_tables.py's")
        surrogates = set(range(0xd800, 0xe000))
        every = [cp for cp in range(0x110000) if cp not in surrogates]
        defs = RECORD_SCHEMA.root["$defs"]
        text = RECORD_SCHEMA._patterns[defs["text"]["pattern"]]
        shown = RECORD_SCHEMA._patterns[defs["shown"]["allOf"][1]["pattern"]]
        banned = {cp for cp in every if not text.search(chr(cp))}
        unseen = {cp for cp in every if not shown.search(chr(cp))}
        expected = text_rule_tables.points
        self.expect(banned == expected(text_rule_tables.banned()) - surrogates,
                    "the schema's text pattern is not the table's")
        self.expect(unseen == expected(text_rule_tables.unseen()) - surrogates,
                    "the schema's shown class is not the table's")

    def ecma(self):
        node = shutil.which("node")
        if not node:
            print("node is not installed: ECMA-262 patterns not compared")
            return
        patterns = sorted({p for schema in (RECORD_SCHEMA, REPORT_SCHEMA)
                           for p in schema._patterns})
        script = ("const {patterns, samples} = JSON.parse(require('fs').readFileSync(0, 'utf8'));"
                  "console.log(JSON.stringify(patterns.map(p => {"
                  " const re = new RegExp(p, 'u'); return samples.map(s => re.test(s)); })));")
        done = subprocess.run([node, "-e", script], capture_output=True, text=True, timeout=60,
                              input=json.dumps({"patterns": patterns, "samples": self.SAMPLES}))
        self.expect(done.returncode == 0, f"node: {done.stderr}")
        if done.returncode:
            return
        for pattern, results in zip(patterns, json.loads(done.stdout)):
            schema = RECORD_SCHEMA if pattern in RECORD_SCHEMA._patterns else REPORT_SCHEMA
            python = [bool(schema._patterns[pattern].search(s)) for s in self.SAMPLES]
            self.expect(python == results, f"ECMA and Python differ on {pattern[:40]}")

    # The writer's text rule (tr-rule?, tr-shown?) against the schema's
    # patterns, at both ends of every range they name and around them.
    def text_rule(self):
        defs = RECORD_SCHEMA.root["$defs"]
        raw = defs["text"]["pattern"], defs["shown"]["allOf"][1]["pattern"]
        text, shown = (RECORD_SCHEMA._patterns[p] for p in raw)
        # Every code point the patterns name, as an escape or as itself
        # (outside the Basic Multilingual Plane), and its neighbours.
        points = {0x41, 0x7e, 0x80, 0xff, 0x3164, 0x1f600, 0x10ffff}
        for pattern in raw:
            points |= {int(m.group(1), 16) for m in re.finditer(r"\\u([0-9a-f]{4})", pattern)}
            points |= {ord(char) for char in pattern}
        points = sorted({p + d for p in points for d in (-1, 0, 1) if 0 <= p + d <= 0x10ffff})
        lines = ["require ~+/tests/support/run-records.fs", "include ~+/tests/support/tester.fs",
                 "create one-char 4 allot",
                 ": rule? ( code -- f s ) one-char utf8-put one-char swap 2dup tr-rule? -rot"
                 " tr-shown? ;"]
        for point in points:
            char = chr(point)
            ok, seen = bool(text.search(char)), bool(text.search(char) and shown.search(char))
            lines.append(f"T{{ ${point:x} rule? -> {-int(ok)} {-int(seen)} }}T")
        lines.append("bye")
        source = self.tmp / "text-rule.fs"
        source.write_text("\n".join(lines) + "\n")
        done = subprocess.run([self.gforth, str(source)], cwd=ROOT, stdin=subprocess.DEVNULL,
                              capture_output=True, text=True, timeout=120)
        self.expect(done.returncode == 0 and not done.stdout.strip(),
                    f"text rule differs from the schema: {done.stdout[:300]} {done.stderr[:300]}")
        print(f"Text rule: {len(points)} code points agree between the writer and the schema.")

    # A second Gforth: the same records but for the host's version and engine.
    def other(self, other):
        allowed = {("tool-differs", "$.host.version"), ("tool-differs", "$.host.engine")}
        for export in INPUTS:
            mine = load_strict(Path(self.out(export)).read_text())
            theirs_path = self.out(export, "-other")
            theirs = load_strict(record(other, export, theirs_path).decode("utf-8"))
            self.expect(without(mine, HOST_VERSION, HOST_ENGINE)
                        == without(theirs, HOST_VERSION, HOST_ENGINE),
                        f"{export}: the two Gforths differ beyond the host's version and engine")
            for gforth, old in ((other, self.out(export)), (self.gforth, theirs_path)):
                got = findings(replay(gforth, export, old))
                self.expect(got and set(got) <= allowed, f"{export}: cross replay {got}")
            print(f"{export}: {mine['host']} / {theirs['host']}: equal otherwise")


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--update", action="store_true")
    parser.add_argument("--other-gforth")
    args = parser.parse_args()
    with tempfile.TemporaryDirectory() as tmp:
        checks = Checks(GFORTH, tmp)
        checks.records(args.update)
        if not args.update:
            checks.tamper()
            checks.schema_refusals()
            checks.long_key()
            checks.ecma()
            checks.text_rule()
            checks.tables()
            checks.swapped()
            checks.first_pass()
            checks.many()
        if args.other_gforth:
            checks.other(args.other_gforth)
    for failure in checks.failures:
        print(failure, file=sys.stderr)
    if checks.failures:
        print(f"{len(checks.failures)} run-record check(s) failed", file=sys.stderr)
        return 1
    print(f"Run records: {len(INPUTS)} inputs recorded, replayed and tampered with; "
          "every check passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
