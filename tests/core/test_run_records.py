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
a diagnostic, a label on a rejection, declarations without a run.

--other-gforth runs the same records with a second Gforth (Gforth 0.7.3,
CI's portability host): both write records equal in every field but those
two, and each replays the other's with findings only there.
"""
import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tests" / "support"))
from schema_subset import Validator, load_strict  # noqa: E402

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
        refused("engine with U+202E", comp, host(engine="gforth‮"))
        refused("version with a zero-width space", comp, host(version="1.0.0​"))
        refused("forth with U+0085", comp, host(forth="gforth\u0085"))
        refused("forth empty", comp, host(forth=""))
        refused("forth blank", comp, host(forth="　 "))
        refused("version over 128 bytes", comp, host(version="x" * 129))
        refused("name with U+2028", comp, name("composition "))
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
        # Names in any script stay valid.
        data = copy.deepcopy(comp)
        data["declarations"][0]["name"] = "α.β₁"
        self.expect(not RECORD_SCHEMA.errors(data), "schema refuses a non-ASCII name")

    # Review F2: a key of the old record cut in a path never splits a
    # character, and the report stays one JSON text.
    def long_key(self):
        comp = "tests/reference/composition.ndjson"
        key = "x" + "é" * 100
        path = self.tmp / "long-key.json"
        data = json.loads(Path(self.out(comp)).read_text())
        data[key] = 1
        path.write_text(compact(data), encoding="utf-8")
        got = findings(replay(self.gforth, comp, path))
        full = "$." + key
        cut = full.encode()[:128].decode("utf-8", "ignore")
        self.expect(got == [("unknown-field", cut)] and len(cut.encode()) == 127,
                    f"long multibyte key: {got}")

    # The schemas' patterns mean the same in ECMA-262 (node, u flag) and in
    # the Python reading of schema_subset.py, on samples of every kind.
    SAMPLES = ["", "a", " ", "x" * 128, "x" * 129, "é" * 128, "é" * 129, "a​b",
               "a b", "a\rb", "a\nb", "\x00", "\x85", "­", "﻿", "ㅤ",
               "　", " x", "a\U000110bd", "a\U0001d173", "a\U000e0041",
               "a\U0001f600", "a\ud800", "\U000e0001", "0" * 64, "0" * 40, "mixed-infer",
               "$.declarations[0].verdict", "α"]

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

    # The writer's text rule (rr-rule?, rr-shown?) against the schema's
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
                 ": rule? ( code -- f s ) one-char utf8-put one-char swap 2dup rr-rule? -rot"
                 " rr-shown? ;"]
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
