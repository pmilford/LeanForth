"""Checks of the generated clamp receipt (tasks 2.5.6 and 5.5.1).

Usage (from the repository root):
  python3 tests/program/receipt_check.py                        # make test
  GFORTH=... LEAN=... python3 tests/program/receipt_check.py --record   # make check

Without --record (Python only): scripts/program_receipt.py must write
exactly the committed receipt and its printed form from the committed
evidence (golden output); read strictly, the receipt must validate against
schema 0.3 and its rules, verify against the repository (every hash,
obligation, theorem, count and assumption recomputed), name only paths
inside the repository, and be accepted by LeanForth's checker with every
obligation discharged by a named theorem. Each of a set of tampered
receipts must be refused by the layer named with it (schema, rule or
replay), and each of a set of tampered texts by the strict reader, also
through the command line of `program_receipt.py verify`. Evidence in which
LeanForth rejected a theorem, or did not finish, must give a receipt that
says so and discharges nothing; evidence about another export than the
pinned one, with an axiom outside the allowlist, or with LeanForth's axioms
other than Lean's, must give no receipt. A receipt for an earlier version
of a redefined word must say which later version the name means after
loading, and none may be written for an IR 0.2 program.

With --record it also runs Lean, its exporter, LeanForth and Gforth again
(scripts/program_receipt.py record) and requires the fresh evidence to
equal the committed evidence in everything but its date, and the fresh
export's manifest to equal the pinned one byte for byte, so the receipt's
CHECK and RUN parts are what the tools report today. Under make check the
recording is the target program-clamp-record's, run once before this
script in the same make run (PROGRAM_CLAMP_RECORDED names its folder).
"""
import copy
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))
import program_receipt  # noqa: E402
import os
TEST_LIMIT = int(os.environ.get("TEST_TIMEOUT", "1800"))  # seconds; make exports it

GENERATED = Path("tests/program/receipts/generated")
RECEIPT, PRINTED, EVIDENCE = (GENERATED / "lf-clamp.json", GENERATED / "lf-clamp.md",
                              GENERATED / "lf-clamp-evidence.json")


def paths(node):
    if isinstance(node, dict):
        for key, value in node.items():
            if key == "path" and isinstance(value, str):
                yield value
            else:
                yield from paths(value)
    elif isinstance(node, list):
        for item in node:
            yield from paths(item)


def path_problems(receipt):
    problems = []
    for path in paths(receipt):
        parts = Path(path).parts
        if Path(path).is_absolute() or ".." in parts or not (ROOT / path).is_file():
            problems.append(f"path outside the repository or missing: {path}")
    return problems


def clamp_problems(receipt):
    """What this receipt must say: accepted by LeanForth's checker, which re-checked the proofs
    Lean wrote, every obligation discharged by a theorem, and no label."""
    problems = []
    if not isinstance(receipt["program"]["ir"], dict):
        problems.append("program.ir is not an object")
    if receipt["check"]["status"] != "accepted-by-leanforth":
        problems.append("check status is not accepted-by-leanforth")
    if receipt["verify"].get("settledBy") != "accepted-by-leanforth":
        problems.append("verify is not settled by LeanForth's check")
    note = receipt["check"]["note"]
    if "wrote the proofs" not in note or "LeanForth's checker re-checked" not in note:
        problems.append("the check note does not say that Lean wrote the proofs and LeanForth "
                        "re-checked them")
    if "label" in receipt["check"]:
        problems.append("the check part has a label")
    for obligation in receipt["verify"]["obligations"]:
        if obligation["status"] != "discharged" or not obligation.get("theorem"):
            problems.append(f"obligation {obligation['id']} not discharged by a named theorem")
    return problems


def refusals(receipt, evidence):
    """Every problem of a receipt, from the reader (schema, rule) and from replay."""
    return program_receipt.receipt_problems(receipt) + program_receipt.verify(
        receipt, program_receipt.CONTRACT, evidence)


def tampered(receipt):
    """(what was changed, the layer that must refuse it, receipt) for each tampering."""
    def change(description, code, edit):
        mutant = copy.deepcopy(receipt)
        edit(mutant)
        return description, code, mutant
    assumptions = receipt["assumptions"]
    return [
        change("source hash", "replay", lambda r: r["program"]["source"].update(sha256="0" * 64)),
        change("source line", "replay", lambda r: r["program"]["source"].update(line=13)),
        change("IR hash", "replay", lambda r: r["program"]["ir"].update(sha256="1" * 64)),
        change("contract statement", "replay",
               lambda r: r["contract"].update(statement="Always true.")),
        change("check claimed by the Lean reference", "schema",
               lambda r: r["check"].update(status="checked-by-lean-reference")),
        change("check rejected but obligations discharged", "schema",
               lambda r: r["check"].update(status="rejected")),
        change("a check label", "schema", lambda r: r["check"].update(label="verified")),
        change("the withdrawn label put back", "schema", lambda r: r["check"].update(
            label="experimental — not independently audited")),
        change("the checker's version", "replay",
               lambda r: [t.update(version="0.0.9") for t in r["tools"] if t["name"] == "leanforth"]
               and r["check"]["checker"].update(version="0.0.9")),
        change("an extra axiom", "schema", lambda r: r["check"]["axioms"].append("sorryAx")),
        change("a theorem dropped", "rule", lambda r: r["check"]["theorems"].pop()),
        change("each theorem's axioms under-reported", "rule",
               lambda r: [t.update(axioms=["propext"]) for t in r["check"]["theorems"]]),
        change("one theorem's axioms under-reported", "replay",
               lambda r: r["check"]["theorems"][0].update(axioms=["propext"])),
        change("verify status", "schema", lambda r: r["verify"].update(status="open")),
        change("verify settled by the Lean reference", "schema",
               lambda r: r["verify"].update(settledBy="checked-by-lean-reference")),
        change("verify without settledBy", "schema", lambda r: r["verify"].pop("settledBy")),
        change("an obligation dropped", "replay", lambda r: r["verify"]["obligations"].pop()),
        change("an obligation's theorem", "rule",
               lambda r: r["verify"]["obligations"][0].update(theorem="ProgramVC.Other.O1")),
        change("more runtime cases", "replay",
               lambda r: r["run"].update(cases=r["run"]["cases"] + 1)),
        change("run status failed", "schema", lambda r: r["run"].update(status="failed")),
        change("run failed with the pass label", "schema",
               lambda r: r["run"].update(status="failed", failures=1)),
        change("the trusted-reader assumption dropped", "schema",
               lambda r: r.update(assumptions=[a for a in assumptions
                                               if a["kind"] != "trusted-reader"])),
        change("the stack-capacity assumption dropped", "schema",
               lambda r: r.update(assumptions=[a for a in assumptions
                                               if a["kind"] != "stack-capacity"])),
        change("the generator's assumption made 'other'", "schema",
               lambda r: r["assumptions"][6].update(kind="other")),
        change("the review's repro: contract theorem, file and A7 removed", "schema",
               lambda r: (r["contract"].pop("lean"), r["contract"].pop("file"),
                          r.update(assumptions=[a for a in assumptions if a["id"] != "A7"]))),
        change("the trusted-leanforth assumption dropped", "schema",
               lambda r: r.update(assumptions=[a for a in assumptions
                                               if a["kind"] != "trusted-leanforth"])),
        change("the trusted-lean assumption dropped", "replay",
               lambda r: r.update(assumptions=[a for a in assumptions
                                               if a["kind"] != "trusted-lean"])),
        change("the leanforth tool dropped", "schema",
               lambda r: r.update(tools=[t for t in r["tools"] if t["name"] != "leanforth"])),
        change("the export's manifest dropped from the evidence", "replay",
               lambda r: r["check"]["evidence"].pop()),
        change("a duplicate assumption id", "rule",
               lambda r: r["assumptions"][1].update(id="A1")),
        change("an assumption reworded", "replay",
               lambda r: r["assumptions"][3].update(text="Gforth is correct.")),
        change("a merged verdict", "schema", lambda r: r.update(verified=True)),
        change("an evidence file outside the repository", "schema",
               lambda r: r["run"]["evidence"][0].update(path="../outside.fs")),
    ]


def tampered_texts(text):
    """(what was changed, text) for each change the strict reader must refuse."""
    changes = [
        ("a duplicate check status (the review's dup-status.json)",
         '"status": "accepted-by-leanforth",',
         '"status": "checked-by-lean-reference",\n    "status": "accepted-by-leanforth",'),
        ("a duplicate key in verify", '"settledBy": "accepted-by-leanforth",',
         '"settledBy": "checked-by-lean-reference", "settledBy": "accepted-by-leanforth",'),
        ("a fractional count", '"cases": 986', '"cases": 986.0'),
        ("failures that read as zero", '"failures": 0', '"failures": 1e-400'),
        ("a source line that reads as 12", '"line": 12', '"line": 12.0000000000000001'),
        ("a count beyond 2**53", '"cases": 986', '"cases": 9007199254740993'),
        ("a lone surrogate", '"note": "Lean 4.35.0 wrote', '"note": "\\ud800 Lean 4.35.0 wrote'),
        ("NaN", '"cases": 986', '"cases": NaN'),
        ("deep nesting", '"floatingPoint": false',
         '"floatingPoint": ' + "[" * 100000 + "]" * 100000),
    ]
    out = []
    for description, old, new in changes:
        changed = text.replace(old, new, 1)
        if changed == text:
            raise SystemExit(f"tampered text not applied: {description}")
        out.append((description, changed))
    return out + [("a byte-order mark", "﻿" + text), ("text after the receipt", text + "{}")]


def command_refuses(text):
    """Whether `program_receipt.py verify` and `validate` exit 1 on a receipt text."""
    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory) / "receipt.json"
        path.write_text(text, encoding="utf-8")
        for action in ("verify", "validate"):
            done = subprocess.run([sys.executable, "-I", "scripts/program_receipt.py", action,
                                   str(path)], capture_output=True, text=True, timeout=120)
            if done.returncode != 1 or ": not-strict-json: " not in done.stderr:
                return False
    return True


def offline_problems():
    evidence = program_receipt.read_json(EVIDENCE)
    built = program_receipt.build(program_receipt.CONTRACT, evidence)
    problems = []
    if program_receipt.dump(built) != RECEIPT.read_text(encoding="utf-8"):
        problems.append(f"{RECEIPT} differs from what the generator writes")
    if program_receipt.markdown(built) != PRINTED.read_text(encoding="utf-8"):
        problems.append(f"{PRINTED} differs from what the generator writes")
    receipt, read = program_receipt.read_file(RECEIPT)
    if read:
        return problems + read
    problems += path_problems(receipt) + clamp_problems(receipt)
    problems += program_receipt.verify(receipt, program_receipt.CONTRACT, evidence)
    for description, code, mutant in tampered(receipt):
        found = refusals(mutant, evidence) + path_problems(mutant)
        if not any(p.startswith(f"{code}: ") for p in found):
            problems.append(f"a tampered receipt was not refused by {code}: {description}")
    for description, text in tampered_texts(RECEIPT.read_text(encoding="utf-8")):
        mutant, found = program_receipt.read_text(text)
        if mutant is not None or not found[0].startswith("not-strict-json: "):
            problems.append(f"a tampered text was read: {description}")
    first = tampered_texts(RECEIPT.read_text(encoding="utf-8"))[0][1]
    if not command_refuses(first):
        problems.append("program_receipt.py verify or validate accepted a duplicate key")
    for arguments in (["export"], ["export", "a.ndjson", "b.ndjson"], ["verify"], ["nothing"]):
        done = subprocess.run([sys.executable, "-I", "scripts/program_receipt.py", *arguments],
                              capture_output=True, text=True, timeout=120)
        if done.returncode != 2 or "usage" not in done.stderr:
            problems.append(f"program_receipt.py {' '.join(arguments)}: exit {done.returncode}, "
                            "not a usage error")
    other = copy.deepcopy(evidence)
    other["run"]["cases"] -= 1
    if not program_receipt.verify(receipt, program_receipt.CONTRACT, other):
        problems.append("the receipt verified against different evidence")
    for change in ({"sha256": "0" * 64}, {"words": "src/program/ir-reader.fs"},
                   {"source": "2" * 64}, None):
        other = copy.deepcopy(evidence)
        other["ir"] = None if change is None else {**other["ir"], **change}
        try:
            program_receipt.build(program_receipt.CONTRACT, other)
            problems.append(f"a receipt was built from evidence whose IR is {other['ir']}")
        except SystemExit:
            pass
    return problems + verdict_problems(evidence) + axiom_bit_problems()


# Check report 0.4's axiomBits and the axioms read from them: an axiom outside the
# allowlist (bit 8) is always named, by notProvedBy or, without it, by a placeholder.
AXIOM_BITS = [
    ({"axiomBits": 0}, []),
    ({"axiomBits": 5}, ["propext", "Quot.sound"]),
    ({"axiomBits": 7}, ["propext", "Classical.choice", "Quot.sound"]),
    ({"axiomBits": 9, "notProvedBy": ["sorryAx"]}, ["propext", "sorryAx"]),
    ({"axiomBits": 8}, ["an axiom outside the allowlist"]),
    ({}, []),
]


def axiom_bit_problems():
    return [f"axioms of {declaration}: {program_receipt.axiom_names(declaration)}, "
            f"expected {expected}" for declaration, expected in AXIOM_BITS
            if program_receipt.axiom_names(declaration) != expected]


CONTRACT_THEOREM = "ProgramVC.LfClamp0.contract"


def with_leanforth(evidence, edit):
    other = copy.deepcopy(evidence)
    edit(other)
    return other


# LeanForth's verdicts on the theorems, and the receipt they must give: (what changed in the
# evidence, the check status, or None for no receipt at all).
VERDICTS = [
    ("the contract theorem rejected", lambda e: e["leanforth"]["theorems"][CONTRACT_THEOREM]
     .update(verdict="rejected", axioms=[]), "rejected"),
    ("an obligation rejected, the contract theorem accepted",
     lambda e: e["leanforth"]["theorems"]["ProgramVC.LfClamp0.O2"]
     .update(verdict="rejected", axioms=[]), "rejected"),
    ("the contract theorem unknown", lambda e: e["leanforth"]["theorems"][CONTRACT_THEOREM]
     .update(verdict="unknown", axioms=[]), "unsupported"),
    ("the contract theorem exhausted", lambda e: e["leanforth"]["theorems"][CONTRACT_THEOREM]
     .update(verdict="exhausted", axioms=[]), "failed"),
    ("the contract theorem missing from the report",
     lambda e: e["leanforth"]["theorems"].pop(CONTRACT_THEOREM), "failed"),
    ("the contract theorem NOT PROVED (sorryAx, as Lean also reports it)",
     lambda e: (e["leanforth"]["theorems"][CONTRACT_THEOREM]["axioms"].append("sorryAx"),
                e["lean"]["axioms"][CONTRACT_THEOREM].append("sorryAx")), None),
    ("LeanForth's axioms other than Lean's",
     lambda e: e["leanforth"]["theorems"][CONTRACT_THEOREM].update(axioms=["propext"]), None),
    ("another export than the pinned one", lambda e: e["export"].update(sha256="3" * 64), None),
    ("an export of another size", lambda e: e["export"].update(bytes=1), None),
]


def verdict_problems(evidence):
    """A receipt never says more than LeanForth's verdicts: a rejected or unfinished check
    gives a receipt that says so and discharges nothing; the rest give none."""
    problems = []
    for description, edit, status in VERDICTS:
        other = with_leanforth(evidence, edit)
        try:
            receipt = program_receipt.build(program_receipt.CONTRACT, other)
        except SystemExit:
            if status is not None:
                problems.append(f"no receipt for evidence with {description}")
            continue
        if status is None:
            problems.append(f"a receipt was built from evidence with {description}")
            continue
        read = program_receipt.receipt_problems(receipt)
        if (read or receipt["check"]["status"] != status or receipt["verify"]["status"] != "open"
                or "settledBy" in receipt["verify"]
                or any("theorem" in o for o in receipt["verify"]["obligations"])
                or any(a["kind"] == "trusted-leanforth" for a in receipt["assumptions"])
                or receipt["check"]["axioms"]):
            problems.append(f"evidence with {description} gave check "
                            f"{receipt['check']['status']}, verify {receipt['verify']['status']}: "
                            f"{read}")
        if "Axioms of each theorem" not in program_receipt.markdown(receipt):
            problems.append(f"no printed form for evidence with {description}")
    return problems


# Versions (ADR 0019 Amendment 1, A1): the sentence a receipt for an
# earlier version gets, from a file that defines a name twice, and a name
# x'1 of its own that is no version; and the refusal of IR 0.2 programs.
VERSIONS_SOURCE = ": f 1 ;\n: g f ;\n: F f 1+ ;\n: x'1 2 ;\n3 constant k\n"
VERSIONS_IR = """lf-ir 0.1
source t.fs
word f @1:1
word g @2:1
word f'1 @3:1
word x'1 @4:1
constant k @5:12
"""


def version_problems():
    problems = []
    later = {w: program_receipt.later_version(VERSIONS_IR, VERSIONS_SOURCE, w)
             for w in ("f", "g", "f'1", "x'1", "k")}
    if later != {"f": ("f'1", 3), "g": None, "f'1": None, "x'1": None, "k": None}:
        problems.append(f"later versions: {later}")
    sentence = program_receipt.version_sentence("f", 1, later["f"])
    if "f'1, line 3" not in sentence or program_receipt.version_sentence("g", 2, None):
        problems.append(f"version sentence: {sentence!r}")
    for text in (VERSIONS_IR.replace("0.1", "0.2", 1), "lf-ir 0.3\n"):
        try:
            program_receipt.refuse_ir_02(text, "t.ir")
            problems.append(f"a receipt would be written for {text.splitlines()[0]}")
        except SystemExit:
            pass
    program_receipt.refuse_ir_02(VERSIONS_IR, "t.ir")
    return problems


# make check records the evidence once per run (target program-clamp-record:
# `program_receipt.py record --out DIR/evidence.json --manifest-out DIR/manifest.json
# --keep DIR`) and names DIR here; tests/program/clamp_mutants.py checks its mutants
# against the snapshot kept there, instead of checking the export a second time.
# Run alone, without PROGRAM_CLAMP_RECORDED, this script records for itself.
RECORDED = os.environ.get("PROGRAM_CLAMP_RECORDED")


def recording_problems(folder):
    """Record the evidence and the export's manifest into folder; a problem if that fails."""
    done = subprocess.run([sys.executable, "scripts/program_receipt.py", "record", "--out",
                           str(folder / "evidence.json"), "--manifest-out",
                           str(folder / "manifest.json")],
                          capture_output=True, text=True, timeout=TEST_LIMIT)
    return [] if done.returncode == 0 else [f"recording evidence failed:\n{done.stdout}{done.stderr}"]


def record_problems():
    with tempfile.TemporaryDirectory() as directory:
        folder = Path(RECORDED or directory)
        failed = [] if RECORDED else recording_problems(folder)
        if failed:
            return failed
        fresh = program_receipt.read_json(folder / "evidence.json")
        manifest = folder / "manifest.json"
        pinned = manifest.read_bytes() == Path(program_receipt.EXPORT_MANIFEST).read_bytes()
    committed = program_receipt.read_json(EVIDENCE)
    fresh["recordedAt"] = committed["recordedAt"]
    problems = [] if pinned else [f"the fresh export's manifest differs from "
                                  f"{program_receipt.EXPORT_MANIFEST}"]
    return problems + [f"fresh evidence differs: {d}"
                       for d in program_receipt.differences(fresh, committed)]


def main():
    problems = offline_problems() + version_problems()
    if "--record" in sys.argv and not problems:
        problems = record_problems()
    for problem in problems:
        print(problem, file=sys.stderr)
    if problems:
        return 1
    receipt = program_receipt.read_json(RECEIPT)
    done = ("fresh Lean, export, LeanForth and Gforth evidence agrees" if "--record" in sys.argv
            else "golden output, strict reading, schema 0.3 and its rules, verification, "
                 f"{len(VERDICTS)} verdict cases and tampering checks pass")
    texts = len(tampered_texts(RECEIPT.read_text(encoding="utf-8")))
    print(f"clamp receipt: check {receipt['check']['status']}, verify "
          f"{receipt['verify']['status']} by {receipt['verify']['settledBy']} "
          f"({len(receipt['verify']['obligations'])} obligations), "
          f"run {receipt['run']['status']} ({receipt['run']['cases']} cases); "
          f"{len(tampered(receipt))} tampered receipts and {texts} tampered texts refused; {done}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
