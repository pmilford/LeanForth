"""Checks of the generated clamp receipt (task 2.5.6).

Usage (from the repository root):
  python3 tests/program/receipt_check.py                        # make test
  GFORTH=... LEAN=... python3 tests/program/receipt_check.py --record   # make check

Without --record (Python only): scripts/program_receipt.py must write
exactly the committed receipt and its printed form from the committed
evidence (golden output); read strictly, the receipt must validate against
schema 0.2 and its rules, verify against the repository (every hash,
obligation, theorem, count and assumption recomputed), name only paths
inside the repository, and be checked by the Lean reference with every
obligation discharged by a named theorem. Each of a set of tampered
receipts must be refused by the layer named with it (schema, rule or
replay), and each of a set of tampered texts by the strict reader, also
through the command line of `program_receipt.py verify`.

With --record it also runs Lean and Gforth again (scripts/program_receipt.py
record) and requires the fresh evidence to equal the committed evidence in
everything but its date, so the receipt's CHECK and RUN parts are what the
tools report today.
"""
import copy
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))
import program_receipt  # noqa: E402

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
    """What this receipt must say: checked by Lean, every obligation discharged by a theorem."""
    problems = []
    if not isinstance(receipt["program"]["ir"], dict):
        problems.append("program.ir is not an object")
    if receipt["check"]["status"] != "checked-by-lean-reference":
        problems.append("check status is not checked-by-lean-reference")
    if receipt["verify"].get("settledBy") != "checked-by-lean-reference":
        problems.append("verify is not settled by the Lean reference")
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
        change("check claimed by LeanForth", "schema",
               lambda r: r["check"].update(status="accepted-by-leanforth")),
        change("check label", "schema", lambda r: r["check"].update(label="verified")),
        change("an extra axiom", "schema", lambda r: r["check"]["axioms"].append("sorryAx")),
        change("a theorem dropped", "rule", lambda r: r["check"]["theorems"].pop()),
        change("each theorem's axioms under-reported", "rule",
               lambda r: [t.update(axioms=["propext"]) for t in r["check"]["theorems"]]),
        change("one theorem's axioms under-reported", "replay",
               lambda r: r["check"]["theorems"][0].update(axioms=["propext"])),
        change("verify status", "schema", lambda r: r["verify"].update(status="open")),
        change("verify settled by LeanForth", "schema",
               lambda r: r["verify"].update(settledBy="accepted-by-leanforth")),
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
                          r.update(assumptions=assumptions[:6]))),
        change("a trusted-leanforth assumption added", "schema",
               lambda r: r["assumptions"].append(
                   {"id": "A8", "kind": "trusted-leanforth",
                    "text": "LeanForth's checker accepted the proofs."})),
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
         '"status": "checked-by-lean-reference",',
         '"status": "accepted-by-leanforth",\n    "status": "checked-by-lean-reference",'),
        ("a duplicate key in verify", '"settledBy": "checked-by-lean-reference",',
         '"settledBy": "accepted-by-leanforth", "settledBy": "checked-by-lean-reference",'),
        ("a fractional count", '"cases": 986', '"cases": 986.0'),
        ("failures that read as zero", '"failures": 0', '"failures": 1e-400'),
        ("a source line that reads as 12", '"line": 12', '"line": 12.0000000000000001'),
        ("a count beyond 2**53", '"cases": 986', '"cases": 9007199254740993'),
        ("a lone surrogate", '"note": "Lean proved', '"note": "\\ud800 Lean proved'),
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
    return problems


def record_problems():
    with tempfile.TemporaryDirectory() as directory:
        fresh_path = Path(directory) / "evidence.json"
        done = subprocess.run([sys.executable, "scripts/program_receipt.py", "record", "--out",
                               str(fresh_path)], capture_output=True, text=True, timeout=600)
        if done.returncode != 0:
            return [f"recording evidence failed:\n{done.stdout}{done.stderr}"]
        fresh = program_receipt.read_json(fresh_path)
    committed = program_receipt.read_json(EVIDENCE)
    fresh["recordedAt"] = committed["recordedAt"]
    return [f"fresh evidence differs: {d}" for d in program_receipt.differences(fresh, committed)]


def main():
    problems = offline_problems()
    if "--record" in sys.argv and not problems:
        problems = record_problems()
    for problem in problems:
        print(problem, file=sys.stderr)
    if problems:
        return 1
    receipt = program_receipt.read_json(RECEIPT)
    done = "fresh Lean and Gforth evidence agrees" if "--record" in sys.argv else \
        "golden output, strict reading, schema 0.2 and its rules, verification and " \
        "tampering checks pass"
    texts = len(tampered_texts(RECEIPT.read_text(encoding="utf-8")))
    print(f"clamp receipt: check {receipt['check']['status']}, verify "
          f"{receipt['verify']['status']} by {receipt['verify']['settledBy']} "
          f"({len(receipt['verify']['obligations'])} obligations), "
          f"run {receipt['run']['status']} ({receipt['run']['cases']} cases); "
          f"{len(tampered(receipt))} tampered receipts and {texts} tampered texts refused; {done}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
