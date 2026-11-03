"""Checks of the generated clamp receipt (task 2.5.6).

Usage (from the repository root):
  python3 tests/program/receipt_check.py                        # make test
  GFORTH=... LEAN=... python3 tests/program/receipt_check.py --record   # make check

Without --record (Python only): scripts/program_receipt.py must write
exactly the committed receipt and its printed form from the committed
evidence (golden output); the receipt must validate against schema 0.1,
verify against the repository (every hash, obligation, theorem, count and
assumption recomputed), name only paths inside the repository, carry every
obligation's theorem and only allowed axioms; and each of a set of
tampered receipts must be rejected, by the schema or by verification.

With --record it also runs Lean and Gforth again (scripts/program_receipt.py
record) and requires the fresh evidence to equal the committed evidence in
everything but its date, so the receipt's CHECK and RUN parts are what the
tools report today.
"""
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))
sys.path.insert(0, str(ROOT / "tests" / "support"))
import program_receipt  # noqa: E402
from schema_subset import InstanceError, Validator, load_strict  # noqa: E402

SCHEMA = Path("schemas/program-receipt-0.1.schema.json")
GENERATED = Path("tests/program/receipts/generated")
RECEIPT, PRINTED, EVIDENCE = (GENERATED / "lf-clamp.json", GENERATED / "lf-clamp.md",
                              GENERATED / "lf-clamp-evidence.json")


def schema_errors(receipt):
    """Schema 0.1's errors for a receipt, after a strict round trip through JSON."""
    validator = Validator(load_strict(SCHEMA.read_text(encoding="utf-8")))
    try:
        instance = load_strict(json.dumps(receipt, ensure_ascii=False))
    except (InstanceError, ValueError) as error:
        return [f"not strict JSON: {error}"]
    return validator.errors(instance)


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


def rule_problems(receipt):
    """The rules the review of schema 0.1 asks for, whatever the schema enforces."""
    problems = []
    if not isinstance(receipt["program"]["ir"], dict):
        problems.append("program.ir is not an object")
    if not any(a["kind"] == "trusted-reader" for a in receipt["assumptions"]):
        problems.append("no trusted-reader assumption")
    if receipt["check"]["status"] != "checked-by-lean-reference":
        problems.append("check status is not checked-by-lean-reference")
    for obligation in receipt["verify"]["obligations"]:
        if obligation["status"] != "discharged" or not obligation.get("theorem"):
            problems.append(f"obligation {obligation['id']} not discharged by a named theorem")
    if set(receipt["check"]["axioms"]) - set(program_receipt.ALLOWED_AXIOMS):
        problems.append("an axiom outside the allowlist")
    return problems


def rejected(receipt, evidence):
    return schema_errors(receipt) + program_receipt.verify(receipt, program_receipt.CONTRACT,
                                                           evidence)


def tampered(receipt):
    """(what was changed, receipt) for each tampering that must be rejected."""
    def change(description, edit):
        mutant = copy.deepcopy(receipt)
        edit(mutant)
        return description, mutant
    return [
        change("source hash", lambda r: r["program"]["source"].update(sha256="0" * 64)),
        change("source line", lambda r: r["program"]["source"].update(line=13)),
        change("IR hash", lambda r: r["program"]["ir"].update(sha256="1" * 64)),
        change("contract statement", lambda r: r["contract"].update(statement="Always true.")),
        change("check claimed by LeanForth",
               lambda r: r["check"].update(status="accepted-by-leanforth")),
        change("check label", lambda r: r["check"].update(label="verified")),
        change("an extra axiom", lambda r: r["check"]["axioms"].append("sorryAx")),
        change("a theorem dropped", lambda r: r["check"]["theorems"].pop()),
        change("verify status", lambda r: r["verify"].update(status="open")),
        change("an obligation dropped", lambda r: r["verify"]["obligations"].pop()),
        change("an obligation's theorem",
               lambda r: r["verify"]["obligations"][0].update(theorem="ProgramVC.Other.O1")),
        change("more runtime cases", lambda r: r["run"].update(cases=r["run"]["cases"] + 1)),
        change("run status failed", lambda r: r["run"].update(status="failed")),
        change("the trusted-reader assumption dropped",
               lambda r: r.update(assumptions=[a for a in r["assumptions"]
                                               if a["kind"] != "trusted-reader"])),
        change("an assumption reworded",
               lambda r: r["assumptions"][3].update(text="Gforth is correct.")),
        change("a merged verdict", lambda r: r.update(verified=True)),
        change("an evidence file outside the repository",
               lambda r: r["run"]["evidence"][0].update(path="../outside.fs")),
    ]


def offline_problems():
    evidence = json.loads(EVIDENCE.read_text(encoding="utf-8"))
    built = program_receipt.build(program_receipt.CONTRACT, evidence)
    problems = []
    if program_receipt.dump(built) != RECEIPT.read_text(encoding="utf-8"):
        problems.append(f"{RECEIPT} differs from what the generator writes")
    if program_receipt.markdown(built) != PRINTED.read_text(encoding="utf-8"):
        problems.append(f"{PRINTED} differs from what the generator writes")
    receipt = json.loads(RECEIPT.read_text(encoding="utf-8"))
    problems += schema_errors(receipt) + path_problems(receipt) + rule_problems(receipt)
    problems += program_receipt.verify(receipt, program_receipt.CONTRACT, evidence)
    for description, mutant in tampered(receipt):
        if not rejected(mutant, evidence) and not path_problems(mutant):
            problems.append(f"a tampered receipt was accepted: {description}")
    other = copy.deepcopy(evidence)
    other["run"]["cases"] -= 1
    if not program_receipt.verify(receipt, program_receipt.CONTRACT, other):
        problems.append("the receipt verified against different evidence")
    return problems


def record_problems():
    with tempfile.TemporaryDirectory() as directory:
        fresh_path = Path(directory) / "evidence.json"
        done = subprocess.run([sys.executable, "scripts/program_receipt.py", "record", "--out",
                               str(fresh_path)], capture_output=True, text=True, timeout=600)
        if done.returncode != 0:
            return [f"recording evidence failed:\n{done.stdout}{done.stderr}"]
        fresh = json.loads(fresh_path.read_text(encoding="utf-8"))
    committed = json.loads(EVIDENCE.read_text(encoding="utf-8"))
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
    receipt = json.loads(RECEIPT.read_text(encoding="utf-8"))
    done = "fresh Lean and Gforth evidence agrees" if "--record" in sys.argv else \
        "golden output, schema 0.1, verification and tampering checks pass"
    print(f"clamp receipt: check {receipt['check']['status']}, verify "
          f"{receipt['verify']['status']} ({len(receipt['verify']['obligations'])} obligations), "
          f"run {receipt['run']['status']} ({receipt['run']['cases']} cases); "
          f"{len(tampered(receipt))} tampered receipts rejected; {done}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
