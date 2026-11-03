"""Checks of the verification-condition generator v0 (task 2.5.5).

Usage (from the repository root):
  python3 tests/program/vc_check.py               # make test: Python only
  LEAN=... python3 tests/program/vc_check.py --lean   # make check
  python3 tests/program/vc_check.py --write       # regenerate the golden files

Without --lean: scripts/program_vc.py, run on the contracts below, must
write exactly the committed tests/program/vc/obligations.lean and
obligations.json (golden output); the file's copies of the IR semantics
must be verbatim; every contract must come out as its `expect` line says
(discharged, refuted or unsupported); and the generator must refute a
contract mutated to be wrong, refuse a loop, and refuse a malformed
contract.

With --lean it also has Lean 4.35.0 check the golden file (warnings are
errors, so `sorry` fails), requires every theorem the summary names to use
only Lean's propext, Classical.choice and Quot.sound, requires every
program Lean prints back to equal its IR file without source locations,
and plants two faults that Lean must reject: a postcondition changed
without its proofs, and a program changed (MAX for MIN) without its
contract. Checked by the Lean reference, not by LeanForth.
"""
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "scripts"))
from check_program_ir import copy_problems, LOCATION  # noqa: E402
import program_vc  # noqa: E402

CONTRACTS = [f"tests/program/contracts/{name}.contract" for name in (
    "lf-clamp", "lf-checked-add", "lf-checked-abs", "lf-in-range", "lf-gcd", "lf-factorial",
    "wrong-clamp-swapped", "wrong-checked-add-total", "wrong-in-range-exclusive")]
GOLDEN_LEAN = Path("tests/program/vc/obligations.lean")
GOLDEN_JSON = Path("tests/program/vc/obligations.json")
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def generated():
    text, summary = program_vc.generate(CONTRACTS)
    return text, json.dumps({"generator": program_vc.GENERATOR_VERSION, "contracts": summary},
                            indent=2, ensure_ascii=False) + "\n"


def expectations(summary):
    problems = []
    for entry, path in zip(summary["contracts"], CONTRACTS):
        expect = re.search(r"^expect (\S+)$", Path(path).read_text(encoding="utf-8"), re.M)
        if not expect or expect.group(1) != entry["status"]:
            problems.append(f"{path}: {entry['status']}, expected {expect and expect.group(1)}")
    return problems


def status_of(contract_text):
    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory) / "mutant.contract"
        path.write_text(contract_text, encoding="utf-8")
        try:
            _, summary = program_vc.generate([str(path)])
        except program_vc.Malformed:
            return "malformed"
    return summary[0]["status"]


def negative_problems():
    clamp = Path(CONTRACTS[0]).read_text(encoding="utf-8")
    problems = []
    cases = [
        ("min and max exchanged", clamp.replace("min(max(value, lower), upper)",
                                                "max(min(value, lower), upper)"), "refuted"),
        ("an off-by-one bound", clamp.replace("lower <= r && r <= upper",
                                              "lower < r && r <= upper"), "refuted"),
        ("a loop word", clamp.replace("word lf-clamp", "word lf-euclid")
         .replace("tests/program/ir/clamp.ir", "tests/program/ir/examples.ir")
         .replace("inputs value lower upper", "inputs value lower"), "unsupported"),
        ("an input named c", clamp.replace("inputs value lower upper", "inputs value c upper"),
         "malformed"),
    ]
    for name, text, expected in cases:
        got = status_of(text)
        if got != expected:
            problems.append(f"mutated contract ({name}): {got}, expected {expected}")
    return problems


def offline_problems():
    text, summary_text = generated()
    problems = []
    if text != GOLDEN_LEAN.read_text(encoding="utf-8"):
        problems.append(f"{GOLDEN_LEAN} differs from what the generator writes")
    if summary_text != GOLDEN_JSON.read_text(encoding="utf-8"):
        problems.append(f"{GOLDEN_JSON} differs from what the generator writes")
    copies, copied = copy_problems(GOLDEN_LEAN.read_text(encoding="utf-8"))
    problems += copies + ([] if copied == {program_vc.MODEL} else ["no verbatim copies"])
    problems += expectations(json.loads(summary_text))
    return problems + negative_problems()


def run_lean(lean, path):
    done = subprocess.run([lean, "-DwarningAsError=true", str(path)], capture_output=True,
                          text=True, timeout=600)
    return done.returncode, done.stdout + done.stderr


def printed_programs(output):
    programs, name, lines = {}, None, []
    for line in output.splitlines():
        if line.startswith("vc-program-end"):
            programs[name], name = lines, None
        elif line.startswith("vc-program "):
            name, lines = line.split()[1], []
        elif name is not None:
            lines.append(line)
    return programs


def lean_problems(lean):
    code, output = run_lean(lean, GOLDEN_LEAN)
    if code != 0:
        return [f"Lean rejected {GOLDEN_LEAN} ({code}):\n{output}"]
    problems, summary = [], json.loads(GOLDEN_JSON.read_text(encoding="utf-8"))
    programs = printed_programs(output)
    for entry in summary["contracts"]:
        for theorem in entry["theorems"]:
            match = re.search(rf"'{re.escape(theorem)}' depends on axioms: \[(.*)\]", output)
            used = {a.strip() for a in match.group(1).split(",")} if match else None
            if used is None or used - ALLOWED_AXIOMS:
                problems.append(f"{theorem}: axioms {used}")
        if entry["status"] == "unsupported":
            continue
        name = entry["namespace"].split(".")[-1]
        ir = [LOCATION.sub("", line) for line in
              Path(entry["ir"]).read_text(encoding="utf-8").splitlines()]
        if programs.get(name) != ir:
            problems.append(f"{name}: the program Lean prints differs from {entry['ir']}")
    return problems + planted_problems(lean)


PLANTS = [
    ("a postcondition changed without its proofs",
     "(r = (min (max value lower) upper))", "(r = (max (min value lower) upper))"),
    ("a program changed without its contract",
     '("lf-clamp", .word [.prim .twoDup, .prim .gt, .ifElse [.prim .twoDrop, .prim .drop, '
     '.prim .false, .exit] [], .prim .toR, .prim .max, .prim .fromR, .prim .min',
     '("lf-clamp", .word [.prim .twoDup, .prim .gt, .ifElse [.prim .twoDrop, .prim .drop, '
     '.prim .false, .exit] [], .prim .toR, .prim .min, .prim .fromR, .prim .max'),
]


def planted_problems(lean):
    problems, text = [], GOLDEN_LEAN.read_text(encoding="utf-8")
    with tempfile.TemporaryDirectory() as directory:
        for name, old, new in PLANTS:
            if old not in text:
                problems.append(f"planted fault ({name}) does not apply")
                continue
            path = Path(directory) / "planted.lean"
            path.write_text(text.replace(old, new, 1), encoding="utf-8")
            if run_lean(lean, path)[0] == 0:
                problems.append(f"Lean accepted a planted fault: {name}")
    return problems


def main():
    if "--write" in sys.argv:
        text, summary_text = generated()
        GOLDEN_LEAN.write_text(text, encoding="utf-8")
        GOLDEN_JSON.write_text(summary_text, encoding="utf-8")
        return 0
    problems = offline_problems()
    if "--lean" in sys.argv and not problems:
        problems = lean_problems(os.environ.get("LEAN", "lean"))
    for problem in problems:
        print(problem, file=sys.stderr)
    if problems:
        return 1
    summary = json.loads(GOLDEN_JSON.read_text(encoding="utf-8"))["contracts"]
    counts = {s: sum(e["status"] == s for e in summary)
              for s in ("discharged", "refuted", "unsupported")}
    obligations = sum(len(e["obligations"]) for e in summary)
    done = "checked by Lean" if "--lean" in sys.argv else "golden output and expectations agree"
    print(f"program VCs: {counts['discharged']} contracts discharged ({obligations} obligations), "
          f"{counts['refuted']} refuted, {counts['unsupported']} unsupported; {done}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
