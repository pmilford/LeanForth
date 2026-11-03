#!/usr/bin/env python3
"""Program receipts v0 from the actual checks (task 2.5.6).

Usage (from the repository root):
  python3 scripts/program_receipt.py write   # receipt and printed form from recorded evidence
  python3 scripts/program_receipt.py verify RECEIPT.json   # recompute and compare
  GFORTH=... LEAN=... python3 scripts/program_receipt.py record --out EVIDENCE.json
Options: --contract (default tests/program/contracts/lf-clamp.contract),
--evidence, --out, --markdown.

A receipt (schema 0.1, docs/programming/PROGRAM_RECEIPTS.md) states what is
known about one word, in three separate parts:
  CHECK  which theorems Lean checked (the contract theorem and the path
         obligations of scripts/program_vc.py), with their axioms;
  VERIFY whether the obligations generated from the IR and the contract
         are discharged;
  RUN    what the three-way runtime comparison of the IR interpreter, the
         host word and Lean's model showed (tests/program/ir-run-table.fs).
and every assumption they rest on.

`write` builds the receipt only from the repository (source, IR, contract,
the generated obligations and their summary, hashed as they are) and from
an evidence record, which `record` makes by running Lean and Gforth:
Lean's version and the axioms of each theorem, and the runtime counts.
`verify` rebuilds the receipt the same way and reports every field that
differs, so a receipt edited by hand, or one whose files changed since,
is rejected. A receipt that verifies is consistent with the repository and
the evidence; it is not an approval of anything, and it passes no review
gate. Untrusted tooling.
"""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import subprocess
import sys
import tempfile
import textwrap

sys.path.insert(0, str(Path(__file__).resolve().parent))
import program_vc  # noqa: E402

VERSION = "0.1"
CONTRACT = "tests/program/contracts/lf-clamp.contract"
VC_LEAN = "tests/program/vc/obligations.lean"
VC_SUMMARY = "tests/program/vc/obligations.json"
TABLE = "tests/program/ir-run-table.fs"
CHECK_EVIDENCE = [VC_LEAN, "scripts/program_vc.py"]
RUN_EVIDENCE = [TABLE, "src/program/ir-run.fs", "tests/program/ir_run_differential.py",
                "tests/reference/program-ir-run.lean"]
ALLOWED_AXIOMS = ["propext", "Classical.choice", "Quot.sound"]
CHECK_LABEL = "checked by the Lean reference, not by LeanForth"
RUN_LABEL = "runtime-tested; testing is not proof"


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def file_ref(path):
    return {"path": path, "sha256": sha256(path)}


def word_line(ir_text, word):
    """The source line of a word's colon, from the IR's location."""
    match = re.search(rf"^word {re.escape(word)} @(\d+):\d+$", ir_text, re.M)
    if not match:
        raise SystemExit(f"no located word {word} in the IR")
    return int(match.group(1))


def vc_entry(contract_id):
    summary = json.loads(Path(VC_SUMMARY).read_text(encoding="utf-8"))
    found = [c for c in summary["contracts"] if c["id"] == contract_id]
    if len(found) != 1 or found[0]["status"] != "discharged":
        raise SystemExit(f"{contract_id}: no discharged contract in {VC_SUMMARY}")
    return found[0]


def obligation_text(o):
    return f"If {o['path']}: {o['statement']}."


def assumptions(word, prims, cases):
    return [
        {"id": "A1", "kind": "host-cells",
         "text": "Every value is one signed host cell. The Lean theorems hold for every cell "
                 "width of at least two bits; the runtime comparison ran on 64-bit cells."},
        {"id": "A2", "kind": "twos-complement",
         "text": "Cells are two's complement, so the host's arithmetic wraps as the IR "
                 "semantics says (src/lib/portability.fs)."},
        {"id": "A3", "kind": "trusted-reader",
         "text": "The reader (src/program/ir-reader.fs) translated the colon definition into "
                 "the IR faithfully, and nothing else in the source file changes what its "
                 "words mean on the host. The reader splits the file into lines at LF itself "
                 "and finds names ignoring letter case as Gforth does; it refuses a "
                 "redefinition, under any spelling, of a word it knows (the IR's words, some "
                 "other standard words and the file's own), any byte outside printable ASCII "
                 "other than a space, a tab, an LF and a CR just before an LF, and a division "
                 "before CONSTANT; it never runs "
                 "the source. Gforth is assumed to load the file with its default settings "
                 "(decimal BASE, standard words), and the file to define no name that code "
                 "compiled after it in the same session uses, other than the words under "
                 "test: the reader accepts definitions of other host words, such as . or "
                 "DEPTH, which would change what such code, a test harness for example, "
                 "means. Nothing proves the translation; make test compares the reader's "
                 "output with the IR named here."},
        {"id": "A4", "kind": "trusted-runtime",
         "text": f"Gforth and its compiler execute {prims} as the IR semantics says. The "
                 f"runtime comparison tested this on {cases} cases; it does not prove it."},
        {"id": "A5", "kind": "stack-capacity",
         "text": "The data and return stacks have room for the word's items; stack overflow "
                 "is not modeled."},
        {"id": "A6", "kind": "trusted-lean",
         "text": "Lean 4.35.0, the pinned toolchain, checked the theorems correctly."},
        {"id": "A7", "kind": "other",
         "text": "The obligations come from an untrusted generator (scripts/program_vc.py). "
                 "This is safe only because the contract theorem Lean proved is stated "
                 "against the IR semantics copied verbatim from "
                 "tests/reference/program-ir.lean, and Lean prints the generated program "
                 f"back equal to the IR file; {word}'s proof is not checked by LeanForth."},
    ]


def prim_words(ir_text, word):
    """The Forth words of a word's body, in order of first use, upper case."""
    body = ir_text.split(f"word {word} ", 1)[1].split("\nend", 1)[0].splitlines()[1:]
    seen = []
    for line in body:
        words = program_vc.ir_tokens(line)
        name = words[1] if words[:1] == ["prim"] else words[0] if words else ""
        if name and name.upper() not in seen:
            seen.append(name.upper())
    return ", ".join(seen[:-1]) + " and " + seen[-1] if len(seen) > 1 else "".join(seen)


def build(contract_path, evidence):
    contract = program_vc.parse_contract(Path(contract_path).read_text(encoding="utf-8"),
                                         contract_path)
    vc = vc_entry(contract["id"])
    ir_text = Path(contract["ir"]).read_text(encoding="utf-8")
    word = contract["word"]
    source = program_vc.ir_source(ir_text)
    lean, run = evidence["lean"], evidence["run"]
    used = {a for t in vc["theorems"] for a in lean["axioms"][t]}
    # Any axiom outside the allowlist is listed too, and the schema rejects it.
    axioms = [a for a in ALLOWED_AXIOMS if a in used] + sorted(used - set(ALLOWED_AXIOMS))
    contract_theorem = f"{vc['namespace']}.contract"
    host = {"forth": run["forth"], "version": run["version"], "os": run["os"],
            "arch": run["arch"], "cellBits": run["cellBits"]}
    return {
        "schema": "leanforth-program-receipt",
        "schemaVersion": "0.1",
        "provenance": {
            "kind": "generated",
            "generator": {"name": "python", "version": f"program_receipt.py {VERSION}"},
            "createdAt": evidence["recordedAt"],
            "note": f"Written by scripts/program_receipt.py from the repository files named "
                    f"below, at the hashes given, and the evidence recorded on "
                    f"{evidence['recordedAt']} by make check. A receipt is a statement of "
                    "evidence, not an approval; it passes no review gate.",
        },
        "program": {
            "word": word,
            "stackEffect": contract["stack"],
            "source": {"path": source, "line": word_line(ir_text, word),
                       "sha256": sha256(source)},
            "ir": {"version": "0.1", "sha256": sha256(contract["ir"])},
            "floatingPoint": False,
        },
        "contract": {"id": contract["id"], "statement": contract["statement"],
                     "lean": contract_theorem, "file": file_ref(contract_path)},
        "check": {
            "status": "checked-by-lean-reference",
            "checker": {"name": "lean", "version": lean["version"], "commit": lean["commit"]},
            "theorems": [contract_theorem] + [o["theorem"] for o in vc["obligations"]],
            "label": CHECK_LABEL,
            "axioms": axioms,
            "evidence": [file_ref(p) for p in CHECK_EVIDENCE],
            "note": f"Lean proved {contract_theorem}, the contract stated against the IR "
                    "semantics for every cell width, input and stack below, from the path "
                    "obligations listed under verify. Checked by Lean 4.35.0, not by "
                    "LeanForth, whose checker cannot check programs yet.",
        },
        "verify": {
            "status": "discharged",
            "generator": {"name": "python", "version": f"program_vc.py {program_vc.GENERATOR_VERSION}"},
            "obligations": [{"id": o["id"], "statement": obligation_text(o),
                             "status": "discharged", "theorem": o["theorem"]}
                            for o in vc["obligations"]],
            "note": "One obligation per path through the word's IR (IF splits a path), "
                    "generated by an untrusted generator from the IR and the contract; each "
                    "is discharged by the Lean theorem named with it.",
        },
        "run": {
            "status": "passed" if run["failures"] == 0 else "failed",
            "host": host,
            "cases": run["cases"],
            "failures": run["failures"],
            "label": RUN_LABEL,
            "evidence": [file_ref(p) for p in RUN_EVIDENCE],
            "note": f"On {run['cases']} inputs (the existing clamp tables and seeded random "
                    f"cells) the host word and the IR interpreter left the same stack; Lean's "
                    f"evaluation of the model agreed on all {run['leanAgreed']} clamp cases, "
                    "including failures the host cannot run (too few inputs, no fuel).",
        },
        "assumptions": assumptions(word, prim_words(ir_text, word), run["cases"]),
        "tools": [{"name": "lean", "version": lean["version"], "commit": lean["commit"]},
                  {"name": run["forth"], "version": run["version"]},
                  {"name": "python", "version": f"program_vc.py {program_vc.GENERATOR_VERSION}"}],
    }


# ---------------------------------------------------------------- printed form

WIDTH = 90


def wrapped(label, body, indent=10):
    lines = textwrap.wrap(body, WIDTH - indent)
    return [f"{label:<{indent}}{lines[0]}"] + [" " * indent + line for line in lines[1:]]


def short(digest):
    return digest[:16] + "…"


def markdown(receipt):
    p, c, check, verify, run = (receipt[k] for k in ("program", "contract", "check", "verify",
                                                      "run"))
    out = [f"# Program receipt: `{p['word']}`", "",
           "Generated by `scripts/program_receipt.py` from "
           "[the JSON receipt](lf-clamp.json) (schema 0.1); do not edit. "
           "CHECK, VERIFY and RUN are separate answers: none of them alone, and not all "
           "three together, make the word verified on the host. This receipt passes no "
           "review gate.", "", "```text"]
    out.append(f"Program {p['word']} {p['stackEffect']}")
    out.append(f"  Source: {p['source']['path']} line {p['source']['line']}, "
               f"sha256 {short(p['source']['sha256'])}")
    out.append(f"  IR:     version {p['ir']['version']}, sha256 {short(p['ir']['sha256'])}")
    out += wrapped("Contract", f"{c['id']}: {c['statement']}")
    out.append("")
    out += wrapped("CHECK", f"{check['status']} — {check['label']}. Lean "
                   f"{check['checker']['version']} ({check['checker']['commit'][:8]}) proved "
                   f"{', '.join(check['theorems'])}. Axioms: {', '.join(check['axioms'])}.")
    out += wrapped("VERIFY", f"{verify['status']} — {len(verify['obligations'])} obligations "
                   "generated from the IR and the contract by an untrusted generator; each "
                   "discharged by the Lean theorem named below.")
    host = run["host"]
    out += wrapped("RUN", f"{run['status']} — {run['label']}. {host['forth']} "
                   f"{host['version']}, {host['os']} {host['arch']}, {host['cellBits']}-bit "
                   f"cells: {run['cases']} cases, {run['failures']} failures.")
    out.append("")
    out.append("Assumptions")
    for a in receipt["assumptions"]:
        out += wrapped(f"  {a['id']}", f"{a['kind']}: {a['text']}", indent=6)
    out.append("")
    out.append("Proof outline (from the verification conditions)")
    for o in verify["obligations"]:
        out += wrapped(f"  {o['id']}", f"{o['statement']} [{o['theorem']}]", indent=6)
    out += wrapped("  ∎", f"The paths cover every input, so {c['lean']} holds: the word "
                   "returns normally and the postcondition holds for every cell width, "
                   "input and stack below.", indent=6)
    out += ["```", ""]
    return "\n".join(out)


# ----------------------------------------------------------------- recording

def command(args, both=False):
    """A command's standard output (and error, when both), or stop on failure."""
    done = subprocess.run(args, capture_output=True, text=True, timeout=600,
                          stdin=subprocess.DEVNULL)
    if done.returncode != 0:
        raise SystemExit(f"{' '.join(args)} failed:\n{done.stdout}{done.stderr}")
    return done.stdout + done.stderr if both else done.stdout


def record(contract_path):
    """Run Lean and Gforth now and return the evidence the receipt needs."""
    lean, gforth = os.environ.get("LEAN", "lean"), os.environ.get("GFORTH", "gforth")
    contract = program_vc.parse_contract(Path(contract_path).read_text(encoding="utf-8"),
                                         contract_path)
    vc = vc_entry(contract["id"])
    version = re.match(r"Lean \(version ([0-9.]+),", command([lean, "--version"])).group(1)
    output = command([lean, "-DwarningAsError=true", VC_LEAN])
    axioms = {}
    for theorem in vc["theorems"]:
        match = re.search(rf"'{re.escape(theorem)}' depends on axioms: \[(.*)\]", output)
        if not match:
            raise SystemExit(f"no axiom report for {theorem}")
        axioms[theorem] = [a.strip() for a in match.group(1).split(",") if a.strip()]
    table = command([gforth, TABLE]).splitlines()
    clamp = [line for line in table if line.startswith("# clamp ")]
    counts = dict(zip(clamp[0].split()[2::2], map(int, clamp[0].split()[3::2])))
    lines = [line for line in table if line.startswith("clamp lf-clamp ")]
    agreed = lean_agreement(lean, lines)
    forth = (command([gforth, "--version"], both=True).split() + ["gforth", "unknown"])[:2]
    return {
        "recordedAt": datetime.date.today().isoformat(),
        "lean": {"version": version, "commit": command([lean, "--githash"]).strip(),
                 "axioms": axioms},
        "run": {"forth": forth[0], "version": forth[1], "os": platform.system().lower(),
                "arch": platform.machine().replace("_", "-"), "cellBits": 64,
                "cases": counts["host"], "failures": counts["mismatches"],
                "leanAgreed": agreed},
    }


def lean_agreement(lean, lines):
    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory) / "clamp.txt"
        path.write_text("\n".join(lines) + "\n", encoding="utf-8")
        model = command([lean, "-DwarningAsError=true", "--run",
                         "tests/reference/program-ir-run.lean", str(path)]).splitlines()
    if model != lines:
        raise SystemExit("Lean's model and the interpreter disagree on clamp cases")
    return len(lines)


# ------------------------------------------------------------------- verifying

def differences(left, right, where="$"):
    if isinstance(left, dict) and isinstance(right, dict):
        found = []
        for key in sorted(set(left) | set(right)):
            if key not in left or key not in right:
                found.append(f"{where}.{key}: {'missing' if key not in left else 'unexpected'}")
            else:
                found += differences(left[key], right[key], f"{where}.{key}")
        return found
    if isinstance(left, list) and isinstance(right, list):
        if len(left) != len(right):
            return [f"{where}: {len(left)} items, expected {len(right)}"]
        return [d for i, (a, b) in enumerate(zip(left, right))
                for d in differences(a, b, f"{where}[{i}]")]
    return [] if left == right and type(left) is type(right) else \
        [f"{where}: {json.dumps(left, ensure_ascii=False)[:60]}, expected "
         f"{json.dumps(right, ensure_ascii=False)[:60]}"]


def verify(receipt, contract_path, evidence):
    """Every field of the receipt that the repository and evidence do not imply."""
    return differences(receipt, build(contract_path, evidence))


def dump(receipt):
    return json.dumps(receipt, indent=2, ensure_ascii=False) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("action", choices=["write", "verify", "record"])
    parser.add_argument("receipt", nargs="?")
    parser.add_argument("--contract", default=CONTRACT)
    parser.add_argument("--evidence", default="tests/program/receipts/generated/lf-clamp-evidence.json")
    parser.add_argument("--out", default="tests/program/receipts/generated/lf-clamp.json")
    parser.add_argument("--markdown", default="tests/program/receipts/generated/lf-clamp.md")
    args = parser.parse_args()
    if args.action == "record":
        Path(args.out).write_text(dump(record(args.contract)), encoding="utf-8")
        return 0
    evidence = json.loads(Path(args.evidence).read_text(encoding="utf-8"))
    if args.action == "write":
        receipt = build(args.contract, evidence)
        Path(args.out).write_text(dump(receipt), encoding="utf-8")
        Path(args.markdown).write_text(markdown(receipt), encoding="utf-8")
        return 0
    receipt = json.loads(Path(args.receipt).read_text(encoding="utf-8"))
    problems = verify(receipt, args.contract, evidence)
    for problem in problems:
        print(problem, file=sys.stderr)
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
