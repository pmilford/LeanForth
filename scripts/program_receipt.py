#!/usr/bin/env python3
"""Program receipts v0 from the actual checks (task 2.5.6).

Usage (from the repository root):
  python3 scripts/program_receipt.py write   # receipt and printed form from recorded evidence
  python3 scripts/program_receipt.py validate RECEIPT.json...   # read strictly, check the rules
  python3 scripts/program_receipt.py verify RECEIPT.json   # validate, recompute and compare
  GFORTH=... LEAN=... python3 scripts/program_receipt.py record --out EVIDENCE.json
Options: --contract (default tests/program/contracts/lf-clamp.contract),
--evidence, --out, --markdown.

A receipt (schema 0.2, docs/programming/PROGRAM_RECEIPTS.md) states what is
known about one word, in three separate parts:
  CHECK  which theorems Lean checked (the contract theorem and the path
         obligations of scripts/program_vc.py), each with its axioms;
  VERIFY whether the obligations generated from the IR and the contract
         are discharged, and by which check;
  RUN    what the three-way runtime comparison of the IR interpreter, the
         host word and Lean's model showed (tests/program/ir-run-table.fs).
and every assumption they rest on.

`write` builds the receipt only from the repository (source, IR, contract,
the generated obligations and their summary, hashed as they are) and from
an evidence record, which `record` makes by running Lean and Gforth:
Lean's version and the axioms of each theorem, the runtime counts, and the
hash of the IR that the program words (src/program/verify.fs, ADR 0019)
write for the word's source, which must be the IR file's, byte for byte.
`validate` reads any receipt the way every reader here does: strict JSON
(tests/support/schema_subset.py: no duplicate keys, no fractions, no lone
surrogates, bounded nesting), schema 0.2 and the rules JSON Schema cannot
state (rule_problems). Only schema 0.2 is read: 0.1 was a draft the owner
never approved, and a receipt that names it is refused (it would otherwise
escape 0.2's rules). `verify` validates, then rebuilds the receipt the same
way and reports every field that differs, so a receipt edited by hand, or
one whose files changed since, is rejected. Each problem is one line
`FILE: CODE: PATH: MESSAGE` on standard error, CODE one of unreadable,
not-strict-json, superseded-version, unknown-version, schema, rule, replay;
the exit status is 0 when there is none, 1 when there is one and 2 for a
usage error. A receipt that verifies is
consistent with the repository and the evidence; it is not an approval of
anything, and it passes no review gate. Untrusted tooling.
"""
import argparse
import datetime
import functools
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

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
sys.path.insert(0, str(ROOT / "tests" / "support"))
import program_vc  # noqa: E402
from schema_subset import (MAX_SAFE_INTEGER, InstanceError, Validator,  # noqa: E402
                           load_strict)

VERSION = "0.2"
SCHEMA_VERSION = "0.2"
SCHEMA = ROOT / "schemas" / f"program-receipt-{SCHEMA_VERSION}.schema.json"
# Drafts the owner never approved. Their schema files stay unchanged as a
# record, but a receipt naming one is refused: 0.2 closed holes 0.1 has.
SUPERSEDED_VERSIONS = ("0.1",)
CONTRACT = "tests/program/contracts/lf-clamp.contract"
VC_LEAN = "tests/program/vc/obligations.lean"
VC_SUMMARY = "tests/program/vc/obligations.json"
TABLE = "tests/program/ir-run-table.fs"
CHECK_EVIDENCE = [VC_LEAN, "scripts/program_vc.py"]
RUN_EVIDENCE = [TABLE, "src/program/ir-run.fs", "tests/program/ir_run_differential.py",
                "tests/reference/program-ir-run.lean"]
IR_WORDS = "src/program/verify.fs"   # the program words that write the IR (ADR 0019)
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


def read_json(path, max_integer=MAX_SAFE_INTEGER):
    """A JSON file read strictly, or stop with the reason."""
    try:
        return load_strict(Path(path).read_text(encoding="utf-8"), max_integer)
    except (InstanceError, ValueError) as error:
        raise SystemExit(f"{path}: not strict JSON: {error}") from None


def vc_entry(contract_id):
    summary = read_json(VC_SUMMARY, max_integer=2 ** 64)   # it lists 64-bit test cells
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
         "text": f"The program words ({IR_WORDS}, the mode shift of ADR 0019) wrote the IR "
                 "faithfully: each Forth word the file uses means in the IR what the host's "
                 "word of that name does, and nothing else in the source file changes what "
                 "its words mean on the host. They run the file through Forth's own text "
                 "interpreter, one line at a time, with only their entry word visible; each "
                 "token must be a word of the file (a call, bound when Forth finds it), a "
                 "word of FORTH-WORDLIST with verification semantics and the identity it had "
                 "when they loaded, or a plain decimal, which they read themselves; no word "
                 "of the file or of the host runs. A standard word redefined after they "
                 "loaded and before the run is refused, except, on Gforth 0.7.3, a "
                 "compile-only word, since all of those share one token there; one "
                 "redefined before they loaded is not noticed, so the verifying Forth too "
                 "is assumed to have its own standard words. They refuse a redefinition, "
                 "under any spelling, of a Forth-2012 "
                 "Core or Core Ext word or of the file's own words, a name that reads as a "
                 "number, any byte outside printable ASCII other than a space, a tab, an LF "
                 "and a CR just before an LF, and a division before CONSTANT. Gforth is "
                 "assumed to load the file with its default settings (decimal BASE, standard "
                 "words), and the file to define no name that code compiled after it in the "
                 "same session uses, other than the words under test: definitions of host "
                 "words outside those word sets, such as Gforth's own, are accepted and would "
                 "change what such code, a test harness for example, means. Nothing proves "
                 "the translation; recording the evidence wrote this IR again with the "
                 "program words, and make test compares them with the IR named here and with "
                 "the earlier reader (src/program/ir-reader.fs)."},
        {"id": "A4", "kind": "trusted-runtime",
         "text": f"Gforth and its compiler execute {prims} as the IR semantics says. The "
                 f"runtime comparison tested this on {cases} cases; it does not prove it."},
        {"id": "A5", "kind": "stack-capacity",
         "text": "The data and return stacks have room for the word's items; stack overflow "
                 "is not modeled."},
        {"id": "A6", "kind": "trusted-lean",
         "text": "Lean 4.35.0, the pinned toolchain, checked the theorems correctly."},
        {"id": "A7", "kind": "untrusted-generator",
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


def allowlist_order(axioms):
    """Axioms in the allowlist's order; any other is listed too, and the schema rejects it."""
    return [a for a in ALLOWED_AXIOMS if a in axioms] + sorted(set(axioms) - set(ALLOWED_AXIOMS))


def build(contract_path, evidence):
    contract = program_vc.parse_contract(Path(contract_path).read_text(encoding="utf-8"),
                                         contract_path)
    vc = vc_entry(contract["id"])
    ir_text = Path(contract["ir"]).read_text(encoding="utf-8")
    word = contract["word"]
    source = program_vc.ir_source(ir_text)
    written = evidence.get("ir", {})
    wanted = {"words": IR_WORDS, "sha256": sha256(contract["ir"]), "source": sha256(source)}
    if written != wanted:
        raise SystemExit(f"the evidence does not show the program words ({IR_WORDS}) "
                         f"writing {contract['ir']} from {source} as they are: {written}")
    lean, run = evidence["lean"], evidence["run"]
    contract_theorem = f"{vc['namespace']}.contract"
    names = [contract_theorem] + [o["theorem"] for o in vc["obligations"]]
    if sorted(names) != sorted(vc["theorems"]):
        raise SystemExit(f"{contract['id']}: the theorems in {VC_SUMMARY} are not the contract "
                         "theorem and one per obligation")
    theorems = [{"name": n, "axioms": allowlist_order(lean["axioms"][n])} for n in names]
    axioms = allowlist_order({a for t in theorems for a in t["axioms"]})
    host = {"forth": run["forth"], "version": run["version"], "os": run["os"],
            "arch": run["arch"], "cellBits": run["cellBits"]}
    return {
        "schema": "leanforth-program-receipt",
        "schemaVersion": SCHEMA_VERSION,
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
            "theorems": theorems,
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
            "settledBy": "checked-by-lean-reference",
            "generator": {"name": "python", "version": f"program_vc.py {program_vc.GENERATOR_VERSION}"},
            "obligations": [{"id": o["id"], "statement": obligation_text(o),
                             "status": "discharged", "theorem": o["theorem"]}
                            for o in vc["obligations"]],
            "note": "One obligation per path through the word's IR (IF splits a path), "
                    "generated by an untrusted generator from the IR and the contract; each "
                    "is discharged by the Lean theorem named with it, checked by the Lean "
                    "reference, not by LeanForth.",
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
    lines = textwrap.wrap(body, WIDTH - indent, break_on_hyphens=False)
    return [f"{label:<{indent}}{lines[0]}"] + [" " * indent + line for line in lines[1:]]


def short(digest):
    return digest[:16] + "…"


def markdown(receipt):
    p, c, check, verify, run = (receipt[k] for k in ("program", "contract", "check", "verify",
                                                      "run"))
    out = [f"# Program receipt: `{p['word']}`", "",
           "Generated by `scripts/program_receipt.py` from "
           f"[the JSON receipt](lf-clamp.json) (schema {receipt['schemaVersion']}); do not edit. "
           "CHECK, VERIFY and RUN are separate answers: none of them alone, and not all "
           "three together, make the word verified on the host. This receipt passes no "
           "review gate.", "", "```text"]
    out.append(f"Program {p['word']} {p['stackEffect']}")
    out.append(f"  Source: {p['source']['path']} line {p['source']['line']}, "
               f"sha256 {short(p['source']['sha256'])}")
    out.append(f"  IR:     version {p['ir']['version']}, sha256 {short(p['ir']['sha256'])}")
    out += wrapped("Contract", f"{c['id']}: {c['statement']}")
    out.append("")
    proved = "; ".join(f"{t['name']} (axioms {', '.join(t['axioms']) or 'none'})"
                       for t in check["theorems"])
    out += wrapped("CHECK", f"{check['status']} — {check['label']}. Lean "
                   f"{check['checker']['version']} ({check['checker']['commit'][:8]}) proved "
                   f"{proved}. All axioms: {', '.join(check['axioms'])}.")
    out += wrapped("VERIFY", f"{verify['status']}, settled by {verify['settledBy']} — "
                   f"{len(verify['obligations'])} obligations generated from the IR and the "
                   "contract by an untrusted generator; each discharged by the Lean theorem "
                   "named below.")
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


def ir_written(gforth, ir_path):
    """The IR the program words write for the IR file's source, which must be
    that file byte for byte: its hash and the source's, for the evidence.
    The source is hashed before and after the run, and must not change in
    between, so the hash covers exactly the bytes the words read (the
    runner reads every byte of the file, with no limit)."""
    source = program_vc.ir_source(Path(ir_path).read_text(encoding="utf-8"))
    if not re.fullmatch(r"[\w./-]+", source):
        raise SystemExit(f"source path not usable in a Forth string: {source}")
    before = sha256(source)
    out = command([gforth, IR_WORDS, "-e", f's" {source}" lf-verify-file .', "-e", "bye"])
    *lines, outcome = out.rstrip("\n").split("\n")
    text = "\n".join(lines) + "\n"
    if outcome.strip() != "0" or text != Path(ir_path).read_text(encoding="utf-8"):
        raise SystemExit(f"the program words ({IR_WORDS}) do not write {ir_path} for "
                         f"{source}:\n{out}")
    if sha256(source) != before:
        raise SystemExit(f"{source} changed while the program words read it")
    return {"words": IR_WORDS, "sha256": hashlib.sha256(text.encode("utf-8")).hexdigest(),
            "source": before}


def record(contract_path):
    """Run Lean and Gforth now and return the evidence the receipt needs."""
    lean, gforth = os.environ.get("LEAN", "lean"), os.environ.get("GFORTH", "gforth")
    contract = program_vc.parse_contract(Path(contract_path).read_text(encoding="utf-8"),
                                         contract_path)
    vc = vc_entry(contract["id"])
    written = ir_written(gforth, contract["ir"])
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
        "ir": written,
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


# --------------------------------------------------------------------- reading

@functools.lru_cache(maxsize=None)
def validator():
    return Validator(read_json(SCHEMA))


def repeated(where, what, items):
    """A problem for each item that appears more than once."""
    seen, problems = set(), []
    for item in items:
        if item in seen:
            problems.append(f"{where}: {what} {json.dumps(item, ensure_ascii=False)} "
                            "appears more than once")
        seen.add(item)
    return problems


def rule_problems(receipt):
    """Schema 0.2's rules that JSON Schema cannot state, for a receipt the schema accepts.

    Ids, theorem names and axioms are distinct; check.axioms is the union of
    the theorems' axioms; a settled obligation's theorem, and for a
    discharged verify the contract's theorem, are among the checked
    theorems; failures are at most the cases; the checker and the generator
    are among the tools.
    """
    check, verify, run = receipt["check"], receipt["verify"], receipt["run"]
    theorems = check.get("theorems", [])
    names = [t["name"] for t in theorems]
    problems = (repeated("$.assumptions", "id", [a["id"] for a in receipt["assumptions"]])
                + repeated("$.verify.obligations", "id", [o["id"] for o in verify["obligations"]])
                + repeated("$.check.theorems", "theorem", names)
                + repeated("$.check.axioms", "axiom", check["axioms"]))
    for i, theorem in enumerate(theorems):
        problems += repeated(f"$.check.theorems[{i}].axioms", "axiom", theorem["axioms"])
    if set(check["axioms"]) != {a for t in theorems for a in t["axioms"]}:
        problems.append("$.check.axioms: not the union of the theorems' axioms")
    for i, obligation in enumerate(verify["obligations"]):
        if "theorem" in obligation and obligation["theorem"] not in names:
            problems.append(f"$.verify.obligations[{i}].theorem: not among check.theorems")
    if verify["status"] == "discharged" and receipt["contract"]["lean"] not in names:
        problems.append("$.contract.lean: the contract's theorem is not among check.theorems")
    if run["failures"] > run["cases"]:
        problems.append("$.run.failures: more failures than cases")
    for where, tool in (("$.check.checker", check.get("checker")),
                        ("$.verify.generator", verify.get("generator"))):
        if tool is not None and tool not in receipt["tools"]:
            problems.append(f"{where}: not among tools")
    return problems


def receipt_problems(receipt):
    """Problems of a parsed receipt: its schema version, schema and rules."""
    version = receipt.get("schemaVersion") if isinstance(receipt, dict) else None
    shown = json.dumps(version, ensure_ascii=False)
    if isinstance(version, str) and version in SUPERSEDED_VERSIONS:
        return [f"superseded-version: $.schemaVersion: {shown} was a draft that was never "
                f"approved; only {SCHEMA_VERSION} is read"]
    if version != SCHEMA_VERSION:
        return [f"unknown-version: $.schemaVersion: {shown} is not {SCHEMA_VERSION}"]
    problems = [f"schema: {p}" for p in validator().errors(receipt)]
    return problems or [f"rule: {p}" for p in rule_problems(receipt)]


def read_text(text):
    """(receipt or None, problems) for a receipt's text, read strictly."""
    try:
        receipt = load_strict(text)
    except InstanceError as error:
        return None, [f"not-strict-json: $: {error}"]
    return receipt, receipt_problems(receipt)


def read_file(path):
    """(receipt or None, problems) for a receipt file; unreadable if it cannot be read as UTF-8."""
    try:
        text = Path(path).read_text(encoding="utf-8")
    except (OSError, ValueError) as error:
        return None, [f"unreadable: $: {error}"]
    return read_text(text)


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
    return [f"replay: {d}" for d in differences(receipt, build(contract_path, evidence))]


def dump(receipt):
    return json.dumps(receipt, indent=2, ensure_ascii=False) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("action", choices=["write", "validate", "verify", "record"])
    parser.add_argument("receipts", nargs="*")
    parser.add_argument("--contract", default=CONTRACT)
    parser.add_argument("--evidence", default="tests/program/receipts/generated/lf-clamp-evidence.json")
    parser.add_argument("--out", default="tests/program/receipts/generated/lf-clamp.json")
    parser.add_argument("--markdown", default="tests/program/receipts/generated/lf-clamp.md")
    args = parser.parse_args()
    if args.action == "record":
        Path(args.out).write_text(dump(record(args.contract)), encoding="utf-8")
        return 0
    if args.action == "write":
        receipt = build(args.contract, read_json(args.evidence))
        Path(args.out).write_text(dump(receipt), encoding="utf-8")
        Path(args.markdown).write_text(markdown(receipt), encoding="utf-8")
        return 0
    if args.action == "verify" and len(args.receipts) != 1 or not args.receipts:
        parser.error("verify needs one receipt" if args.action == "verify" else
                     "validate needs receipts")
    status = 0
    for path in args.receipts:
        receipt, problems = read_file(path)
        if args.action == "verify" and not problems:
            problems = verify(receipt, args.contract, read_json(args.evidence))
        for problem in problems:
            print(f"{path}: {problem}", file=sys.stderr)
        status = status or int(bool(problems))
    return status


if __name__ == "__main__":
    sys.exit(main())
