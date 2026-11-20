#!/usr/bin/env python3
"""Program receipts from the actual checks (tasks 2.5.6 and 5.5.1).

Usage (from the repository root):
  python3 scripts/program_receipt.py write   # receipt and printed form from recorded evidence
  python3 scripts/program_receipt.py validate RECEIPT.json...   # read strictly, check the rules
  python3 scripts/program_receipt.py verify RECEIPT.json   # validate, recompute and compare
  GFORTH=... LEAN=... python3 scripts/program_receipt.py record --out EVIDENCE.json
  LEAN=... python3 scripts/program_receipt.py export OUT.ndjson   # the export LeanForth checks
Options: --contract (default tests/program/contracts/lf-clamp.contract),
--evidence, --out, --markdown, --manifest-out (record: also save the
export's manifest there, to pin a new export), --keep FOLDER (record: keep
the export and the snapshot of LeanForth's check in FOLDER, for
tests/program/clamp_mutants.py; make check records once for both tests).

A receipt (schema 0.3, docs/programming/PROGRAM_RECEIPTS.md) states what is
known about one word, in three separate parts:
  CHECK  LeanForth's verdict on the contract theorem and the path
         obligations of scripts/program_vc.py: Lean wrote the proofs, its
         exporter wrote them with every declaration they use, and
         LeanForth's checker (bin/leanforth check) checked that export;
         each accepted theorem with its axioms;
  VERIFY whether the obligations generated from the IR and the contract
         are discharged, and by which check;
  RUN    what the three-way runtime comparison of the IR interpreter, the
         host word and Lean's model showed (tests/program/ir-run-table.fs).
and every assumption they rest on.

`write` builds the receipt only from the repository (source, IR, contract,
the generated obligations and their summary, the pinned export's manifest,
hashed as they are) and from an evidence record, which `record` makes by
running Lean, Lean's exporter, LeanForth and Gforth: Lean's version and its
own axiom report for each theorem, the export's hash, LeanForth's verdict
and axioms for each theorem, the runtime counts, and the hash of the IR that
the program words (src/program/verify.fs, ADR 0019) write for the word's
source, which must be the IR file's, byte for byte. `export` writes the
export alone, for a user to check with bin/leanforth check.
`validate` reads any receipt the way every reader here does: strict JSON
(tests/support/schema_subset.py: no duplicate keys, no fractions, no lone
surrogates, bounded nesting), its schema (0.3, or 0.2, which the owner
approved on 2026-11-03 and which stays readable) and the rules JSON Schema
cannot state (rule_problems). 0.1 was a draft the owner never approved, and
a receipt that names it is refused (it would otherwise escape 0.2's rules).
`verify` validates, then rebuilds the receipt the same way and reports
every field that differs, so a receipt edited by hand, or one whose files
changed since, is rejected; only 0.3 receipts are rebuilt. Each problem is
one line `FILE: CODE: PATH: MESSAGE` on standard error, CODE one of
unreadable, not-strict-json, superseded-version, unknown-version, schema,
rule, replay; the exit status is 0 when there is none, 1 when there is one
and 2 for a usage error. A receipt that verifies is
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
TEST_LIMIT = int(os.environ.get("TEST_TIMEOUT", "1800"))  # seconds; make exports it

VERSION = "0.3"
SCHEMA_VERSION = "0.3"   # what write produces
SCHEMA = ROOT / "schemas" / f"program-receipt-{SCHEMA_VERSION}.schema.json"
# The versions read, each against its own schema: 0.2, approved by the owner
# on 2026-11-03, stays readable; 0.3 is 0.2 without check.label (the owner
# withdrew the result label on 2026-11-12). Receipts for IR 0.2 programs
# (the SHA-256 words) will take version 0.4 at the owner's [format] gate.
READ_VERSIONS = ("0.2", "0.3")
# Drafts the owner never approved. Their schema files stay unchanged as a
# record, but a receipt naming one is refused: 0.2 closed holes 0.1 has.
SUPERSEDED_VERSIONS = ("0.1",)
CONTRACT = "tests/program/contracts/lf-clamp.contract"
VC_LEAN = "tests/program/vc/obligations.lean"
VC_SUMMARY = "tests/program/vc/obligations.json"
TABLE = "tests/program/ir-run-table.fs"
# The export of the contract theorem and its obligations with their closure,
# pinned by its manifest (scripts/export.sh writes both; the export itself,
# 23 MB, is made again by `export` or `record`, byte for byte).
EXPORT_MANIFEST = "tests/program/vc/lf-clamp.ndjson.manifest.json"
EXPORT_MODULE = "ProgramVC"
CHECK_EVIDENCE = [VC_LEAN, "scripts/program_vc.py", "scripts/export.sh", EXPORT_MANIFEST]
RUN_EVIDENCE = [TABLE, "src/program/ir-run.fs", "tests/program/ir_run_differential.py",
                "tests/reference/program-ir-run.lean"]
IR_WORDS = "src/program/verify.fs"   # the program words that write the IR (ADR 0019)
VERDICT_VERSION = "src/kernel/verdict-version.fs"
LEANFORTH_JOBS = "2"   # workers of LeanForth's check (owner's CPU rule, 2026-11-12)
ALLOWED_AXIOMS = ["propext", "Classical.choice", "Quot.sound"]
AXIOM_BITS = {1: "propext", 2: "Classical.choice", 4: "Quot.sound"}   # check report 0.4
RUN_LABEL = "runtime-tested; testing is not proof"
# LeanForth's verdicts on the theorems, and the check status they give: the
# first status whose verdicts occur wins; all accepted is the only positive one.
CHECK_FROM_VERDICTS = [("rejected", {"rejected"}), ("unsupported", {"unsupported", "unknown"})]


class Refusal(SystemExit):
    """No receipt can be written, and why: the problem code that
    scripts/program_verify.py reports (docs/design/VERIFY_COMMAND.md §4) and
    a message. Uncaught it stops this script with the message, as SystemExit."""

    def __init__(self, code, message):
        super().__init__(message)
        self.problem = code


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def file_ref(path):
    return {"path": path, "sha256": sha256(path)}


def word_line(ir_text, word):
    """The source line of a word's colon, from the IR's location."""
    match = re.search(rf"^word {re.escape(word)} @(\d+):\d+$", ir_text, re.M)
    if not match:
        raise Refusal("word-not-found", f"no located word {word} in the IR")
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


def refuse_ir_02(ir_text, path):
    """Schema 0.3 has program.ir.version "0.1" only: a receipt for an IR 0.2
    program (output words, LSHIFT or -ROT) needs schema 0.4, which the owner
    decides at the [format] gate (docs/programming/PROGRAM_RECEIPTS.md,
    "Schema 0.4"). Until then none is written."""
    if ir_text.split("\n", 1)[0] != "lf-ir 0.1":
        raise Refusal("ir-needs-receipt-0.4",
                      f"{path} is not IR 0.1: a receipt for an IR 0.2 program needs receipt "
                      "schema 0.4 (program.ir.version \"0.2\" and program.output), which "
                      "awaits the owner's [format] gate; no receipt written")


def source_name(source_lines, kind, line, column):
    """The name a definition's source gives it, folded to lower case: for a
    word the token after the colon at line:column, for a constant the token
    there."""
    text = source_lines[line - 1][column - 1:].split()
    return (text[1] if kind == "word" else text[0]).lower()


def later_version(ir_text, source_text, word):
    """When the file defines word's source name again after it (ADR 0019
    Amendment 1, A1), the IR name and source line of the last version, which
    the name means after loading; otherwise None."""
    found = re.findall(r"^(word|constant) (\S+) @(\d+):(\d+)$", ir_text, re.M)
    lines = source_text.splitlines()
    names = [(n, int(l), source_name(lines, k, int(l), int(c))) for k, n, l, c in found]
    mine = [d for d in names if d[0] == word]
    if len(mine) != 1:
        raise Refusal("word-not-found", f"no single located definition {word} in the IR")
    versions = [d for d in names if d[2] == mine[0][2]]
    return None if versions[-1][0] == word else versions[-1][:2]


def version_sentence(word, line, later):
    """The trusted-reader assumption's words on which version this is."""
    if later is None:
        return ""
    return (f" This receipt is about {word}, defined on line {line}; after loading, the name "
            f"means its later version {later[0]}, line {later[1]}, which this receipt does not "
            "cover, though words compiled before that line still call this one.")


NOT_RUN = "no runtime test ran here (RUN: not run; plan 8.4.2)"
# How the receipt's IR was written again, for the trusted-reader assumption.
READER_CHECKED = ("recording the evidence wrote this IR again with the program words, and make "
                  "test compares them with the IR named here and with the earlier reader "
                  "(src/program/ir-reader.fs).")


def assumptions(word, prims, cases, version="", *, lean_file=VC_LEAN,
                stated="the contract theorem is", checked=READER_CHECKED):
    """The assumptions A1-A7 of a receipt about word: prims are the Forth words it executes,
    cases the runtime comparison's count, or None when none ran (leanforth verify); version
    the trusted reader's sentence on a redefined name; Lean elaborated lean_file; `stated`
    names the theorem stated against the IR semantics; `checked` says how the IR was
    written again."""
    tested = (f"The runtime comparison tested this on {cases} cases; it does not prove it."
              if cases is not None else f"Not tested: {NOT_RUN}.")
    return [
        {"id": "A1", "kind": "host-cells",
         "text": "Every value is one signed host cell. The Lean theorems hold for every cell "
                 "width of at least two bits; " +
                 ("the runtime comparison ran on 64-bit cells." if cases is not None else
                  f"{NOT_RUN}.")},
        {"id": "A2", "kind": "twos-complement",
         "text": "Cells are two's complement, so the host's arithmetic wraps as the IR "
                 "semantics says (src/lib/portability.fs)."},
        {"id": "A3", "kind": "trusted-reader",
         "text": f"The program words ({IR_WORDS}, the mode shift of ADR 0019) wrote the IR "
                 "faithfully: each Forth word the file uses means in the IR what the host's "
                 "word of that name does, and nothing else in the source file changes what "
                 "its words mean on the host. They run the file through Forth's own text "
                 "interpreter, one line at a time, with only their entry word visible; each "
                 "token must be a word of the file (a call, bound when Forth finds it, to "
                 "the version visible there), a word of FORTH-WORDLIST with verification "
                 "semantics and the identity it had when they loaded, or a number in a "
                 "Forth-2012 form (decimal, # $ % prefixes or 'c'), which they read "
                 "themselves; no word of the file or of the host runs. A standard word "
                 "redefined after they loaded and before the run is refused, except, on "
                 "Gforth 0.7.3, a compile-only word, since all of those share one token "
                 "there; one redefined before they loaded is not noticed, so the verifying "
                 "Forth too is assumed to have its own standard words. A file may define its "
                 "own words again, as Forth allows; each version has its own IR name (x, "
                 "x'1, ...), and program.word names one. They refuse a redefinition, under "
                 "any spelling, of a word with verification semantics or of a Forth-2012 "
                 "Core or Core Ext word, a name the IR gives another version, a name that "
                 "reads as a number, any byte outside printable ASCII other than a space, a "
                 "tab, an LF and a CR just before an LF, and a division before CONSTANT. "
                 "Gforth is assumed to load the file with its default settings (decimal "
                 "BASE, standard words), and the file to define no name that code compiled "
                 "after it in the same session uses, other than the words under test: "
                 "definitions of host words outside those word sets, such as Gforth's own, "
                 "are accepted and would change what such code, a test harness for example, "
                 f"means. Nothing proves the translation; {checked}" + version},
        {"id": "A4", "kind": "trusted-runtime",
         "text": f"Gforth and its compiler execute {prims} as the IR semantics says. {tested}"},
        {"id": "A5", "kind": "stack-capacity",
         "text": "The data and return stacks have room for the word's items; stack overflow "
                 "is not modeled."},
        {"id": "A6", "kind": "trusted-lean",
         "text": f"Lean 4.35.0, the pinned toolchain, elaborated {lean_file} and its exporter "
                 "(lean4export 3.1.0, through scripts/export.sh) wrote the export faithfully: "
                 "the contract statement, the IR semantics and the program that LeanForth "
                 "checked mean what that Lean source says. Lean also wrote the proofs, from "
                 "the generator's tactic scripts, and checked them itself; that check is not "
                 "relied on here, since LeanForth's checker checked the export again."},
        {"id": "A7", "kind": "untrusted-generator",
         "text": "The obligations come from an untrusted generator (scripts/program_vc.py). "
                 f"This is safe only because {stated} stated against the IR "
                 "semantics copied verbatim from tests/reference/program-ir.lean, and Lean "
                 "prints the generated program back equal to the IR file."},
    ]


def leanforth_assumption(leanforth, what="contract theorem, its obligations"):
    """The trusted-leanforth assumption of a receipt LeanForth's checker accepted; what names
    the theorems checked."""
    return {"id": "A8", "kind": "trusted-leanforth",
            "text": f"LeanForth's checker (bin/leanforth check, {leanforth['version']}, verdict "
                    f"version {leanforth['verdictVersion']}) checked every declaration of the "
                    f"export correctly: it accepted all {leanforth['accepted']:,} of them, the "
                    f"{what} and every definition, inductive type "
                    "and lemma they use, directly or not, each with its axioms. It follows "
                    "Lean 4.35.0's kernel rules; it has no tactics and wrote no proof."}


def ir_body(ir_text, name):
    """The body lines of the definition name (a word or a constant) in the IR text."""
    found = re.search(rf"^(?:word|constant) {re.escape(name)} @[^\n]*\n(.*?)^end",
                      ir_text, re.M | re.S)
    return found.group(1).splitlines() if found else []


def prim_words(ir_text, word, seen=None, done=None):
    """The Forth words a word executes, in order of first use, upper case: those of its
    body and, where it calls a word or a constant of the file, those of the callee."""
    seen, done = ([] if seen is None else seen), ({word} if done is None else done)
    for line in ir_body(ir_text, word):
        words = program_vc.ir_tokens(line)
        if words[:1] == ["call"] and len(words) == 2:
            if words[1] not in done:
                done.add(words[1])
                prim_words(ir_text, words[1], seen, done)
            continue
        name = words[1] if words[:1] == ["prim"] else "" if words[:1] == ["lit"] else \
            words[0] if words else ""
        if name and name.upper() not in seen:
            seen.append(name.upper())
    return ", ".join(seen[:-1]) + " and " + seen[-1] if len(seen) > 1 else "".join(seen)


def allowlist_order(axioms):
    """Axioms in the allowlist's order; any other is listed too, and the schema rejects it."""
    return [a for a in ALLOWED_AXIOMS if a in axioms] + sorted(set(axioms) - set(ALLOWED_AXIOMS))


def export_verdicts(leanforth):
    """The verdicts LeanForth gave the export's declarations: those its counts record
    (leanforth verify's evidence), and "unaccounted" when it accepted fewer declarations
    than the export has and the counts do not name the others' verdicts (the clamp
    evidence has no counts): a check that did not accept everything never reads as
    accepted."""
    counts = leanforth.get("counts", {})
    found = {VERDICT_OF_COUNT.get(key, key) for key, n in counts.items()
             if n and key not in NOT_VERDICTS}
    named = sum(n for key, n in counts.items() if key not in NOT_VERDICTS)
    total = leanforth["declarations"]
    short = leanforth["accepted"] != total and named != total
    return found | ({"unaccounted"} if short else set())


# check report 0.4's counts: by verdict, as the verdicts the declarations carry, and the
# two that are not verdicts (the total, and NOT PROVED, a mark on accepted declarations)
VERDICT_OF_COUNT = {"notChecked": "not-checked"}
NOT_VERDICTS = ("declarations", "notProved")


def check_status(leanforth, names):
    """The check status LeanForth's verdicts give: accepted-by-leanforth only when it
    accepted every one of the theorems and every declaration of the export; a theorem
    accepted but NOT PROVED (an axiom outside the allowlist) has no status in schema 0.3,
    so no receipt is written."""
    verdicts = {verdict_of(leanforth, n) for n in names} | export_verdicts(leanforth)
    if verdicts == {"accepted"}:
        for name in names:
            if set(leanforth["theorems"][name]["axioms"]) - set(ALLOWED_AXIOMS):
                raise Refusal("not-proved",
                              f"{name}: accepted by LeanForth but NOT PROVED (an axiom outside "
                              "the allowlist); schema 0.3 has no status for it, no receipt "
                              "written")
        return "accepted-by-leanforth"
    return next((status for status, found in CHECK_FROM_VERDICTS if verdicts & found), "failed")


def verdict_of(leanforth, name):
    return leanforth["theorems"].get(name, {}).get("verdict", "missing")


def lean_agrees(lean, leanforth, names):
    """LeanForth's axioms for each accepted theorem must be Lean's own (#print axioms)."""
    for name in names:
        if sorted(leanforth["theorems"][name]["axioms"]) != sorted(lean["axioms"][name]):
            raise Refusal("axioms-differ",
                          f"{name}: LeanForth reports axioms {leanforth['theorems'][name]} and "
                          f"Lean {lean['axioms'][name]}; no receipt written")


def pinned_export(evidence):
    """The evidence must be about the export the manifest in the repository pins."""
    manifest = read_json(EXPORT_MANIFEST)
    if evidence["export"] != {"sha256": manifest["sha256"], "bytes": manifest["bytes"]}:
        raise SystemExit(f"the evidence is about another export than {EXPORT_MANIFEST} pins: "
                         f"{evidence['export']}")


def leanforth_version(leanforth):
    return f"{leanforth['version']}, verdict version {leanforth['verdictVersion']}"


def check_part(status, contract_theorem, theorems, evidence, files=CHECK_EVIDENCE,
               pinned=f"that {EXPORT_MANIFEST} pins", proofs=None):
    """The check part: LeanForth's verdict on Lean's export of the theorems. files are the
    evidence files, pinned says what pins the export, proofs what Lean proved (by default
    the contract theorem and its path obligations). A file is a path, hashed now, or a
    reference {path, sha256} already hashed."""
    lean, leanforth = evidence["lean"], evidence["leanforth"]
    verdicts = "; ".join(f"{t['name']} {verdict_of(leanforth, t['name'])}" for t in theorems)
    said = (f"accepted all {leanforth['accepted']:,} of them, these theorems among them"
            if status == "accepted-by-leanforth" else f"gave these verdicts: {verdicts}")
    proofs = proofs or f"the proofs of {contract_theorem} and its path obligations"
    return {
        "status": status,
        "checker": {"name": "leanforth", "version": leanforth_version(leanforth)},
        "theorems": theorems,
        "axioms": allowlist_order({a for t in theorems for a in t["axioms"]}),
        "evidence": [p if isinstance(p, dict) else file_ref(p) for p in files],
        "note": f"Lean {lean['version']} wrote {proofs}, from the tactic scripts of the "
                "untrusted generator, and its "
                "exporter wrote them with every declaration they use, "
                f"{leanforth['declarations']:,} in all, to the export with SHA-256 "
                f"{evidence['export']['sha256']} {pinned}. "
                f"LeanForth's checker re-checked that export and {said}: the status is "
                "LeanForth's verdict. LeanForth has no tactics yet and wrote no proof.",
    }


def verify_part(status, vc, unsettled="LeanForth's checker did not accept the theorems"):
    """The verify part from the check status: every obligation of the generator's summary
    vc discharged when LeanForth accepted the theorems, else every one open, because of
    what `unsettled` says."""
    settled = status == "accepted-by-leanforth"
    part = {"status": "discharged" if settled else "open"}
    if settled:
        part["settledBy"] = status
    part["generator"] = {"name": "python",
                         "version": f"program_vc.py {program_vc.GENERATOR_VERSION}"}
    part["obligations"] = [
        dict({"id": o["id"], "statement": obligation_text(o)},
             **({"status": "discharged", "theorem": o["theorem"]} if settled else
                {"status": "open"}))
        for o in vc["obligations"]]
    part["note"] = ("One obligation per path through the word's IR (IF splits a path), "
                    "generated by an untrusted generator from the IR and the contract; " +
                    ("each is discharged by the theorem named with it, which Lean proved and "
                     "LeanForth's checker accepted." if settled else
                     f"none is discharged, since {unsettled}."))
    return part


def build(contract_path, evidence):
    contract = program_vc.parse_contract(program_vc.read_contract(contract_path),
                                         contract_path)
    vc = vc_entry(contract["id"])
    ir_text = Path(contract["ir"]).read_text(encoding="utf-8")
    refuse_ir_02(ir_text, contract["ir"])
    word = contract["word"]
    source = program_vc.ir_source(ir_text)
    written = evidence.get("ir", {})
    wanted = {"words": IR_WORDS, "sha256": sha256(contract["ir"]), "source": sha256(source)}
    if written != wanted:
        raise SystemExit(f"the evidence does not show the program words ({IR_WORDS}) "
                         f"writing {contract['ir']} from {source} as they are: {written}")
    pinned_export(evidence)
    lean, leanforth, run = evidence["lean"], evidence["leanforth"], evidence["run"]
    contract_theorem = f"{vc['namespace']}.contract"
    names = [contract_theorem] + [o["theorem"] for o in vc["obligations"]]
    if sorted(names) != sorted(vc["theorems"]):
        raise SystemExit(f"{contract['id']}: the theorems in {VC_SUMMARY} are not the contract "
                         "theorem and one per obligation")
    status = check_status(leanforth, names)
    accepted = status == "accepted-by-leanforth"
    if accepted:
        lean_agrees(lean, leanforth, names)
    theorems = [{"name": n, "axioms": allowlist_order(leanforth["theorems"][n]["axioms"])
                 if accepted else []} for n in names]
    host = {"forth": run["forth"], "version": run["version"], "os": run["os"],
            "arch": run["arch"], "cellBits": run["cellBits"]}
    trusted = assumptions(word, prim_words(ir_text, word), run["cases"],
                          version_sentence(word, word_line(ir_text, word),
                                           later_version(ir_text, Path(source).read_text(
                                               encoding="utf-8"), word)))
    if accepted:
        trusted.append(leanforth_assumption(leanforth))
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
        "check": check_part(status, contract_theorem, theorems, evidence),
        "verify": verify_part(status, vc),
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
        "assumptions": trusted,
        "tools": [{"name": "lean", "version": lean["version"], "commit": lean["commit"]},
                  {"name": "leanforth", "version": leanforth_version(leanforth)},
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
    axioms = "; ".join(f"{t['name']} ({', '.join(t['axioms']) or 'none'})"
                       for t in check["theorems"])
    out += wrapped("CHECK", f"{check['status']}, by {check['checker']['name']} "
                   f"{check['checker']['version']}. {check['note']} Axioms of each theorem: "
                   f"{axioms}. All axioms: {', '.join(check['axioms']) or 'none'}.")
    settled = (f"settled by {verify['settledBy']}" if "settledBy" in verify
               else "nothing settled")
    out += wrapped("VERIFY", f"{verify['status']}, {settled} — {len(verify['obligations'])} "
                   "obligations generated from the IR and the contract by an untrusted "
                   "generator, each listed below with the theorem that discharges it.")
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
        out += wrapped(f"  {o['id']}", f"{o['statement']} [{o.get('theorem', o['status'])}]",
                       indent=6)
    if verify["status"] == "discharged":
        out += wrapped("  ∎", f"The paths cover every input, so {c['lean']} holds: the word "
                       "returns normally and the postcondition holds for every cell width, "
                       "input and stack below.", indent=6)
    out += ["```", ""]
    return "\n".join(out)


# ----------------------------------------------------------------- recording

def command(args, both=False, env=None):
    """A command's standard output (and error, when both), or stop on failure."""
    done = subprocess.run(args, capture_output=True, text=True, timeout=TEST_LIMIT,
                          stdin=subprocess.DEVNULL, env=None if env is None else
                          dict(os.environ, **env))
    if done.returncode != 0:
        raise SystemExit(f"{' '.join(args)} failed:\n{done.stdout}{done.stderr}")
    return done.stdout + done.stderr if both else done.stdout


def lean_compile_args(lean, source, folder, module=EXPORT_MODULE):
    """Pinned Lean compiling source (an obligations file) as module into folder; warnings
    are errors, so `sorry` fails."""
    return [lean, "-DwarningAsError=true", "-o", str(Path(folder) / f"{module}.olean"), source]


def export_args(out, theorems, module=EXPORT_MODULE):
    """scripts/export.sh writing the theorems of the compiled module with every declaration
    they use to out, and the manifest beside it (LEAN_PATH names the compiled module's
    folder, LEAN the pinned Lean)."""
    return ["bash", str(ROOT / "scripts" / "export.sh"), str(Path(out).resolve()), module, "--",
            *theorems]


def export_theorems(lean, theorems, out, source=VC_LEAN, module=EXPORT_MODULE):
    """Pinned Lean compiles source (the obligations file) as module in a scratch folder, and
    its exporter writes the theorems with every declaration they use to out, with the
    manifest beside it (scripts/export.sh). Returns Lean's compiler output, which holds its
    axiom reports."""
    with tempfile.TemporaryDirectory() as folder:
        output = command(lean_compile_args(lean, source, folder, module))
        command(export_args(out, theorems, module), env={"LEAN_PATH": folder, "LEAN": lean})
    return output


def lean_axioms(output, theorems):
    """Each theorem's axioms from Lean's `#print axioms` lines in its compiler output."""
    axioms = {}
    for theorem in theorems:
        match = re.search(rf"'{re.escape(theorem)}' depends on axioms: \[(.*)\]", output)
        if not match and f"'{theorem}' does not depend on any axioms" in output:
            axioms[theorem] = []
            continue
        if not match:
            raise SystemExit(f"no axiom report for {theorem}")
        axioms[theorem] = [a.strip() for a in match.group(1).split(",") if a.strip()]
    return axioms


def pinned_lean():
    """$LEAN, else the project's pinned Lean 4.35.0 (lean_pin.DEFAULT), unchecked: the program
    verifier refuses another Lean itself, with its own messages (tests/program/test_program_verify.py)."""
    import lean_pin
    return os.environ.get("LEAN", lean_pin.DEFAULT)


def checked_lean():
    """pinned_lean(), refused before it is run when lean_pin finds it an elan proxy or no
    toolchain's binary (nothing is run to find out): record and export run Lean themselves,
    with no verifier before them (Forth review of reuse-b, 4). The refusal is the
    verifier's lean-not-found."""
    import lean_pin
    lean = pinned_lean()
    reason = lean_pin.unrun(lean)
    if reason:
        raise SystemExit(f"lean-not-found: {reason}; install the pinned Lean 4.35.0 with "
                         "scripts/install-lean.sh")
    return lean


# The checker, as the CLI starts it for an export: bin/leanforth-checker prints what
# bin/leanforth prints for one, on the checker's load alone (tests/cli/test_checker_launcher.py).
LEANFORTH = ["bash", str(ROOT / "bin" / "leanforth-checker")]


def leanforth_args(export, options=("--jobs", LEANFORTH_JOBS)):
    """LeanForth's final check of the export with its JSON report (no snapshot is read)."""
    return [*LEANFORTH, "check", "--json", *options, str(export)]


def leanforth_identity():
    """LeanForth's version (bin/leanforth version) and verdict version."""
    version = command([*LEANFORTH, "version"]).split("\n")[0]
    return {"version": version.split()[-1],
            "verdictVersion": int(re.search(r"(\d+) constant lf-verdict-version",
                                            (ROOT / VERDICT_VERSION).read_text()).group(1))}


def leanforth_theorems(report, theorems):
    """The verdict and axioms LeanForth's check report gives each theorem ("missing" for one
    it does not list)."""
    found = {d["name"]: d for d in report["declarations"] if d["name"] in theorems}
    return {name: {"verdict": found[name]["verdict"] if name in found else "missing",
                   "axioms": axiom_names(found.get(name, {}))} for name in theorems}


def leanforth_check(export, theorems, snapshot=None):
    """LeanForth's check of the export (bin/leanforth check --json): its version, the counts,
    the exit status and the verdict and axioms of each theorem. With snapshot, a file name,
    the check also writes the checked environment there (--save-snapshot; the verdicts are
    the same), for a later check of the export with changed copies added (clamp_mutants.py)."""
    saving = ["--save-snapshot", str(snapshot)] if snapshot else []
    done = subprocess.run(leanforth_args(export, ["--jobs", LEANFORTH_JOBS, *saving]),
                          capture_output=True, text=True,
                          timeout=TEST_LIMIT, stdin=subprocess.DEVNULL)
    try:
        report = load_strict(done.stdout)
    except InstanceError as error:
        raise SystemExit(f"leanforth check gave no JSON report ({done.returncode}): {error}\n"
                         f"{done.stderr[-2000:]}") from None
    return {**leanforth_identity(),
            "exitStatus": done.returncode, "declarations": report["counts"]["declarations"],
            "accepted": report["counts"]["accepted"],
            "theorems": leanforth_theorems(report, theorems)}


def axiom_names(declaration):
    """An accepted declaration's axioms from its axiomBits (check report 0.4); bit 8, an axiom
    outside the allowlist, is named by its notProvedBy list."""
    bits = declaration.get("axiomBits", 0)
    others = list(declaration.get("notProvedBy", [])) or (
        ["an axiom outside the allowlist"] if bits & 8 else [])
    return [name for bit, name in AXIOM_BITS.items() if bits & bit] + others


FORTH_PATH = r"[\w./-]+"   # a source path the program words' Forth string can hold


def program_words_args(gforth, source):
    """Gforth running the program words (ADR 0019's correctness mode) on the source file at
    the path source (relative to the checkout; FORTH_PATH): they print its IR, then their
    outcome (ADR 0008's number), a refusal's diagnostic line before it."""
    return [gforth, IR_WORDS, "-e", f's" {source}" lf-verify-file .', "-e", "bye"]


def program_words_output(out):
    """(outcome, IR text, diagnostic) from the program words' output: the outcome a number
    (None when the last line is not one), the IR text up to the diagnostic line, which a
    refusal prints before the outcome (`unsupported @13:7: ...`; None when ok)."""
    *lines, last = out.rstrip("\n").split("\n")
    outcome = int(last.strip()) if re.fullmatch(r"\s*[0-9]+\s*", last) else None
    diagnostic = lines.pop() if outcome not in (0, None) and lines else None
    return outcome, "\n".join(lines) + "\n", diagnostic


def ir_written(gforth, ir_path):
    """The IR the program words write for the IR file's source, which must be
    that file byte for byte: its hash and the source's, for the evidence.
    The source is hashed before and after the run and the two hashes must
    agree, so a change still present after the run is refused. A change made
    during the run and undone before the second hash is not detected; such
    bytes could only have produced the same IR, which is compared byte for
    byte. A hash taken inside the runner of exactly what it read is not
    built yet (ADR 0019 section 5); the runner reads every byte of the file,
    with no limit."""
    source = program_vc.ir_source(Path(ir_path).read_text(encoding="utf-8"))
    if not re.fullmatch(FORTH_PATH, source):
        raise SystemExit(f"source path not usable in a Forth string: {source}")
    before = sha256(source)
    out = command(program_words_args(gforth, source))
    outcome, text, _ = program_words_output(out)
    if outcome != 0 or text != Path(ir_path).read_text(encoding="utf-8"):
        raise SystemExit(f"the program words ({IR_WORDS}) do not write {ir_path} for "
                         f"{source}:\n{out}")
    if sha256(source) != before:
        raise SystemExit(f"{source} changed while the program words read it")
    return {"words": IR_WORDS, "sha256": hashlib.sha256(text.encode("utf-8")).hexdigest(),
            "source": before}


KEPT_EXPORT, KEPT_SNAPSHOT = "lf-clamp.ndjson", "lf-clamp.lfsnap"   # record --keep FOLDER
KEPT = (KEPT_EXPORT, f"{KEPT_EXPORT}.manifest.json", KEPT_SNAPSHOT)


def kept_snapshot(folder):
    """The snapshot record --keep made in folder; stop when the check wrote none, so that no
    earlier run's snapshot is ever read in its place (review L3 of speed-lf)."""
    snapshot = Path(folder) / KEPT_SNAPSHOT
    if not snapshot.is_file() or snapshot.stat().st_size == 0:
        raise SystemExit(f"LeanForth's check wrote no snapshot {snapshot}")
    return snapshot


def record(contract_path, manifest_out=None, keep=None):
    """Run Lean, its exporter, LeanForth and Gforth now and return the evidence the receipt
    needs; with manifest_out, also save the fresh export's manifest there. With keep, a
    folder, the export (KEPT_EXPORT, its manifest beside it) is written there and kept, and
    LeanForth's check also saves its snapshot there (KEPT_SNAPSHOT), which must then exist:
    make check records once, and the receipt's test and the clamp mutants' test both read
    the result. The files KEPT of an earlier run are removed first, by name."""
    lean, gforth = checked_lean(), os.environ.get("GFORTH", "gforth")
    contract = program_vc.parse_contract(program_vc.read_contract(contract_path),
                                         contract_path)
    vc = vc_entry(contract["id"])
    written = ir_written(gforth, contract["ir"])
    version = re.match(r"Lean \(version ([0-9.]+),", command([lean, "--version"])).group(1)
    for name in KEPT if keep else ():
        (Path(keep) / name).unlink(missing_ok=True)
    with tempfile.TemporaryDirectory() as directory:
        folder = Path(keep or directory)
        export = folder / KEPT_EXPORT
        output = export_theorems(lean, vc["theorems"], export)
        manifest = read_json(f"{export}.manifest.json")
        if manifest_out:
            Path(manifest_out).write_bytes(Path(f"{export}.manifest.json").read_bytes())
        leanforth = leanforth_check(export, vc["theorems"], keep and folder / KEPT_SNAPSHOT)
        if keep:
            kept_snapshot(folder)
    axioms = lean_axioms(output, vc["theorems"])
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
        "export": {"sha256": manifest["sha256"], "bytes": manifest["bytes"]},
        "leanforth": leanforth,
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
def validator(version=SCHEMA_VERSION):
    """The validator of a schema version the reader reads."""
    return Validator(read_json(ROOT / "schemas" / f"program-receipt-{version}.schema.json"))


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
    """The rules of schemas 0.2 and 0.3 that JSON Schema cannot state, for a receipt the
    schema accepts (the two versions have the same rules).

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
    read = " and ".join(READ_VERSIONS)
    if isinstance(version, str) and version in SUPERSEDED_VERSIONS:
        return [f"superseded-version: $.schemaVersion: {shown} was a draft that was never "
                f"approved; only {read} are read"]
    if not isinstance(version, str) or version not in READ_VERSIONS:
        return [f"unknown-version: $.schemaVersion: {shown} is not {read}"]
    problems = [f"schema: {p}" for p in validator(version).errors(receipt)]
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
    parser.add_argument("action", choices=["write", "validate", "verify", "record", "export"])
    parser.add_argument("receipts", nargs="*")
    parser.add_argument("--contract", default=CONTRACT)
    parser.add_argument("--evidence", default="tests/program/receipts/generated/lf-clamp-evidence.json")
    parser.add_argument("--out", default="tests/program/receipts/generated/lf-clamp.json")
    parser.add_argument("--markdown", default="tests/program/receipts/generated/lf-clamp.md")
    parser.add_argument("--manifest-out")
    parser.add_argument("--keep")
    args = parser.parse_args()
    if args.action == "record":
        Path(args.out).write_text(dump(record(args.contract, args.manifest_out, args.keep)),
                                  encoding="utf-8")
        return 0
    if args.action == "export":
        if len(args.receipts) != 1:
            parser.error("export needs one output file, OUT.ndjson")
        vc = vc_entry(program_vc.parse_contract(program_vc.read_contract(args.contract),
                                                args.contract)["id"])
        export_theorems(checked_lean(), vc["theorems"], args.receipts[0])
        print(f"wrote {args.receipts[0]} and its manifest: {', '.join(vc['theorems'])} with "
              "every declaration they use; check it with bin/leanforth check")
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
