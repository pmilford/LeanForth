"""The SHA-256 helper words' proofs, written by Lean, re-checked by LeanForth (plan 5.5.1, SHA-2).

Usage (from the repository root; make check, target reference-program-sha-export):
  LEAN=... python3 tests/program/sha_export_check.py

Pinned Lean compiles tests/reference/program-ir.lean, whose Part 8 proves
that the words of src/program/sha-words.fs compute FIPS 180-4's functions
for every 32-bit input, and its exporter (scripts/export.sh) writes the four
correctness theorems below with every declaration they use. LeanForth's
checker (bin/leanforth check --jobs 2) must accept every declaration of the
export, each theorem with the axioms Lean's own `#print axioms` reports.

Then the same export with changed copies added at its end
(tests/program/clamp_mutants.py, `copied`), each under its own name next to
the originals, must give these verdicts:
  shaChBodyMutant           sha-ch's body with AND and XOR exchanged      accepted
  shaCh_returnsMutant       sha-ch's proof, about the changed body        rejected
  shaCh_correctProofMutant  shaCh_correct's proof with the lemmas of
                            sha-ch and sha-maj exchanged                  rejected
and the originals stay accepted.

No receipt is written: these words are IR 0.2 programs (LSHIFT, -ROT), and
a receipt for one needs receipt schema 0.4, which awaits the owner's
[format] gate (docs/programming/PROGRAM_RECEIPTS.md, "Schema 0.4").
Finite evidence about four theorems; untrusted test tool.
"""
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))
sys.path.insert(0, str(ROOT / "tests" / "program"))
import program_receipt  # noqa: E402
from clamp_mutants import copied, leanforth  # noqa: E402

SOURCE = "tests/reference/program-ir.lean"
MODULE = "ProgramIRModel"
SPACE = "ProgramIR"
THEOREMS = [f"{SPACE}.{name}" for name in ("shaRotr_correct", "shaCh_correct", "shaMaj_correct",
                                           "shaBigSigma0_correct")]
# (new name, original, constants renamed in its type and value, pairs exchanged in its
# value, LeanForth's expected verdict), as tests/program/clamp_mutants.py's copied takes them.
COPIES = [
    ("shaChBodyMutant", "shaChBody", {}, [("ProgramIR.Prim.and", "ProgramIR.Prim.xor")],
     "accepted"),
    ("shaCh_returnsMutant", "shaCh_returns", {"shaChBody": "shaChBodyMutant"}, [], "rejected"),
    ("shaCh_correctProofMutant", "shaCh_correct", {},
     [("ProgramIR.lookup_shaCh", "ProgramIR.lookup_shaMaj"),
      ("ProgramIR.shaCh_returns", "ProgramIR.shaMaj_returns")], "rejected"),
]


def problems_of(code, report, expected, exit_status):
    verdicts = {d["name"]: (d["verdict"], program_receipt.axiom_names(d))
                for d in report["declarations"]}
    problems = [f"{name}: {verdicts.get(name, ('missing',))[0]}, expected {verdict}"
                for name, verdict in expected.items()
                if verdicts.get(name, ("missing",))[0] != verdict]
    others = [n for n, (v, _) in verdicts.items() if v != "accepted" and n not in expected]
    if others or code != exit_status:
        problems.append(f"exit {code} (expected {exit_status}), other declarations not "
                        f"accepted: {others[:5]} {report.get('error', '')}")
    return problems, verdicts


def main():
    lean = program_receipt.pinned_lean()
    with tempfile.TemporaryDirectory() as folder:
        export, mutants = Path(folder) / "sha-words.ndjson", Path(folder) / "mutants.ndjson"
        output = program_receipt.export_theorems(lean, THEOREMS, export, SOURCE, MODULE)
        axioms = program_receipt.lean_axioms(output, THEOREMS)
        code, report = leanforth(export, "--jobs", program_receipt.LEANFORTH_JOBS)
        problems, verdicts = problems_of(code, report, {t: "accepted" for t in THEOREMS}, 0)
        for theorem in THEOREMS:
            if sorted(verdicts.get(theorem, ("", []))[1]) != sorted(axioms[theorem]):
                problems.append(f"{theorem}: LeanForth's axioms {verdicts.get(theorem)}, "
                                f"Lean's {axioms[theorem]}")
        mutants.write_text(copied(export.read_text(encoding="utf-8"), SPACE,
                                  [step[:4] for step in COPIES]), encoding="utf-8")
        subprocess.run([sys.executable, str(ROOT / "scripts" / "export_manifest.py"),
                        str(mutants)], check=True, stdin=subprocess.DEVNULL)
        changed, changed_report = leanforth(mutants, "--jobs", program_receipt.LEANFORTH_JOBS)
    expected = {t: "accepted" for t in THEOREMS}
    expected.update({f"{SPACE}.{new}": verdict for new, *_, verdict in COPIES})
    problems += problems_of(changed, changed_report, expected, 1)[0]
    for problem in problems:
        print(problem, file=sys.stderr)
    if problems:
        return 1
    print(f"SHA-256 helper words: LeanForth accepted all {report['counts']['accepted']:,} "
          f"declarations of the export of {', '.join(t.split('.')[-1] for t in THEOREMS)} "
          "(axioms as Lean's), and rejected sha-ch's proof for a changed body and a changed "
          "proof of shaCh_correct; no receipt (schema 0.4 awaits the [format] gate)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
