"""leanforth verify's driver v0 end to end with pinned Lean and LeanForth (plan 8.4.1b).

Usage (from the repository root):
  GFORTH=... LEAN=... python3 tests/program/verify_lean_check.py CONTRACT...   # make check
  GFORTH=... LEAN=... python3 tests/program/verify_lean_check.py --all         # every contract
  ... --write CONTRACT... | --all --write                                     # new golden files

For each named contract of tests/program/contracts/ (by file name without
.contract), runs `python3 -I scripts/program_verify.py SOURCE --contract
CONTRACT --out build/verify-lean/NAME` as a user would, with the real program
words, the generator, pinned Lean (LEAN, the Makefile's cache when it is on),
Lean's exporter and LeanForth's checker (bin/leanforth check --json --jobs 2,
a final run). Each must end with the exit status and the summary line of its
outcome (EXPECTED below: discharged 0, refuted 1, unsupported 2, the SHA
words refused as needing receipt 0.4, 2), its receipt must be read by the
strict reader (scripts/program_receipt.py validate) and equal the golden one
in tests/program/verify/golden/ but for its date and the --out folder, the
export must be removed and its manifest kept. The files of the last run, and what it
printed (verify.out), stay in
build/verify-lean/NAME (ignored by git). make check runs lf-clamp and
wrong-clamp-swapped (about 100 s each, two workers); --all runs all thirteen
(the plan's acceptance: about 13 minutes), recorded in
docs/programming/PROGRAM_VERIFY.md. --write writes the golden receipts
instead of comparing them.
"""
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))
import program_receipt  # noqa: E402

TEST_LIMIT = int(os.environ.get("TEST_TIMEOUT", "1800"))
GOLDEN = ROOT / "tests" / "program" / "verify" / "golden"
OUT = ROOT / "build" / "verify-lean"
# contract: (source, word, exit status, verify status or None for no receipt)
EXPECTED = {
    "lf-clamp": ("src/program/clamp.fs", "lf-clamp", 0, "discharged"),
    "lf-checked-add": ("src/program/examples.fs", "lf-checked-add", 0, "discharged"),
    "lf-checked-abs": ("src/program/examples.fs", "lf-checked-abs", 0, "discharged"),
    "lf-in-range": ("src/program/examples.fs", "lf-in-range", 0, "discharged"),
    "wrong-clamp-swapped": ("src/program/clamp.fs", "lf-clamp", 1, "refuted"),
    "wrong-checked-add-total": ("src/program/examples.fs", "lf-checked-add", 1, "refuted"),
    "wrong-in-range-exclusive": ("src/program/examples.fs", "lf-in-range", 1, "refuted"),
    "lf-gcd": ("src/program/examples.fs", "lf-gcd", 2, "unsupported"),
    "lf-factorial": ("src/program/examples.fs", "lf-factorial", 2, "unsupported"),
    "sha-rotr": ("src/program/sha-words.fs", "sha-rotr", 2, None),
    "sha-ch": ("src/program/sha-words.fs", "sha-ch", 2, None),
    "sha-maj": ("src/program/sha-words.fs", "sha-maj", 2, None),
    "sha-big-sigma0": ("src/program/sha-words.fs", "sha-big-sigma0", 2, None),
}
SUMMARY = {"discharged": "discharged (", "refuted": "NOT VERIFIED: refuted: ",
           "unsupported": "NOT VERIFIED: unsupported: ",
           None: "NOT VERIFIED: ir-needs-receipt-0.4; no receipt written"}


def normalized(text, out):
    """A receipt's text with its date, its --out folder and the hash of its evidence record
    (which holds the date and the tools' paths) replaced, for comparison."""
    text = re.sub(r'"createdAt": "[0-9-]+"', '"createdAt": "DATE"', text)
    text = re.sub(r"(evidence\.json, SHA-256 )[0-9a-f]{64}", r"\1EVIDENCE", text)
    text = re.sub(r'(evidence\.json",\n\s*"sha256": ")[0-9a-f]{64}', r"\1EVIDENCE", text)
    return text.replace(out.relative_to(ROOT).as_posix(), "OUT")


def run(name, write):
    """The problems of one contract's run."""
    source, word, status, verify = EXPECTED[name]
    out = OUT / name   # the driver removes an earlier run's files there, by name
    done = subprocess.run([sys.executable, "-I", "scripts/program_verify.py", source,
                           "--contract", f"tests/program/contracts/{name}.contract", "--out",
                           str(out.relative_to(ROOT))], cwd=ROOT, capture_output=True,
                          text=True, timeout=TEST_LIMIT, stdin=subprocess.DEVNULL)
    text = done.stdout + done.stderr
    out.mkdir(parents=True, exist_ok=True)
    (out / "verify.out").write_text(text, encoding="utf-8")   # what the command printed
    problems = []
    if done.returncode != status:
        problems.append(f"exit status {done.returncode}, expected {status}:\n{text}")
    if SUMMARY[verify] not in text:
        problems.append(f"no summary line {SUMMARY[verify]!r}:\n{text}")
    receipt_path = out / f"{word}.receipt.json"
    golden = GOLDEN / f"{name}.receipt.json"
    if verify is None:
        return problems + ([f"{receipt_path} written"] if receipt_path.exists() else [])
    receipt, read = program_receipt.read_file(receipt_path)
    if read:
        return problems + [f"{receipt_path}: {p}" for p in read]
    if receipt["verify"]["status"] != verify:
        problems.append(f"verify {receipt['verify']['status']}, expected {verify}")
    if (out / f"{word}.ndjson").exists():
        problems.append("the export was not removed")
    if verify in ("discharged", "refuted") and not (out / f"{word}.ndjson.manifest.json").exists():
        problems.append("the export's manifest was not kept")
    found = normalized(receipt_path.read_text(encoding="utf-8"), out)
    if write:
        golden.write_text(found, encoding="utf-8")
    elif not golden.exists() or found != golden.read_text(encoding="utf-8"):
        problems.append(f"{receipt_path} differs from {golden.relative_to(ROOT)}")
    return problems


def main():
    write, names = "--write" in sys.argv, [a for a in sys.argv[1:] if not a.startswith("--")]
    names = list(EXPECTED) if "--all" in sys.argv else names
    unknown = [n for n in names if n not in EXPECTED]
    if not names or unknown:
        print(f"usage: verify_lean_check.py [--write] --all | CONTRACT... ({unknown})",
              file=sys.stderr)
        return 2
    failed = 0
    for name in names:
        problems = run(name, write)
        for problem in problems:
            print(f"{name}: {problem}", file=sys.stderr)
        failed += bool(problems)
        print(f"{name}: {'FAILED' if problems else 'as expected'} "
              f"({EXPECTED[name][3] or 'refused: needs receipt 0.4'})")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
