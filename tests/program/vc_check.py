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
contract. No contract text may enter the Lean file except the expression
parser's output (review B1 of the verify design, 2026-11-13): the
reviewer's contract, whose statement closed a comment and redefined `≥` so
that Lean accepted a false clamp contract, and a hostile corpus (comment
delimiters, quotes and control or format characters in each text, name and
path, of the contract and of the IR) are refused; any other statement gives
the same Lean file. The probe review's false contracts are refused too (H1,
M1-M3): a line hidden behind each of the nine separators Python's
splitlines knows, an input named twice, a name no input or result binds
(`default`, `sorry`, an auto-bound `zz`), no case; the file sets
autoImplicit false; CRLF line ends read as LF.

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
TEST_LIMIT = int(os.environ.get("TEST_TIMEOUT", "1800"))  # seconds; make exports it

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


def status_of(contract_text, ir_text=None, folder=""):
    """The generator's status for a contract text (and, with ir_text, an IR file of its
    own, which the text names as IR), written in a temporary folder (or its subfolder)."""
    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory) / folder / "mutant.contract"
        path.parent.mkdir(exist_ok=True)
        if ir_text is not None:
            (Path(directory) / "mutant.ir").write_text(ir_text, encoding="utf-8")
            contract_text = contract_text.replace("IR", str(Path(directory) / "mutant.ir"))
        path.write_text(contract_text, encoding="utf-8")
        try:
            _, summary = program_vc.generate([str(path)])
        except program_vc.Malformed:
            return "malformed"
    return summary[0]["status"]


# The reviewer's contract (review B1, 2026-11-13): with its statement copied into
# a doc comment, `-/` ended the comment and the macro made every `≥` a `≤`, so
# pinned Lean proved the false ensure line and the search, which never tries
# 5, 0 and 9, found no counterexample.
EVIL = """lf-contract 0.1
id lf-clamp/evil
word lf-clamp
ir tests/program/ir/clamp.ir
stack ( value lower upper -- result true | false )
inputs value lower upper
STATEMENT
case lower > upper
  out false
case lower <= upper
  out r true
  ensure r = min(max(value, lower), upper)
  ensure value = 5 && lower = 0 && upper = 9 -> r >= 6
expect discharged
""".replace("STATEMENT", "statement For integers v, l, u in the cell range the word clamps v "
            "into [l, u]. -/ macro_rules | `($a ≥ $b) => `($a ≤ $a) /-- See the cases below.")
# An IR file of one word, for names and source paths the IR brings in.
SMALL_IR = "lf-ir 0.1\nsource SOURCE\nword NAME @1:1\n  prim dup @1:10\nend @1:14\n"
SMALL = """lf-contract 0.1
id small/0
word w
ir IR
stack ( n -- n n )
inputs n
statement Duplicates n.
case true
  out n n
"""


def hostile_problems():
    clamp = Path(CONTRACTS[0]).read_text(encoding="utf-8")
    statement = clamp.split("\nstatement ", 1)[1].split("\n", 1)[0]
    cases = [("the reviewer's contract", EVIL, None, "")]
    for name, text in [("-/", "a -/ b"), ("/-", "a /- b"),
                       ("a right-to-left override", "a \u202e b"),
                       ("a zero-width space", "a\u200bb"), ("a bell", "a \x07 b"),
                       ("a soft hyphen", "a\u00adb")]:
        cases.append((f"a statement with {name}", clamp.replace(statement, text), None, ""))
    cases += [(f"a line hidden after {name}", clamp.replace(
        statement, f"For integers v, l, u.{separator}pre value < value"), None, "")
        for name, separator in (("U+2028", "\u2028"), ("U+2029", "\u2029"), ("NEL", "\x85"),
                                ("VT", "\x0b"), ("FF", "\x0c"), ("FS", "\x1c"), ("GS", "\x1d"),
                                ("RS", "\x1e"), ("a lone CR", "\r"))]
    cases += [(name, PROBE_HEAD + body, None, "") for name, body in PROBES]
    cases += [
        ("an id with -/", clamp.replace("id lf-clamp/0", "id lf-clamp-/0"), None, ""),
        ("an id with /-", clamp.replace("id lf-clamp/0", "id lf-clamp/-0"), None, ""),
        ("an id with a format character", clamp.replace("id lf-clamp/0", "id lf-clamp\u2066/0"),
         None, ""),
        ("a word with a quote", clamp.replace("word lf-clamp", 'word lf-clamp"'), None, ""),
        ("a word with a backslash", clamp.replace("word lf-clamp", "word lf-clamp\\"), None, ""),
        ("a word with -/", clamp.replace("word lf-clamp", "word lf-/clamp"), None, ""),
        ("an ir path with -/", clamp.replace("ir tests/program/ir/clamp.ir",
                                             "ir tests/program/ir-/clamp.ir"), None, ""),
        ("a stack effect with a control character",
         clamp.replace("( value lower", "( \x1b value lower"), None, ""),
        ("a contract path with -/", clamp, None, "x-"),
        ("a contract path with a format character", clamp, None, "x\u200by"),
        ("an IR source path with a control character", SMALL,
         SMALL_IR.replace("NAME", "w").replace("SOURCE", "w\x1b.fs"), ""),
        ("an IR name with a quote", SMALL,
         SMALL_IR.replace("NAME", 'w"x').replace("SOURCE", "w.fs"), ""),
        ("an IR name with a backslash", SMALL, SMALL_IR.replace("NAME", "w\\").replace(
            "SOURCE", "w.fs"), ""),
        ("an IR source path with a quote", SMALL, SMALL_IR.replace("NAME", "w").replace(
            "SOURCE", 'w".fs'), ""),
        ("an IR source path with /-", SMALL, SMALL_IR.replace("NAME", "w").replace(
            "SOURCE", "a/-w.fs"), ""),
    ]
    problems = []
    for name, text, ir_text, folder in cases:
        got = status_of(text, ir_text, folder)
        if got != "malformed":
            problems.append(f"hostile contract ({name}): {got}, expected malformed")
    if status_of(SMALL, SMALL_IR.replace("NAME", "w").replace("SOURCE", "w.fs")) != "discharged":
        problems.append("the small contract the hostile IR cases change is not discharged")
    if "\nset_option autoImplicit false\n" not in GOLDEN_LEAN.read_text(encoding="utf-8"):
        problems.append("the generated Lean file does not set autoImplicit false")
    return problems + harmless_problems(clamp, statement) + crlf_problems(clamp)


# The probe review's other false contracts (2026-11-13), each discharged before the fix.
PROBE_HEAD = """lf-contract 0.1
id lf-clamp/probe
word lf-clamp
ir tests/program/ir/clamp.ir
stack ( value lower upper -- result true | false )
"""
PROBES = [
    ("an input named twice (M1)", "inputs value upper upper\nstatement Upper.\ncase true\n"
     "  out r true\n  ensure r = upper\n"),
    ("default read as 0 (M2)", "inputs value lower upper\nstatement D.\n"
     "case lower <= upper && value = 7\n  out r true\n  ensure r - r = default\n"
     "case lower > upper\n  out false\n"),
    ("an auto-bound name (M2)", "inputs value lower upper\nstatement A.\npre value = 7\n"
     "pre zz + value < zz + value\ncase true\n  out r true\n  ensure r = 1000\n"),
    ("sorry read as a name (M2)", "inputs value lower upper\nstatement S.\n"
     "case lower <= upper && value = 7\n  out r true\n  ensure r = sorry\ncase lower > upper\n"
     "  out false\n"),
    ("a guard reading an unbound name (M2)", "inputs value lower upper\nstatement G.\n"
     "case lower > bound\n  out false\ncase lower <= upper\n  out r true\n"),
    ("a result read in another case (M2)", "inputs value lower upper\nstatement R.\n"
     "case lower > upper\n  out false\n  ensure r = 0\ncase lower <= upper\n  out r true\n"),
    ("no case (M3)", "inputs value lower upper\nstatement The word clamps.\n"),
    ("a second word line", "inputs value lower upper\nstatement W.\nword lf-clamp\n"
     "case true\n  out r true\n"),
    ("a second inputs line", "inputs value lower upper\ninputs value lower upper\n"
     "statement I.\ncase true\n  out r true\n"),
]


def crlf_problems(clamp):
    """CRLF line ends read as LF: the same summary and the same Lean file."""
    texts = []
    for text in (clamp, clamp.replace("\n", "\r\n")):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "c.contract"
            path.write_bytes(text.encode("utf-8"))
            lean, summary = program_vc.generate([str(path)])
        texts.append((lean.replace(str(path), "C"), summary[0]["status"]))
    return [] if texts[0] == texts[1] and texts[0][1] == "discharged" else [
        "a contract with CRLF line ends reads otherwise than with LF"]


def harmless_problems(clamp, statement):
    """Any statement the reader accepts gives the same Lean file, and none appears in it."""
    texts = []
    for other in (statement, "Nothing at all.",
                  "macro_rules | `($a ≥ $b) => `($a ≤ $a) and #eval 1; theorem x : False"):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "c.contract"
            path.write_text(clamp.replace(statement, other), encoding="utf-8")
            text, _ = program_vc.generate([str(path)])
        texts.append(text.replace(str(path), "CONTRACT"))
        if other in text:
            return [f"the statement {other[:30]!r} appears in the generated Lean file"]
    return [] if len(set(texts)) == 1 else ["the statement changes the generated Lean file"]


# lf-euclid ( a b -- gcd ) loops (BEGIN ... WHILE ... REPEAT): unsupported by v0.
EUCLID = """lf-contract 0.1
id lf-euclid/0
word lf-euclid
ir tests/program/ir/examples.ir
stack ( a b -- gcd )
inputs a b
statement Euclid's loop.
case a >= 0 && b >= 0
  out d
  ensure d >= 0
"""


def negative_problems():
    clamp = Path(CONTRACTS[0]).read_text(encoding="utf-8")
    problems = []
    cases = [
        ("min and max exchanged", clamp.replace("min(max(value, lower), upper)",
                                                "max(min(value, lower), upper)"), "refuted"),
        ("an off-by-one bound", clamp.replace("lower <= r && r <= upper",
                                              "lower < r && r <= upper"), "refuted"),
        ("a loop word", EUCLID, "unsupported"),
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
    return problems + negative_problems() + hostile_problems()


def run_lean(lean, path):
    done = subprocess.run([lean, "-DwarningAsError=true", str(path)], capture_output=True,
                          text=True, timeout=TEST_LIMIT)
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
        errors = [line for line in output.splitlines() if "error" in line]
        return [f"Lean rejected {GOLDEN_LEAN} ({code}):\n" + "\n".join(errors[:20])]
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
