"""Tie the Lean model of the program IR to its sources.

Usage (from the repository root):
  python3 tests/program/check_program_ir.py          # make test: no Lean needed
  LEAN=... python3 tests/program/check_program_ir.py --lean   # make check

Without --lean it checks that every block of tests/reference/program-ir.lean
between `-- BEGIN VERBATIM <path> <first>-<last>` and `-- END VERBATIM`
equals those lines of that reference file, so the theorems are about the
existing reference models themselves, and that the six reference files are
all copied. It also checks that the reader's table of the 38 primitives
(src/program/ir-reader.fs) lists Lean's `Prim.word` spellings in the order
of `Prim`, each with the data-stack effect that Lean's `step` gives it.

With --lean it also runs the file with the pinned Lean (warnings are
errors, so `sorry` fails), requires every listed theorem's `#print axioms`
line to name only Lean's propext, Classical.choice and Quot.sound, and
compares the IR text the file prints with the reader's golden output
(tests/program/ir/*.ir) with the source locations removed. That last check
connects the IR terms the proofs are about to what the reader produces from
the actual Forth source; all-primitives.ir covers every primitive.
"""
import os
from pathlib import Path
import re
import subprocess
import sys
import unittest

MODEL = Path("tests/reference/program-ir.lean")
GOLDEN = [Path("tests/program/ir/clamp.ir"), Path("tests/program/ir/examples.ir"),
          Path("tests/program/ir/all-primitives.ir")]
READER = Path("src/program/ir-reader.fs")
REFERENCES = {
    "tests/reference/clamp.lean", "tests/reference/stack-clamp.lean",
    "tests/reference/program-examples.lean", "tests/reference/checked-add.lean",
    "tests/reference/factorial-reference.lean", "tests/reference/gcd-reference.lean",
}
THEOREMS = [
    "clamp_correct", "clamp_matches_stack_model", "checkedAdd_correct", "checkedAbs_correct",
    "inRange_correct", "gcd_correct", "factorial_correct", "swapped_clamp_refuted",
    "unchecked_add_refuted",
]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
BEGIN = re.compile(r"^-- BEGIN VERBATIM (\S+) (\d+)-(\d+)$")
LOCATION = re.compile(r" @\d+:\d+$")


def copy_problems(text, read=lambda p: Path(p).read_text(encoding="utf-8")):
    """Problems with the verbatim blocks of a model text, and the files copied."""
    problems, copied, lines = [], set(), text.splitlines()
    index = 0
    while index < len(lines):
        match = BEGIN.match(lines[index])
        index += 1
        if not match:
            continue
        path, first, last = match.group(1), int(match.group(2)), int(match.group(3))
        copied.add(path)
        try:
            end = lines.index("-- END VERBATIM", index)
        except ValueError:
            problems.append(f"{path} {first}-{last}: no END VERBATIM")
            break
        source = read(path).splitlines()
        if not 1 <= first <= last <= len(source):
            problems.append(f"{path} {first}-{last}: lines out of range")
        elif lines[index:end] != source[first - 1:last]:
            problems.append(f"{path} {first}-{last}: copy differs from the source")
        index = end + 1
    return problems, copied


def check_copies():
    problems, copied = copy_problems(MODEL.read_text(encoding="utf-8"))
    problems += [f"{path}: not copied" for path in sorted(REFERENCES - copied)]
    return problems


def axiom_problems(output):
    problems = []
    for name in THEOREMS:
        match = re.search(rf"'ProgramIR\.{name}' depends on axioms: \[(.*)\]", output)
        if not match:
            problems.append(f"{name}: no axiom report")
            continue
        used = {a.strip() for a in match.group(1).split(",") if a.strip()}
        if used - ALLOWED_AXIOMS:
            problems.append(f"{name}: uses {sorted(used - ALLOWED_AXIOMS)}")
    return problems


# The reader's primitive table: `21 s" +" ir-data` (effect: taken, given);
# ir-division marks / and MOD, ir-return the return-stack words.
READER_PRIM = re.compile(r'(\d)(\d) s" (\S+)" ir-(?:data|division|return)\b')
LEAN_WORD = re.compile(r'\| \.(\w+) => "([^"]+)"')
# A case of Lean's `step`: the data stack before, then after.
LEAN_STEP = re.compile(r'\| \.(\w+), ⟨([^,⟩]*), [^⟩]*⟩ =>.*?\.next ⟨([^,⟩]*), [^⟩]*⟩', re.S)


def reader_primitives(text):
    """(spelling, taken, given) of each primitive, in the reader's order."""
    return [(m.group(3), int(m.group(1)), int(m.group(2))) for m in READER_PRIM.finditer(text)]


def lean_primitives(text):
    """(spelling, taken, given) of each Prim constructor, in declaration order."""
    order = re.search(r"inductive Prim where(.*?)deriving", text, re.S).group(1)
    names = re.findall(r"\w+", order.replace("|", " "))
    words = dict(LEAN_WORD.findall(text[text.index("def Prim.word"):]))
    step = text[text.index("def step"):text.index("| _, _ => .failed .underflow")]
    effects = {m.group(1): (m.group(2).count("::"), m.group(3).count("::"))
               for m in LEAN_STEP.finditer(step)}
    return [(words.get(n), *effects.get(n, (None, None))) for n in names]


def primitive_problems(reader_text, lean_text):
    reader, lean = reader_primitives(reader_text), lean_primitives(lean_text)
    problems = [] if len(lean) == 38 else [f"Lean has {len(lean)} primitives, not 38"]
    if len(reader) != len(lean):
        problems.append(f"the reader has {len(reader)} primitives, Lean {len(lean)}")
    for index, (ours, theirs) in enumerate(zip(reader, lean)):
        if ours != theirs:
            problems.append(f"primitive {index}: reader {ours}, Lean {theirs}")
    return problems


def golden_text():
    lines = []
    for path in GOLDEN:
        lines += [LOCATION.sub("", line) for line in path.read_text(encoding="utf-8").splitlines()]
    return lines


def check_lean():
    lean = os.environ.get("LEAN", "lean")
    run = subprocess.run([lean, "-DwarningAsError=true", "--run", str(MODEL)],
                         capture_output=True, text=True, timeout=600)
    output = run.stdout + run.stderr
    if run.returncode != 0:
        return [f"Lean failed ({run.returncode}):\n{output}"]
    problems = axiom_problems(output)
    lines = output.splitlines()
    starts = [i for i, line in enumerate(lines) if line.startswith("lf-ir ")]
    printed = lines[starts[0]:] if starts else []
    if printed != golden_text():
        problems.append("the IR printed by Lean differs from the reader's golden output")
    return problems


class Copies(unittest.TestCase):
    def test_model_copies_match(self):
        self.assertEqual(check_copies(), [])

    def test_a_changed_copy_is_detected(self):
        text = MODEL.read_text(encoding="utf-8")
        changed = text.replace("if value < lower then lower", "if value <= lower then lower", 1)
        self.assertNotEqual(text, changed)
        problems, _ = copy_problems(changed)
        self.assertTrue(any("copy differs" in p for p in problems), problems)

    def test_reader_primitives_match_lean(self):
        reader = READER.read_text(encoding="utf-8")
        lean = MODEL.read_text(encoding="utf-8")
        self.assertEqual(len(reader_primitives(reader)), 38)
        self.assertEqual(primitive_problems(reader, lean), [])

    def test_a_changed_primitive_is_detected(self):
        reader = READER.read_text(encoding="utf-8")
        lean = MODEL.read_text(encoding="utf-8")
        for old, new in (('21 s" <>" ir-data', '21 s" =/=" ir-data'),
                         ('23 s" tuck" ir-data', '22 s" tuck" ir-data'),
                         ('21 s" nip" ir-data', '20 s" nip" ir-data'),
                         ('01 s" r@" ir-return', '')):
            with self.subTest(change=old):
                changed = reader.replace(old, new, 1)
                self.assertNotEqual(reader, changed)
                self.assertTrue(primitive_problems(changed, lean))
        swapped = reader.replace('s" rot"', 's" @@@"').replace('s" 2dup"', 's" rot"')
        self.assertTrue(primitive_problems(swapped.replace('s" @@@"', 's" 2dup"'), lean))

    def test_axiom_report_rejects_other_axioms(self):
        good = "\n".join(f"'ProgramIR.{n}' depends on axioms: [propext]" for n in THEOREMS)
        self.assertEqual(axiom_problems(good), [])
        bad = good.replace("[propext]", "[propext, sorryAx]", 1)
        self.assertTrue(axiom_problems(bad))
        self.assertTrue(axiom_problems(good.replace("clamp_correct", "other", 1)))


def main():
    if "--lean" in sys.argv:
        problems = check_copies() + check_lean()
        for problem in problems:
            print(problem, file=sys.stderr)
        if problems:
            return 1
        print(f"program IR model: copies, {len(THEOREMS)} axiom reports and "
              f"{len(golden_text())} IR lines agree")
        return 0
    return 0 if unittest.main(argv=[sys.argv[0]], exit=False).result.wasSuccessful() else 1


if __name__ == "__main__":
    sys.exit(main())
