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
of `Prim`, each with the data-stack effect that Lean's `step` gives it,
and that both statements of the reader's threat model (its header comment
and PROGRAM_IR.md) list calls of its internal words, such as ir-feed, as
misuse it does not detect.

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
DOC = Path("docs/programming/PROGRAM_IR.md")
REFERENCES = {
    "tests/reference/clamp.lean", "tests/reference/stack-clamp.lean",
    "tests/reference/program-examples.lean", "tests/reference/checked-add.lean",
    "tests/reference/factorial-reference.lean", "tests/reference/gcd-reference.lean",
}
THEOREMS = [f"ProgramIR.{name}" for name in (
    "clamp_correct", "clamp_matches_stack_model", "checkedAdd_correct", "checkedAbs_correct",
    "inRange_correct", "gcd_correct", "factorial_correct", "swapped_clamp_refuted",
    "unchecked_add_refuted",
    # Part 5: the contracts of the five words other than clamp (plan task 1.5.3).
    "checkedAdd_meets_contract", "checkedAbs_meets_contract", "inRange_meets_contract",
    "loop_rule", "euclid_by_invariant", "gcd_meets_contract", "factorialFrom_by_invariant",
    "factorial_meets_contract", "unchecked_add_violates_contract",
    "plain_abs_violates_contract", "unguarded_in_range_violates_contract",
    "gcd_top_only_violates_contract", "wrapping_factorial_violates_contract",
    # Part 6: well-formedness of the programs (ADR 0019, test plan 4).
    "clamp_wellFormed", "examples_wellFormed", "allPrimitives_wellFormed",
    "forward_call_not_wellFormed", "recursion_not_wellFormed", "redefinition_not_wellFormed",
    "constant_calling_word_not_wellFormed", "constant_with_if_not_wellFormed")] + [
    # The reference contracts' own proofs, copied verbatim into Part 5.
    "CheckedAddReference.checkedAdd_contract", "ProgramExamplesReference.checkedAbs_contract",
    "ProgramExamplesReference.inRange_contract", "GcdReference.checked_contract",
    "FactorialReference.checked_contract",
]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
BEGIN = re.compile(r"^-- BEGIN VERBATIM (\S+) (\d+)-(\d+)$")
LOCATION = re.compile(r" @\d+:\d+$")
INTERNAL_FEED = re.compile(r"(?<![-\w])ir-feed(?![-\w])")   # not lf-ir-feed


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
        quoted = re.escape(f"'{name}'")
        match = re.search(rf"^{quoted} depends on axioms: \[(.*)\]$", output, re.M)
        if not match and not re.search(rf"^{quoted} does not depend on any axioms$", output, re.M):
            problems.append(f"{name}: no axiom report")
            continue
        used = {a.strip() for a in match.group(1).split(",") if a.strip()} if match else set()
        if used - ALLOWED_AXIOMS:
            problems.append(f"{name}: uses {sorted(used - ALLOWED_AXIOMS)}")
    return problems


# The reader's primitive table: `21 s" +" ir-data` (effect: taken, given);
# ir-division marks / and MOD, ir-return the return-stack words.
READER_PRIM = re.compile(r'(\d)(\d) s" (\S+)" ir-(?:data|division|return)\b')
# The program words' table (src/program/verify-semantics.fs), the same way.
WORDS_PRIM = re.compile(r'(\d)(\d) s" (\S+)" pv-(?:data|division|return)\b')
WORDS = Path("src/program/verify-semantics.fs")
LEAN_WORD = re.compile(r'\| \.(\w+) => "([^"]+)"')
# A case of Lean's `step`: the data stack before, then after.
LEAN_STEP = re.compile(r'\| \.(\w+), ⟨([^,⟩]*), [^⟩]*⟩ =>.*?\.next ⟨([^,⟩]*), [^⟩]*⟩', re.S)


def reader_primitives(text, pattern=READER_PRIM):
    """(spelling, taken, given) of each primitive, in the reader's order."""
    return [(m.group(3), int(m.group(1)), int(m.group(2))) for m in pattern.finditer(text)]


def lean_primitives(text):
    """(spelling, taken, given) of each Prim constructor, in declaration order."""
    order = re.search(r"inductive Prim where(.*?)deriving", text, re.S).group(1)
    names = re.findall(r"\w+", order.replace("|", " "))
    words = dict(LEAN_WORD.findall(text[text.index("def Prim.word"):]))
    step = text[text.index("def step"):text.index("| _, _ => .failed .underflow")]
    effects = {m.group(1): (m.group(2).count("::"), m.group(3).count("::"))
               for m in LEAN_STEP.finditer(step)}
    return [(words.get(n), *effects.get(n, (None, None))) for n in names]


def primitive_problems(reader_text, lean_text, pattern=READER_PRIM):
    reader, lean = reader_primitives(reader_text, pattern), lean_primitives(lean_text)
    problems = [] if len(lean) == 38 else [f"Lean has {len(lean)} primitives, not 38"]
    if len(reader) != len(lean):
        problems.append(f"the reader has {len(reader)} primitives, Lean {len(lean)}")
    for index, (ours, theirs) in enumerate(zip(reader, lean)):
        if ours != theirs:
            problems.append(f"primitive {index}: reader {ours}, Lean {theirs}")
    return problems


def undetected_misuse(text, comment=""):
    """The paragraph, in the reader's header comment or in PROGRAM_IR.md, that
    lists the misuse the reader does not detect, as one line of words."""
    lines = text.splitlines()
    start = next(i for i, line in enumerate(lines)
                 if line.startswith(comment + "Other misuse is not detected"))
    end = next(i for i in range(start, len(lines)) if lines[i].strip() in ("", comment.strip()))
    return " ".join(line[len(comment):] for line in lines[start:end])


def threat_model_problems(reader_text, doc_text):
    """Both lists of undetected misuse must name calls of the reader's internal
    words, which skip its entry check (an output word calling ir-feed)."""
    problems = []
    for where, paragraph in (("reader", undetected_misuse(reader_text, "\\ ")),
                             ("PROGRAM_IR.md", undetected_misuse(doc_text))):
        if "internal word" not in paragraph or not INTERNAL_FEED.search(paragraph):
            problems.append(f"{where}: undetected misuse omits calls of internal words")
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

    def test_program_words_primitives_match_lean(self):
        words = WORDS.read_text(encoding="utf-8")
        lean = MODEL.read_text(encoding="utf-8")
        self.assertEqual(len(reader_primitives(words, WORDS_PRIM)), 38)
        self.assertEqual(primitive_problems(words, lean, WORDS_PRIM), [])
        for old, new in (('21 s" <>" pv-data', '21 s" =/=" pv-data'),
                         ('23 s" tuck" pv-data', '22 s" tuck" pv-data'),
                         ('01 s" r@" pv-return', '')):
            with self.subTest(change=old):
                changed = words.replace(old, new, 1)
                self.assertNotEqual(words, changed)
                self.assertTrue(primitive_problems(changed, lean, WORDS_PRIM))

    def test_threat_model_names_internal_words(self):
        reader = READER.read_text(encoding="utf-8")
        doc = DOC.read_text(encoding="utf-8")
        self.assertEqual(threat_model_problems(reader, doc), [])
        self.assertEqual(len(threat_model_problems(reader.replace("ir-feed,", "it,"), doc)), 1)
        self.assertEqual(len(threat_model_problems(reader, doc.replace("internal word", "w"))), 1)

    def test_axiom_report_rejects_other_axioms(self):
        good = "\n".join(f"'{n}' depends on axioms: [propext]" for n in THEOREMS)
        self.assertEqual(axiom_problems(good), [])
        bad = good.replace("[propext]", "[propext, sorryAx]", 1)
        self.assertTrue(axiom_problems(bad))
        self.assertTrue(axiom_problems(good.replace("clamp_correct", "other", 1)))
        # A theorem may use no axioms at all; Lean says so in other words.
        none = good.replace("depends on axioms: [propext]", "does not depend on any axioms", 1)
        self.assertEqual(axiom_problems(none), [])
        # A report about another name that merely starts the same does not count.
        longer = good.replace("'ProgramIR.loop_rule'", "'ProgramIR.loop_rule_x'", 1)
        self.assertTrue(axiom_problems(longer))


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
