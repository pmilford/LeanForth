"""The term printer against pinned Lean 4.35.0 (make check).

Usage: python3 tests/present/printer-differential.py   (from the repository
root; LEAN and GFORTH name the toolchains)

1. Cases: tests/reference/printer-cases.lean prints each case expression
   with Lean's ppExpr (pp.unicode.fun on); the lines must equal both the
   Unicode lines of tests/present/print-cases.golden and what the Forth
   printer prints now.
2. Fixtures: for each pinned fixture, Lean's #print of every declaration
   (pp.unicode.fun on) must equal the Unicode section of the Forth output
   (and of fixtures.golden).
3. ASCII round trip: every fixture declaration's ASCII type and value,
   given back to Lean as source, must elaborate against the original
   constant: example : TYPE := @name and example : TYPE := VALUE.
Finite differential evidence about the stated cases; it never accepts a
theorem. Any difference fails.
"""
import os
import pathlib
import subprocess
import sys
import tempfile

sys.path.insert(0, "tests/present")
from check_golden import FIXTURES, fixture_output, run_forth  # noqa: E402
TEST_LIMIT = int(os.environ.get("TEST_TIMEOUT", "1800"))  # seconds; make exports it

LEAN = os.environ.get("LEAN", "lean")
HERE = pathlib.Path("tests/present")


class Mismatch(Exception):
    pass


def lean_output(path):
    result = subprocess.run([LEAN, "-DwarningAsError=true", str(path)], capture_output=True,
                            text=True, timeout=TEST_LIMIT)
    if result.returncode != 0:
        raise Mismatch(f"Lean failed on {path}:\n{result.stdout}{result.stderr}")
    return result.stdout


def unicode_lines(text):
    return [line.split("\t", 1)[1] for line in text.splitlines() if line.startswith("unicode\t")]


def section(text, mode):
    """Lines of one mode's section in fixture-reader output."""
    lines, inside = [], False
    for line in text.splitlines():
        if line.startswith("-- "):
            inside = line == f"-- {mode}"
        elif inside:
            lines.append(line)
    return lines


def same(label, lean, forth):
    if lean != forth:
        for number, (a, b) in enumerate(zip(lean, forth), 1):
            if a != b:
                raise Mismatch(f"{label}, line {number}:\n  Lean:  {a}\n  Forth: {b}")
        raise Mismatch(f"{label}: Lean printed {len(lean)} lines, Forth {len(forth)}")
    return len(lean)


def check_cases():
    lean = lean_output("tests/reference/printer-cases.lean").splitlines()
    golden = unicode_lines((HERE / "print-cases.golden").read_text(encoding="utf-8"))
    live = unicode_lines(run_forth(HERE / "print-cases.fs"))
    same("cases: golden", lean, golden)
    return same("cases: Forth", lean, live)


def names(fixture):
    """Declaration names in source order, from the fixture's Lean source."""
    found = []
    for line in pathlib.Path(f"tests/reference/{fixture}.lean").read_text().splitlines():
        words = line.split()
        if len(words) > 1 and words[0] in ("theorem", "def"):
            found.append(words[1])
    return found


def check_fixture(fixture, workdir):
    source = pathlib.Path(f"tests/reference/{fixture}.lean").read_text(encoding="utf-8")
    prints = "".join(f"#print {name}\n" for name in names(fixture))
    path = pathlib.Path(workdir) / f"{fixture.replace('-', '_')}_print.lean"
    path.write_text(source + "\nset_option pp.unicode.fun true\n" + prints, encoding="utf-8")
    lean = lean_output(path).splitlines()
    forth = fixture_output(fixture)
    golden_text = (HERE / "fixtures.golden").read_text(encoding="utf-8")
    golden = golden_text.split(f"== {fixture}\n", 1)[1].split("\n== ", 1)[0]
    same(f"{fixture}: golden", lean, section(golden, "unicode"))
    count = same(f"{fixture}: Forth", lean, section(forth, "unicode"))
    return count, round_trip(fixture, source, section(forth, "ascii"), workdir)


def round_trip(fixture, source, ascii_lines, workdir):
    """ASCII output, read back by Lean, against the original constants."""
    checks = []
    for header, value in zip(ascii_lines[0::2], ascii_lines[1::2]):
        _, name, rest = header.split(" ", 2)
        claim = rest[len(": "):-len(" :=")]
        constant = name.split(".{")[0]
        checks.append(f"example : {claim} := @{constant}\nexample : {claim} := {value}\n")
    path = pathlib.Path(workdir) / f"{fixture.replace('-', '_')}_ascii.lean"
    # fun {P} proof => proof names P without using it, as Lean prints it.
    unused = "set_option linter.unusedVariables false\n"
    path.write_text(source + "\n" + unused + "".join(checks), encoding="utf-8")
    lean_output(path)
    return len(checks)


def main():
    try:
        cases = check_cases()
        lines = trips = 0
        with tempfile.TemporaryDirectory() as workdir:
            for fixture in FIXTURES:
                count, trip = check_fixture(fixture, workdir)
                lines, trips = lines + count, trips + trip
    except (Mismatch, OSError, ValueError, RuntimeError, subprocess.TimeoutExpired) as error:
        print(f"printer differential: {error}", file=sys.stderr)
        return 1
    print(f"Term printer agrees with pinned Lean on {cases} cases and {lines} #print lines "
          f"of {len(FIXTURES)} fixtures; {trips} ASCII declarations elaborate in Lean.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
