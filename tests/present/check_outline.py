"""Golden test of the proof outline (plan task 2.4.4; make test; Gforth and
Python only).

Usage: python3 tests/present/check_outline.py [--write]   (from the repository root)

tests/present/outline-cases.fs checks each pinned export (and a broken copy
of composition) with the derivation log on and prints the proof outlines,
composition's every step, and the outlines that must not be printed (a
truncated log, a log without formulas, a rejected declaration); the output
must equal tests/present/outlines.golden, byte for byte. Then the text is
checked for the outline's promises: each accepted outline names the steps
it covers and ends with the structured-template footer; no outline appears
after a truncated log, a log without formulas or a rejected declaration.
Every accepted outline also shows the statement in three forms (Lean's
notation, mathematics, LeanForth words; plan task 8.6.2), and the LeanForth
block runs through the authoring words to the identical statement
(tests/present/statement-roundtrip.fs, run here on every pinned example).
The LaTeX style (plan task 8.6.1) has its own golden file,
tests/present/outlines-latex.golden, from tests/present/outline-latex-cases.fs:
each fragment is checked structurally (balanced braces and environments, only
the macros the printer writes) and, when pdflatex is installed, compiled in a
small document; without pdflatex the compile is skipped and says so.
--write regenerates the golden files; review the diff before committing them.
"""
import os
import pathlib
import re
import shutil
import subprocess
import sys
import tempfile

GFORTH = os.environ.get("GFORTH", "gforth")
CASES = pathlib.Path("tests/present/outline-cases.fs")
GOLDEN = pathlib.Path("tests/present/outlines.golden")
LATEX_CASES = pathlib.Path("tests/present/outline-latex-cases.fs")
LATEX_GOLDEN = pathlib.Path("tests/present/outlines-latex.golden")
ROUND_TRIP = pathlib.Path("tests/present/statement-roundtrip.fs")
EXAMPLES = {"identity": "identity", "composition": "composition", "type-identity": "type-identity",
            "poly-identity": "poly-identity", "constant-fixture": "constant-fixture"}
# The macros the LaTeX style writes (the term printer's tokens, latex-text.fs and
# the outline's layout) and the environments it opens.
MACROS = {"textbf", "textit", "texttt", "ttfamily", "small", "par", "noindent", "hspace",
          "fontdimen", "font", "multicolumn", "linewidth", "begin", "end", "forall", "to",
          "leftarrow", "blacksquare", "lambda", "mapsto", "mathrm", "mathit", "mathsf", "max",
          "operatorname", "hat", "sim", "backslash", "textbackslash", "textasciitilde"}
GREEK = ("alpha beta gamma delta epsilon zeta eta theta iota kappa lambda mu nu xi pi rho sigma "
         "tau upsilon phi chi psi omega").split()
ENVIRONMENTS = {"flushleft", "tabular"}
FOREIGN = "No outline: the checker's log does not belong to this declaration's published"
NO_OUTLINE = {
    "composition, log truncated": "No proof outline: the declaration is accepted, but the"
                                  " checker's log was truncated",
    "composition, log without formulas": "Proof outline not available: the log was kept",
    "composition-wrong-argument": "No proof outline: the declaration was not accepted.",
    "a rejected declaration's log, given as accepted": FOREIGN,
    "composition's log, after identity is loaded": FOREIGN,
    "composition's log, damaged": "No outline: the checker's log fails its structural check"
                                  " (part 2)",
}


def printed(cases=CASES, lines=None):
    given = {"input": "\n".join(lines).encode() + b"\n"} if lines else {"stdin": subprocess.DEVNULL}
    result = subprocess.run([GFORTH, str(cases)], capture_output=True, timeout=300, **given)
    if result.returncode != 0 or result.stderr:
        raise RuntimeError(f"{cases} failed:\n{result.stdout.decode()}{result.stderr.decode()}")
    return result.stdout.decode("utf-8")


def sections(text):
    parts = re.split(r"^== (.*)$", text, flags=re.M)
    return dict(zip(parts[1::2], parts[2::2]))


def promises(text):
    """The outline's promises, as text: a list of failures."""
    failures = []
    for name, body in sections(text).items():
        if name in NO_OUTLINE:
            if NO_OUTLINE[name] not in body or "Proof (" in body or "∎" in body:
                failures.append(f"{name}: an outline where none may be printed")
            continue
        if name.endswith("--detail"):
            continue
        for outline in body.split("\nTheorem ")[1:] + body.split("\nDefinition ")[1:]:
            lines = [l for l in outline.splitlines() if re.match(r"^\s+\d+\s{2}", l)]
            if not lines or any(not re.search(r"\bs\d+", l) for l in lines):
                failures.append(f"{name}: an outline line names no step")
            if "(structured-template)" not in outline or "∎" not in outline:
                failures.append(f"{name}: no structured-template footer")
            if "experimental, not independently audited" not in outline:
                failures.append(f"{name}: no audit label")
    return failures


def differences(golden, text):
    """The first difference between the printed text and a golden file, as a list."""
    expected = golden.read_text(encoding="utf-8")
    if text == expected:
        return []
    got, want = text.splitlines(), expected.splitlines()
    for number, (a, b) in enumerate(zip(got, want), 1):
        if a != b:
            return [f"{golden}:{number}: expected {b!r}\n  printed {a!r}"]
    return [f"{golden}: {len(got)} lines printed, {len(want)} expected"]


def forms(text):
    """Each accepted outline shows the statement in the three forms, in order."""
    failures = []
    for name, body in sections(text).items():
        if name in NO_OUTLINE or name.endswith("--detail"):
            continue
        for outline in re.split(r"\n(?=(?:Theorem|Definition) )", body)[1:]:
            labels =[re.search(r"^  (Statement|Type) in (LeanForth|Lean|mathematics)", l)
                      for l in outline.splitlines()]
            found = [m.group(2) for m in labels if m]
            if found != ["Lean", "mathematics", "LeanForth"]:
                failures.append(f"{name}: statement forms {found}")
    return failures


def blocks(text):
    """The LeanForth block of each accepted outline of each section: its lines,
    without their indentation, from the axiom line to the end line."""
    result = {}
    for name, body in sections(text).items():
        found = re.findall(r"^    (axiom .*?^    end \S+)$", body, flags=re.M | re.S)
        result[name] = ["\n".join(l[4:] if l.startswith("    ") else l for l in b.splitlines())
                        for b in found]
    return result


def round_trips(text):
    """Run each block through the authoring words: the identical statement, term for term
    (the type's tree dump, names and kinds included, of the checker's input)."""
    failures = []
    with tempfile.TemporaryDirectory() as tmp:
        for name, found in blocks(text).items():
            if name not in EXAMPLES:
                continue
            words = pathlib.Path(tmp) / f"{name}.lf"
            words.write_text("\n\n".join(found) + "\n", encoding="utf-8")
            export = f"tests/reference/{EXAMPLES[name]}.ndjson"
            out = printed(ROUND_TRIP, [export, str(words)])
            if "round trip: same" not in out or "DIFFERENT" in out:
                failures.append(f"{name}: the LeanForth statements do not build the same "
                                f"terms:\n{out}")
    return failures


def structure(name, body):
    """A fragment's structure: balanced braces (not counting escaped ones), matching
    environments, and only known macros."""
    failures = []
    plain = re.sub(r"\\[{}$%&#_ ]", "", body)
    depth = 0
    for char in plain:
        depth += (char == "{") - (char == "}")
        if depth < 0:
            break
    if depth != 0:
        failures.append(f"{name}: unbalanced braces")
    opened = []
    for kind, env in re.findall(r"\\(begin|end)\{(\w+)\}", body):
        if kind == "begin":
            opened.append(env)
        elif not opened or opened.pop() != env:
            failures.append(f"{name}: \\end{{{env}}} does not match")
    if opened or any(env not in ENVIRONMENTS for _, env in re.findall(r"\\(begin|end)\{(\w+)\}", body)):
        failures.append(f"{name}: environments left open or unknown: {opened}")
    if body.count("$") % 2:
        failures.append(f"{name}: an odd number of $")
    unknown = set(re.findall(r"\\([A-Za-z]+)", body)) - MACROS - set(GREEK)
    if unknown:
        failures.append(f"{name}: unknown macros {sorted(unknown)}")
    return failures


PREAMBLE = ("\\documentclass{article}\n\\usepackage[utf8]{inputenc}\n"
            "\\usepackage{amsmath,amssymb}\n"
            "\\DeclareUnicodeCharacter{03B1}{\\ensuremath{\\alpha}}\n\\begin{document}\n")


def compiled(parts):
    """Compile each fragment in a small document; (failures, how many compiled)."""
    if shutil.which("pdflatex") is None:
        return [], 0
    failures = []
    with tempfile.TemporaryDirectory() as tmp:
        for index, (name, body) in enumerate(parts.items()):
            tex = pathlib.Path(tmp) / f"outline{index}.tex"
            tex.write_text(PREAMBLE + body + "\n\\end{document}\n", encoding="utf-8")
            run = subprocess.run(["pdflatex", "-interaction=nonstopmode", "-halt-on-error",
                                  tex.name], cwd=tmp, stdin=subprocess.DEVNULL,
                                 capture_output=True, text=True, timeout=120)
            if run.returncode != 0:
                failures.append(f"{name}: pdflatex failed:\n{run.stdout[-1200:]}")
    return failures, len(parts)


def latex_failures(text):
    parts = sections(text)
    failures = []
    for name, body in parts.items():
        failures += structure(name, body)
    more, count = compiled(parts)
    note = (f"{count} fragments compiled with pdflatex" if count
            else "pdflatex not found: the fragments were checked structurally only")
    return failures + more, note


def main(write):
    text = printed()
    latex = printed(LATEX_CASES)
    if write:
        GOLDEN.write_text(text, encoding="utf-8")
        LATEX_GOLDEN.write_text(latex, encoding="utf-8")
        print(f"wrote {GOLDEN} and {LATEX_GOLDEN}")
        return 0
    failures = promises(text) + forms(text) + differences(GOLDEN, text)
    failures += differences(LATEX_GOLDEN, latex)
    more, note = latex_failures(latex)
    failures += more + round_trips(text)
    for failure in failures:
        print(failure)
    if failures:
        return 1
    print(f"{GOLDEN}: {len(GOLDEN.read_text(encoding='utf-8').splitlines())} lines as expected; "
          f"{len(sections(text))} sections keep the outline's promises and show the statement "
          f"in three forms; {LATEX_GOLDEN}: {len(sections(latex))} fragments, {note}")
    return 0


if __name__ == "__main__":
    sys.exit(main("--write" in sys.argv[1:]))
