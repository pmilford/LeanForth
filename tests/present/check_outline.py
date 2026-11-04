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
--write regenerates the golden file; review the diff before committing it.
"""
import os
import pathlib
import re
import subprocess
import sys

GFORTH = os.environ.get("GFORTH", "gforth")
CASES = pathlib.Path("tests/present/outline-cases.fs")
GOLDEN = pathlib.Path("tests/present/outlines.golden")
FOREIGN = "No outline: the checker's log does not belong to this declaration's published"
NO_OUTLINE = {
    "composition, log truncated": "No proof outline: the declaration is accepted, but the"
                                  " checker's log was truncated",
    "composition, log without formulas": "Proof outline not available: the log was kept",
    "composition-wrong-argument": "No proof outline: the declaration was not accepted.",
    "a rejected declaration's log, given as accepted": FOREIGN,
    "composition's log, after identity is loaded": FOREIGN,
}


def printed():
    result = subprocess.run([GFORTH, str(CASES)], stdin=subprocess.DEVNULL,
                            capture_output=True, timeout=300)
    if result.returncode != 0 or result.stderr:
        raise RuntimeError(f"{CASES} failed:\n{result.stdout.decode()}{result.stderr.decode()}")
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


def main(write):
    text = printed()
    if write:
        GOLDEN.write_text(text, encoding="utf-8")
        print(f"wrote {GOLDEN}")
        return 0
    expected = GOLDEN.read_text(encoding="utf-8")
    failures = promises(text)
    if text != expected:
        got, want = text.splitlines(), expected.splitlines()
        for number, (a, b) in enumerate(zip(got, want), 1):
            if a != b:
                failures.append(f"{GOLDEN}:{number}: expected {b!r}\n  printed {a!r}")
                break
        else:
            failures.append(f"{GOLDEN}: {len(got)} lines printed, {len(want)} expected")
    for failure in failures:
        print(failure)
    if failures:
        return 1
    print(f"{GOLDEN}: {len(expected.splitlines())} lines as expected; "
          f"{len(sections(text))} sections keep the outline's promises")
    return 0


if __name__ == "__main__":
    sys.exit(main("--write" in sys.argv[1:]))
