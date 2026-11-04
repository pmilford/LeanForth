#!/usr/bin/env python3
"""Tests of the LeanForth authoring words (plan task 8.1.2; make test, make check).

Usage (from the repository root; GFORTH and LEAN name the toolchains):
  python3 tests/author/check_author.py            golden, round trips, catalogue, layering
  python3 tests/author/check_author.py --write    regenerate tests/author/fixtures.golden
  python3 tests/author/check_author.py --lean     the lean: lines against pinned Lean's #print
  python3 tests/author/check_author.py --faults   planted faults (needs Lean too)

1. Golden: tests/author/report.fs runs every fixture tests/author/*.lf; the
   output must equal fixtures.golden, every fixture that ran must report a
   round trip with the same terms and the same text, and every other one an
   error with its line and column.
2. Catalogue: the error table of docs/programming/LEANFORTH_WORDS.md gives
   exactly the codes and messages of src/author/errors.fs, in order.
3. Layering: no module that src/core, src/kernel or src/main.fs loads,
   directly or through other modules, is under src/author (the checker never
   loads the authoring program).
4. --lean: for each fixture with a Lean source tests/reference/author-STEM.lean,
   pinned Lean (-DwarningAsError=true) prints every declaration; its output
   must equal the fixture's lean: lines, apart from the differences listed in
   KNOWN, each with its reason.
5. --faults: each planted fault, in a copy of src/, must change a round trip
   or a lean: line compared with Lean; the spelling check disabled must be
   caught by the Lean comparison (the round trip cannot see it, ADR 0017 §13).
Finite evidence about these files; it never accepts a theorem.
"""
import os
import pathlib
import re
import shutil
import subprocess
import sys
import tempfile

GFORTH = os.environ.get("GFORTH", "gforth")
LEAN = os.environ.get("LEAN", "lean")
HERE = pathlib.Path("tests/author")
GOLDEN = HERE / "fixtures.golden"
DOC = pathlib.Path("docs/programming/LEANFORTH_WORDS.md")
SAME = "round trip: terms, names, kinds, labels and notes same; printed text same"

# Lean's line -> the term printer's line, where they differ, with the reason.
KNOWN = {
    "08-monoid": {
        "fun {M} [MyMonoid M] a ↦ MyMonoid.mul_one a":
            ("fun {M} [inst : MyMonoid M] a ↦ MyMonoid.mul_one a",
             "Lean omits an instance binder's name that the printed body does not show; "
             "the term printer shows it because the term uses it (ADR 0017, example 8)"),
    },
}

# (name, file, old text, new text): one deliberate bug each.
FAULTS = [
    ("implicit kind lost", "src/present/print-forth.fs",
     'lf-binder-implicit of s" implicit:"', 'lf-binder-implicit of s" explicit:"'),
    ("-> for a used binder", "src/present/print-forth.fs",
     "lf-term-second@ 0 lf-pp-loose? >r 0= r> ;", "drop true outcome-ok ;"),
    ("universe arguments dropped", "src/present/print-forth.fs",
     "lf-pp-const-levels 0= if outcome-invalid exit then",
     "drop outcome-ok exit lf-pp-const-levels 0= if outcome-invalid exit then"),
    ("labels and notes not printed", "src/present/print-forth.fs",
     "dup ok? if over lf-pf-notes then nip ;", "nip ;"),
    ("$ swaps function and argument", "src/author/words.fs",
     ": lfa-two-terms ( a b -- ta tb ) swap lfa>term swap lfa>term ;",
     ": lfa-two-terms ( a b -- ta tb ) lfa>term swap lfa>term ;"),
    ("-> does not shift", "src/author/build.fs",
     "over lf-term-first@ swap < if exit then", "drop exit"),
    ("spelling check ignored", "src/author/groups.fs",
     "if swap lfa-key-spelling rot lfa-spelling compare 0= else 2drop false then ;",
     "if 2drop true else 2drop false then ;"),
]


class Failure(Exception):
    pass


def fixtures():
    return sorted(HERE.glob("*.lf"))


def report(fixture, root="."):
    command = [GFORTH, "tests/author/report.fs", "-e", f's" {fixture}" report bye']
    run = subprocess.run(command, cwd=root, stdin=subprocess.DEVNULL, capture_output=True,
                         timeout=120)
    text = run.stdout.decode("utf-8") + run.stderr.decode("utf-8")
    if run.returncode != 0:
        raise Failure(f"{fixture}: report.fs failed:\n{text}")
    return text


def outputs(root="."):
    return {path.stem: report(f"tests/author/{path.name}", root) for path in fixtures()}


def joined(texts):
    return "".join(f"== {stem}\n{text}" for stem, text in sorted(texts.items()))


def check_trips(texts):
    trips = 0
    for stem, text in texts.items():
        first = text.splitlines()[0]
        if first == "ran: ok":
            trip = [line for line in text.splitlines() if line.startswith("round trip:")]
            if trip != [SAME]:
                raise Failure(f"{stem}: round trip not identical: {trip}")
            trips += 1
        elif not re.match(r"ran: error \d+ at line:col \d+:\d+ ", first):
            raise Failure(f"{stem}: neither ran nor stopped with a position: {first}")
    return trips


def check_golden(write):
    texts = outputs()
    text = joined(texts)
    if write:
        GOLDEN.write_text(text, encoding="utf-8")
        print(f"wrote {GOLDEN}")
        return
    if text != GOLDEN.read_text(encoding="utf-8"):
        raise Failure(f"output differs from {GOLDEN} (run with --write and review the diff)")
    trips = check_trips(texts)
    errors = len(texts) - trips
    print(f"authoring words: {len(texts)} fixtures equal {GOLDEN}; {trips} round trips "
          f"identical (terms and text), {errors} mistakes stopped with line and column")


DUMP = (": dump ( -- ) lfa-catalogue begin dup lfa-last? 0= while dup lfa-entry-code 0 .r"
        " 9 emit dup lfa-entry-text type cr lfa-entry-next repeat drop ; dump bye")


def check_catalogue():
    run = subprocess.run([GFORTH, "src/author/errors.fs", "-e", DUMP], stdin=subprocess.DEVNULL,
                         capture_output=True, text=True, timeout=120, check=True)
    forth = [tuple(line.split("\t", 1)) for line in run.stdout.splitlines() if "\t" in line]
    forth = [(int(code), text) for code, text in forth]
    doc = []
    for line in DOC.read_text(encoding="utf-8").splitlines():
        match = re.match(r"\|\s*(\d+)\s*\|\s*[a-z]+\s*\|\s*(.*?)\s*\|\s*$", line)
        if match:
            doc.append((int(match.group(1)), match.group(2).replace("\\|", "|")))
    if not forth or forth != doc:
        for row in sorted(set(forth) ^ set(doc)):
            print(f"  {'code only' if row in forth else 'docs only'}: {row}")
        raise Failure(f"error catalogue: {DOC} and src/author/errors.fs differ")
    print(f"authoring error catalogue: {len(forth)} codes, documentation and code agree")


REQUIRE = re.compile(r"^\s*(?:require|include)\s+(\S+)", re.M)


def loads(path, seen):
    """Every source file path loads, transitively, including itself."""
    path = path.resolve()
    if path in seen:
        return seen
    seen.add(path)
    for target in REQUIRE.findall(path.read_text(encoding="utf-8")):
        loads(path.parent / target, seen)
    return seen


def check_layering():
    roots = [pathlib.Path("src/main.fs")] + sorted(pathlib.Path("src/core").glob("*.fs")) + \
        sorted(pathlib.Path("src/kernel").glob("*.fs"))
    author = pathlib.Path("src/author").resolve()
    for root in roots:
        bad = [p for p in loads(root, set()) if author in p.parents]
        if bad:
            raise Failure(f"{root} loads the authoring program: {bad[0]}")
    print(f"layering: none of {len(roots)} checker modules (main.fs, core/, kernel/) "
          "loads src/author")


def lean_lines(stem, workdir):
    source = pathlib.Path(f"tests/reference/author-{stem}.lean")
    run = subprocess.run([LEAN, "-DwarningAsError=true", str(source)], capture_output=True,
                         text=True, timeout=300)
    if run.returncode != 0:
        raise Failure(f"Lean failed on {source}:\n{run.stdout}{run.stderr}")
    return run.stdout.splitlines()


def forth_lean(text):
    return [line[len("lean: "):] for line in text.splitlines() if line.startswith("lean: ")]


def compare(stem, lean, forth):
    """Lines that differ, apart from the known differences."""
    known = KNOWN.get(stem, {})
    differ = []
    if len(lean) != len(forth):
        return [f"{stem}: Lean printed {len(lean)} lines, the words {len(forth)}"]
    for want, got in zip(lean, forth):
        if want != got and known.get(want, (None,))[0] != got:
            differ.append(f"{stem}:\n  Lean:  {want}\n  Forth: {got}")
    return differ


def lean_reference():
    stems = [path.stem for path in fixtures()
             if pathlib.Path(f"tests/reference/author-{path.stem}.lean").exists()]
    with tempfile.TemporaryDirectory() as workdir:
        return {stem: lean_lines(stem, workdir) for stem in stems}


def check_lean():
    reference = lean_reference()
    texts = outputs()
    lines = 0
    for stem, lean in reference.items():
        differ = compare(stem, lean, forth_lean(texts[stem]))
        if differ:
            raise Failure("lean: lines differ from pinned Lean:\n" + "\n".join(differ))
        lines += len(lean)
    known = sum(len(v) for v in KNOWN.values())
    print(f"authoring words agree with pinned Lean's #print: {lines} lines of "
          f"{sum(1 for _ in reference)} fixtures ({known} known printer difference, "
          "listed with its reason)")


def planted(root, fault):
    name, path, old, new = fault
    target = root / path
    text = target.read_text(encoding="utf-8")
    if text.count(old) != 1:
        raise Failure(f"fault {name}: the text to replace is not in {path} exactly once")
    target.write_text(text.replace(old, new), encoding="utf-8")
    return target, text


def check_faults():
    reference = lean_reference()
    with tempfile.TemporaryDirectory() as workdir:
        root = pathlib.Path(workdir)
        shutil.copytree("src", root / "src")
        shutil.copytree(HERE, root / "tests/author")
        caught = 0
        for fault in FAULTS:
            target, original = planted(root, fault)
            texts = outputs(root)
            target.write_text(original, encoding="utf-8")
            trips = sum(1 for text in texts.values() for line in text.splitlines()
                        if line.startswith("round trip:") and line != SAME)
            ran = [stem for stem in reference if texts[stem].startswith("ran: ok")]
            changed = [stem for stem in ran
                       if compare(stem, reference[stem], forth_lean(texts[stem]))]
            stopped = len(reference) - len(ran)
            print(f"fault {fault[0]}: round trips differing {trips}; fixtures that still run "
                  f"but print differently from Lean {len(changed)} {changed}; "
                  f"fixtures that no longer run {stopped}")
            if fault[0] == "spelling check ignored" and not changed:
                raise Failure("the spelling fault was not caught by the Lean comparison")
            if trips + len(changed) + stopped == 0:
                raise Failure(f"fault {fault[0]} was not caught")
            caught += 1
    print(f"planted faults: {caught} of {len(FAULTS)} caught")


def main(args):
    try:
        if "--lean" in args:
            check_lean()
        elif "--faults" in args:
            check_faults()
        else:
            check_golden("--write" in args)
            if "--write" not in args:
                check_catalogue()
                check_layering()
    except (Failure, OSError, subprocess.SubprocessError) as error:
        print(f"check_author: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
