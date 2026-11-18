#!/usr/bin/env python3
"""Tests of the LeanForth authoring words (plan task 8.1.2; make test, make check).

Usage (from the repository root; GFORTH and LEAN name the toolchains):
  python3 tests/author/check_author.py            golden, round trips, catalogue, layering
  python3 tests/author/check_author.py --write    regenerate tests/author/fixtures.golden
  python3 tests/author/check_author.py --lean     the terms and the lean: lines against Lean
  python3 tests/author/check_author.py --faults   planted faults (needs Lean too)
  python3 tests/author/check_author.py --records  the export records only (and Lean's,
                                                  when LEAN is set)

1. Golden: tests/author/report.fs runs every fixture tests/author/*.lf; the
   output must equal fixtures.golden, every fixture that ran must report a
   round trip with the same terms and the same text, and every other one an
   error with its line and column.
   Records: the export records the kernel is given for every fixture that
   ran (src/author/export.fs, report.fs's record: lines) must read as an
   export and hold each theorem, definition and axiom exactly as the words
   built it (kind, universe parameters, type and value, node for node,
   binder names and kinds too), once, in file order, and nothing else.
   With --lean (and --records with LEAN set) each declaration's whole
   record must equal pinned Lean's export of the fixture's Lean source
   (kind, name, all, levelParams, hints, safety, isUnsafe, type and value
   apart from binder names and kinds, which that exporter merges).
2. Catalogue: the error table of docs/programming/LEANFORTH_WORDS.md gives
   exactly the codes and messages of src/author/errors.fs, in order.
3. Layering: no module that src/core, src/kernel or src/main.fs loads,
   directly or through other modules, is under src/author (the checker never
   loads the authoring program).
4. Corpus: the round trip over every term of the term printer's cases
   (tests/present/print-case-list.fs, built as Lean builds them, corpus-
   cases.fs) and over every declaration of the five pinned Lean exports
   (tests/reference/*.ndjson, corpus-lean.fs): print as words, run in a new
   context, compare the terms and the printed text.
5. --lean: for each fixture with a Lean source tests/reference/author-STEM.lean,
   pinned Lean (-DwarningAsError=true) compiles it. Term for term
   (lean_terms.py), against Lean's own declarations (a Lean metaprogram) and
   against the pinned exporter's (lean4export 3.1.0, the toolchain's
   leanexport; apart from binder names and kinds, which that exporter
   merges): each theorem, definition and axiom the fixture makes must have
   exactly Lean's universe parameters, statement and proof (every node,
   index, constant, universe argument, level, binder name and binder kind;
   dump.fs's format), and each import stub Lean's universe parameters and,
   when it states one, Lean's type; each is protected exactly when Lean's
   is; the binder names listed in KNOWN_NAMES are read as Lean's. As text:
   Lean's #print of every declaration must equal the fixture's lean: lines,
   apart from the differences listed in KNOWN, each with its reason.
6. --faults: each planted fault, in a copy of src/, must be caught: a unit
   test of tests/author/author.fs fails, or a fixture's output changes (a
   round trip, a term or a lean: line compared with Lean, or a fixture that
   no longer runs). Some must be caught by the comparison with Lean: the
   spelling check disabled (the round trip cannot see it, ADR 0017 §13),
   every universe argument 0 (the printed text hides universe arguments)
   and the three name-resolution faults (16-namespaces.lf and
   18-protected.lf); a fixture that Lean accepts and the faulty words
   refuse counts as a difference.
Finite evidence about these files; it never accepts a theorem.
"""
import json
import os
import pathlib
import re
import shutil
import subprocess
import sys
import tempfile

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from lean_terms import (Export, ExportError, compile_and_export, parse_dumps,  # noqa: E402
                        structural)
TEST_LIMIT = int(os.environ.get("TEST_TIMEOUT", "1800"))  # seconds; make exports it

GFORTH = os.environ.get("GFORTH", "gforth")
if "/" in GFORTH:  # the planted faults run Gforth in a copy of the tree
    GFORTH = os.path.abspath(GFORTH)
LEAN = os.environ.get("LEAN", "lean")
HERE = pathlib.Path("tests/author")
GOLDEN = HERE / "fixtures.golden"
DOC = pathlib.Path("docs/programming/LEANFORTH_WORDS.md")
SAME = "round trip: terms, names, kinds, labels and notes same; printed text same"
# Fixtures that name the constants of Lean's library (plan task 8.2.1d), with
# the export they run against: a slice of Init (scripts/export.sh, Init and
# the names in INIT_SLICE, with their dependencies). The term printer has no
# types for a library's constants, so their arguments print explicitly; their
# Lean sources print with pp.explicit too.
INIT_SLICE = HERE / "init-slice.ndjson"
INIT_NAMES = ["Nat.add_comm", "Eq.refl", "HAdd.hAdd", "instHAdd", "instAddNat", "OfNat.ofNat",
              "instOfNatNat", "id", "Id", "True.intro", "And.intro", "Nat.rec", "Nat.succ",
              "congrArg"]
LIBRARIES = {stem: str(INIT_SLICE)
             for stem in ("07-add-comm", "14-case", "19-add-zero", "20-zero-add")}
LIBRARIES["08-monoid"] = str(HERE / "monoid-slice.ndjson")   # the class alone, made by Lean

# Lean's line -> the term printer's line, where they differ, with the reason.
PRIVATE = ("Lean prints a private declaration by its short name, marked private; the "
           "words have no private declarations and name it in full, numeric part and all")
TWICE = "_private.tests.reference.author-21-numeric-name.0.twice"
KNOWN = {
    "21-numeric-name": {
        "private theorem twice : ∀ (p : Prop), p → p :=":
            (f"theorem {TWICE} : ∀ (p : Prop), p → p :=", PRIVATE),
        "fun p h ↦ twice p h": (f"fun p h ↦ {TWICE} p h", PRIVATE),
    },
}

# (name, who must catch it, [(file, old text, new text), ...]): one deliberate
# bug each. "any": a unit test or a fixture's output; "lean": the comparison
# with Lean. The faults after the first seven each undo one fix of the
# review of 2026-11-03 (findings 1-7).
VALUES = "src/author/values.fs"
GROUPS = "src/author/groups.fs"
SPACES = "src/author/namespaces.fs"
DECLS = "src/author/declarations.fs"
PRINT = "src/present/print-forth.fs"
FAULTS = [
    ("implicit kind lost", "any",
     [(PRINT, 'lf-binder-implicit of s" implicit:"', 'lf-binder-implicit of s" explicit:"')]),
    ("-> for a used binder", "any",
     [(PRINT, "lf-term-second@ 0 lf-pp-loose? >r 0= r> ;", "drop true outcome-ok ;")]),
    ("universe arguments dropped", "any",
     [(PRINT, "lf-pp-const-levels 0= if outcome-invalid r> 0 exit then 0 r> lf-pf-args ;",
       "drop outcome-ok r> 0 exit lf-pp-const-levels 0= if outcome-invalid r> 0 exit then"
       " 0 r> lf-pf-args ;")]),
    ("labels and notes not printed", "any",
     [(PRINT, ": lf-pf-notes-after ( outcome term -- outcome ) swap ok-then? if lf-pf-notes then ;",
       ": lf-pf-notes-after ( outcome term -- outcome ) drop ;")]),
    ("$ swaps function and argument", "any",
     [("src/author/words.fs", ": lfa-fn-arg ( f a -- tf ta ) swap lfa>function swap lfa>term ;",
       ": lfa-fn-arg ( f a -- tf ta ) lfa>term swap lfa>function ;")]),
    ("-> does not shift", "any",
     [("src/author/build.fs", "over lf-term-first@ swap < if exit then", "drop exit")]),
    ("spelling check ignored", "lean",
     [(GROUPS, "if swap lfa-key-spelling rot lfa-spelling compare 0= else 2drop false then ;",
       "if 2drop true else 2drop false then ;")]),
    ("1: a value used twice", "any",
     [(VALUES, "  dup lfa-item-taken @ 0= lfa-e-not-value lfa-must true over lfa-item-taken ! ;",
       "  ;")]),
    ("1: a variable used outside its binder", "any",
     [(VALUES, ": lfa-in-scope ( slot -- slot ) dup lfa-depth < lfa-e-not-value lfa-must ;",
       ": lfa-in-scope ( slot -- slot ) ;")]),
    ("2: a dotted declaration's body outside its namespace", "lean",
     [(DECLS, "lfa-inside? if lfa-full lfa-cut else lfa-current-space\n  then ;",
       "lfa-current-space ;")]),
    ("2: the root and open namespaces before the namespace around", "lean",
     [(SPACES, "  lfa-const-around if true exit then lfa-const-open",
       "  2drop lfa-const-open")]),
    ("3: names that are numbers", "any",
     [(SPACES, "  2dup lfa-number-like? 0= lfa-e-bad-name lfa-must ;", "  ;"),
      (GROUPS, "  2dup lfa-number-like? 0= lfa-e-bad-name lfa-must\n", ""),
      (DECLS, "0<> -rot lfa-number-like? 0= and ;", "0<> nip nip ;")]),
    ("4: numbers not checked before a word or at the end of a line", "any",
     [(GROUPS, "  lfa-unread-to 2dup lfa-stray nip 0= if lfa-numerals-read exit then\n"
               "  lfa-stray 2dup lfa-token! lfa-stray-code lfa-fail ;", "  drop ;")]),
    ("4: Gforth 1.0's recognizers left as they are", "any",
     [("src/author/runner.fs", "['] lfa-recognize is rec-forth ;", ";")]),
    ("5: an unclosed ( comment", "any",
     [("src/author/words.fs", "[char] ) parse lfa-closed? lfa-e-comment-end lfa-must",
       "[char] ) parse 2drop")]),
    ("5: leading zeros in numeric name parts", "any",
     [(DECLS, "  2dup lfa-leading-zero? 0= lfa-e-bad-name lfa-must\n", "")]),
    ("5: declarations not told apart by name", "any",
     [(DECLS, ": lfa-declared? ( name -- flag ) lfa-decl-find dup if nip then ;",
       ": lfa-declared? ( name -- flag ) drop false ;")]),
    ("5: labels and notes printed whatever their text", "any",
     [(PRINT, "  dup lf-pf-spellable-note? 0= if drop outcome-unsupported exit then\n", "")]),
    ("6: a long line reported at the line before", "any",
     [("src/author/runner.fs",
       "  lfa-line! lfa-the-line lfa-next-token lfa-token! 2drop lfa-e-line lfa-fail ;",
       "  2drop lfa-e-line lfa-fail ;")]),
    ("6: an unknown token reported after the number-like ones", "any",
     [(GROUPS, "2dup lfa-plain-decimal? 0= if 2swap 2drop exit then",
       "2dup lfa-number-like? 0= if 2swap 2drop exit then")]),
    ("6: a value left below the parameters", "any",
     [(DECLS, ": lfa-params-tight ( -- ) lfa-depth 0 ?do i lfa-no-gap loop ;",
       ": lfa-params-tight ( -- ) ;")]),
    ("re-review: a protected constant found by one part through a namespace", "lean",
     [(SPACES, "  dup lfa-hidden? if drop false else true then ;", "  true ;")]),
    ("re-review: protected not printed", "any",
     [(PRINT, ": lf-pf-modifier ( decl -- ) lf-fdecl-protected @ if s\" protected \" lf-pp-put"
              " then ;", ": lf-pf-modifier ( decl -- ) drop ;")]),
    ("7: every universe argument is 0", "lean",
     [(VALUES, "  >r dup lf-level-identity drop swap lfa-sought-ref lfa-ref-pairs",
       "  >r drop 0 dup lf-level-identity drop swap lfa-sought-ref lfa-ref-pairs")]),
]


class Failure(Exception):
    pass


def fixtures():
    return sorted(HERE.glob("*.lf"))


def run_word(fixture):
    """The driver and its word for the fixture: with the library it names, if any."""
    library = LIBRARIES.get(pathlib.Path(fixture).stem)
    if library:
        return "tests/author/report-library.fs", f's" {library}" s" {fixture}" report-with'
    return "tests/author/report.fs", f's" {fixture}" report'


def report(fixture, root="."):
    driver, word = run_word(fixture)
    command = [GFORTH, driver, "-e", f"{word} bye"]
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
    check_records(texts)


# ---- The records the kernel is given (src/author/export.fs; H1 of the
# review of 2026-11-12): each fixture's record: lines, read as an export,
# against the terms the words built (here) and against pinned Lean's export
# of the fixture's Lean source (check_lean).
def forth_records(text):
    """The records export.fs wrote for a fixture (its record: lines)."""
    lines = [line[len("record: "):] for line in text.splitlines() if line.startswith("record: ")]
    try:
        return Export(lines, leanforth=True)
    except (ExportError, KeyError, ValueError) as error:
        raise Failure(f"the records do not read as an export: {error!r}") from error


def own_terms(text):
    """The fixture's own theorems, definitions and axioms (term: lines), not its stubs."""
    return {name: decl for name, decl in forth_terms(text).items() if decl[0] != STUB}


def records_differ(stem, text):
    """Where the records differ from the words' terms: each theorem, definition
    and axiom written once, in file order, with its kind, universe parameters,
    type and value node for node (binder names and kinds too); nothing else."""
    records, own = forth_records(text), own_terms(text)
    if records.order != list(own) or "\nrecords: " in text:
        return [f"{stem}: records declare {records.order}, the words {list(own)}"]
    try:
        return [f"{stem}: {name}: {what}\n  record: {want}\n  words: {got}"
                for name, decl in own.items()
                for what, got, want in term_parts(decl, records.declaration(name), lambda t: t)
                if got != want]
    except (ExportError, KeyError) as error:
        return [f"{stem}: a record names what no record before it holds: {error!r}"]


def check_records(texts):
    differ = [line for stem, text in sorted(texts.items()) if text.startswith("ran: ok")
              for line in records_differ(stem, text)]
    if differ:
        raise Failure("the records differ from the words' terms:\n" + "\n".join(differ))
    decls = sum(len(own_terms(text)) for text in texts.values() if text.startswith("ran: ok"))
    print(f"export records: {decls} declarations of the fixtures written as the words built "
          "them (kind, universe parameters, type and value, node for node)")


def lean_records_differ(stem, text, export):
    """Where the records differ from pinned Lean's export of the fixture's Lean
    source: each declaration's whole record (kind, name, all, levelParams,
    hints, safety, type and value apart from binder names and kinds)."""
    records = forth_records(text)
    return [f"{stem}: {name}: record\n  Lean's export: {want}\n  LeanForth's:   {got}"
            for name in own_terms(text)
            for got, want in [(records.resolved(name), export.resolved(name))] if got != want]


DUMP = (": dump ( -- ) lfa-catalogue begin dup lfa-last? 0= while dup lfa-message-code @ 0 .r"
        " 9 emit dup lfa-message-text type cr lfa-message-next repeat drop ; dump bye")


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
    """Every source file path loads, transitively, including itself. A
    target that is not a file of the checkout is a file of the Forth host
    (tasker.fs, which src/lib/task.fs loads on Gforth 0.7.3)."""
    path = path.resolve()
    if path in seen or not path.exists():
        return seen
    seen.add(path)
    for target in REQUIRE.findall(path.read_text(encoding="utf-8")):
        loads(path.parent / target, seen)
    return seen


def check_layering():
    """The kernel never loads the words (ADR 0017 Amendment 1: since plan task
    8.2.1c the command line does, through src/cli/check-lf.fs, so main.fs does
    too; the kernel, the data model and the importer must not)."""
    roots = sorted(pathlib.Path("src/core").glob("*.fs")) + \
        sorted(pathlib.Path("src/kernel").glob("*.fs")) + \
        sorted(pathlib.Path("src/import").glob("*.fs"))
    author = pathlib.Path("src/author").resolve()
    for root in roots:
        bad = [p for p in loads(root, set()) if author in p.parents]
        if bad:
            raise Failure(f"{root} loads the authoring program: {bad[0]}")
    lf = pathlib.Path("src/cli/check-lf.fs")
    if not any(author in p.parents for p in loads(lf, set())):
        raise Failure(f"{lf} no longer loads the authoring words: update this check")
    print(f"layering: none of {len(roots)} checker modules (core/, kernel/, import/) "
          "loads src/author; the command line does (cli/check-lf.fs)")


def check_corpus():
    sys.path.insert(0, "tests/present")
    sys.path.insert(0, "tests/support")
    from present_transport import encode
    from ndjson_preview import preview
    run = subprocess.run([GFORTH, "tests/author/corpus-cases.fs"], stdin=subprocess.DEVNULL,
                         capture_output=True, text=True, timeout=TEST_LIMIT)
    cases = [line for line in run.stdout.splitlines() if line.startswith("case ")]
    bad = [line for line in cases if not line.endswith(SAME)]
    if run.returncode != 0 or not cases or bad:
        raise Failure("corpus cases:\n" + run.stdout + run.stderr)
    fixtures = ("identity", "composition", "type-identity", "poly-identity", "constant-fixture")
    for name in fixtures:
        with open(f"tests/reference/{name}.ndjson", "rb") as stream:
            data = encode(preview(stream))
        run = subprocess.run([GFORTH, "tests/author/corpus-lean.fs"], input=data,
                             capture_output=True, timeout=120)
        out = run.stdout.decode("utf-8") + run.stderr.decode("utf-8")
        if run.returncode != 0 or out.strip().splitlines()[-1:] != [SAME]:
            raise Failure(f"corpus {name}:\n{out}")
    print(f"corpus round trips: {len(cases)} printer cases and the declarations of "
          f"{len(fixtures)} Lean exports give the same terms and text")


LF_EXPORTS = [f"tests/reference/{name}.ndjson" for name in
              ("identity", "composition", "type-identity", "poly-identity",
               "constant-fixture")] + ["tests/reference/inductive/nat-add-zero.ndjson",
                                    "tests/author/lf-root-constants.ndjson"]
LF_LINE_START = ("kernel-form", "\\ ", "  ", ":=", "theorem ", "def ", "axiom ", "import-stub ", "end ", "protected ")


def print_lf(export):
    """`leanforth print --lf` of an export: (the text, what it listed on stderr)."""
    run = subprocess.run(["bin/leanforth", "print", "--lf", "--no-manifest", str(export)],
                         stdin=subprocess.DEVNULL, capture_output=True, timeout=TEST_LIMIT)
    # 2 (unsupported) exactly when a declaration was not written (review N3).
    stubbed = b"\nnote: the text is not the export: " in b"\n" + run.stderr
    if run.returncode != (2 if stubbed else 0):
        raise Failure(f"print --lf {export}: exit {run.returncode}:\n"
                      + run.stderr.decode("utf-8", "replace"))
    return run.stdout.decode("utf-8"), run.stderr.decode("utf-8")


def lf_terms(text):
    """The declarations the words make of the written text: name -> dumps."""
    with tempfile.TemporaryDirectory() as work:
        path = pathlib.Path(work) / "export.lf"
        path.write_text(text, encoding="utf-8")
        run = subprocess.run([GFORTH, "tests/author/terms.fs", "-e", f's" {path}" terms-run bye'],
                             stdin=subprocess.DEVNULL, capture_output=True, timeout=TEST_LIMIT)
    out = run.stdout.decode("utf-8", "replace")
    if run.returncode != 0 or not out.startswith("ran: ok\n"):
        raise Failure("the written text does not run:\n" + out[:600] + run.stderr.decode()[:300])
    return forth_terms(out)


def check_lf_text(name, text):
    """Every line of the text is a comment, a declaration line or blank, and no
    character the text rule bans (a line end, a bidirectional control) is in it."""
    for line in text.splitlines():
        if line and not line.startswith(LF_LINE_START):
            raise Failure(f"{name}: a line that starts no declaration word: {line[:60]!r}")
    if re.search("[  ‪-‮⁦-⁩\r\x00]", text):
        raise Failure(f"{name}: a banned character in the written text")


def check_export_lf(export):
    """The text written for the export reads back to the export's own terms: each
    theorem, def and axiom with its universe parameters, type and value, each
    import stub with its universe parameters and (when it has one) type, node for
    node; every declaration is written, stubbed or listed as not written at all."""
    text, listing = print_lf(export)
    check_lf_text(str(export), text)
    forth = lf_terms(text)
    lean = Export(pathlib.Path(export).read_text(encoding="utf-8").splitlines())
    for name, decl in forth.items():
        if name not in lean.decls:
            raise Failure(f"{export}: {name} is not in the export")
        want = lean.declaration(name)
        for what, got, expected in term_parts(decl, want, lambda t: t):
            if got != expected:
                raise Failure(f"{export}: {name}: {what}\n  export: {expected}\n  text: {got}")
    unstubbed = text.count("no import-stub could be written either")
    if len(forth) + unstubbed != len(lean.decls):
        raise Failure(f"{export}: {len(forth)} written or stubbed and {unstubbed} listed, "
                      f"of {len(lean.decls)} declarations")
    whole = sum(1 for _, (kind, *_rest) in forth.items() if kind != STUB)
    return len(lean.decls), whole, len(forth) - whole


def craft(source, work):
    """The identity export with names that would break a line: a line feed and a
    right-to-left override in binder names, a line end in the declaration's name."""
    text = pathlib.Path(source).read_text(encoding="utf-8")
    for old, new in (('"str":"P"', '"str":"P\\u202ex"'), ('"str":"proof"', '"str":"p\\nq"'),
                     ('"str":"identity"', '"str":"id\\nfake: accepted"')):
        assert old in text
        text = text.replace(old, new)
    path = pathlib.Path(work) / "crafted.ndjson"
    path.write_text(text, encoding="utf-8")
    return path


def named(source, work, spelling):
    """The identity export with its declaration named by the JSON string spelling."""
    text = pathlib.Path(source).read_text(encoding="utf-8")
    assert '"str":"identity"' in text
    path = pathlib.Path(work) / "named.ndjson"
    path.write_text(text.replace('"str":"identity"', f'"str":"{spelling}"'), encoding="utf-8")
    return path


def check_lf_names():
    """A part between guillemets («1», «ab») has no spelling: listed as not written, never
    printed as text the reader takes for another name or stops at. A Zs space or filler
    in a name is written and read back exactly. Constants of a dotted declaration are
    written with root: (lf-root-constants.ndjson, in LF_EXPORTS)."""
    with tempfile.TemporaryDirectory() as work:
        for spelling in ("\u00ab1\u00bb", "\u00abab\u00bb", "A.\u00ab12\u00bb.f"):
            text, listing = print_lf(named("tests/reference/identity.ndjson", work, spelling))
            if "not written: " not in text or "\nend " in text:
                raise Failure(f"name {spelling}: written as text instead of listed")
            lf_terms(text)
        for spelling in ("a\u00a0b", "a\u3164b", "a\u0301"):
            text, _ = print_lf(named("tests/reference/identity.ndjson", work, spelling))
            name = json.loads(f'"{spelling}"')
            if name not in lf_terms(text):
                raise Failure(f"name {spelling}: not read back as the same name")


def check_lf_crafted():
    check_lf_names()
    with tempfile.TemporaryDirectory() as work:
        text, listing = print_lf(craft("tests/reference/identity.ndjson", work))
    check_lf_text("crafted names", text)
    lf_terms(text)  # what is left still runs
    if "fake: accepted" in "\n".join(line for line in text.splitlines()
                                     if not line.startswith("\\ ")):
        raise Failure("crafted names: a name reached a line of its own")
    if "not written: " not in text:
        raise Failure("crafted names: the declaration was neither written nor listed")


def check_lf_files():
    counts = [check_export_lf(export) for export in LF_EXPORTS]
    check_lf_crafted()
    print(f"export to LeanForth: {len(counts)} exports written and read back to their own "
          f"terms ({sum(c[0] for c in counts)} declarations: {sum(c[1] for c in counts)} "
          f"written whole, {sum(c[2] for c in counts)} as import stubs); crafted names "
          "break no line")


def forth_lean(text):
    return [line[len("lean: "):] for line in text.splitlines() if line.startswith("lean: ")]


STUB = 3  # lf-decl-stub: an import stub stands for a constant of any kind


def forth_terms(text):
    """The fixture's declarations from its term: lines (dump.fs, without notes):
    name -> (kind, protected, universe names, type, value)."""
    lines = [line[len("term: "):] for line in text.splitlines() if line.startswith("term: ")]
    return parse_dumps(lines, int)


def term_parts(forth, lean, same):
    """(what, Forth's, Lean's) for each part compared; same maps a term to
    the form compared (exact, or structural for the exporter's, which does
    not say what is protected)."""
    kind, protected, universes, type_, value = forth
    lean_kind, lean_protected, lean_universes, lean_type, lean_value = lean
    parts = [("universe parameters", universes, lean_universes)]
    if lean_protected is not None:
        parts.append(("protected", protected, lean_protected))
    if kind != STUB:
        parts += [("kind", kind, lean_kind), ("type", same(type_), same(lean_type)),
                  ("value", same(value), same(lean_value))]
    elif type_ != "none":
        parts.append(("type", same(type_), same(lean_type)))
    return parts


# A binder name a fixture uses where Lean's source has another, with the reason.
KNOWN_NAMES = {
    "12-hygienic-used": {
        "P._@.Main._hyg.#3":
            ("P", "the fixture gives a used binder a hygienic name, as Lean's elaborator "
                  "makes them, to test that the printer keeps it; Lean source cannot "
                  "write such a name"),
    },
}


def known_names(stem, decl):
    """decl with each binder name of KNOWN_NAMES[stem] read as Lean's."""
    kind, protected, universes, type_, value = decl
    for old, (new, _) in KNOWN_NAMES.get(stem, {}).items():
        type_, value = (re.sub(r"\((lam|pi) " + re.escape(old) + " ", rf"(\1 {new} ", term)
                        for term in (type_, value))
    return kind, protected, universes, type_, value


def compare_terms(stem, forth, lean):
    """Where the words' declarations differ from Lean's, term for term: from
    Lean's environment exactly, and from the pinned export apart from binder
    names and kinds (which the exporter merges)."""
    _, dumps, exported, _ = lean
    differ = []
    for name, decl in forth.items():
        decl = known_names(stem, decl)
        for source, ref, same in (("Lean", dumps, lambda t: t),
                                  ("Lean's export", exported, structural)):
            differ += [f"{stem}: {name}: {what}\n  {source}: {want}\n  Forth: {got}"
                       for what, got, want in term_parts(decl, ref[name], same) if got != want]
    return differ


def compared_terms(forth):
    """The number of declarations and of terms (types and values) compared."""
    terms = sum((kind != STUB or type_ != "none") + (kind != STUB)
                for kind, _, _, type_, _ in forth.values())
    return len(forth), terms


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


def lean_reference(texts):
    """For each fixture with a Lean source: Lean's #print lines, and Lean's
    exported declarations of the names the fixture declares (the fixture
    must have run)."""
    reference = {}
    with tempfile.TemporaryDirectory() as workdir:
        for path in fixtures():
            source = pathlib.Path(f"tests/reference/author-{path.stem}.lean")
            if not source.exists():
                continue
            names = list(forth_terms(texts[path.stem]))
            if not names:
                raise Failure(f"{path.stem}: the fixture did not run; nothing to compare")
            try:
                printed, dumps, export = compile_and_export(LEAN, source, names, workdir)
                exported = {name: export.declaration(name) for name in names}
            except ExportError as error:
                raise Failure(str(error)) from error
            reference[path.stem] = (printed, dumps, exported, export)
    return reference


def flat(lines):
    """Lean's #print lines with each continuation (an indented line, where
    Lean's formatter broke a line at a space) joined to the line before."""
    out = []
    for line in lines:
        if line.startswith("  ") and out:
            out[-1] += " " + line.strip()
        else:
            out.append(line)
    return out


def library_lines(printed, lines):
    """A fixture with a library (review L4): the term printer has no types for
    the library's constants, so it shows every argument and marks each such
    application with @; the Lean source prints with pp.explicit, which marks
    only those with implicit arguments, and a raw literal n as nat_lit n,
    where the term printer writes n. Compared joined, without @ and nat_lit."""
    lean = [re.sub(r"\(nat_lit (\d+)\)", r"\1", line) for line in flat(printed)]
    return [line.replace("@", "") for line in lean], [line.replace("@", "") for line in lines]


def lean_differences(stem, reference, text):
    """The lean: lines (for a fixture with a library as library_lines says),
    the terms and the records."""
    printed, lines = reference[stem][0], forth_lean(text)
    if stem in LIBRARIES:
        printed, lines = library_lines(printed, lines)
    return (compare(stem, printed, lines),
            compare_terms(stem, forth_terms(text), reference[stem]),
            lean_records_differ(stem, text, reference[stem][3]))


def check_lean_records(texts, reference):
    differ = [line for stem in reference for line in records_differ(stem, texts[stem])
              + lean_records_differ(stem, texts[stem], reference[stem][3])]
    if differ:
        raise Failure("records differ from pinned Lean's export:\n" + "\n".join(differ))
    decls = sum(len(own_terms(texts[stem])) for stem in reference)
    print(f"export records equal pinned Lean's export of the Lean sources: {decls} "
          f"declarations of {len(reference)} fixtures (kind, name, levelParams, hints, "
          "safety, type and value)")


def check_records_only():
    """--records: the records against the words' terms and, with LEAN set,
    against pinned Lean's export (the writer's planted faults run this)."""
    texts = outputs()
    check_records(texts)
    if os.environ.get("LEAN"):
        check_lean_records(texts, lean_reference(texts))


def check_lean():
    texts = outputs()
    reference = lean_reference(texts)
    lines = decls = terms = 0
    for stem, (printed, _, _, _) in reference.items():
        differ_text, differ_terms, _ = lean_differences(stem, reference, texts[stem])
        if differ_terms:
            raise Failure("terms differ from pinned Lean's export:\n" + "\n".join(differ_terms))
        if differ_text:
            raise Failure("lean: lines differ from pinned Lean:\n" + "\n".join(differ_text))
        counted = compared_terms(forth_terms(texts[stem]))
        shown = len(flat(printed) if stem in LIBRARIES else printed)
        decls, terms, lines = decls + counted[0], terms + counted[1], lines + shown
    known = sum(len(v) for v in KNOWN.values())
    names = sum(len(v) for v in KNOWN_NAMES.values())
    print(f"authoring words build Lean's terms, term for term: {decls} declarations of "
          f"{len(reference)} fixtures, {terms} terms (statements, proofs, stubs' stated types), "
          "equal to Lean's own (which are protected, binder names and kinds included; "
          f"{names} listed binder name) and to the pinned export (apart from binder names "
          "and kinds, which that exporter merges)")
    print(f"authoring words agree with pinned Lean's #print: {lines} lines "
          f"({known} known printer differences, listed with their reasons; the "
          f"{len(LIBRARIES)} fixtures with a library compared without @ and line breaks)")
    check_lean_records(texts, reference)


# ---- LeanForth text checked by the kernel (plan tasks 8.2.1c-d; ADR 0017
# Amendments 1 and 2): `leanforth check [--env EXPORT] FILE.lf`.
WRONG = HERE / "wrong"
# Fixtures that stop before anything is checked, with check's exit code: a
# mistake in the text (4), a stub (4: error 48), a line too long (3: full).
TEXT_EXIT = {"10a-missing-app": 4, "10b-typo": 4, "10c-universe": 4, "10d-case": 4,
             "13-structure-ctor": 4, "17-long-line": 3}
VERDICT = re.compile(r"^(?!error:)(\S+): "
                     r"(accepted|rejected|unsupported|unknown|exhausted|full|invalid)", re.M)
WRONG_LIBRARIES = {"07-add-comm": str(INIT_SLICE), "19-add-zero": str(INIT_SLICE),
                   "20-zero-add": str(INIT_SLICE)}


def library_of(path):
    return LIBRARIES.get(path.stem) if path.parent == HERE else WRONG_LIBRARIES.get(path.stem)


def leanforth_check(path, library=None, *options):
    """bin/leanforth check of a text: (exit code, its output)."""
    command = ["bin/leanforth", "check", *options]
    command += ["--env", library] if library else []
    run = subprocess.run(command + [str(path)], stdin=subprocess.DEVNULL, capture_output=True,
                         timeout=TEST_LIMIT)
    return run.returncode, run.stdout.decode("utf-8", "replace") + run.stderr.decode()


def printed_name(name):
    """A dump's name (#N a numeric part) as check prints it, guillemets aside."""
    return re.sub(r"(^|\.)#(\d+)", r"\1\2", name)


def own_verdicts(path, out):
    """(name, verdict or None) for each of the text's own theorems, definitions
    and axioms, by name (review L3): the names from the words' run of the
    text (report.fs), the verdicts from check's lines."""
    found = {name.replace("«", "").replace("»", ""): verdict
             for name, verdict in VERDICT.findall(out)}
    names = [printed_name(name) for name in own_terms(report(str(path)))]
    return [(name, found.get(name)) for name in names]


def text_checked(path, want_code, want_verdict):
    code, out = leanforth_check(path, library_of(path))
    if code != want_code:
        raise Failure(f"check {path}: exit {code}, want {want_code}:\n{out[-600:]}")
    verdicts = own_verdicts(path, out) if want_verdict else []
    if want_verdict and (not verdicts or any(v != want_verdict for _, v in verdicts)):
        raise Failure(f"check {path}: not every declaration {want_verdict}: {verdicts}\n"
                      f"{out[-600:]}")
    if code in (2, 3, 4) and (VERDICT.search(out) or "was not checked" not in out):
        raise Failure(f"check {path}: a failed text must not be checked:\n{out[-600:]}")
    return out


def check_texts():
    """Every fixture checked as text: those whose Lean source pinned Lean
    accepts are accepted (exit 0), the others stop with their error; every
    wrong twin is rejected (exit 1)."""
    for path in fixtures():
        want = TEXT_EXIT.get(path.stem, 0)
        text_checked(path, want, "accepted" if want == 0 else None)
    wrong = sorted(WRONG.glob("*.lf"))
    for path in wrong:
        text_checked(path, 1, "rejected")
    print(f"leanforth check FILE.lf: {len(fixtures()) - len(TEXT_EXIT)} fixtures accepted, "
          f"{len(TEXT_EXIT)} stopped before any check, {len(wrong)} wrong twins rejected")


# A constant of the Init slice whose name has a numeric part (lfc-part's
# numeric branch, review L4).
NUMERIC = "_private.Init.Data.Nat.Basic.0.Nat.zero_add.match_1_1"


# Texts written here, each with check's options, library, exit code and a
# line the output must hold: every outcome of a text and of the command.
def cli_cases():
    slice_ = str(INIT_SLICE)
    head = "theorem t\n  Nat explicit: n\n  Eq 1 ^ Nat $ n $ n $\n:=\n"
    return [
        ("axiom", "axiom ax\n  Prop implicit: P  P\nend ax\n"
         "theorem uses\n  Prop implicit: Q  Q\n:=\n  ax Q $\nend uses\n", [], None, 0,
         "uses: accepted; axioms: unlisted; NOT PROVED: depends on ax"),
        ("axiom strict", "axiom ax\n  Prop implicit: P  P\nend ax\n"
         "theorem uses\n  Prop implicit: Q  Q\n:=\n  ax Q $\nend uses\n", ["--strict-axioms"],
         None, 6, "NOT PROVED"),
        ("library refl", head + "  Eq.refl 1 ^ Nat $ n $\nend t\n", [], slice_, 0,
         "t: accepted"),
        ("library, a long word in comments", head + "  Eq.refl 1 ^ Nat $ n $  ( https://"
         + "a" * 320 + " )  note\" " + "b" * 320 + "\"\nend t\n", [], slice_, 0, "t: accepted"),
        ("library wrong case", head + "  eq.refl 1 ^ Nat $ n $\nend t\n", [], slice_, 4,
         "error 1 at line:col 5:3 (token `eq.refl`)"),
        ("library typo", head + "  Eq.reff 1 ^ Nat $ n $\nend t\n", [], slice_, 4,
         "error 1 at line:col 5:3"),
        ("library name taken", "theorem Nat.add_comm\n  Prop explicit: p p\n:=\n  p\n"
         "end Nat.add_comm\n", [], slice_, 4, "error 28 at line:col 1:21"),
        ("library name with a numeric part taken", f"theorem {NUMERIC}\n  Prop explicit: p p\n"
         f":=\n  p\nend {NUMERIC}\n", [], slice_, 4, "error 28 at line:col 1:21"),
        ("library name with another numeric part", head + "  "
         + NUMERIC.replace(".0.", ".1.") + "\nend t\n", [], slice_, 4, "error 1 at line:col 5:3"),
        ("1024 records, the library's among them", "".join(
            f"axiom a{i} Prop end a{i}\n" for i in range(1022)) + head
         + "  Eq.refl 1 ^ Nat $ n $\nend t\n", [], slice_, 3,
         "error 66 at line:col 1025:3 (token `Eq`)"),
        ("library unread manifest", "theorem t Prop explicit: p p explicit: h p := "
         "identity p $ h $ end t\n", ["--no-manifest"], "tests/reference/identity.ndjson", 0,
         "t: accepted"),
        ("a library name of no declaration", "theorem t Prop explicit: p p := proof end t\n",
         ["--no-manifest"], "tests/reference/identity.ndjson", 4,
         "error 1 at line:col 1:45 (token `proof`)"),
        ("library not an export", "theorem t Prop explicit: p p := p end t\n",
         ["--no-manifest"], "tests/author/01-identity.lf", 4,
         "error: invalid: unexpected character (line 1, byte 0)"),
        ("open of a library namespace, a gap (8.2.1d)", "open Nat\n" + head
         + "  Eq.refl 1 ^ Nat $ n $\nend t\n", [], slice_, 4,
         "error 26 at line:col 1:18 (token `Nat`)"),
        ("library short name", "namespace Eq\n" + head + "  refl 1 ^ Nat $ n $\nend t\n"
         "end Eq\n", [], slice_, 2, "error 55 at line:col 6:3 (token `refl`)"),
        ("stub with library", "import-stub Nat end Nat\n", [], slice_, 4,
         "error 48 at line:col 1:13 (token `import-stub`)"),
        ("stub alone", "protected import-stub N.x end N.x\n", [], None, 4, "error 48"),
        ("nothing", "\\ a comment\n", [], None, 4, "error 49"),
        ("error after a good one", "theorem t\n  Prop explicit: p  p\n:=\n  p\nend t\n"
         "theorem u\n  Prop\n:=\n  x\nend u\n", [], None, 4,
         "the LeanForth text was not checked: error 1 at line:col 9:3 (token `x`)"),
        ("error after a good one, outside", "theorem t\n  Prop implicit: P  P explicit: h  P\n"
         ":=\n  h\nend t\nnope\n", [], None, 4,
         "the LeanForth text was not checked: error 1 at line:col 6:1 (token `nope`)"),
        ("not supported", "theorem t\n  Prop explicit: p  p\n:=\n  p let:\nend t\n", [], None,
         2, "error 51 at line:col 4:5 (token `let:`)"),
        ("bare projection leaf", "axiom S 0 Type end S\ndef d\n  0 Type\n:=\n  0 proj# S\nend d\n",
         [], None, 4, "error 56 at line:col 6:1 (token `end`)"),
        ("unknown in library run", head + "  n\nend t\n" + "theorem u Prop := x end u\n",
         [], slice_, 4, "error 1"),
        ("fuel", (HERE / "20-zero-add.lf").read_text(encoding="utf-8"), ["--fuel", "50"],
         slice_, 3, "zero_add': exhausted"),
        ("jobs", (HERE / "07-add-comm.lf").read_text(encoding="utf-8"), ["--jobs", "2"],
         slice_, 0, "add_comm': accepted"),
        ("no library file", "theorem t Prop explicit: p p := p end t\n", [],
         "no-such-library.ndjson", 4, "error: cannot open the export"),
        ("json", "theorem t Prop explicit: p p := p end t\n", ["--json"], None, 4,
         "not with a text"),
    ]


# The texts above are in the kernel form, which their first line says
# (ADR 0021 D8): natural LeanForth is the default.
KERNEL = "kernel-form "


# Natural LeanForth (plan FE1a): read into syntax, then stopped as not
# supported yet where the elaborator meets a step it does not have (the
# numeral 0 without the elaboration data: error 139, plans FE1e5 and S2;
# exit 2), or refused as a mistake (exit 4); never checked.
def natural_cases():
    slice_ = str(INIT_SLICE)
    head = "theorem t\n  Nat explicit: n\n  0 n + n =\n:=\n"
    return [
        ("natural term proof", head + "  n Eq.refl\nend t\n", [], slice_, 2,
         "error 139 at line:col 6:1 (token `end`)"),
        ("natural tactic proof", head + "  by n by-induction\nend t\n", [], slice_, 2,
         "error 139 at line:col 6:1 (token `end`)"),
        ("natural ' and $", head + "  ' Nat.succ n $\nend t\n", [], slice_, 2,
         "error 139 at line:col 6:1 (token `end`)"),
        ("natural kernel word", "theorem t Prop explicit: p p := p end t\n", [], None, 2,
         "error 70 at line:col 1:11 (token `Prop`)"),
        ("natural by twice", head + "  by by\nend t\n", [], slice_, 4,
         "error 69 at line:col 5:6 (token `by`)"),
        ("natural ' before a number", head + "  ' 5\nend t\n", [], slice_, 4,
         "error 59 at line:col 5:3 (token `'`)"),
        ("natural arguments missing", head + "  Eq.refl\nend t\n", [], slice_, 4,
         "error 3 at line:col 5:3 (token `Eq.refl`)"),
        ("kernel-form inside", head + "  kernel-form\nend t\n", [], slice_, 4,
         "error 57 at line:col 5:3 (token `kernel-form`)"),
    ]


def check_text_cases():
    with tempfile.TemporaryDirectory() as work:
        for name, text, options, library, want, line in natural_cases():
            path = pathlib.Path(work) / "case.lf"
            path.write_text(text, encoding="utf-8")
            code, out = leanforth_check(path, library, *options)
            if VERDICT.search(out) or code != want or line not in out:
                raise Failure(f"natural case {name}: exit {code} (want {want}), "
                              f"want the line {line!r}:\n{out[-800:]}")
        for name, text, options, library, want, line in cli_cases():
            path = pathlib.Path(work) / "case.lf"
            path.write_text(KERNEL + text, encoding="utf-8")
            code, out = leanforth_check(path, library, *options)
            if want == 4 and VERDICT.search(out):
                raise Failure(f"check case {name}: a verdict beside an error:\n{out[-800:]}")
            if code != want or line not in out:
                raise Failure(f"check case {name}: exit {code} (want {want}), "
                              f"want the line {line!r}:\n{out[-800:]}")
        code, out = leanforth_check(HERE / "01-identity.lf", None, "--env")
        if code != 4:
            raise Failure(f"--env without its export: exit {code}")
        run = subprocess.run(["bin/leanforth", "check", "--env", str(INIT_SLICE),
                              "tests/reference/composition.ndjson"], stdin=subprocess.DEVNULL,
                             capture_output=True, timeout=TEST_LIMIT)
        if run.returncode != 4 or b"--env goes only with a LeanForth text" not in run.stdout:
            raise Failure(f"--env with an export: exit {run.returncode}")
        check_snapshot_cases(pathlib.Path(work))
    print(f"leanforth check FILE.lf: {len(cli_cases()) + 5} cases of every outcome and misuse, "
          f"a snapshot as the library among them; {len(natural_cases())} natural-form cases "
          "stopped, never checked")


def check_snapshot_cases(work):
    """The library from a snapshot of the Init slice (check --snapshot FILE
    FILE.lf): its declarations taken from it, the text's checked."""
    snap = work / "slice.lfsnap"
    subprocess.run(["bin/leanforth", "check", "--save-snapshot", str(snap), str(INIT_SLICE)],
                   stdin=subprocess.DEVNULL, capture_output=True, timeout=TEST_LIMIT, check=True)
    code, out = leanforth_check(HERE / "07-add-comm.lf", None, "--snapshot", str(snap))
    taken = "60 declarations: 60 accepted; 59 from the snapshot, 1 checked in this run"
    if code != 0 or taken not in out or "add_comm': accepted (checked in this run, uses " \
            "results from the snapshot); axioms: none" not in out:
        raise Failure(f"07-add-comm.lf against a snapshot: exit {code}:\n{out[-800:]}")
    code, out = leanforth_check(WRONG / "07-add-comm.lf", None, "--snapshot", str(snap))
    if code != 1 or "add_comm': rejected" not in out:
        raise Failure(f"the wrong twin against a snapshot: exit {code}:\n{out[-800:]}")
    code, out = leanforth_check(HERE / "07-add-comm.lf", str(INIT_SLICE), "--snapshot", str(snap))
    if code != 4 or "not with a text" not in out:
        raise Failure(f"--env with --snapshot: exit {code}:\n{out[-400:]}")
    # Natural text against the snapshot's library (review fe1ab L4): the
    # argument counts come from the snapshot's tier (Eq.refl takes one);
    # without the elaboration data the elaborator stops at end (139).
    natural = work / "natural.lf"
    for proof, want, line in (("  n Eq.refl\n", 2, "error 139 at line:col 6:1 (token `end`)"),
                              ("  Eq.refl\n", 4, "error 3 at line:col 5:3 (token `Eq.refl`)")):
        natural.write_text("theorem t\n  Nat explicit: n\n  n n =\n:=\n" + proof + "end t\n",
                           encoding="utf-8")
        code, out = leanforth_check(natural, None, "--snapshot", str(snap))
        if code != want or line not in out or VERDICT.search(out):
            raise Failure(f"natural text against a snapshot: exit {code} (want {want}):\n"
                          f"{out[-400:]}")


def check_wrong_lean():
    """Pinned Lean refuses every wrong twin's Lean source, as check rejects
    the text (check_texts)."""
    with tempfile.TemporaryDirectory() as work:
        for path in sorted(WRONG.glob("*.lf")):
            source = pathlib.Path(f"tests/reference/author-wrong-{path.stem}.lean")
            run = subprocess.run([LEAN, "-DwarningAsError=true", "-o",
                                  str(pathlib.Path(work) / "Wrong.olean"), str(source)],
                                 stdin=subprocess.DEVNULL, capture_output=True, text=True,
                                 timeout=TEST_LIMIT)
            if run.returncode == 0 or "error" not in run.stdout + run.stderr:
                raise Failure(f"pinned Lean accepts {source}, whose text check rejects")
    print(f"pinned Lean refuses all {len(list(WRONG.glob('*.lf')))} wrong twins, "
          "as leanforth check rejects them")


def check_slices():
    """scripts/export.sh with pinned Lean reproduces the two library exports
    the fixtures run against, byte for byte: a slice of Init and the class of
    08-monoid (its Lean source compiled, then MyMonoid.mul_one exported)."""
    with tempfile.TemporaryDirectory() as work:
        work = pathlib.Path(work)
        env = dict(os.environ, LEAN=LEAN, LEAN_PATH=str(work))
        run = subprocess.run([LEAN, "-DwarningAsError=true", "-o", str(work / "AuthorMonoid.olean"),
                              "tests/reference/author-08-monoid.lean"], stdin=subprocess.DEVNULL,
                             capture_output=True, timeout=TEST_LIMIT, env=env)
        if run.returncode != 0:
            raise Failure("pinned Lean refuses tests/reference/author-08-monoid.lean")
        for out, args in ((INIT_SLICE, ["Init", "--", *INIT_NAMES]),
                          (HERE / "monoid-slice.ndjson", ["AuthorMonoid", "--",
                                                          "MyMonoid.mul_one"])):
            made = work / out.name
            subprocess.run(["bash", "scripts/export.sh", str(made), *args], env=env,
                           stdin=subprocess.DEVNULL, capture_output=True, timeout=TEST_LIMIT,
                           check=True)
            for suffix in ("", ".manifest.json"):
                mine = pathlib.Path(str(out) + suffix).read_bytes()
                if pathlib.Path(str(made) + suffix).read_bytes() != mine:
                    raise Failure(f"scripts/export.sh does not reproduce {out}{suffix}")
    print("library exports reproduced byte for byte: tests/author/init-slice.ndjson, "
          "monoid-slice.ndjson and their manifests")


def planted(root, fault):
    """Plant a fault's edits in the copy; the original texts, to restore."""
    name, _, edits = fault
    originals = {}
    for path, old, new in edits:
        target = root / path
        text = target.read_text(encoding="utf-8")
        if text.count(old) != 1:
            raise Failure(f"fault {name}: the text to replace is not in {path} exactly once")
        originals.setdefault(target, text)
        target.write_text(text.replace(old, new), encoding="utf-8")
    return originals


def unit_tests_fail(root):
    run = subprocess.run([GFORTH, "tests/author/author.fs"], cwd=root, stdin=subprocess.DEVNULL,
                         capture_output=True, timeout=120)
    return run.returncode != 0


def fault_caught(fault, root, clean, reference):
    """What catches a planted fault: a list of findings, empty if nothing."""
    name, catcher, _ = fault
    if catcher == "any" and unit_tests_fail(root):
        return ["a unit test fails"]
    texts = outputs(root)
    lean = [stem for stem in reference if texts[stem].startswith("ran: ok")
            and any(lean_differences(stem, reference, texts[stem]))]
    refused = [stem for stem in reference if not texts[stem].startswith("ran: ok")]
    lean_found = [f"terms or #print differ from Lean's: {lean}"] if lean else []
    lean_found += [f"refused where Lean accepts: {refused}"] if refused else []
    if catcher == "lean":
        return lean_found
    return lean_found + [f"{stem}'s output changed" for stem in texts if texts[stem] != clean[stem]]


def check_faults():
    clean = outputs()
    reference = lean_reference(clean)
    with tempfile.TemporaryDirectory() as workdir:
        root = pathlib.Path(workdir)
        shutil.copytree("src", root / "src")
        shutil.copytree(HERE, root / "tests/author")
        shutil.copytree("tests/support", root / "tests/support")
        caught = 0
        for fault in FAULTS:
            originals = planted(root, fault)
            try:
                found = fault_caught(fault, root, clean, reference)
            finally:
                for target, text in originals.items():
                    target.write_text(text, encoding="utf-8")
            print(f"fault {fault[0]}: {'; '.join(found[:3]) or 'NOT CAUGHT'}")
            if not found:
                by = "by the comparison with Lean " if fault[1] == "lean" else ""
                raise Failure(f"fault {fault[0]} was not caught {by}")
            caught += 1
    print(f"planted faults: {caught} of {len(FAULTS)} caught")


def main(args):
    try:
        if "--lean" in args:
            check_lean()
            check_wrong_lean()
            check_slices()
        elif "--faults" in args:
            check_faults()
        elif "--records" in args:
            check_records_only()
        else:
            check_golden("--write" in args)
            if "--write" not in args:
                check_catalogue()
                check_layering()
                check_corpus()
                check_lf_files()
                check_texts()
                check_text_cases()
    except (Failure, OSError, subprocess.SubprocessError) as error:
        print(f"check_author: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
