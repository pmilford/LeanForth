#!/usr/bin/env python3
"""Tests of the LeanForth authoring words (plan task 8.1.2; make test, make check).

Usage (from the repository root; GFORTH and LEAN name the toolchains):
  python3 tests/author/check_author.py            golden, round trips, catalogue, layering
  python3 tests/author/check_author.py --write    regenerate tests/author/fixtures.golden
  python3 tests/author/check_author.py --lean     the terms and the lean: lines against Lean
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

GFORTH = os.environ.get("GFORTH", "gforth")
if "/" in GFORTH:  # the planted faults run Gforth in a copy of the tree
    GFORTH = os.path.abspath(GFORTH)
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
     [(PRINT, "  >r r@ frame-restore swap ok-then? if lf-pf-notes then r> 0 ;",
       "  >r r@ frame-restore drop r> 0 ;")]),
    ("$ swaps function and argument", "any",
     [("src/author/words.fs", ": lfa-two-terms ( a b -- ta tb ) swap lfa>term swap lfa>term ;",
       ": lfa-two-terms ( a b -- ta tb ) lfa>term swap lfa>term ;")]),
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
     [(GROUPS, "  lfa-unread-to lfa-stray dup 0= if 2drop exit then\n"
               "  2dup lfa-token! lfa-stray-code lfa-fail ;", "  drop ;")]),
    ("4: Gforth 1.0's recognizers left as they are", "any",
     [("src/author/runner.fs", "['] lfa-recognize is rec-forth ;", ";")]),
    ("5: an unclosed ( comment", "any",
     [("src/author/words.fs", "[char] ) parse lfa-closed? lfa-e-comment-end lfa-must",
       "[char] ) parse 2drop")]),
    ("5: leading zeros in numeric name parts", "any",
     [(DECLS, "  2dup lfa-leading-zero? 0= lfa-e-bad-name lfa-must\n", "")]),
    ("5: declarations not told apart by name", "any",
     [(DECLS, "  lfa-decl-count 0 ?do dup i lfa-decl-name = if drop true unloop exit then loop"
              " drop\n  false ;", "  drop false ;")]),
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


def check_corpus():
    sys.path.insert(0, "tests/present")
    sys.path.insert(0, "tests/support")
    from present_transport import encode
    from ndjson_preview import preview
    run = subprocess.run([GFORTH, "tests/author/corpus-cases.fs"], stdin=subprocess.DEVNULL,
                         capture_output=True, text=True, timeout=300)
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
LF_LINE_START = ("\\ ", "  ", ":=", "theorem ", "def ", "axiom ", "import-stub ", "end ", "protected ")


def print_lf(export):
    """`leanforth print --lf` of an export: (the text, what it listed on stderr)."""
    run = subprocess.run(["bin/leanforth", "print", "--lf", "--no-manifest", str(export)],
                         stdin=subprocess.DEVNULL, capture_output=True, timeout=300)
    if run.returncode != 0:
        raise Failure(f"print --lf {export}: exit {run.returncode}:\n"
                      + run.stderr.decode("utf-8", "replace"))
    return run.stdout.decode("utf-8"), run.stderr.decode("utf-8")


def lf_terms(text):
    """The declarations the words make of the written text: name -> dumps."""
    with tempfile.TemporaryDirectory() as work:
        path = pathlib.Path(work) / "export.lf"
        path.write_text(text, encoding="utf-8")
        run = subprocess.run([GFORTH, "tests/author/terms.fs", "-e", f's" {path}" terms-run bye'],
                             stdin=subprocess.DEVNULL, capture_output=True, timeout=300)
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
    _, dumps, exported = lean
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
            reference[path.stem] = (printed, dumps, exported)
    return reference


def lean_differences(stem, reference, text):
    printed = reference[stem][0]
    return (compare(stem, printed, forth_lean(text)),
            compare_terms(stem, forth_terms(text), reference[stem]))


def check_lean():
    texts = outputs()
    reference = lean_reference(texts)
    lines = decls = terms = 0
    for stem, (printed, _, _) in reference.items():
        differ_text, differ_terms = lean_differences(stem, reference, texts[stem])
        if differ_terms:
            raise Failure("terms differ from pinned Lean's export:\n" + "\n".join(differ_terms))
        if differ_text:
            raise Failure("lean: lines differ from pinned Lean:\n" + "\n".join(differ_text))
        counted = compared_terms(forth_terms(texts[stem]))
        decls, terms, lines = decls + counted[0], terms + counted[1], lines + len(printed)
    known = sum(len(v) for v in KNOWN.values())
    names = sum(len(v) for v in KNOWN_NAMES.values())
    print(f"authoring words build Lean's terms, term for term: {decls} declarations of "
          f"{len(reference)} fixtures, {terms} terms (statements, proofs, stubs' stated types), "
          "equal to Lean's own (which are protected, binder names and kinds included; "
          f"{names} listed binder name) and to the pinned export (apart from binder names "
          "and kinds, which that exporter merges)")
    print(f"authoring words agree with pinned Lean's #print: {lines} lines "
          f"({known} known printer difference, listed with its reason)")


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
        elif "--faults" in args:
            check_faults()
        else:
            check_golden("--write" in args)
            if "--write" not in args:
                check_catalogue()
                check_layering()
                check_corpus()
                check_lf_files()
    except (Failure, OSError, subprocess.SubprocessError) as error:
        print(f"check_author: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
