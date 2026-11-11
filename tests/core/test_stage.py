#!/usr/bin/env python3
"""Cases of the importer stage (src/import/stage.fs) that need a changed
export: each is written into a temporary folder from a reference export,
loaded with tests/support/compact-load.fs (compact-try, or
compact-try-unchecked where the file has no manifest), and its report
compared with the expected one:

- an expression naming a constant that no declaration has: read ok, then
  sealing is invalid ("unknown constant", the name given), never ok --
  unless it names a recursor Lean's kernel generates for a type of the
  file (P.rec, P.rec_<digits>; ADR 0016 amendment 1), which loads,
  resolved as a name several declarations have (payload 0);
- two declarations of one name and a constant naming it: loaded; both
  declarations are found by the name (the newest, then the one before it
  along the chain) and the constant is resolved to neither (payload 0),
  as ADR 0016 C4 says, so that ADR 0012 E5 decides;
- a file cut cleanly between two lines, and one changed byte, with the
  original's manifest: invalid (the manifest differs), rolled back;
- no manifest beside the file: invalid;
- a reader failure (a reference to a later expression): invalid;
- numbers beyond 32 bits (a numeric name component, a projection's
  index, an inductive type's parameter count): full;
- the pinned Lean version changed: unsupported.

Then the input tier saved and loaded (src/import/snapshot-tier.fs; plan
step SN2), each step in its own Gforth process:

- every reference export (manifest checked) and three other fixtures
  staged and saved by one process, loaded, sealed and saved again by
  another: the same bytes; with LF_OTHER_GFORTH set (for example Gforth
  0.7.3), also written by GFORTH and loaded by the other, and the reverse;
- stage-continue, after a read and after a loaded snapshot: an unknown
  constant of the second read is refused, constants only the first read
  contained are not, and the second read dumps exactly as when staged
  alone; a prefix of an export continued by the whole export gives the
  whole export's saved tier byte for byte.

Usage: GFORTH=path/to/gforth python3 tests/core/test_stage.py [-v]
"""
import os
import pathlib
import shutil
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent.parent
GFORTH = os.environ.get("GFORTH") or str(ROOT / ".tools/gforth/bin/gforth")
if not os.path.isabs(GFORTH) and os.sep in GFORTH:
    GFORTH = str(ROOT / GFORTH)
VERBOSE = "-v" in sys.argv[1:]
IDENTITY = ROOT / "tests/reference/identity.ndjson"
FIXTURE = ROOT / "tests/reference/constant-fixture.ndjson"
BLOCK = ROOT / "tests/core/ndjson-block.ndjson"


def report(path, checked=False, manifest=None):
    """compact-try's report on the export at path."""
    use = f's" {manifest}" compact-manifest-use ' if manifest else ""
    word = "compact-try" if checked else "compact-try-unchecked"
    run = subprocess.run(
        [GFORTH, "tests/support/compact-load.fs", "-e", f'{use}s" {path}" {word} bye'],
        cwd=ROOT, stdin=subprocess.DEVNULL, capture_output=True, text=True, timeout=120)
    if run.returncode != 0 or run.stderr:
        raise AssertionError(f"gforth failed on {path}: {run.stderr.strip()}")
    return run.stdout


def lines(path):
    return path.read_text(encoding="utf-8").splitlines(keepends=True)


def write(folder, name, text_lines):
    path = folder / name
    path.write_text("".join(text_lines), encoding="utf-8")
    return path


def cases(folder):
    """(name, path, checked, manifest, expected substrings, refused substrings)."""
    identity = lines(IDENTITY)
    fixture = lines(FIXTURE)
    block = lines(BLOCK)
    out = []
    # An unknown constant: P (name 2) has no declaration.
    path = write(folder, "unknown.ndjson",
                 identity + ['{"const":{"name":2,"us":[]},"ie":7}\n'])
    out.append(("unknown constant", path, False, None,
                ["why unknown constant", "outcome=1", "culprit=P"], ["ok decls"]))
    # The theorem twice, then a constant naming it.
    path = write(folder, "twice.ndjson",
                 identity + [identity[-1], '{"const":{"name":1,"us":[]},"ie":7}\n'])
    out.append(("duplicate names", path, False, None,
                ["ok decls=2", "declarations=2 found=2", "by text: found=2",
                 "constants=1 wrong=0"], ["outcome="]))
    # The fixture cut after its 21st line, and with one byte changed, each
    # with the whole fixture's manifest.
    manifest = str(FIXTURE) + ".manifest.json"
    path = write(folder, "cut.ndjson", fixture[:21])
    out.append(("truncated", path, True, manifest,
                ["export differs from its manifest", "outcome=1"], ["ok decls"]))
    changed = fixture[:1] + [fixture[1].replace("fixtureId", "fixtureIc")] + fixture[2:]
    path = write(folder, "changed.ndjson", changed)
    out.append(("one byte changed", path, True, manifest,
                ["field sha256", "outcome=1"], ["ok decls"]))
    path = write(folder, "bare.ndjson", fixture)
    out.append(("no manifest", path, True, None,
                ["manifest missing", "outcome=1"], ["ok decls"]))
    # The reader's own failure: an application of an expression not yet read.
    path = write(folder, "forward.ndjson",
                 identity[:-1] + ['{"app":{"arg":1,"fn":9},"ie":7}\n'] + identity[-1:])
    out.append(("bad reference", path, False, None,
                ["why bad reference", "outcome=1"], ["ok decls"]))
    # Numbers beyond 32 bits.
    path = write(folder, "wide-name.ndjson",
                 identity[:-1] + ['{"in":4,"num":{"i":4294967296,"pre":1}}\n'] + identity[-1:])
    out.append(("numeric name beyond 32 bits", path, False, None,
                ["number beyond 32 bits", "outcome=6"], ["ok decls"]))
    path = write(folder, "wide-proj.ndjson",
                 identity[:-1]
                 + ['{"ie":7,"proj":{"idx":4294967296,"struct":1,"typeName":1}}\n']
                 + identity[-1:])
    out.append(("projection index beyond 32 bits", path, False, None,
                ["number beyond 32 bits", "outcome=6"], ["ok decls"]))
    wide = [line.replace('"numParams":0', '"numParams":4294967296', 1)
            if '"inductive"' in line else line for line in block]
    path = write(folder, "wide-type.ndjson", wide)
    out.append(("parameter count beyond 32 bits", path, False, None,
                ["number beyond 32 bits", "outcome=6"], ["ok decls"]))
    # Lean-checked reproducer of a TEMPORARY GAP (review rvKC L1; plan task
    # 5.2.6 closes it): pinned Lean 4.35.0 accepts def Big.<n> : Sort 1 :=
    # Sort 0 for a numeric name part n = 2^32 (wide-cases/big-name.lean,
    # exported by the pinned leanexport), where the stage is full. With
    # 2^32 - 1 the file is staged. Never describe the first as a difference
    # from Lean: when the gap is closed, its expected outcome becomes ok.
    for name, expected, refused in (
            ("big-name", ["number beyond 32 bits", "outcome=6"], ["ok decls"]),
            ("big-name-2p32m1", ["ok decls=1"], ["outcome="])):
        out.append((f"Lean-accepted name part, {name}",
                    ROOT / f"tests/core/wide-cases/{name}.ndjson", False, None,
                    expected, refused))
    # A bound variable's index: the range of C1 (2^20 - 1 and more) is full; one
    # beyond 32 bits no field could hold is invalid (not full). Pinned Lean
    # has no verdict for either: it panics ("too many bound variables",
    # expr.cpp:107-109) at 1048575 (review rvKC L2), so both are refusals.
    for index, name, outcome in ((1048575, "bvar-range", "outcome=6"),
                                 (4294967296, "bvar-wide", "outcome=1")):
        path = write(folder, name + ".ndjson",
                     [line.replace('"bvar":0', f'"bvar":{index}') for line in identity])
        out.append((f"bound variable index {index}", path, False, None,
                    ["handler refused the record", outcome], ["ok decls"]))
    path = write(folder, "lean.ndjson",
                 [identity[0].replace("4.35.0", "4.36.0")] + identity[1:])
    out.append(("another Lean version", path, False, None,
                ["unsupported exporter, format or Lean version", "outcome=5"], ["ok decls"]))
    # ADR 0016 amendment 1: a recursor Lean's kernel generates for a type of
    # the file (B, name 2, a type of the block) may be named without a
    # declaration (B.rec, B.rec_1: loaded, resolved at the check); any other
    # undeclared name is still an unknown constant: another last part, a
    # malformed rec_, or a prefix that names no type (the theorem t, the
    # constructor A.mk).
    def named(pre, text):
        return block + ['{"in":8,"str":{"pre":%d,"str":"%s"}}\n' % (pre, text),
                        '{"const":{"name":8,"us":[]},"ie":3}\n']
    for text in ("rec", "rec_1"):
        path = write(folder, f"generated-{text}.ndjson", named(2, text))
        out.append((f"generated B.{text}", path, False, None,
                    ["ok decls=7", "constants=3 wrong=0"], ["outcome="]))
    # (the culprit is printed by its last part)
    for pre, text, whole in ((2, "recOn", "B.recOn"), (2, "rec_", "B.rec_"),
                             (2, "rec_x", "B.rec_x"), (7, "rec", "t.rec"),
                             (3, "rec", "A.mk.rec")):
        path = write(folder, f"undeclared-{pre}-{text}.ndjson", named(pre, text))
        out.append((f"undeclared {whole}", path, False, None,
                    ["why unknown constant", "outcome=1", f"culprit={text}\n"],
                    ["ok decls"]))
    # The unchanged files load.
    out.append(("identity", IDENTITY, True, None,
                ["ok decls=1", "found=1", "constants=0 wrong=0"], ["outcome="]))
    out.append(("block", BLOCK, False, None,
                ["ok decls=7", "declarations=6 found=6", "constants=2 wrong=0"], ["outcome="]))
    return out


def forth(words, engine=None):
    """Run words after loading tests/support/compact-load.fs; its output."""
    run = subprocess.run(
        [engine or GFORTH, "tests/support/compact-load.fs", "-e", words + " bye"],
        cwd=ROOT, stdin=subprocess.DEVNULL, capture_output=True, text=True, timeout=300)
    if run.returncode != 0 or run.stderr:
        raise AssertionError(f"gforth failed on {words}: {run.stderr.strip()}")
    return run.stdout


SAVED_EXPORTS = sorted((ROOT / "tests/reference").glob("*.ndjson"))
OTHER_EXPORTS = [BLOCK, ROOT / "tests/core/reexport/kinds.ndjson",
                 ROOT / "tests/core/stage-cases/marks.ndjson"]


def saved(export, path, engine=None, checked=True):
    load = "compact-load" if checked else "compact-load-unchecked"
    text = forth(f's" {export}" 12 {load} drop s" {path}" compact-save', engine)
    if "saved=0" not in text:
        raise AssertionError(f"not saved: {export}: {text}")


def resaved(first, second, engine=None):
    return forth(f's" {first}" s" {second}" compact-resave', engine)


def declaration_line(line):
    return not any(key in line for key in ('"in":', '"il":', '"ie":', '"meta"'))


def tier_cases(folder):
    """The input tier saved and loaded, and stage-continue (plan step SN2):
    (name, ok?, detail), each run in its own Gforth process."""
    out = []
    # Saved by one process, loaded, sealed and saved again by another: the
    # same bytes (every section and its SHA-256). LF_OTHER_GFORTH (for
    # example Gforth 0.7.3) loads what GFORTH wrote and the reverse.
    engines = [(None, None)]
    other = os.environ.get("LF_OTHER_GFORTH")
    if other:
        engines += [(None, other), (other, None)]
    exports = [(e, True) for e in SAVED_EXPORTS] + [(e, False) for e in OTHER_EXPORTS]
    for writer, loader in engines:
        for export, checked in exports:
            first, second = folder / "first.tier", folder / "second.tier"
            saved(export, first, writer, checked)
            text = resaved(first, second, loader)
            same = first.read_bytes() == second.read_bytes()
            out.append((f"saved and loaded {export.name} ({writer or 'GFORTH'} -> "
                        f"{loader or 'GFORTH'})", same and "sealed=0" in text, text))
    # stage-continue: an unknown constant of the second read is refused; a
    # constant of the first read the second never contains is not.
    identity, fixture = lines(IDENTITY), lines(FIXTURE)
    unknown = write(folder, "unknown2.ndjson",
                    identity + ['{"const":{"name":2,"us":[]},"ie":7}\n'])
    tier = folder / "a.tier"
    for how, word, extra in (("read", "compact-continue-try", ""),
                             ("snapshot", "compact-snap-continue-try", f' s" {tier}"')):
        text = forth(f's" {FIXTURE}" s" {unknown}"{extra} {word}')
        out.append((f"continued ({how}): unknown constant refused",
                    "outcome=1" in text and "culprit=P" in text, text))
        text = forth(f's" {FIXTURE}" s" {IDENTITY}"{extra} {word}')
        out.append((f"continued ({how}): earlier constants kept",
                    "ok decls=1" in text and "found=1" in text and "wrong=0" in text, text))
        # The second read's records and declarations are its own: dumped
        # through its export maps, as when it is staged alone.
        dump = word.replace("-try", "-dump")
        alone = forth(f's" {IDENTITY}" compact-dump-unchecked')
        text = forth(f's" {FIXTURE}" s" {IDENTITY}"{extra} {dump}')
        out.append((f"continued ({how}): the second read dumps as alone",
                    text == alone and "decl." in text, text))
    # A prefix of an export, then the whole export: the same tier, byte for
    # byte, as the whole staged alone (equal records keep their numbers).
    for export in (BLOCK, ROOT / "tests/core/reexport/kinds.ndjson"):
        whole = lines(export)
        cut = next(i for i, line in enumerate(whole) if declaration_line(line)) + 1
        prefix = write(folder, "prefix.ndjson", whole[:cut])
        alone, joined, snapped = (folder / n for n in ("alone.tier", "joined.tier",
                                                         "snapped.tier"))
        saved(export, alone, checked=False)
        forth(f's" {prefix}" s" {export}" compact-continue-load drop s" {joined}" compact-save')
        forth(f's" {prefix}" s" {export}" s" {tier}" compact-snap-continue-load drop '
              f's" {snapped}" compact-save')
        out.append((f"prefix then whole {export.name}",
                    alone.read_bytes() == joined.read_bytes() == snapped.read_bytes(), ""))
    return out


def main():
    failures = 0
    with tempfile.TemporaryDirectory() as tmp:
        folder = pathlib.Path(tmp)
        all_cases = cases(folder)
        for name, path, checked, manifest, expected, refused in all_cases:
            text = report(path, checked, manifest)
            missing = [e for e in expected if e not in text]
            present = [r for r in refused if r in text]
            if missing or present:
                failures += 1
                print(f"FAIL {name}: missing {missing}, unexpected {present}\n{text}")
            elif VERBOSE:
                print(f"ok   {name}\n{text}")
        tiers = tier_cases(folder)
        for name, good, text in tiers:
            if not good:
                failures += 1
                print(f"FAIL {name}\n{text}")
            elif VERBOSE:
                print(f"ok   {name}")
    if failures:
        print(f"{failures} of {len(all_cases) + len(tiers)} stage cases failed")
        return 1
    print(f"All {len(all_cases)} changed-export cases of the stage and {len(tiers)} "
          "saved-tier and continued-read cases behave as expected.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
